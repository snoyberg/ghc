
{-
  Author: George Karachalias <george.karachalias@cs.kuleuven.be>
-}

{-# OPTIONS_GHC -Wwarn #-}   -- unused variables

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}

module Check ( toTcTypeBag, pprUncovered, checkSingle2, checkMatches2, PmResult ) where

#include "HsVersions.h"

import TmOracle

import HsSyn
import TcHsSyn
import Id
import ConLike
import DataCon
import Name
import TysWiredIn
import TyCon
import SrcLoc
import Util
import BasicTypes
import Outputable
import FastString

-- For the new checker (We need to remove and reorder things)
import DsMonad ( DsM, initTcDsForSolver, getDictsDs)
import TcSimplify( tcCheckSatisfiability )
import TcType ( mkTcEqPred, toTcType, toTcTypeBag )
import Bag
import ErrUtils
import Data.List (find)
import MonadUtils -- MonadIO
import Var (EvVar)
import Type
import UniqSupply -- ( UniqSupply
                  -- , splitUniqSupply      -- :: UniqSupply -> (UniqSupply, UniqSupply)
                  -- , listSplitUniqSupply  -- :: UniqSupply -> [UniqSupply]
                  -- , uniqFromSupply )     -- :: UniqSupply -> Unique
import Control.Monad (liftM3)
import Data.Maybe (isNothing, fromJust)
import DsGRHSs (isTrueLHsExpr)

{-
This module checks pattern matches for:
\begin{enumerate}
  \item Equations that are redundant
  \item Equations with inaccessible right-hand-side
  \item Exhaustiveness
\end{enumerate}

The algorithm used is described in the paper "GADTs meet their match"

    http://people.cs.kuleuven.be/~george.karachalias/papers/gadtpm_ext.pdf

%************************************************************************
%*                                                                      *
\subsection{Pattern Match Check Types}
%*                                                                      *
%************************************************************************
-}

type PmM a = DsM a

data PmConstraint = TmConstraint Id PmExpr -- Term equalities: x ~ e
                  | TyConstraint [EvVar]   -- Type equalities
                  | BtConstraint Id        -- Strictness constraints: x ~ _|_

data Abstraction = P | V   -- Used to parameterise PmPat

type ValAbs  = PmPat 'V -- Value Abstraction
type Pattern = PmPat 'P -- Pattern

{-
data PatVec = PVNil
            | GuardCons Guard          PatVec
            | PatCons   (PmPat PatVec) PatVec

data ValueVec = VNil
              | VCons (PmPat ValueVec) ValueVec

data PmPat rec_pats
  = ConAbs { ...
           , cabs_args :: rec_pats }
  | VarAbs Id
-}

type PatVec   = [Pattern] -- Just a type synonym for pattern vectors ps
type ValueVec = [ValAbs]  -- Just a type synonym for velue   vectors as

-- The difference between patterns (PmPat 'P)
-- and value abstractios (PmPat 'V)
-- is that the patterns can contain guards (GBindAbs)
-- and value abstractions cannot.  Enforced with a GADT.

-- The *arity* of a PatVec [p1,..,pn] is
-- the number of p1..pn that are not Guards

{-  ???
data PmPat p = ConAbs { cabs_args :: [p] }
             | VarAbs

data PmGPat = Guard PatVec Expr
            | NonGuard (PmPat PmGPat)   -- Patterns

newtype ValAbs = VA (PmPat ValAbs)
-}


data PmPat :: Abstraction -> * where
  -- Guard: P <- e (strict by default) Instead of a single P use a list [AsPat]
  GBindAbs { gabs_pats :: PatVec   -- Of arity 1
           , gabs_expr :: PmExpr } :: PmPat 'P

  -- Constructor: K ps
  -- The patterns ps are the ones visible in the source language
  ConAbs   { cabs_con     :: DataCon
           , cabs_arg_tys :: [Type]          -- The univeral arg types, 1-1 with the universal
                                             -- tyvars of the constructor/pattern synonym
                                             --   Use (conLikeResTy pat_con pat_arg_tys) to get
                                             --   the type of the pattern

           , cabs_tvs     :: [TyVar]         -- Existentially bound type variables (tyvars only)
           , cabs_dicts   :: [EvVar]         -- Ditto *coercion variables* and *dictionaries*
           , cabs_args    :: [PmPat abs] } :: PmPat abs

  -- Variable: x
  VarAbs  { vabs_id :: Id } :: PmPat abs

-- data T a where
--     MkT :: forall p q. (Eq p, Ord q) => p -> q -> T [p]
-- or  MkT :: forall p q r. (Eq p, Ord q, [p] ~ r) => p -> q -> T r

{- pats ::= pat1 .. patn
   pat ::= K ex_tvs ev_vars pats arg_tys     -- K is from data type T
                                             -- Pattern has type T ty1 .. tyn
         | var
         | pats <- expr       -- Arity(pats) = 1

   arg_tys ::= ty1 .. tyn
-}


data ValSetAbs   -- Reprsents a set of value vector abstractions
                 -- Notionally each value vector abstraction is a triple (Gamma |- us |> Delta)
                 -- where 'us'    is a ValueVec
                 --       'Delta' is a constraint
  -- INVARIANT VsaInvariant: an empty ValSetAbs is always represented by Empty
  -- INVARIANT VsaArity: the number of Cons's in any path to a leaf is the same
  -- The *arity* of a ValSetAbs is the number of Cons's in any path to a leaf
  = Empty                               -- {}
  | Union ValSetAbs ValSetAbs           -- S1 u S2
  | Singleton                           -- { |- empty |> empty }
  | Constraint [PmConstraint] ValSetAbs -- Extend Delta
  | Cons ValAbs ValSetAbs               -- map (ucon u) vs

{-
%************************************************************************
%*                                                                      *
\subsection{Entry point to the checker: check}
%*                                                                      *
%************************************************************************
-}

type PmResult = ( [[LPat Id]] -- redundant (do not show the guards)
                , [[LPat Id]] -- inaccessible rhs (do not show the guards)
                , [([ValAbs],[PmConstraint])] ) -- missing (to be improved)

initial_uncovered :: [Type] -> DsM ValSetAbs
initial_uncovered tys = do
  us <- getUniqueSupplyM
  cs <- ((:[]) . TyConstraint . bagToList) <$> getDictsDs
  let vsa = zipWith mkPmVar (listSplitUniqSupply us) tys
  return $ mkConstraint cs (foldr Cons Singleton vsa)

{-
%************************************************************************
%*                                                                      *
\subsection{Transform source syntax to *our* syntax}
%*                                                                      *
%************************************************************************
-}

-- -----------------------------------------------------------------------
-- | Utilities

nullaryPmConPat :: DataCon -> PmPat abs
-- Nullary data constructor and nullary type constructor
nullaryPmConPat con = ConAbs { cabs_con = con, cabs_arg_tys = []
                             , cabs_tvs = [], cabs_dicts = [], cabs_args = [] }
truePmPat :: PmPat abs
truePmPat = nullaryPmConPat trueDataCon

falsePmPat :: PmPat abs
falsePmPat = nullaryPmConPat falseDataCon

nilPmPat :: Type -> PmPat abs
nilPmPat ty = mkPmConPat nilDataCon [ty] [] [] []

-- The result wont be a list after the change
mkListPmPat :: Type -> [PmPat abs] -> [PmPat abs] -> [PmPat abs]
mkListPmPat ty xs ys = [ConAbs { cabs_con = consDataCon, cabs_arg_tys = [ty]
                               , cabs_tvs = [], cabs_dicts = []
                               , cabs_args = xs++ys }]

mkPmConPat :: DataCon -> [Type] -> [TyVar] -> [EvVar] -> [PmPat abs] -> PmPat abs
mkPmConPat con arg_tys ex_tvs dicts args
  = ConAbs { cabs_con     = con
           , cabs_arg_tys = arg_tys
           , cabs_tvs     = ex_tvs
           , cabs_dicts   = dicts
           , cabs_args    = args }

-- -----------------------------------------------------------------------
-- | Transform a Pat Id into a list of (PmPat Id) -- Note [Translation to PmPat]

translatePat :: Pat Id -> UniqSM PatVec
translatePat pat = case pat of
  WildPat ty         -> (:[]) <$> mkPmVarSM ty
  VarPat  id         -> return [VarAbs id]
  ParPat p           -> translatePat (unLoc p)
  LazyPat p          -> translatePat (unLoc p) -- COMEHERE: We ignore laziness   for now

  BangPat p          -> translatePat (unLoc p) -- COMEHERE: We ignore strictness for now
                                               -- This might affect the divergence checks?
  AsPat lid p -> do
    ps <- translatePat (unLoc p)
    let idp = VarAbs (unLoc lid)
        g   = GBindAbs ps (PmExprVar (unLoc lid))
    return [idp, g]

  SigPatOut p ty -> translatePat (unLoc p) -- TODO: Use the signature?

  CoPat wrapper p ty -> do
    ps      <- translatePat p
    (xp,xe) <- mkPmId2FormsSM ty {- IS THIS TYPE CORRECT OR IS IT THE OPPOSITE?? -}
    let g = GBindAbs ps $ hsExprToPmExpr $ HsWrap wrapper (unLoc xe)
    return [xp,g]

  -- (n + k)  ===>   x (True <- x >= k) (n <- x-k)
  NPlusKPat n k ge minus -> do
    (xp, xe) <- mkPmId2FormsSM $ idType (unLoc n)
    let ke = noLoc (HsOverLit k)         -- k as located expression
        g1 = GBindAbs [truePmPat]        $ hsExprToPmExpr $ OpApp xe (noLoc ge)    no_fixity ke -- True <- (x >= k)
        g2 = GBindAbs [VarAbs (unLoc n)] $ hsExprToPmExpr $ OpApp xe (noLoc minus) no_fixity ke -- n    <- (x -  k)
    return [xp, g1, g2]

  -- (fun -> pat)   ===>   x (pat <- fun x)
  ViewPat lexpr lpat arg_ty -> do
    (xp,xe) <- mkPmId2FormsSM arg_ty
    ps      <- translatePat (unLoc lpat) -- p translated recursively
    let g  = GBindAbs ps $ hsExprToPmExpr $ HsApp lexpr xe -- p <- f x
    return [xp,g]

  ListPat ps ty Nothing -> do
    foldr (mkListPmPat ty) [nilPmPat ty] <$> translatePatVec (map unLoc ps)

  ListPat lpats elem_ty (Just (pat_ty, to_list)) -> do
    (xp, xe) <- mkPmId2FormsSM pat_ty
    ps       <- translatePatVec (map unLoc lpats) -- list as value abstraction
    let pats = foldr (mkListPmPat elem_ty) [nilPmPat elem_ty] ps
        g  = GBindAbs pats $ hsExprToPmExpr $ HsApp (noLoc to_list) xe -- [...] <- toList x
    return [xp,g]

  ConPatOut { pat_con = L _ (PatSynCon _) } ->
    -- Pattern synonyms have a "matcher" (see Note [Pattern synonym representation] in PatSyn.hs
    -- We should be able to transform (P x y)
    -- to   v (Just (x, y) <- matchP v (\x y -> Just (x,y)) Nothing
    -- That is, a combination of a variable pattern and a guard
    -- But there are complications with GADTs etc, and this isn't done yet
    (:[]) <$> mkPmVarSM (hsPatType pat)

  ConPatOut { pat_con     = L _ (RealDataCon con)
            , pat_arg_tys = arg_tys
            , pat_tvs     = ex_tvs
            , pat_dicts   = dicts
            , pat_args    = ps } -> do
    args <- translateConPatVec con ps
    return [mkPmConPat con arg_tys ex_tvs dicts args]

  NPat lit mb_neg eq -> do
    var <- mkPmIdSM (hsPatType pat)
    let olit  | Just _ <- mb_neg = PmExprNeg  lit -- negated literal
              | otherwise        = PmExprOLit lit -- non-negated literal
        guard = eqTrueExpr (PmExprEq (PmExprVar var) olit)
    return [VarAbs var, guard]

  LitPat lit
    | HsString src s <- lit -> -- If it is a real string convert it to a list of characters
        foldr (mkListPmPat charTy) [nilPmPat charTy] <$>
          translatePatVec (map (LitPat . HsChar src) (unpackFS s))
    | otherwise -> do
        var <- mkPmIdSM (hsPatType pat)
        let guard = eqTrueExpr $ PmExprEq (PmExprVar var) (PmExprLit lit)
        return [VarAbs var, guard]

  PArrPat ps ty -> do
    tidy_ps <-translatePatVec (map unLoc ps)
    let fake_con = parrFakeCon (length ps)
    return [mkPmConPat fake_con [ty] [] [] (concat tidy_ps)]

  TuplePat ps boxity tys -> do
    tidy_ps   <- translatePatVec (map unLoc ps)
    let tuple_con = tupleCon (boxityNormalTupleSort boxity) (length ps)
    return [mkPmConPat tuple_con tys  [] [] (concat tidy_ps)]

  -- --------------------------------------------------------------------------
  -- Not supposed to happen
  ConPatIn {}      -> panic "Check.translatePat: ConPatIn"
  SplicePat {}     -> panic "Check.translatePat: SplicePat"
  QuasiQuotePat {} -> panic "Check.translatePat: QuasiQuotePat"
  SigPatIn {}      -> panic "Check.translatePat: SigPatIn"

translatePatVec :: [Pat Id] -> UniqSM [PatVec] -- Do not concatenate them (sometimes we need them separately)
translatePatVec pats = mapM translatePat pats

translateConPatVec :: DataCon -> HsConPatDetails Id -> UniqSM PatVec
translateConPatVec _ (PrefixCon ps)   = concat <$> translatePatVec (map unLoc ps)
translateConPatVec _ (InfixCon p1 p2) = concat <$> translatePatVec (map unLoc [p1,p2])
translateConPatVec c (RecCon (HsRecFields fs _))
  | null fs   = mapM mkPmVarSM $ dataConOrigArgTys c
  | otherwise = concat <$> translatePatVec (map (unLoc . snd) all_pats)
  where
    -- TODO: The functions below are ugly and they do not care much about types too
    field_pats = map (\lbl -> (lbl, noLoc (WildPat (dataConFieldType c lbl)))) (dataConFieldLabels c)
    all_pats   = foldr (\(L _ (HsRecField id p _)) acc -> insertNm (getName (unLoc id)) p acc)
                       field_pats fs

    insertNm nm p [] = [(nm,p)]
    insertNm nm p (x@(n,_):xs)
      | nm == n    = (nm,p):xs
      | otherwise  = x : insertNm nm p xs

translateMatch :: LMatch Id (LHsExpr Id) -> UniqSM (PatVec,[PatVec])
translateMatch (L _ (Match lpats _ grhss)) = do
  pats'   <- concat <$> translatePatVec pats
  guards' <- mapM translateGuards guards
  return (pats', guards')
  where
    extractGuards :: LGRHS Id (LHsExpr Id) -> [GuardStmt Id]
    extractGuards (L _ (GRHS gs _)) = map unLoc gs

    pats   = map unLoc lpats
    guards = map extractGuards (grhssGRHSs grhss)

-- -----------------------------------------------------------------------
-- | Transform source guards (GuardStmt Id) to PmPats (Pattern)

-- A. What to do with lets?
-- B. write a function hsExprToPmExpr for better results? (it's a yes)

translateGuards :: [GuardStmt Id] -> UniqSM PatVec
translateGuards guards = concat <$> mapM translateGuard guards

translateGuard :: GuardStmt Id -> UniqSM PatVec
translateGuard (BodyStmt e _ _ _) = translateBoolGuard e
translateGuard (LetStmt    binds) = translateLet binds
translateGuard (BindStmt p e _ _) = translateBind p e
translateGuard (LastStmt      {}) = panic "translateGuard LastStmt"
translateGuard (ParStmt       {}) = panic "translateGuard ParStmt"
translateGuard (TransStmt     {}) = panic "translateGuard TransStmt"
translateGuard (RecStmt       {}) = panic "translateGuard RecStmt"

translateLet :: HsLocalBinds Id -> UniqSM PatVec
translateLet binds = return [] -- NOT CORRECT: A let cannot fail so in a way we
  -- are fine with it but it can bind things which we do not bring in scope.
  -- Hence, they are free while they shouldn't. More constraints would make it
  -- more expressive but omitting some is always safe (Is it? Make sure it is)

translateBind :: LPat Id -> LHsExpr Id -> UniqSM PatVec
translateBind (L _ p) e = do
  ps <- translatePat p
  let expr = lhsExprToPmExpr e
  return [GBindAbs ps expr]

translateBoolGuard :: LHsExpr Id -> UniqSM PatVec
translateBoolGuard e
  | Just _ <- isTrueLHsExpr e = return []
    -- The formal thing to do would be to generate (True <- True)
    -- but it is trivial to solve so instead we give back an empty
    -- PatVec for efficiency
  | otherwise = return [GBindAbs [truePmPat] (lhsExprToPmExpr e)]

{-
%************************************************************************
%*                                                                      *
\subsection{Main Pattern Matching Check}
%*                                                                      *
%************************************************************************
-}

-- ----------------------------------------------------------------------------
-- | Process a vector

-- -- covered, uncovered, eliminated
process_guards :: UniqSupply -> [PatVec] -> (ValSetAbs, ValSetAbs, ValSetAbs)
process_guards _us [] = (Singleton, Empty, Empty) -- No guard == Trivially True guard
process_guards us  gs = go us Singleton gs
  where

    -- THINK ABOUT THE BASE CASES, THEY ARE WRONG
    go _usupply missing []       = (Empty, missing, Empty)
    go  usupply missing (gv:gvs) = (mkUnion cs css, uss, mkUnion ds dss)
      where
        (us1, us2, us3, us4) = splitUniqSupply4 usupply

        cs = covered2   us1 Singleton gv missing
        us = uncovered2 us2 Empty     gv missing
        ds = divergent2 us3 Empty     gv missing

        (css, uss, dss) = go us4 us gvs

-- ----------------------------------------------------------------------------
-- ----------------------------------------------------------------------------

--- ----------------------------------------------------------------------------
-- | Main function 1 (covered)

-- covered :: UniqSupply -> PatVec -> ValSetAbs -> ValSetAbs
-- covered us vec missing == covered2 us Singleton vec missing

-- ----------------------------------------------------------------------------
-- | Main function 2 (uncovered)

-- uncovered :: UniqSupply -> PatVec -> ValSetAbs -> ValSetAbs
-- uncovered us vec missing == uncovered2 us Empty vec missing

-- ----------------------------------------------------------------------------
-- | Main function 3 (divergent)

-- divergent :: UniqSupply -> PatVec -> ValSetAbs -> ValSetAbs
-- divergent us vec missing == divergent2 us Empty vec missing

-- ----------------------------------------------------------------------------
-- | Getting some more uniques

-- Do not want an infinite list
splitUniqSupply3 :: UniqSupply -> (UniqSupply, UniqSupply, UniqSupply)
splitUniqSupply3 us = (us1, us2, us3)
  where
    (us1, us') = splitUniqSupply us
    (us2, us3) = splitUniqSupply us'

-- Do not want an infinite list
splitUniqSupply4 :: UniqSupply -> (UniqSupply, UniqSupply, UniqSupply, UniqSupply)
splitUniqSupply4 us = (us1, us2, us3, us4)
  where
    (us1, us2, us') = splitUniqSupply3 us
    (us3, us4)      = splitUniqSupply us'

getUniqueSupplyM3 :: MonadUnique m => m (UniqSupply, UniqSupply, UniqSupply)
getUniqueSupplyM3 = liftM3 (,,) getUniqueSupplyM getUniqueSupplyM getUniqueSupplyM

-- ----------------------------------------------------------------------------
-- | Basic utilities

-- | Get the type out of a PmPat. For guard patterns (ps <- e) we use the type
-- of the first (or the single -WHEREVER IT IS- valid to use?) pattern
pmPatType :: PmPat abs -> Type
pmPatType (GBindAbs { gabs_pats = pats })
  = ASSERT (patVecArity pats == 1) (pmPatType p)
  where Just p = find ((==1) . patternArity) pats
pmPatType (ConAbs { cabs_con = con, cabs_arg_tys = tys })
  = mkTyConApp (dataConTyCon con) tys
pmPatType (VarAbs { vabs_id = x }) = idType x

mkOneConFull :: Id -> UniqSupply -> DataCon -> (ValAbs, [PmConstraint])
--  *  x :: T tys, where T is an algebraic data type
--     NB: in the case of a data familiy, T is the *representation* TyCon
--     e.g.   data instance T (a,b) = T1 a b
--       leads to
--            data TPair a b = T1 a b  -- The "representation" type
--       It is TPair, not T, that is given to mkOneConFull
--
--  * 'con' K is a constructor of data type T
--
-- After instantiating the universal tyvars of K we get
--          K tys :: forall bs. Q => s1 .. sn -> T tys
--
-- Results: ValAbs:          K (y1::s1) .. (yn::sn)
--          [PmConstraint]:  Q, x ~ K y1..yn

mkOneConFull x usupply con = (con_abs, constraints)
  where

    (usupply1, usupply2, usupply3) = splitUniqSupply3 usupply

    res_ty = idType x -- res_ty == TyConApp (dataConTyCon (cabs_con cabs)) (cabs_arg_tys cabs)
    (univ_tvs, ex_tvs, eq_spec, thetas, arg_tys, dc_res_ty) = dataConFullSig con
    data_tc = dataConTyCon con   -- The representation TyCon
    tc_args = case splitTyConApp_maybe res_ty of
                 Just (tc, tys) -> ASSERT( tc == data_tc ) tys
                 Nothing -> pprPanic "mkOneConFull: Not a type application" (ppr res_ty)

    subst1  = zipTopTvSubst univ_tvs tc_args

    -- IS THE SECOND PART OF THE TUPLE THE SET OF FRESHENED EXISTENTIALS? MUST BE
    (subst, ex_tvs') = cloneTyVarBndrs subst1 ex_tvs usupply1

    arguments  = mkConVars usupply2 (substTys subst arg_tys)      -- Constructor arguments (value abstractions)
    theta_cs   = substTheta subst (eqSpecPreds eq_spec ++ thetas) -- All the constraints bound by the constructor

    evvars = zipWith (nameType "oneCon") (listSplitUniqSupply usupply3) theta_cs
    con_abs    = ConAbs { cabs_con     = con
                        , cabs_arg_tys = tc_args
                        , cabs_tvs     = ex_tvs'
                        , cabs_dicts   = evvars
                        , cabs_args    = arguments }

    constraints = [ TmConstraint x (valAbsToPmExpr con_abs)
                  , TyConstraint evvars ] -- Both term and type constraints

-- mkOneConFull :: Id -> UniqSupply -> DataCon -> (ValAbs, [PmConstraint])
-- -- Invariant:  x :: T tys, where T is an algebraic data type
-- mkOneConFull x usupply con = (con_abs, all_cs)
--   where
--     -- Some more uniqSupplies
--     (usupply1, usupply') = splitUniqSupply usupply
--     (usupply2, usupply3) = splitUniqSupply usupply'
-- 
--     -- Instantiate variable with the approproate constructor pattern
--     (_tvs, qs, _arg_tys, res_ty) = dataConSig con -- take the constructor apart
--     con_abs = mkConFull usupply1 con -- (Ki ys), ys fresh
-- 
--     -- All generated/collected constraints
--     ty_eq_ct = TyConstraint [newEqPmM usupply2 (idType x) res_ty]  -- type_eq: tau_x ~ tau (result type of the constructor)
--     tm_eq_ct = TmConstraint x (valAbsToPmExpr con_abs)             -- term_eq: x ~ K ys
--     uniqs_cs = listSplitUniqSupply usupply3 `zip` qs
--     thetas   = map (uncurry (nameType "cconvar")) uniqs_cs         -- constructors_thetas: the Qs from K's sig
--     all_cs   = [tm_eq_ct, ty_eq_ct, TyConstraint thetas]           -- all constraints

mkConVars :: UniqSupply -> [Type] -> [ValAbs] -- ys, fresh with the given type
mkConVars usupply tys = map (uncurry mkPmVar) $
  zip (listSplitUniqSupply usupply) tys

dropNValSetAbs :: Int -> ValSetAbs -> ValSetAbs
dropNValSetAbs n vsa
  | n > 0     = dropNValSetAbs (n-1) (tailValSetAbs vsa)
  | otherwise = vsa

tailValSetAbs :: ValSetAbs -> ValSetAbs
tailValSetAbs Empty               = Empty
tailValSetAbs Singleton           = panic "tailValSetAbs: Singleton"
tailValSetAbs (Union vsa1 vsa2)   = tailValSetAbs vsa1 `mkUnion` tailValSetAbs vsa2
tailValSetAbs (Constraint cs vsa) = cs `mkConstraint` tailValSetAbs vsa
tailValSetAbs (Cons _ vsa)        = vsa -- actual work

wrapK :: DataCon -> ValSetAbs -> ValSetAbs
wrapK con = wrapK_aux (dataConSourceArity con) emptylist
  where
    wrapK_aux :: Int -> DList ValAbs -> ValSetAbs -> ValSetAbs
    wrapK_aux _ _    Empty               = Empty
    wrapK_aux 0 args vsa                 = mkPmConPat con [] [] [] {- FIXME -} (toList args) `mkCons` vsa
    wrapK_aux _ _    Singleton           = panic "wrapK: Singleton"
    wrapK_aux n args (Cons vs vsa)       = wrapK_aux (n-1) (args `snoc` vs) vsa
    wrapK_aux n args (Constraint cs vsa) = cs `mkConstraint` wrapK_aux n args vsa
    wrapK_aux n args (Union vsa1 vsa2)   = wrapK_aux n args vsa1 `mkUnion` wrapK_aux n args vsa2

newtype DList a = DL { unDL :: [a] -> [a] }

toList :: DList a -> [a]
toList = ($[]) . unDL
{-# INLINE toList #-}

emptylist :: DList a
emptylist = DL id
{-# INLINE emptylist #-}

infixl `snoc`
snoc :: DList a -> a -> DList a
snoc xs x = DL (unDL xs . (x:))
{-# INLINE snoc #-}

-- ----------------------------------------------------------------------------
-- | Smart constructors (NB: An empty value set can only be represented as `Empty')

mkConstraint :: [PmConstraint] -> ValSetAbs -> ValSetAbs
-- The smart constructor for Constraint (maintains VsaInvariant)
mkConstraint _cs Empty                = Empty
mkConstraint cs1 (Constraint cs2 vsa) = Constraint (cs1++cs2) vsa -- careful about associativity
mkConstraint cs  other_vsa            = Constraint cs other_vsa

mkUnion :: ValSetAbs -> ValSetAbs -> ValSetAbs
-- The smart constructor for Union (maintains VsaInvariant)
mkUnion Empty vsa = vsa
mkUnion vsa Empty = vsa
mkUnion vsa1 vsa2 = Union vsa1 vsa2

mkCons :: ValAbs -> ValSetAbs -> ValSetAbs
mkCons _ Empty = Empty
mkCons va vsa  = Cons va vsa

isNotEmptyValSetAbs :: ValSetAbs -> Bool
isNotEmptyValSetAbs Empty = False -- Empty the only representation for an empty Value Set Abstraction
isNotEmptyValSetAbs _     = True

valAbsToPmExpr :: ValAbs -> PmExpr
valAbsToPmExpr (VarAbs x)                  = PmExprVar x
valAbsToPmExpr (ConAbs { cabs_con  = c
                       , cabs_args = ps }) = PmExprCon c (map valAbsToPmExpr ps)

eqTrueExpr :: PmExpr -> Pattern
eqTrueExpr expr = GBindAbs [truePmPat] expr

no_fixity :: a -- CHECKME: Can we retrieve the fixity from the operator name?
no_fixity = panic "Check: no fixity"

-- Get all constructors in the family (including given)
allConstructors :: DataCon -> [DataCon]
allConstructors = tyConDataCons . dataConTyCon

mkPmVar :: UniqSupply -> Type -> PmPat abs
mkPmVar usupply ty = VarAbs (mkPmId usupply ty)

mkPmVarSM :: Type -> UniqSM (PmPat abs)
mkPmVarSM ty = flip mkPmVar ty <$> getUniqueSupplyM

mkPmId :: UniqSupply -> Type -> Id
mkPmId usupply ty = mkLocalId name ty
  where
    unique  = uniqFromSupply usupply
    occname = mkVarOccFS (fsLit (show unique))
    name    = mkInternalName unique occname noSrcSpan

mkPmIdSM :: Type -> UniqSM Id
mkPmIdSM ty = flip mkPmId ty <$> getUniqueSupplyM

mkPmId2FormsSM :: Type -> UniqSM (PmPat abs, LHsExpr Id)
mkPmId2FormsSM ty = do
  us <- getUniqueSupplyM
  let x = mkPmId us ty
  return (VarAbs x, noLoc (HsVar x))

-- -----------------------------------------------------------------------
-- | Types and constraints

newEvVar :: Name -> Type -> EvVar
newEvVar name ty = mkLocalId name (toTcType ty)

newEqPmM :: UniqSupply -> Type -> Type -> EvVar
newEqPmM usupply ty1 ty2 = newEvVar name (mkTcEqPred ty1 ty2)
  where
    unique = uniqFromSupply usupply
    name   = mkSystemName unique (mkVarOccFS (fsLit "pmcobox"))

nameType :: String -> UniqSupply -> Type -> EvVar
nameType name usupply ty = newEvVar idname ty
  where
    unique  = uniqFromSupply usupply
    occname = mkVarOccFS (fsLit (name++"_"++show unique))
    idname  = mkInternalName unique occname noSrcSpan

valSetAbsToList :: ValSetAbs -> [([ValAbs],[PmConstraint])]
valSetAbsToList Empty               = []
valSetAbsToList (Union vsa1 vsa2)   = valSetAbsToList vsa1 ++ valSetAbsToList vsa2
valSetAbsToList Singleton           = [([],[])]
valSetAbsToList (Constraint cs vsa) = [(vs, cs ++ cs') | (vs, cs') <- valSetAbsToList vsa]
valSetAbsToList (Cons va vsa)       = [(va:vs, cs) | (vs, cs) <- valSetAbsToList vsa]

splitConstraints :: [PmConstraint] -> ([EvVar], [(Id, PmExpr)], Maybe Id) -- Type constraints, term constraints, forced variables
splitConstraints [] = ([],[],Nothing)
splitConstraints (c : rest)
  = case c of
      TyConstraint cs  -> (cs ++ ty_cs, tm_cs, bot_cs)
      TmConstraint x e -> (ty_cs, (x,e):tm_cs, bot_cs)
      BtConstraint cs  -> ASSERT (isNothing bot_cs) (ty_cs, tm_cs, Just cs) -- NB: Only one x ~ _|_
  where
    (ty_cs, tm_cs, bot_cs) = splitConstraints rest

{-
%************************************************************************
%*                                                                      *
\subsection{The oracles}
%*                                                                      *
%************************************************************************
-}

-- Same interface to check all kinds of different constraints like in the paper
satisfiable :: [PmConstraint] -> PmM Bool
satisfiable constraints = do
  let (ty_cs, tm_cs, bot_cs) = splitConstraints constraints
  sat <- tyOracle (listToBag ty_cs)
  case sat of
    True -> case tmOracle tm_cs of
      Left eq -> return False
      Right (residual, (expr_eqs, mapping)) ->
        let answer = isNothing bot_cs || -- just term eqs ==> OK (success)
                     notNull residual || -- something we cannot reason about -- gives inaccessible while it shouldn't
                     notNull expr_eqs || -- something we cannot reason about
                     notForced (fromJust bot_cs) mapping -- Was not evaluated before
        in  return answer
    False -> return False -- inconsistent type constraints

-- | For coverage & laziness
-- True  => Set may be non-empty
-- False => Set is definitely empty
-- Fact:  anySatValSetAbs s = pruneValSetAbs /= Empty
--        (but we implement it directly for efficiency)
anySatValSetAbs :: ValSetAbs -> PmM Bool
anySatValSetAbs = anySatValSetAbs' []
  where
    anySatValSetAbs' :: [PmConstraint] -> ValSetAbs -> PmM Bool
    anySatValSetAbs' _cs Empty                = return False
    anySatValSetAbs'  cs (Union vsa1 vsa2)    = anySatValSetAbs' cs vsa1 `orM` anySatValSetAbs' cs vsa2
    anySatValSetAbs'  cs Singleton            = satisfiable cs
    anySatValSetAbs'  cs (Constraint cs' vsa) = anySatValSetAbs' (cs' ++ cs) vsa -- in front for faster concatenation
    anySatValSetAbs'  cs (Cons va vsa)        = anySatValSetAbs' cs vsa

    orM m1 m2 = m1 >>= \x ->
      if x then return True else m2

-- | For exhaustiveness check
-- Prune the set by removing unsatisfiable paths
pruneValSetAbs :: ValSetAbs -> PmM ValSetAbs
pruneValSetAbs = pruneValSetAbs' []
  where
    pruneValSetAbs' :: [PmConstraint] -> ValSetAbs -> PmM ValSetAbs
    pruneValSetAbs' _cs Empty = return Empty
    pruneValSetAbs'  cs (Union vsa1 vsa2) = do
      mb_vsa1 <- pruneValSetAbs' cs vsa1
      mb_vsa2 <- pruneValSetAbs' cs vsa2
      return $ mkUnion mb_vsa1 mb_vsa2
    pruneValSetAbs' cs Singleton = do
      sat <- satisfiable cs
      return $ if sat then mkConstraint cs Singleton -- always leave them at the end
                      else Empty
    pruneValSetAbs' cs (Constraint cs' vsa)
      = pruneValSetAbs' (cs' ++ cs) vsa -- in front for faster concatenation
    pruneValSetAbs' cs (Cons va vsa) = do
      mb_vsa <- pruneValSetAbs' cs vsa
      return $ mkCons va mb_vsa

{-
%************************************************************************
%*                                                                      *
\subsection{The type equality oracle (OutsideIn(X) wrapper)}
%*                                                                      *
%************************************************************************

-}

-- -----------------------------------------------------------------------
-- | Interface to the solver
-- This is a hole for a contradiction checker. The actual type must be
-- (Bag EvVar, PmGuard) -> Bool. It should check whether are satisfiable both:
--  * The type constraints
--  * THe term constraints
tyOracle :: Bag EvVar -> PmM Bool
tyOracle evs
  = do { ((_warns, errs), res) <- initTcDsForSolver $ tcCheckSatisfiability evs
       ; case res of
            Just sat -> return sat
            Nothing  -> pprPanic "tyOracle" (vcat $ pprErrMsgBagWithLoc errs) }

{-
%************************************************************************
%*                                                                      *
\subsection{Pretty Printing}
%*                                                                      *
%************************************************************************
-}

pprUncovered :: [([ValAbs],[PmConstraint])] -> SDoc
pprUncovered vsa = vcat (map pprOne vsa)
  where
    pprOne (vs, cs) = ppr vs <+> ptext (sLit "|>") <+> ppr cs

instance Outputable PmConstraint where
  ppr (TmConstraint x expr) = ppr x <+> equals <+> ppr expr
  ppr (TyConstraint theta)  = pprSet $ map idType theta
  ppr (BtConstraint x)      = braces (ppr x <+> ptext (sLit "~") <+> ptext (sLit "_|_"))

instance Outputable (PmPat abs) where
  ppr (GBindAbs pats expr)          = ppr pats <+> ptext (sLit "<-") <+> ppr expr
  ppr (ConAbs { cabs_con  = con
              , cabs_args = args }) = sep [ppr con, pprWithParens args]
  ppr (VarAbs x)                    = ppr x

instance Outputable ValSetAbs where
  ppr = pprValSetAbs

pprWithParens :: [PmPat abs] -> SDoc
pprWithParens pats = sep (map paren_if_needed pats)
  where paren_if_needed p | ConAbs { cabs_args = args } <- p, not (null args) = parens (ppr p)
                          | GBindAbs ps _               <- p, not (null ps)   = parens (ppr p)
                          | otherwise = ppr p

pprValSetAbs :: ValSetAbs -> SDoc
pprValSetAbs = hang (ptext (sLit "Set:")) 2 . vcat . map print_vec . valSetAbsToList
  where
    print_vec (vec, cs) =
      let (ty_cs, tm_cs, bots) = splitConstraints cs
      in  hang (ptext (sLit "vector:") <+> ppr vec <+> ptext (sLit "|>")) 2 $
            vcat [ ptext (sLit "type_cs:") <+> pprSet (map idType ty_cs)
                 , ptext (sLit "term_cs:") <+> ppr tm_cs
                 , ptext (sLit "bottoms:") <+> ppr bots ]

pprSet :: Outputable id => [id] -> SDoc
pprSet lits = braces $ sep $ punctuate comma $ map ppr lits

{-
Note [Pattern match check give up]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
There are some cases where we cannot perform the check. A simple example is
trac #322:
\begin{verbatim}
  f :: Maybe Int -> Int
  f 1 = 1
  f Nothing = 2
  f _ = 3
\end{verbatim}

In this case, the first line is compiled as
\begin{verbatim}
  f x | x == fromInteger 1 = 1
\end{verbatim}

To check this match, we should perform arbitrary computations at compile time
(@fromInteger 1@) which is highly undesirable. Hence, we simply give up by
returning a @Nothing@.
-}


{-
%************************************************************************
%*                                                                      *
\subsection{Sanity Checks}
%*                                                                      *
%************************************************************************
-}

type PmArity = Int

patVecArity :: PatVec -> PmArity
patVecArity = sum . map patternArity

patternArity :: Pattern -> PmArity
patternArity (GBindAbs {}) = 0
patternArity (ConAbs   {}) = 1
patternArity (VarAbs   {}) = 1

-- Should get a default value because an empty set has any arity
-- (We have no value vector abstractions to see)
vsaArity :: PmArity -> ValSetAbs -> PmArity
vsaArity  arity Empty = arity
vsaArity _arity vsa   = ASSERT (allTheSame arities) (head arities)
  where arities = vsaArities vsa

vsaArities :: ValSetAbs -> [PmArity] -- Arity for every path. INVARIANT: All the same
vsaArities Empty              = []
vsaArities (Union vsa1 vsa2)  = vsaArities vsa1 ++ vsaArities vsa2
vsaArities Singleton          = [0]
vsaArities (Constraint _ vsa) = vsaArities vsa
vsaArities (Cons _ vsa)       = [1 + arity | arity <- vsaArities vsa]

allTheSame :: Eq a => [a] -> Bool
allTheSame []     = True
allTheSame (x:xs) = all (==x) xs

{-
%************************************************************************
%*                                                                      *
\subsection{Let's start over, shall we?}
%*                                                                      *
%************************************************************************
-}

--- ----------------------------------------------------------------------------
-- | Main function 1 (covered)

--THE SECOND ARGUMENT IS THE CONT, WHAT TO PLUG AT THE END (GUARDS)
covered2 :: UniqSupply -> ValSetAbs -> PatVec -> ValSetAbs -> ValSetAbs

-- CEmpty (New case because of representation)
covered2 _usupply gvsa _vec Empty = Empty

-- CNil
covered2 _usupply gvsa [] Singleton = gvsa

-- Pure induction (New case because of representation)
covered2 usupply gvsa vec (Union vsa1 vsa2)
  = covered2 usupply1 gvsa vec vsa1 `mkUnion` covered2 usupply2 gvsa vec vsa2
  where (usupply1, usupply2) = splitUniqSupply usupply

-- Pure induction (New case because of representation)
covered2 usupply gvsa vec (Constraint cs vsa)
  = cs `mkConstraint` covered2 usupply gvsa vec vsa

-- CGuard
covered2 usupply gvsa (pat@(GBindAbs p e) : ps) vsa
  = cs `mkConstraint` (tailValSetAbs $ covered2 usupply2 gvsa (p++ps) (VarAbs y `mkCons` vsa))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    y  = mkPmId usupply1 (pmPatType pat)
    cs = [TmConstraint y e]

-- CVar
covered2 usupply gvsa (VarAbs x : ps) (Cons va vsa)
  = va `mkCons` (cs `mkConstraint` covered2 usupply gvsa ps vsa)
  where cs = [TmConstraint x (valAbsToPmExpr va)]

-- CConCon
covered2 usupply gvsa (ConAbs { cabs_con = c1, cabs_args = args1 } : ps)
                (Cons (ConAbs { cabs_con = c2, cabs_args = args2 }) vsa)
  | c1 /= c2  = Empty
  | otherwise = wrapK c1 (covered2 usupply gvsa (args1 ++ ps) (foldr mkCons vsa args2))

-- CConVar
covered2 usupply gvsa (cabs@(ConAbs { cabs_con = con, cabs_args = args }) : ps) (Cons (VarAbs x) vsa)
  = covered2 usupply2 gvsa (cabs : ps) (con_abs `mkCons` (all_cs `mkConstraint` vsa))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    (con_abs, all_cs)    = mkOneConFull x usupply1 con -- if cs empty do not do it

covered2 _usupply _gvsa (ConAbs {} : _) Singleton  = panic "covered2: length mismatch: constructor-sing"
covered2 _usupply _gvsa (VarAbs _  : _) Singleton  = panic "covered2: length mismatch: variable-sing"
covered2 _usupply _gvsa []              (Cons _ _) = panic "covered2: length mismatch: Cons"

-- ----------------------------------------------------------------------------
-- | Main function 2 (uncovered)

uncovered2 :: UniqSupply -> ValSetAbs -> PatVec -> ValSetAbs -> ValSetAbs

-- UEmpty (New case because of representation)
uncovered2 _usupply gvsa _vec Empty = Empty

-- UNil
uncovered2 _usupply gvsa [] Singleton = gvsa

-- Pure induction (New case because of representation)
uncovered2 usupply gvsa vec (Union vsa1 vsa2) = uncovered2 usupply1 gvsa vec vsa1 `mkUnion` uncovered2 usupply2 gvsa vec vsa2
  where (usupply1, usupply2) = splitUniqSupply usupply

-- Pure induction (New case because of representation)
uncovered2 usupply gvsa vec (Constraint cs vsa) = cs `mkConstraint` uncovered2 usupply gvsa vec vsa

-- UGuard
uncovered2 usupply gvsa (pat@(GBindAbs p e) : ps) vsa
  = cs `mkConstraint` (tailValSetAbs $ uncovered2 usupply2 gvsa (p++ps) (VarAbs y `mkCons` vsa))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    y  = mkPmId usupply1 (pmPatType pat)
    cs = [TmConstraint y e]

-- UVar
uncovered2 usupply gvsa (VarAbs x : ps) (Cons va vsa)
  = va `mkCons` (cs `mkConstraint` uncovered2 usupply gvsa ps vsa)
  where cs = [TmConstraint x (valAbsToPmExpr va)]

-- UConCon
uncovered2 usupply gvsa (ConAbs { cabs_con = c1, cabs_args = args1 } : ps)
             (Cons cabs@(ConAbs { cabs_con = c2, cabs_args = args2 }) vsa)
  | c1 /= c2  = cabs `mkCons` vsa
  | otherwise = wrapK c1 (uncovered2 usupply gvsa (args1 ++ ps) (foldr mkCons vsa args2))

-- UConVar
uncovered2 usupply gvsa (cabs@(ConAbs { cabs_con = con, cabs_args = args }) : ps) (Cons (VarAbs x) vsa)
  = uncovered2 usupply2 gvsa (cabs : ps) inst_vsa -- instantiated vsa [x \mapsto K_j ys]
  where
    -- Some more uniqSupplies
    (usupply1, usupply2) = splitUniqSupply usupply

    -- Unfold the variable to all possible constructor patterns
    uniqs_cons = listSplitUniqSupply usupply1 `zip` allConstructors con
    cons_cs    = map (uncurry (mkOneConFull x)) uniqs_cons
    add_one (va,cs) valset = valset `mkUnion` (va `mkCons` (cs `mkConstraint` vsa))
    inst_vsa   = foldr add_one Empty cons_cs

uncovered2 _usupply _gvsa (ConAbs {} : _) Singleton  = panic "uncovered2: length mismatch: constructor-sing"
uncovered2 _usupply _gvsa (VarAbs _  : _) Singleton  = panic "uncovered2: length mismatch: variable-sing"
uncovered2 _usupply _gvsa []              (Cons _ _) = panic "uncovered2: length mismatch: Cons"

-- ----------------------------------------------------------------------------
-- | Main function 3 (divergent)

divergent2 :: UniqSupply -> ValSetAbs -> PatVec -> ValSetAbs -> ValSetAbs

-- DEmpty (New case because of representation)
divergent2 _usupply gvsa _vec Empty = Empty

-- DNil
divergent2 _usupply gvsa [] Singleton = gvsa

-- Pure induction (New case because of representation)
divergent2 usupply gvsa vec (Union vsa1 vsa2) = divergent2 usupply1 gvsa vec vsa1 `mkUnion` divergent2 usupply2 gvsa vec vsa2
  where (usupply1, usupply2) = splitUniqSupply usupply

-- Pure induction (New case because of representation)
divergent2 usupply gvsa vec (Constraint cs vsa) = cs `mkConstraint` divergent2 usupply gvsa vec vsa

-- DGuard
divergent2 usupply gvsa (pat@(GBindAbs p e) : ps) vsa
  = cs `mkConstraint` (tailValSetAbs $ divergent2 usupply2 gvsa (p++ps) (VarAbs y `mkCons` vsa))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    y  = mkPmId usupply1 (pmPatType pat)
    cs = [TmConstraint y e]

-- DVar
divergent2 usupply gvsa (VarAbs x : ps) (Cons va vsa)
  = va `mkCons` (cs `mkConstraint` divergent2 usupply gvsa ps vsa)
  where cs = [TmConstraint x (valAbsToPmExpr va)]

-- DConCon
divergent2 usupply gvsa (ConAbs { cabs_con = c1, cabs_args = args1 } : ps)
                  (Cons (ConAbs { cabs_con = c2, cabs_args = args2 }) vsa)
  | c1 /= c2  = Empty
  | otherwise = wrapK c1 (divergent2 usupply gvsa (args1 ++ ps) (foldr mkCons vsa args2))

-- DConVar [NEEDS WORK]
divergent2 usupply gvsa (cabs@(ConAbs { cabs_con = con, cabs_args = args }) : ps) (Cons (VarAbs x) vsa)
  = Union (Cons (VarAbs x) (Constraint [BtConstraint x] vsa))
          (divergent2 usupply2 gvsa (cabs : ps) (con_abs `mkCons` (all_cs `mkConstraint` vsa)))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    (con_abs, all_cs)    = mkOneConFull x usupply1 con -- if cs empty do not do it

divergent2 _usupply _gvsa (ConAbs {} : _) Singleton  = panic "divergent2: length mismatch: constructor-sing"
divergent2 _usupply _gvsa (VarAbs _  : _) Singleton  = panic "divergent2: length mismatch: variable-sing"
divergent2 _usupply _gvsa []              (Cons _ _) = panic "divergent2: length mismatch: Cons"


-- ----------------------------------------------------------------------------
patVectProc2 :: (PatVec, [PatVec]) -> ValSetAbs -> PmM (Bool, Bool, ValSetAbs) -- Covers? Forces? U(n+1)?
patVectProc2 (vec,gvs) vsa = do
  us <- getUniqueSupplyM
  let (c_def, u_def, d_def) = process_guards us gvs -- default (the continuation)

  (usC, usU, usD) <- getUniqueSupplyM3
  mb_c <- anySatValSetAbs (covered2   usC c_def vec vsa)
  mb_d <- anySatValSetAbs (divergent2 usD d_def vec vsa)
  return (mb_c, mb_d, uncovered2 usU u_def vec vsa)

-- Single pattern binding (let)
checkSingle2 :: Type -> Pat Id -> DsM PmResult
checkSingle2 ty p = do
  let lp = [noLoc p]
  vec <- liftUs (translatePat p)
  vsa <- initial_uncovered [ty]
  (c,d,us) <- patVectProc2 (vec,[]) vsa -- no guards
  let us' = valSetAbsToList us
  return $ case (c,d) of
    (True,  _)     -> ([],   [],   us')
    (False, True)  -> ([],   [lp], us')
    (False, False) -> ([lp], [],   us')

checkMatches2 :: [Type] -> [LMatch Id (LHsExpr Id)] -> DsM PmResult
checkMatches2 tys matches
  | null matches = return ([],[],[])
  | otherwise    = do
      missing <- initial_uncovered tys
      (rs,is,us) <- checkMatches'2 matches missing
      return (map hsLMatchPats rs, map hsLMatchPats is, valSetAbsToList us) -- Turn them into a list so we can take as many as we want

checkMatches'2 :: [LMatch Id (LHsExpr Id)] -> ValSetAbs -> DsM ( [LMatch Id (LHsExpr Id)] -- Redundant matches
                                                               , [LMatch Id (LHsExpr Id)] -- Inaccessible rhs
                                                               , ValSetAbs )              -- Left uncovered
checkMatches'2 [] missing = do
  missing' <- pruneValSetAbs missing
  return ([], [], missing')

checkMatches'2 (m:ms) missing = do
  patterns_n_guards <- liftUs (translateMatch m)
  -- pprInTcRnIf (ptext (sLit "translated") <+> ppr patterns_n_guards)
  (c,  d,  us ) <- patVectProc2 patterns_n_guards missing
  (rs, is, us') <- checkMatches'2 ms us
  return $ case (c,d) of
    (True,  _)     -> (  rs,   is, us')
    (False, True)  -> (  rs, m:is, us')
    (False, False) -> (m:rs,   is, us')

