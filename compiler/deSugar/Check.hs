
{-
  Author: George Karachalias <george.karachalias@cs.kuleuven.be>
-}

{-# OPTIONS_GHC -Wwarn #-}   -- unused variables

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}

module Check ( toTcTypeBag, pprUncovered, check ) where

#include "HsVersions.h"

import TmOracle

import HsSyn
import TcHsSyn
import DsUtils
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


type PmResult = ([EquationInfo], [EquationInfo], [([ValAbs],[PmConstraint])])

{-
%************************************************************************
%*                                                                      *
\subsection{Entry point to the checker: check}
%*                                                                      *
%************************************************************************
-}


-- | Check a single pattern binding
-- ----------------------------------------------------------------------------

type PmResult2 a = ([a], [a], [([ValAbs],[PmConstraint])])

-- Single pattern binding (let)
checkSingle :: Type -> LPat Id -> DsM (PmResult2 (LPat Id))
checkSingle ty p@(L _ pat) = do
  vec <- liftUs (translatePat pat)
  vsa <- initial_uncovered [ty]
  (c,d,us) <- patVectProc vec vsa
  let us' = valSetAbsToList us
  return $ case (c,d) of
    (True,  _)     -> ([],  [],  us')
    (False, True)  -> ([],  [p], us')
    (False, False) -> ([p], [],  us')

-- | Check many matches
-- ----------------------------------------------------------------------------

checkMatches :: [Type] -> [LMatch Id (LHsExpr Id)] -> DsM (PmResult2 (LMatch Id (LHsExpr Id)))
checkMatches tys matches
  | null matches = return ([],[],[])
  | otherwise    = do
      missing <- initial_uncovered tys
      -- matches <- liftUs (translateMatches matches) -- some shadowing here..
      (rs,is,us) <- checkMatches' matches missing
      return (rs, is, valSetAbsToList us) -- Turn them into a list so we can take as many as we want

checkMatches' :: [LMatch Id (LHsExpr Id)] -> ValSetAbs -> DsM ( [LMatch Id (LHsExpr Id)] -- Redundant matches
                                                              , [LMatch Id (LHsExpr Id)] -- Inaccessible rhs
                                                              , ValSetAbs )              -- Left uncovered
checkMatches' [] missing = do
  missing' <- pruneValSetAbs missing
  return ([], [], missing')

checkMatches' (m:ms) missing = do
  (vec, guards) <- liftUs (translateMatch m)
  -- HERE WE NEED SOME KIND OF MAGIC, PROCESS THE GUARDS AND PLUG THEM IN (CPS STYLE)
  (c,  d,  us ) <- patVectProc undefined {- translated -} missing
  (rs, is, us') <- checkMatches' ms us
  return $ case (c,d) of
    (True,  _)     -> (  rs,   is, us')
    (False, True)  -> (  rs, m:is, us')
    (False, False) -> (m:rs,   is, us')

-- | TO BE DELETED PROBABLY
-- ----------------------------------------------------------------------------

check :: [Type] -> [EquationInfo] -> DsM PmResult
check tys eq_info
  | null eq_info = return ([],[],[]) -- If we have an empty match, do not reason at all
  | otherwise = do
      missing    <- initial_uncovered tys
      (rs,is,us) <- check' eq_info missing
      return (rs, is, valSetAbsToList us)

check' :: [EquationInfo] -> ValSetAbs -> DsM ([EquationInfo], [EquationInfo], ValSetAbs)
check' [] missing = do
  missing' <- pruneValSetAbs missing
  return ([], [], missing')
check' (eq:eqs) missing = do
  -- Translate and process current clause
  translated    <- liftUs (translateEqnInfo eq)
  (c,  d,  us ) <- patVectProc translated missing
  (rs, is, us') <- check' eqs us
  return $ case (c,d) of
    (True,  _)     -> (   rs,    is, us')
    (False, True)  -> (   rs, eq:is, us')
    (False, False) -> (eq:rs,    is, us')

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

  LitPat lit -> do
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

-- -----------------------------------------------------------------------
-- Temporary function (drops the guard (MR at the moment))

translateEqnInfo :: EquationInfo -> UniqSM PatVec
translateEqnInfo (EqnInfo { eqn_pats = ps })
  = concat <$> translatePatVec ps

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

translateMatches :: [LMatch Id (LHsExpr Id)] -> UniqSM [(PatVec,[PatVec])] -- every vector with all its guards
translateMatches = mapM translateMatch -- :: [Located (Match Id (LHsExpr Id))]

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

-- -----------------------------------------------------------------------
-- | Transform source expressions (HsExpr Id) to PmExpr

-- The best thing we can do
lhsExprToPmExpr :: LHsExpr Id -> PmExpr
lhsExprToPmExpr (L _ e) = hsExprToPmExpr e

-- The best thing we can do
hsExprToPmExpr :: HsExpr Id -> PmExpr

hsExprToPmExpr (HsVar         x) = PmExprVar x
hsExprToPmExpr (HsOverLit  olit) = PmExprOLit olit
hsExprToPmExpr (HsLit       lit) = PmExprLit lit

hsExprToPmExpr e@(NegApp (L _ neg) neg_e)
  | PmExprOLit ol <- hsExprToPmExpr neg_e = PmExprNeg ol
  | otherwise                             = PmExprOther e
hsExprToPmExpr (HsPar   (L _ e)) = hsExprToPmExpr e

hsExprToPmExpr e@(ExplicitTuple ps boxity)
  | all tupArgPresent ps = PmExprCon tuple_con tuple_args
  | otherwise            = PmExprOther e
  where
    tuple_con  = tupleCon (boxityNormalTupleSort boxity) (length ps)
    tuple_args = [ lhsExprToPmExpr e | L _ (Present e) <- ps ]

hsExprToPmExpr e@(ExplicitList elem_ty mb_ol elems)
  | Nothing <- mb_ol = foldr cons nil (map lhsExprToPmExpr elems)
  | otherwise        = PmExprOther e {- overloaded list: No PmExprApp -}
  where
    cons x xs = PmExprCon consDataCon [x,xs]
    nil       = PmExprCon nilDataCon  []

hsExprToPmExpr (ExplicitPArr _elem_ty elems)
  = PmExprCon (parrFakeCon (length elems)) (map lhsExprToPmExpr elems)

hsExprToPmExpr e@(RecordCon     _ _ _) = PmExprOther e -- HAS TO BE HANDLED -- SIMILAR TO TRANSLATION OF RECORD PATTERNS
                                                       -- hsExprToPmExpr (RecordCon (Located id) PostTcExpr (HsRecordBinds id)
hsExprToPmExpr (HsTick            _ e) = lhsExprToPmExpr e
hsExprToPmExpr (HsBinTick       _ _ e) = lhsExprToPmExpr e
hsExprToPmExpr (HsTickPragma      _ e) = lhsExprToPmExpr e
hsExprToPmExpr (HsSCC             _ e) = lhsExprToPmExpr e -- Drop the additional info (what to do with it?)
hsExprToPmExpr (HsCoreAnn         _ e) = lhsExprToPmExpr e -- Drop the additional info (what to do with it?)
hsExprToPmExpr (ExprWithTySig   e _ _) = lhsExprToPmExpr e -- Drop the additional info (what to do with it?)
hsExprToPmExpr (ExprWithTySigOut  e _) = lhsExprToPmExpr e -- Drop the additional info (what to do with it?)

-- UNHANDLED CASES
hsExprToPmExpr e@(HsLam             _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsLamCase       _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsApp           _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(OpApp       _ _ _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(SectionL        _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(SectionR        _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsCase          _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsIf        _ _ _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsMultiIf       _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsLet           _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsDo          _ _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsBracket         _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsRnBracketOut  _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsTcBracketOut  _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsSpliceE       _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsQuasiQuoteE     _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsWrap          _ _) = PmExprOther e -- Not handled -- Can we do sth better than this?
hsExprToPmExpr e@(HsUnboundVar      _) = PmExprOther e -- Not handled -- Have no idea about what this thing is
hsExprToPmExpr e@(HsProc          _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(HsStatic          _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(ArithSeq      _ _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(PArrSeq         _ _) = PmExprOther e -- Not handled
hsExprToPmExpr e@(RecordUpd _ _ _ _ _) = PmExprOther e -- Not handled

-- IMPOSSIBLE CASES
hsExprToPmExpr e@(HsIPVar           _) = pprPanic "hsTomPmExpr:" (ppr e)
hsExprToPmExpr e@(HsArrApp  _ _ _ _ _) = pprPanic "hsTomPmExpr:" (ppr e)
hsExprToPmExpr e@(HsArrForm     _ _ _) = pprPanic "hsTomPmExpr:" (ppr e)
hsExprToPmExpr e@EWildPat              = pprPanic "hsTomPmExpr:" (ppr e)
hsExprToPmExpr e@(EAsPat          _ _) = pprPanic "hsTomPmExpr:" (ppr e)
hsExprToPmExpr e@(EViewPat        _ _) = pprPanic "hsTomPmExpr:" (ppr e)
hsExprToPmExpr e@(ELazyPat          _) = pprPanic "hsTomPmExpr:" (ppr e)
hsExprToPmExpr e@(HsType            _) = pprPanic "hsTomPmExpr:" (ppr e)

{-
%************************************************************************
%*                                                                      *
\subsection{Main Pattern Matching Check}
%*                                                                      *
%************************************************************************
-}

-- ----------------------------------------------------------------------------
-- | Process a vector

patVectProc :: PatVec -> ValSetAbs -> PmM (Bool, Bool, ValSetAbs) -- Covers? Forces? U(n+1)?
patVectProc vec vsa = do
  usC <- getUniqueSupplyM
  usU <- getUniqueSupplyM
  usD <- getUniqueSupplyM
  -- mb_c <- anySatValSetAbs (covered   usC vec vsa)
  -- mb_d <- anySatValSetAbs (divergent usD vec vsa)

  -- pprInTcRnIf (ptext (sLit "INPUT UNCOVERED SET:")   <+> ppr vsa)
  -- pprInTcRnIf (ptext (sLit "VECTOR TO CHECK:") <+> ppr vec)

  let css = (covered   usC vec vsa)
  mb_c <- anySatValSetAbs css
  -- pprInTcRnIf (ptext (sLit "COVERED SET:")   <+> ppr css)
  -- pprInTcRnIf (ptext (sLit "SOLVER RESULT:") <+> ppr mb_c)

  let dss = (divergent usD vec vsa)
  mb_d <- anySatValSetAbs dss
  -- pprInTcRnIf (ptext (sLit "DIVERGENT SET:")   <+> ppr dss)
  -- pprInTcRnIf (ptext (sLit "SOLVER RESULT:") <+> ppr mb_d)

  return (mb_c, mb_d, uncovered usU vec vsa)


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

        cs = covered   us1 gv missing
        us = uncovered us2 gv missing
        ds = divergent us3 gv missing

        (css, uss, dss) = go us4 us gvs


--- ----------------------------------------------------------------------------
data WhatToDo = WTD { wtd_empty    :: ValSetAbs              -- What to return at the end of the vector
                    , wtd_mismatch :: ValSetAbs -> ValSetAbs -- ConCon case: what if there is a mismatch?
                    , wtd_cons     :: UniqSupply
                                   -> Pattern -> DataCon -> PatVec
                                   -> Id -> ValSetAbs -> ValSetAbs }

wtdC, wtdU, wtdD :: WhatToDo
wtdC = WTD { wtd_empty = Singleton, wtd_mismatch = const Empty, wtd_cons = consC wtdC }
wtdU = WTD { wtd_empty = Empty,     wtd_mismatch = id,          wtd_cons = consU wtdU }
wtdD = WTD { wtd_empty = Empty,     wtd_mismatch = const Empty, wtd_cons = consD wtdD }

traverse_vsa :: WhatToDo -> UniqSupply -> PatVec -> ValSetAbs -> ValSetAbs
traverse_vsa wtd us []                  vsa = ASSERT( vsaArity 0 vsa == 0 ) vsa
traverse_vsa wtd us (GBindAbs p e : ps) vsa = traverse_guard wtd us p e ps vsa
traverse_vsa wtd us (non_gd : ps)       vsa = traverse_non_gd wtd us non_gd ps vsa

traverse_non_gd :: WhatToDo -> UniqSupply -> Pattern -> PatVec -> ValSetAbs -> ValSetAbs
traverse_non_gd wtd us non_gd ps vsa =
  case vsa of
    Empty             -> Empty
    Singleton         -> wtd_empty wtd
    Union vsa1 vsa2   -> let (us1, us2) = splitUniqSupply us
                         in  mkUnion (traverse_non_gd wtd us1 non_gd ps vsa1)
                                     (traverse_non_gd wtd us2 non_gd ps vsa2)
    Constraint cs vsa -> mkConstraint cs (traverse_non_gd wtd us non_gd ps vsa)
    Cons va vsa       -> traverse_cons wtd us non_gd ps va vsa

traverse_guard :: WhatToDo -> UniqSupply
               -> PatVec -> PmExpr -- ps <- e
               -> PatVec -> ValSetAbs -> ValSetAbs
traverse_guard wtd us p e ps vsa
  = mkConstraint [TmConstraint y e] . tailValSetAbs
  $ traverse_vsa wtd us2 (p++ps) (VarAbs y `mkCons` vsa)
  where
    (us1, us2) = splitUniqSupply us
    y  = mkPmId us1 (pmPatType (GBindAbs p e))

traverse_cons :: WhatToDo -> UniqSupply
              -> Pattern  -> PatVec
              -> ValAbs   -> ValSetAbs
              -> ValSetAbs
traverse_cons wtd us p ps va vsa
  = case p of
      VarAbs x -> mkCons va $ mkConstraint [TmConstraint x (valAbsToPmExpr va)]
                            $ traverse_vsa wtd us ps vsa
      ConAbs { cabs_con = c1, cabs_args = args1 } -> case va of
        ConAbs { cabs_con = c2, cabs_args = args2 }
          | c1 /= c2  -> wtd_mismatch wtd (mkCons va vsa)
          | otherwise -> wrapK c1 $ traverse_vsa wtd us (args1 ++ ps) (foldr mkCons vsa args2)
        VarAbs x -> (wtd_cons wtd) us p c1 ps x vsa
      GBindAbs {} -> panic "traverse_cons: guard"

consC :: WhatToDo -> UniqSupply -> Pattern -> DataCon -> PatVec -> Id -> ValSetAbs -> ValSetAbs
consC wtd us cabs con ps x vsa
  = traverse_cons wtd us2 cabs ps con_abs (mkConstraint all_cs vsa)
  where
    (us1, us2)        = splitUniqSupply us
    (con_abs, all_cs) = mkOneConFull x us1 con

consU :: WhatToDo -> UniqSupply -> Pattern -> DataCon -> PatVec -> Id -> ValSetAbs -> ValSetAbs
consU wtd us cabs con ps x vsa
  = traverse_non_gd wtd us2 cabs ps inst_vsa
  where
    (us1, us2) = splitUniqSupply us
    cons_cs    = zipWith (mkOneConFull x) (listSplitUniqSupply us1) (allConstructors con)
    add_one (va,cs) valset = mkUnion valset $ mkCons va $ mkConstraint cs vsa
    inst_vsa   = foldr add_one Empty cons_cs

consD :: WhatToDo -> UniqSupply -> Pattern -> DataCon -> PatVec -> Id -> ValSetAbs -> ValSetAbs
consD wtd us cabs con ps x vsa
  = mkUnion (mkCons (VarAbs x) (mkConstraint [BtConstraint x] vsa))
            (traverse_cons wtd us2 cabs ps con_abs (mkConstraint all_cs vsa))
  where
    (us1, us2)        = splitUniqSupply us
    (con_abs, all_cs) = mkOneConFull x us1 con

-- ----------------------------------------------------------------------------
-- ----------------------------------------------------------------------------

--- ----------------------------------------------------------------------------
-- | Main function 1 (covered)

covered :: UniqSupply -> PatVec -> ValSetAbs -> ValSetAbs

-- CEmpty (New case because of representation)
covered _usupply _vec Empty = Empty

-- CNil
covered _usupply [] Singleton = Singleton

-- Pure induction (New case because of representation)
covered usupply vec (Union vsa1 vsa2)
  = covered usupply1 vec vsa1 `mkUnion` covered usupply2 vec vsa2
  where (usupply1, usupply2) = splitUniqSupply usupply

-- Pure induction (New case because of representation)
covered usupply vec (Constraint cs vsa)
  = cs `mkConstraint` covered usupply vec vsa

-- CGuard
covered usupply (pat@(GBindAbs p e) : ps) vsa
  = cs `mkConstraint` (tailValSetAbs $ covered usupply2 (p++ps) (VarAbs y `mkCons` vsa))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    y  = mkPmId usupply1 (pmPatType pat)
    cs = [TmConstraint y e]

-- CVar
covered usupply (VarAbs x : ps) (Cons va vsa)
  = va `mkCons` (cs `mkConstraint` covered usupply ps vsa)
  where cs = [TmConstraint x (valAbsToPmExpr va)]

-- CConCon
covered usupply (ConAbs { cabs_con = c1, cabs_args = args1 } : ps)
          (Cons (ConAbs { cabs_con = c2, cabs_args = args2 }) vsa)
  | c1 /= c2  = Empty
  | otherwise = wrapK c1 (covered usupply (args1 ++ ps) (foldr mkCons vsa args2))

-- CConVar
covered usupply (cabs@(ConAbs { cabs_con = con, cabs_args = args }) : ps) (Cons (VarAbs x) vsa)
  = covered usupply2 (cabs : ps) (con_abs `mkCons` (all_cs `mkConstraint` vsa))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    (con_abs, all_cs)    = mkOneConFull x usupply1 con -- if cs empty do not do it

covered _usupply (ConAbs {} : _) Singleton  = panic "covered: length mismatch: constructor-sing"
covered _usupply (VarAbs _  : _) Singleton  = panic "covered: length mismatch: variable-sing"
covered _usupply []               (Cons _ _) = panic "covered: length mismatch: Cons"

-- ----------------------------------------------------------------------------
-- | Main function 2 (uncovered)

uncovered :: UniqSupply -> PatVec -> ValSetAbs -> ValSetAbs

-- UEmpty (New case because of representation)
uncovered _usupply _vec Empty = Empty

-- UNil
uncovered _usupply [] Singleton = Empty

-- Pure induction (New case because of representation)
uncovered usupply vec (Union vsa1 vsa2) = uncovered usupply1 vec vsa1 `mkUnion` uncovered usupply2 vec vsa2
  where (usupply1, usupply2) = splitUniqSupply usupply

-- Pure induction (New case because of representation)
uncovered usupply vec (Constraint cs vsa) = cs `mkConstraint` uncovered usupply vec vsa

-- UGuard
uncovered usupply (pat@(GBindAbs p e) : ps) vsa
  = cs `mkConstraint` (tailValSetAbs $ uncovered usupply2 (p++ps) (VarAbs y `mkCons` vsa))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    y  = mkPmId usupply1 (pmPatType pat)
    cs = [TmConstraint y e]

-- UVar
uncovered usupply (VarAbs x : ps) (Cons va vsa)
  = va `mkCons` (cs `mkConstraint` uncovered usupply ps vsa)
  where cs = [TmConstraint x (valAbsToPmExpr va)]

-- UConCon
uncovered usupply (ConAbs { cabs_con = c1, cabs_args = args1 } : ps)
       (Cons cabs@(ConAbs { cabs_con = c2, cabs_args = args2 }) vsa)
  | c1 /= c2  = cabs `mkCons` vsa
  | otherwise = wrapK c1 (uncovered usupply (args1 ++ ps) (foldr mkCons vsa args2))

-- UConVar
uncovered usupply (cabs@(ConAbs { cabs_con = con, cabs_args = args }) : ps) (Cons (VarAbs x) vsa)
  = uncovered usupply2 (cabs : ps) inst_vsa -- instantiated vsa [x \mapsto K_j ys]
  where
    -- Some more uniqSupplies
    (usupply1, usupply2) = splitUniqSupply usupply

    -- Unfold the variable to all possible constructor patterns
    uniqs_cons = listSplitUniqSupply usupply1 `zip` allConstructors con
    cons_cs    = map (uncurry (mkOneConFull x)) uniqs_cons
    add_one (va,cs) valset = valset `mkUnion` (va `mkCons` (cs `mkConstraint` vsa))
    inst_vsa   = foldr add_one Empty cons_cs

uncovered _usupply (ConAbs {} : _) Singleton  = panic "uncovered: length mismatch: constructor-sing"
uncovered _usupply (VarAbs _  : _) Singleton  = panic "uncovered: length mismatch: variable-sing"
uncovered _usupply []               (Cons _ _) = panic "uncovered: length mismatch: Cons"

-- ----------------------------------------------------------------------------
-- | Main function 3 (divergent)

divergent :: UniqSupply -> PatVec -> ValSetAbs -> ValSetAbs

-- DEmpty (New case because of representation)
divergent _usupply _vec Empty = Empty

-- DNil
divergent _usupply [] Singleton = Empty

-- Pure induction (New case because of representation)
divergent usupply vec (Union vsa1 vsa2) = divergent usupply1 vec vsa1 `mkUnion` divergent usupply2 vec vsa2
  where (usupply1, usupply2) = splitUniqSupply usupply

-- Pure induction (New case because of representation)
divergent usupply vec (Constraint cs vsa) = cs `mkConstraint` divergent usupply vec vsa

-- DGuard
divergent usupply (pat@(GBindAbs p e) : ps) vsa
  = cs `mkConstraint` (tailValSetAbs $ divergent usupply2 (p++ps) (VarAbs y `mkCons` vsa))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    y  = mkPmId usupply1 (pmPatType pat)
    cs = [TmConstraint y e]

-- DVar
divergent usupply (VarAbs x : ps) (Cons va vsa)
  = va `mkCons` (cs `mkConstraint` divergent usupply ps vsa)
  where cs = [TmConstraint x (valAbsToPmExpr va)]

-- DConCon
divergent usupply (ConAbs { cabs_con = c1, cabs_args = args1 } : ps)
            (Cons (ConAbs { cabs_con = c2, cabs_args = args2 }) vsa)
  | c1 /= c2  = Empty
  | otherwise = wrapK c1 (divergent usupply (args1 ++ ps) (foldr mkCons vsa args2))

-- DConVar [NEEDS WORK]
divergent usupply (cabs@(ConAbs { cabs_con = con, cabs_args = args }) : ps) (Cons (VarAbs x) vsa)
  = Union (Cons (VarAbs x) (Constraint [BtConstraint x] vsa))
          (divergent usupply2 (cabs : ps) (con_abs `mkCons` (all_cs `mkConstraint` vsa)))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    (con_abs, all_cs)    = mkOneConFull x usupply1 con -- if cs empty do not do it

divergent _usupply (ConAbs {} : _) Singleton  = panic "divergent: length mismatch: constructor-sing"
divergent _usupply (VarAbs _  : _) Singleton  = panic "divergent: length mismatch: variable-sing"
divergent _usupply []               (Cons _ _) = panic "divergent: length mismatch: Cons"

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

-- | To replace mkConFull.
mkConVars :: UniqSupply -> [Type] -> [ValAbs] -- ys, fresh with the given type
mkConVars usupply tys = map (uncurry mkPmVar) $
  zip (listSplitUniqSupply usupply) tys


mkConFull :: UniqSupply -> DataCon -> ValAbs
mkConFull usupply con = mkPmConPat con [] [] [] {- FIXME -} args
  where
    uniqs_tys = listSplitUniqSupply usupply `zip` dataConOrigArgTys con
    args      = map (uncurry mkPmVar) uniqs_tys

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

mkPmId2Forms :: UniqSupply -> Type -> (PmPat abs, LHsExpr Id)
mkPmId2Forms usupply ty = (VarAbs x, noLoc (HsVar x))
  where x = mkPmId usupply ty

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
  ppr (TyConstraint theta)  = empty -- pprSet $ map idType theta
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

