
{-
  Author: George Karachalias <george.karachalias@cs.kuleuven.be>
-}

{-# OPTIONS_GHC -Wwarn #-}   -- unused variables

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures #-}

module Check ( toTcTypeBag, pprUncovered, check ) where

#include "HsVersions.h"

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
import Unify( tcMatchTys )

-- For the new checker (We need to remove and reorder things)
import DsMonad ( DsM, initTcDsForSolver, getDictsDs, getSrcSpanDs)
import TcSimplify( tcCheckSatisfiability )
import UniqSupply (MonadUnique(..))
import TcType ( mkTcEqPred, toTcType, toTcTypeBag )
import VarSet
import Bag
import ErrUtils
import TcMType (genInstSkolTyVarsX)
import IOEnv (tryM, failM)

import Data.Maybe (isJust)
import Control.Monad ( when, forM, zipWithM, liftM, liftM2, liftM3 )

import MonadUtils -- MonadIO
import Var (EvVar)
import Type

import TcRnTypes  ( pprInTcRnIf ) -- Shouldn't be here
import TysPrim    ( anyTy )       -- Shouldn't be here
import UniqSupply -- ( UniqSupply
                  -- , splitUniqSupply      -- :: UniqSupply -> (UniqSupply, UniqSupply)
                  -- , listSplitUniqSupply  -- :: UniqSupply -> [UniqSupply]
                  -- , uniqFromSupply )     -- :: UniqSupply -> Unique

-- For the term solver
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class (lift)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (foldl')
import Data.Maybe (isNothing, fromJust)
import Control.Arrow (first, second)
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

-- | Expressions the solver supports (It should have been (HsExpr Id) but
-- our term solver cannot handle all of them, so we lift it to PmExpr instead.
data PmExpr = PmExprVar   Id
            | PmExprCon   DataCon [PmExpr]
              -- | We should probably add the following as well
              --     , cabs_arg_tys :: [Type]          -- The univeral arg types, 1-1 with the universal
              --                                       -- tyvars of the constructor/pattern synonym
              --     , cabs_tvs     :: [TyVar]         -- Existentially bound type variables (tyvars only)
              --     , cabs_dicts   :: [EvVar]         -- Ditto *coercion variables* and *dictionaries*
            | PmExprLit   HsLit
            | PmExprOLit  (HsOverLit Id)
            | PmExprNeg   (HsOverLit Id) -- Syntactic negation
            | PmExprEq    PmExpr PmExpr  -- Syntactic equality
            | PmExprOther (HsExpr Id)    -- NOTE [PmExprOther in PmExpr]

-- decomopose (PmExprVar x) (PmExprVar y) = Just (x~y)
-- decompose _ _ = Nothing


{-
%************************************************************************
%*                                                                      *
\subsection{Entry point to the checker: check}
%*                                                                      *
%************************************************************************
-}

check :: [Type] -> [EquationInfo] -> DsM PmResult
check tys eq_info
  | null eq_info = return ([],[],[]) -- If we have an empty match, do not reason at all
  | otherwise = do
      usupply    <- getUniqueSupplyM
      (rs,is,us) <- check' eq_info (initial_uncovered usupply tys)
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

initial_uncovered :: UniqSupply -> [Type] -> ValSetAbs
initial_uncovered usupply tys = foldr Cons Singleton val_abs_vec
  where
    uniqs       = listSplitUniqSupply usupply
    val_abs_vec = zipWith mkPmVar uniqs tys

{-
%************************************************************************
%*                                                                      *
\subsection{Transform source patterns to pattern abstractions}
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
    let g = GBindAbs ps $ PmExprOther $ HsWrap wrapper (unLoc xe)
    return [xp,g]

  -- (n + k)  ===>   x (True <- x >= k) (n <- x-k)
  NPlusKPat n k ge minus -> do
    (xp, xe) <- mkPmId2FormsSM $ idType (unLoc n)
    let ke = noLoc (HsOverLit k)         -- k as located expression
        g1 = GBindAbs [truePmPat]        $ PmExprOther $ OpApp xe (noLoc ge)    no_fixity ke -- True <- (x >= k)
        g2 = GBindAbs [VarAbs (unLoc n)] $ PmExprOther $ OpApp xe (noLoc minus) no_fixity ke -- n    <- (x -  k)
    return [xp, g1, g2]

  -- (fun -> pat)   ===>   x (pat <- fun x)
  ViewPat lexpr lpat arg_ty -> do
    (xp,xe) <- mkPmId2FormsSM arg_ty
    ps      <- translatePat (unLoc lpat) -- p translated recursively
    let g  = GBindAbs ps $ PmExprOther $ HsApp lexpr xe -- p <- f x
    return [xp,g]

  ListPat ps ty Nothing -> do
    foldr (mkListPmPat ty) [nilPmPat ty] <$> translatePatVec (map unLoc ps)

  ListPat lpats elem_ty (Just (pat_ty, to_list)) -> do
    (xp, xe) <- mkPmId2FormsSM pat_ty
    ps       <- translatePatVec (map unLoc lpats) -- list as value abstraction
    let pats = foldr (mkListPmPat elem_ty) [nilPmPat elem_ty] ps
        g  = GBindAbs pats $ PmExprOther $ HsApp (noLoc to_list) xe -- [...] <- toList x
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

-- -----------------------------------------------------------------------
-- Temporary function (drops the guard (MR at the moment))
translateEqnInfo :: EquationInfo -> UniqSM PatVec
translateEqnInfo (EqnInfo { eqn_pats = ps })
  = concat <$> translatePatVec ps
-- -----------------------------------------------------------------------

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
  mb_c <- anySatValSetAbs (covered   usC vec vsa)
  mb_d <- anySatValSetAbs (divergent usD vec vsa)
  return (mb_c, mb_d, uncovered usU vec vsa)

-- ----------------------------------------------------------------------------
-- | Main function 1 (covered)

covered :: UniqSupply -> PatVec -> ValSetAbs -> ValSetAbs

-- | TODO: After you change the representation of patterns
-- traverse :: WhatToTo -> UniqSupply -> ValSetAbs -> ValSetAbs
-- 
-- data WhatToTo = WTD { wtd_empty :: Bool      -- True <=> return Singleton
--                                              -- False <=> return Empty
--                     , wtd_mismatch :: Bool   -- True  <=> return argument VSA
--                                              -- False <=> return Empty
--                     , wtd_cons :: PatVec -> ValAbs -> ValSetAbs -> ValSetAbs }
-- traverse f us [] vsa  = ...
-- traverse f us (Guard .. : ps) vsa = ..
-- traverse f us (non-gd : ps) vsa = traverse_non_gd f us non_gd ps vs


--   = case vsa of
--      Empty             -> Empty
--      Singleton         -> ASSERT( null pv ) Singleton
--      Union vsa1 vsa2   -> Union (traverse f us1 vsa1) (traverse f us2 vsa2)
--      Constraint cs vsa -> mkConstraint cs (traverse f us vsa)
--      Cons va vsa       -> traverseCons f us pv va vsa

-- traverse2 f us (p gs : pv) va vsa = ....
-- 
-- traverse2 f us (x    : pv) va vsa = ....
-- traverse2 f us (p gd : pv) va vsa = ....

-- 
-- 
-- covered pv us vsa = traverse (coveredCons pv) us vsa


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
covered usupply (GBindAbs p e : ps) vsa
  | vsa' <- tailValSetAbs $ covered usupply2 (p++ps) (VarAbs y `mkCons` vsa)
  = cs `mkConstraint` vsa'
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    y  = mkPmId usupply1 anyTy -- CHECKME: Which type to use?
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
uncovered usupply (GBindAbs p e : ps) vsa
  = cs `mkConstraint` (tailValSetAbs $ uncovered usupply2 (p++ps) (VarAbs y `mkCons` vsa))
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    y  = mkPmId usupply1 anyTy -- CHECKME: Which type to use?
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
divergent usupply (GBindAbs p e : ps) vsa
  | vsa' <- tailValSetAbs $ divergent usupply2 (p++ps) (VarAbs y `mkCons` vsa)
  = cs `mkConstraint` vsa'
  where
    (usupply1, usupply2) = splitUniqSupply usupply
    y  = mkPmId usupply1 anyTy -- CHECKME: Which type to use?
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
-- | Basic utilities

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

    (usupply1, usupply') = splitUniqSupply usupply
    (usupply2, usupply3) = splitUniqSupply usupply'

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
  -- sat <- tyOracle (listToBag ty_cs)
  sat <- return True -- Leave it like this until you fix type constraint generation
  case sat of
    True -> case tmOracle tm_cs of
      Left eq -> pprInTcRnIf (ptext (sLit "this is inconsistent:") <+> ppr eq) >> return False
      Right (residual, (expr_eqs, mapping)) ->
        let answer = isNothing bot_cs || -- just term eqs ==> OK (success)
                     notNull residual || -- something we cannot reason about -- gives inaccessible while it shouldn't
                     notNull expr_eqs || -- something we cannot reason about
                     isForced (fromJust bot_cs) mapping
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

-- | Keep as a guide
-- checkTyPmPat :: PmPat Id -> Type -> PmM (Bag EvVar) -- check a type and a set of constraints
-- checkTyPmPat (PmGuardPat  _) _ = panic "checkTyPmPat: PmGuardPat"
-- checkTyPmPat (PmVarPat {})   _ = return emptyBag
-- checkTyPmPat (PmLitPat {})   _ = return emptyBag
-- checkTyPmPat (PmLitCon {})   _ = return emptyBag
-- checkTyPmPat (PmConPat con args) res_ty = do
--   let (univ_tvs, ex_tvs, eq_spec, thetas, arg_tys, dc_res_ty) = dataConFullSig con
--       data_tc = dataConTyCon con   -- The representation TyCon
--       mb_tc_args = case splitTyConApp_maybe res_ty of
--                      Nothing -> Nothing
--                      Just (res_tc, res_tc_tys)
--                        | Just (fam_tc, fam_args, _) <- tyConFamInstSig_maybe data_tc
--                        , let fam_tc_tvs = tyConTyVars fam_tc
--                        -> ASSERT( res_tc == fam_tc )
--                           case tcMatchTys (mkVarSet fam_tc_tvs) fam_args res_tc_tys of
--                             Just fam_subst -> Just (map (substTyVar fam_subst) fam_tc_tvs)
--                             Nothing        -> Nothing
--                        | otherwise
--                        -> ASSERT( res_tc == data_tc ) Just res_tc_tys
-- 
--   loc <- getSrcSpanDs
--   (subst, res_eq) <- case mb_tc_args of
--              Nothing  -> -- The context type doesn't have a type constructor at the head.
--                          -- so generate an equality.  But this doesn't really work if there
--                          -- are kind variables involved
--                          do (subst, _) <- genInstSkolTyVars loc univ_tvs
--                             res_eq <- newEqPmM (substTy subst dc_res_ty) res_ty
--                             return (subst, unitBag res_eq)
--              Just tys -> return (zipTopTvSubst univ_tvs tys, emptyBag)
-- 
--   (subst, _) <- genInstSkolTyVarsX loc subst ex_tvs
--   arg_cs     <- checkTyPmPatVec args (substTys subst arg_tys)
--   theta_cs   <- mapM (nameType "varcon") $
--                 substTheta subst (eqSpecPreds eq_spec ++ thetas)
-- 
--   return (listToBag theta_cs `unionBags` arg_cs `unionBags` res_eq)
-- 
-- checkTyPmPatVec :: [PmPat Id] -> [Type] -> PmM (Bag EvVar)
-- checkTyPmPatVec pats tys
--   = do { cs <- zipWithM checkTyPmPat pats tys
--        ; return (unionManyBags cs) }

genInstSkolTyVars :: SrcSpan -> [TyVar] -> PmM (TvSubst, [TyVar])
-- Precondition: tyvars should be ordered (kind vars first)
-- see Note [Kind substitution when instantiating]
-- Get the location from the monad; this is a complete freshening operation
genInstSkolTyVars loc tvs = genInstSkolTyVarsX loc emptyTvSubst tvs

-- | Keep as a guide
-- -- -----------------------------------------------------------------------
-- -- | Given a signature sig and an output vector, check whether the vector's type
-- -- can match the signature
-- wt :: [Type] -> OutVec -> PmM Bool
-- wt sig (_, vec)
--   | length sig == length vec = do
--       cs     <- checkTyPmPatVec vec sig
--       env_cs <- getDictsDs
--       tyOracle (cs `unionBags` env_cs)
--   | otherwise = pprPanic "wt: length mismatch:" (ppr sig $$ ppr vec)



{-
%************************************************************************
%*                                                                      *
\subsection{The term equality oracle}
%*                                                                      *
%************************************************************************

-- NOTE [Term oracle strategy]

Because of the incremental nature of the algorithm, initially all constraints
are shallow and most of them are simple equalities between variables. In
general, even if we start only with equalities of the form (x ~ e), the oracle
distinguishes between equalities of 3 different forms:

  * Variable equalities (VE) of the form (x ~ y)
  * Simple   equalities (SE) of the form (x ~ e)
  * Complex  equalities (CE) of the form (e ~ e')

The overall strategy works in 2 phases:

A. Preparation Phase
====================
1) Partition initial set into VE and 'actual simples' SE (partitionSimple).
2) Solve VE (solveVarEqs) and apply the resulting substitution in SE.
3) Repeatedly apply [x |-> e] to SE, as long as a simple equality (x ~ e)
   exists in it (eliminateSimples). The result is a set of 'actual' complex
   equalities CE.

Steps (1),(2),(3) are all performed by `prepComplexEq' on CE, which is the
most general form of equality.

B. Solving Phase
================
1) Try to simplify the constraints by means of flattening, evaluation of
   expressions etc. (simplifyComplexEqs).
2) If some simplification happens, prepare the constraints (prepComplexEq) and
   repeat the Solving Phase.

-}

-- ----------------------------------------------------------------------------
-- | Oracle Types

-- | All different kinds of term equalities.
type VarEq     = (Id, Id)
type SimpleEq  = (Id, PmExpr) -- We always use this orientation
type ComplexEq = (PmExpr, PmExpr)

-- | The oracle will try and solve the wanted term constraints. If there is no
-- problem we get back a list of residual constraints. There are 2 types of
-- falures:
--   * Just eq: The set of constraints is non-satisfiable. The eq is evidence
--     (one of the possibly many) of non-satisfiability.
--   * Nothing: The constraints gave rise to a (well-typed) constraint of the
--     form (K ps ~ lit), which actually is equivalent to (K ps ~ from lit),
--     where `from' is the respective overloaded function (fromInteger, etc.)
--     By default we do not unfold functions (not currently, that it) so the
--     oracle gives up (See trac #322).
type Failure = ComplexEq

-- | The oracle environment. As the solver processess the constraints, a
-- substitution theta is generated. Since at every step the algorithm completely
-- eliminates a variable, we end up with a DAG. If there were loops, the
-- algorithm would also loop (we do not inspect function calls that may be
-- recursive so there is not termination problem at the moment).
type PmVarEnv = Map Id PmExpr

type TmOracleEnv = ([ComplexEq], PmVarEnv) -- The first is the things we cannos solve (HsExpr, overloading rubbish, etc.)

-- | The oracle monad.
type TmOracleM a = StateT TmOracleEnv (Except Failure) a -- keep eqs (x~HsExpr) in the environment. We wont do anything with them

-- ----------------------------------------------------------------------------
-- | Oracle utils

-- | Monad stuff
runTmOracleM :: TmOracleM a -> Either Failure (a, TmOracleEnv)
runTmOracleM m = runExcept (runStateT m ([], Map.empty))

liftTmOracleM :: (PmVarEnv -> (res, PmVarEnv)) -> TmOracleM res
liftTmOracleM f = do
  (other_eqs, env) <- get
  let (res, env') = f env
  put (other_eqs, env')
  return res

addUnhandledEqs :: [ComplexEq] -> TmOracleM ()
addUnhandledEqs eqs = modify (first (eqs++))
-- (map toComplex eqs++))

-- | Not actually a ComplexEq, we just wrap it with a PmExprVar
toComplex :: SimpleEq -> ComplexEq
toComplex = first PmExprVar

-- Extend the substitution
addSubst :: Id -> PmExpr -> PmVarEnv -> PmVarEnv
addSubst x e env = case Map.lookup x env of
  Nothing -> Map.insert x e env
  Just e' -> pprPanic "Check.addSubst:" (ppr x $$ ppr e $$ ppr e') -- just for sanity check

-- ----------------------------------------------------------------------------

-- | Split a set of simple equalities (of the form x ~ expr) into equalities
-- between variables only (x ~ y) and the rest (x ~ expr, where expr not a var)
-- Also, return the equalities of the form (x ~ e), where e is an HsExpr (we cannot handle it)
partitionSimple :: [SimpleEq] -> ([VarEq], [SimpleEq], [SimpleEq])
partitionSimple in_cs = foldr select ([],[],[]) in_cs
  where
    select eq@(x,e) ~(var_eqs, other_eqs, res_eqs)
      | PmExprVar y   <- e = ((x,y):var_eqs,    other_eqs,    res_eqs)
      | PmExprOther _ <- e = (      var_eqs,    other_eqs, eq:res_eqs)
      | otherwise          = (      var_eqs, eq:other_eqs,    res_eqs)

partitionSimpleM :: [SimpleEq] -> TmOracleM ([VarEq], [SimpleEq])
partitionSimpleM in_cs = addUnhandledEqs (map toComplex res_eqs) >> return (var_eqs, other_eqs)
  where (var_eqs, other_eqs, res_eqs) = partitionSimple in_cs

-- | Split a set of complex equalities into into the 3 categories
-- Also, return the equalities of the form (x ~ e), where e is an HsExpr (we cannot handle it)
partitionComplex :: [ComplexEq] -> ([VarEq], [SimpleEq], [ComplexEq], [SimpleEq])
partitionComplex in_cs = foldr select ([],[],[],[]) in_cs
  where
    select eq@(e1,e2) ~(var_eqs, simpl_eqs, other_eqs, res_eqs)
      | PmExprVar x <- e1 = selectSimple x e2 (var_eqs, simpl_eqs, other_eqs, res_eqs)
      | PmExprVar y <- e2 = selectSimple y e1 (var_eqs, simpl_eqs, other_eqs, res_eqs)
      | otherwise         = (var_eqs, simpl_eqs, eq:other_eqs, res_eqs)

    selectSimple x e ~(var_eqs, simpl_eqs, other_eqs, res_eqs)
      | PmExprVar y   <- e = ((x,y):var_eqs,       simpl_eqs, other_eqs,       res_eqs)
      | PmExprOther _ <- e = (      var_eqs,       simpl_eqs, other_eqs, (x,e):res_eqs)
      | otherwise          = (      var_eqs, (x,e):simpl_eqs, other_eqs,       res_eqs)

partitionComplexM :: [ComplexEq] -> TmOracleM ([VarEq], [SimpleEq], [ComplexEq])
partitionComplexM in_cs = addUnhandledEqs (map toComplex res_eqs) >> return (var_eqs, simpl_eqs, other_eqs)
  where (var_eqs, simpl_eqs, other_eqs, res_eqs) = partitionComplex in_cs

-- ----------------------------------------------------------------------------

-- Non-satisfiable set of constraints
mismatch :: ComplexEq -> TmOracleM a
mismatch eq = lift (throwE eq)

-- Expressions `True' and `False'
truePmExpr :: PmExpr
truePmExpr = PmExprCon trueDataCon []

falsePmExpr :: PmExpr
falsePmExpr = PmExprCon falseDataCon []

-- Check if a PmExpression is equal to term `True' (syntactically).
isTruePmExpr :: PmExpr -> Bool
isTruePmExpr (PmExprCon c []) = c == trueDataCon
isTruePmExpr _other_expr      = False

-- Check if a PmExpression is equal to term `False' (syntactically).
isFalsePmExpr :: PmExpr -> Bool
isFalsePmExpr (PmExprCon c []) = c == falseDataCon
isFalsePmExpr _other_expr      = False

isTrivialTrueLHsExpr :: LHsExpr Id -> Bool
isTrivialTrueLHsExpr lexpr = isJust (isTrueLHsExpr lexpr)

-- ----------------------------------------------------------------------------
-- | Substitution for PmExpr

substPmExpr :: Id -> PmExpr -> PmExpr -> PmExpr
substPmExpr x e1 e =
  case e of
    PmExprVar z | x == z    -> e1
                | otherwise -> e
    PmExprCon c ps -> PmExprCon c (map (substPmExpr x e1) ps)
    PmExprEq ex ey -> PmExprEq (substPmExpr x e1 ex) (substPmExpr x e1 ey)
    _other_expr    -> e -- The rest are terminals -- we silently ignore
                        -- PmExprOther. See NOTE [PmExprOther in PmExpr]

idSubstPmExpr :: (Id -> Id) -> PmExpr -> PmExpr
idSubstPmExpr fn e =
  case e of
    PmExprVar z    -> PmExprVar (fn z)
    PmExprCon c es -> PmExprCon c (map (idSubstPmExpr fn) es)
    PmExprEq e1 e2 -> PmExprEq (idSubstPmExpr fn e1) (idSubstPmExpr fn e2)
    _other_expr    -> e -- The rest are terminals -- we silently ignore
                        -- PmExprOther. See NOTE [PmExprOther in PmExpr]

-- ----------------------------------------------------------------------------
-- | Substituting in term equalities

idSubstVarEq :: (Id -> Id) -> VarEq -> VarEq
idSubstVarEq fn (x, y) = (fn x, fn y)

idSubstSimpleEq :: (Id -> Id) -> SimpleEq -> SimpleEq
idSubstSimpleEq fn (x,e) = (fn x, idSubstPmExpr fn e)

idSubstComplexEq :: (Id -> Id) -> ComplexEq -> ComplexEq
idSubstComplexEq fn (e1,e2) = (idSubstPmExpr fn e1, idSubstPmExpr fn e2)

substComplexEq :: Id -> PmExpr -> ComplexEq -> ComplexEq
substComplexEq x e (e1, e2) = (substPmExpr x e e1, substPmExpr x e e2)

-- Faster than calling `substSimpleEq' and splitting them afterwards
substSimpleEqs :: Id -> PmExpr -> [SimpleEq] -> ([SimpleEq], [ComplexEq])
substSimpleEqs _ _ [] = ([],[])
substSimpleEqs x e ((y,e1):rest)
  | x == y    = (simple_eqs, (e, e2):complex_eqs)
  | otherwise = ((y, e2):simple_eqs, complex_eqs)
  where (simple_eqs, complex_eqs) = substSimpleEqs x e rest
        e2 = substPmExpr x e e1

-- ----------------------------------------------------------------------------
-- | Solving equalities between variables

-- | A set of equalities between variables is always satisfiable.
solveVarEqs :: PmVarEnv -> [VarEq] -> (Id -> Id, PmVarEnv)
solveVarEqs env eqs = foldl' combine (id, env) eqs
  where
    combine (f, e) = first (.f) . solveVarEq e . idSubstVarEq f

solveVarEq :: PmVarEnv -> VarEq -> (Id -> Id, PmVarEnv)
solveVarEq env (x,y)
  | x == y    = (id, env)
  | otherwise = (subst, addSubst y (PmExprVar x) env)
  where subst = \z -> if z == y then x else z -- (x,y) -> [y |-> x]

-- Monadic version
solveVarEqsM :: [VarEq] -> TmOracleM (Id -> Id)
solveVarEqsM var_eqs = liftTmOracleM (\env -> solveVarEqs env var_eqs)

-- ----------------------------------------------------------------------------
-- | Solving simple equalities

eliminateSimples :: PmVarEnv -> [SimpleEq] -> [ComplexEq] -> ([ComplexEq], PmVarEnv)
eliminateSimples env [] complex_eqs = (complex_eqs, env)
eliminateSimples env ((x,e):eqs) complex_eqs
  = eliminateSimples env' simple_eqs (complex_eqs1 ++ complex_eqs2)
  where
    env' = addSubst x e env
    (simple_eqs, complex_eqs1) = substSimpleEqs x e eqs
    complex_eqs2 = map (substComplexEq x e) complex_eqs

-- Monadic version
eliminateSimplesM :: [SimpleEq] -> [ComplexEq] -> TmOracleM [ComplexEq]
eliminateSimplesM simple_eqs complex_eqs
  = liftTmOracleM (\env -> eliminateSimples env simple_eqs complex_eqs)

-- ----------------------------------------------------------------------------
-- | Solving complex equalities (workhorse)

prepComplexEqM :: [ComplexEq] -> TmOracleM [ComplexEq]
prepComplexEqM []  = return []
prepComplexEqM eqs = do
  (var_eqs, simple_eqs', complex_eqs') <- partitionComplexM eqs
  subst <- solveVarEqsM var_eqs
  let simple_eqs  = map (idSubstSimpleEq  subst) simple_eqs'
  let complex_eqs = map (idSubstComplexEq subst) complex_eqs'
  eliminateSimplesM simple_eqs complex_eqs

-- NB: Call only on prepped equalities (e.g. after prepComplexEq)
iterateComplex :: [ComplexEq] -> TmOracleM [ComplexEq]
iterateComplex []  = return []
iterateComplex eqs = do
  (done, eqs') <- simplifyComplexEqs eqs -- did we have any progress? continue
  if done then prepComplexEqM eqs' >>= iterateComplex
          else return eqs'               -- otherwise, return residual

simplifyComplexEqs :: [ComplexEq] -> TmOracleM (Bool, [ComplexEq])
simplifyComplexEqs eqs = do
  (done, new_eqs) <- mapAndUnzipM simplifyComplexEq eqs
  return (or done, concat new_eqs)

simplifyComplexEq :: ComplexEq -> TmOracleM (Bool, [ComplexEq])
simplifyComplexEq eq =
  case eq of
    -- variables
    (PmExprVar x, PmExprVar y)
      | x == y    -> return (True, [])
      | otherwise -> return (False, [eq])
    (PmExprVar _, _) -> return (False, [eq])
    (_, PmExprVar _) -> return (False, [eq])

    -- literals
    (PmExprLit l1, PmExprLit l2)
      | l1 == l2  -> return (True, [])
      | otherwise -> mismatch eq

    -- overloaded literals
    (PmExprOLit l1, PmExprOLit l2)
      | l1 == l2  -> return (True, [])
      | otherwise -> mismatch eq
    (PmExprOLit _, PmExprNeg _) -> mismatch eq
    (PmExprNeg _, PmExprOLit _) -> mismatch eq

    -- constructors
    (PmExprCon c1 es1, PmExprCon c2 es2)
      | c1 == c2  -> simplifyComplexEqs (es1 `zip` es2)
      | otherwise -> mismatch eq

    -- See NOTE [Deep equalities]
    (PmExprCon c es, PmExprEq e1 e2) -> handleDeepEq c es e1 e2
    (PmExprEq e1 e2, PmExprCon c es) -> handleDeepEq c es e1 e2

    -- Overloaded error (Double check. Some of them may need to be panics)
    (PmExprLit   _, PmExprOLit  _) -> overloaded_syntax
    (PmExprLit   _, PmExprNeg   _) -> overloaded_syntax
    (PmExprOLit  _, PmExprLit   _) -> overloaded_syntax
    (PmExprNeg   _, PmExprLit   _) -> overloaded_syntax
    (PmExprCon _ _, PmExprLit   _) -> overloaded_syntax
    (PmExprCon _ _, PmExprNeg   _) -> overloaded_syntax
    (PmExprCon _ _, PmExprOLit  _) -> overloaded_syntax
    (PmExprLit   _, PmExprCon _ _) -> overloaded_syntax
    (PmExprNeg   _, PmExprCon _ _) -> overloaded_syntax
    (PmExprOLit  _, PmExprCon _ _) -> overloaded_syntax

    _other_equality -> return (False, [eq]) -- can't simplify :(

  where
    overloaded_syntax = addUnhandledEqs [eq] >> return (True,[])

    handleDeepEq :: DataCon -> [PmExpr] -- constructor and arguments
                 -> PmExpr  -> PmExpr   -- the equality
                 -> TmOracleM (Bool, [ComplexEq])
    handleDeepEq c es e1 e2
      | c == trueDataCon = do
          (_, new) <- simplifyComplexEq (e1,e2)
          return (True, new)
      | otherwise = do
         let pmexpr = certainlyEqual e1 e2
         if isTruePmExpr pmexpr || isFalsePmExpr pmexpr
            then return (True,  [(PmExprCon c es,pmexpr)])
            else return (False, [eq])

certainlyEqual :: PmExpr -> PmExpr -> PmExpr -- NOTE [Deep equalities]
certainlyEqual e1 e2 =
  case (e1, e2) of

    -- Simple cases
    (PmExprVar   x, PmExprVar   y) -> eqVars x y  -- variables
    (PmExprLit  l1, PmExprLit  l2) -> eqLit l1 l2 -- simple literals
    (PmExprOLit l1, PmExprOLit l2) -> eqLit l1 l2 -- overloaded literals (same sign)
    (PmExprOLit  _, PmExprNeg   _) -> falsePmExpr -- overloaded literals (different sign)
    (PmExprNeg   _, PmExprOLit  _) -> falsePmExpr -- overloaded literals (different sign)

    -- Constructor case (unfold)
    (PmExprCon c1 es1, PmExprCon c2 es2) -- constructors
      | c1 == c2  -> certainlyEqualMany es1 es2
      | otherwise -> falsePmExpr

    -- Cannot be sure about the rest
    _other_equality -> expr -- Not really expressive, are we?

  where
    expr = PmExprEq e1 e2 -- reconstruct the equality from the arguments

    eqVars :: Id -> Id -> PmExpr
    eqVars x y = if x == y then truePmExpr else expr

    eqLit :: Eq a => a -> a -> PmExpr
    eqLit x y | x == y    = truePmExpr
              | otherwise = falsePmExpr

    certainlyEqualMany :: [PmExpr] -> [PmExpr] -> PmExpr
    certainlyEqualMany es1 es2 =
      let args   = map (uncurry certainlyEqual) (es1 `zip` es2)
          result | all isTruePmExpr  args = truePmExpr
                 | any isFalsePmExpr args = falsePmExpr
                 | otherwise              = expr -- inconclusive
      in  result

-- ----------------------------------------------------------------------------
-- | Entry point to the solver

tmOracle :: [SimpleEq] -> Either Failure ([ComplexEq], TmOracleEnv) -- return residual constraints and final mapping
tmOracle simple_eqs = runTmOracleM (solveAll simple_eqs)

solveAll :: [SimpleEq] -> TmOracleM [ComplexEq]
solveAll []  = return []
solveAll eqs = do
  (var_eqs, simple_eqs') <- partitionSimpleM eqs
  subst <- solveVarEqsM var_eqs
  let simple_eqs = map (idSubstSimpleEq subst) simple_eqs'
  complex_eqs <- eliminateSimplesM simple_eqs []
  iterateComplex complex_eqs

-- ----------------------------------------------------------------------------

getValuePmExpr :: PmVarEnv -> PmExpr -> PmExpr
getValuePmExpr env (PmExprVar x)
  | Just e <- Map.lookup x env = getValuePmExpr env e
  | otherwise                  = PmExprVar x
getValuePmExpr env (PmExprCon c es) = PmExprCon c (map (getValuePmExpr env) es)
getValuePmExpr env (PmExprEq e1 e2) = PmExprEq (getValuePmExpr env e1) (getValuePmExpr env e2)
getValuePmExpr _   other_expr       = other_expr

isForced :: Id -> PmVarEnv -> Bool
isForced x env = case getValuePmExpr env (PmExprVar x) of
  PmExprVar _ -> False
  _other_expr -> True

-- ----------------------------------------------------------------------------

-- NOTE [Representation of substitution]
--
-- Throughout the code we use 2 different ways to represent substitutions:
--   * Substitutions from variables to variables are represented using Haskell
--     functions with type (Id -> Id).
--   * Substitutions from variables to expressions are usually passed explicitly
--     as two arguments (the Id and the PmExpr to substitute it with)
-- By convention, substitutions of the first kind are prefixed by `idSubst'
-- while the latter are prefixed simply by 'subst'.


-- NOTE [PmExprOther in PmExpr]
--
-- Data constructor `PmExprOther' lifts an (HsExpr Id) to a PmExpr. Ideally we
-- would have only (HsExpr Id) but this would be really verbose:
--    The solver is pretty naive and cannot handle many Haskell expressions.
-- Since there is no plan (for the near future) to change the solver there
-- is no need to work with the full HsExpr type (more than 45 constructors).
--
-- Functions `substPmExpr' and `idSubstPmExpr' do not substitute in HsExpr, which
-- could be a problem for a different solver. E.g:
--
-- For the following set of constraints (HsExpr in braces):
--
--   (y ~ x, y ~ z, y ~ True, y ~ False, {not y})
--
-- would be simplified (in one step using `solveVarEqs') to:
--
--   (x ~ True, x ~ False, {not y})
--
-- i.e. y is now free to be unified with anything! This is not a problem now
-- because we never inspect a PmExprOther (They always end up in residual)
-- but a more sophisticated solver may need to do so!


-- NOTE [Deep equalities]
--
-- Solving nested equalities is the most difficult part. The general strategy
-- is the following:
--
--   * Equalities of the form (True ~ (e1 ~ e2)) are transformed to just
--     (e1 ~ e2) and then treated recursively.
--
--   * Equalities of the form (False ~ (e1 ~ e2)) cannot be analyzed unless
--     we know more about the inner equality (e1 ~ e2). That's exactly what
--     `certainlyEqual' tries to do: It takes e1 and e2 and either returns
--     truePmExpr, falsePmExpr or (e1' ~ e2') in case it is uncertain. Note
--     that it is not e but rather e', since it may perform some
--     simplifications deeper.

{-
%************************************************************************
%*                                                                      *
\subsection{Something more incremental for the term oracle maybe??}
%*                                                                      *
%************************************************************************
-}

emptyPmVarEnv :: PmVarEnv
emptyPmVarEnv = Map.empty

solveVarEqI :: VarEq -> PmVarEnv -> Maybe PmVarEnv
solveVarEqI (x,y) env =
  case (Map.lookup x env, Map.lookup y env) of
    (Nothing, Nothing) -> Just $ Map.insert x (PmExprVar y) env
    (Just ex, Nothing) -> Just $ Map.insert y ex            env
    (Nothing, Just ey) -> Just $ Map.insert x ey            env
    (Just ex, Just ey) -> solveComplexEqI (ex,ey) env

solveSimpleEqI :: SimpleEq -> PmVarEnv -> Maybe PmVarEnv
solveSimpleEqI (x, e) env =
  case Map.lookup x env of
    Nothing -> Just $ Map.insert x e env
    Just ex -> solveComplexEqI (e,ex) env

solveComplexEqI :: ComplexEq -> PmVarEnv -> Maybe PmVarEnv
solveComplexEqI (e1,e2) env = undefined {- Actual Work -}

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

instance Outputable PmExpr where
  ppr (PmExprVar x)    = ppr x
  ppr (PmExprCon c es) = sep (ppr c : map parenIfNeeded es)
  ppr (PmExprLit  l)   = pmPprHsLit l -- don't use just ppr to avoid all the hashes
  ppr (PmExprOLit l)   = ppr l
  ppr (PmExprNeg  l)   = char '-' <> ppr l
  ppr (PmExprEq e1 e2) = parens (ppr e1 <+> equals <+> ppr e2)
  ppr (PmExprOther e)  = braces (ppr e) -- Just print it so that we know

parenIfNeeded :: PmExpr -> SDoc
parenIfNeeded e =
  case e of
    PmExprNeg _   -> parens (ppr e)
    PmExprCon _ es | null es   -> ppr e
                   | otherwise -> parens (ppr e)
    _other_expr   -> ppr e

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

