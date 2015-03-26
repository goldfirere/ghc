-- (c) The University of Glasgow 2006

{-# LANGUAGE CPP, DeriveDataTypeable #-}

module TcEvidence (

  -- HsWrapper
  HsWrapper(..), 
  (<.>), mkWpTyEvApps,
  mkWpTyApps, mkWpEvApps, mkWpEvVarApps, mkWpTyLams, mkWpLams, mkWpLet, mkWpCast,
  mkWpFun, idHsWrapper, isIdHsWrapper, pprHsWrapper,

  -- Evidence bindings
  TcEvBinds(..), EvBindsVar(..), 
  EvBindMap(..), emptyEvBindMap, extendEvBinds, dropEvBind,
  lookupEvBind, evBindMapBinds,
  EvBind(..), emptyTcEvBinds, isEmptyTcEvBinds,
  evBindsVars, evBindsSubst, evBindsSubstX, evBindsCvSubstEnv,
  sccEvBinds, evBindVar,
  EvTerm(..), mkEvCast, evVarsOfTerm,
  EvLit(..), evTermCoercion,

  -- TcCoercion
  TcCoercion(..), LeftOrRight(..), pickLR,
  mkTcReflCo, mkTcNomReflCo, mkTcRepReflCo,
  mkTcTyConAppCo, mkTcAppCo, mkTcAppCos, mkTcFunCo,
  mkTcAxInstCo, mkTcUnbranchedAxInstCo, mkTcForAllCo, mkTcForAllCos,
  mkTcSymCo, mkTcTransCo, mkTcNthCo, mkTcLRCo, mkTcSubCo, maybeTcSubCo,
  tcDowngradeRole,
  mkTcAxiomRuleCo, mkTcCoherenceLeftCo, mkTcCoherenceRightCo, mkTcPhantomCo,
  castTcCoercionKind, mkTcKindCo, mkTcKindAppCo, mkTcCoercion, mkTcCoercionArg,
  tcCoercionKind, coVarsOfTcCo, tyCoVarsOfTcCo,
  isEqVar, mkTcCoVarCo,
  isTcReflCo, getTcCoVar_maybe,
  tcCoercionRole, eqVarRole,
  tcCoercionToCoercion
  ) where
#include "HsVersions.h"

import {-# SOURCE #-} TcRnTypes ( CtLoc )
-- TODO (RAE): Remove this boot file.
-- I think it can be done by storing a (Bag EvBind) in HsSyn and then
-- augmenting TcEvBinds (which would be defined in TcRnTypes) to store
-- locations.
    

import Var
import Coercion
import PprCore ()   -- Instance OutputableBndr TyVar
import TcType
import Type
import TyCon
import CoAxiom
import PrelNames
import VarEnv
import VarSet
import Name

import Util
import BasicTypes ( Boxity(..), isBoxed )
import Bag
import Pair
import Digraph
import Control.Applicative
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable (traverse, sequenceA)
#endif
import qualified Data.Data as Data 
import Outputable
import ListSetOps
import FastString
import Data.IORef( IORef )
import Data.List ( mapAccumL )

{-
Note [TcCoercions]
~~~~~~~~~~~~~~~~~~
| TcCoercions are a hack used by the typechecker. Normally,
Coercions have free variables of type (a ~# b): we call these
CoVars. However, the type checker passes around equality evidence
(boxed up) at type (a ~ b).

An TcCoercion is simply a Coercion whose free variables have the
boxed type (a ~ b). After we are done with typechecking the
desugarer finds the free variables, unboxes them, and creates a
resulting real Coercion with kosher free variables.

The data type is similar to Coercion.Coercion, with the following
differences
  * Most important, TcLetCo adds let-bindings for coercions.
    This is what lets us unify two for-all types and generate
    equality constraints underneath

  * UnsafeCo aren't required, but we do have TcPhantomCo

  * Representation invariants are weaker:
     - we are allowed to have type synonyms in TcTyConAppCo
     - the first arg of a TcAppCo can be a TcTyConAppCo
     - TcSubCo is not applied as deep as done with mkSubCo
    Reason: they'll get established when we desugar to Coercion

See also Note [TcCoercion kinds]

Note [TcCoercion kinds]
~~~~~~~~~~~~~~~~~~~~~~~
TcCoercions can be classified either by (t1 ~ t2) OR by (t1 ~# t2).
This is a direct consequence of the fact that both (~) and (~#) are considered
pred-types by classifyPredType. This is all necessary so that the solver can
work with both lifted equality and unlifted equality, which in turn is
necessary because lifted equality can't be used in types.

The way this works out is that the desugarer checks the type of any coercion
variables used in a TcCoercion. Any lifted equality variables get unboxed;
any unlifted ones are left alone. See dsTcCoercion.

Then, because equality should always be lifted in terms, dsEvTerm calls
mkEqBox appropriately. On the other hand, because equality should always
be unlifted in types, no extra processing is done there.

tcCoercionKind returns a (Pair Type), so it's not affected by this ambiguity.

Note [TcAxiomInstCo takes TcCoercions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Why does TcAxiomInstCo take a list of TcCoercions? Because AxiomInstCo does,
of course! Generally, we think of axioms as being applied to a list of types.
The only reason for coercions in AxiomInstCo is to allow for coercion
optimization -- see Note [Coercion axioms applied to coercions] in TyCoRep.
But, of course, we don't want to fiddle with
CoCoArgs in the type-checker, so we ensure that all CoCoArgs are actually
reflexive and then we can proceed.

-}

data TcCoercion 
  = TcRefl Role TcType
  | TcTyConAppCo Role TyCon [TcCoercion]
  | TcAppCo TcCoercion TcCoercion TcCoercion
  | TcForAllCo TyCoVar TcCoercion 
  | TcCoVarCo EqVar
  | TcAxiomInstCo (CoAxiom Branched) BranchIndex [TcCoercion]
          -- See Note [TcAxiomInstCo takes TcCoercions]
  -- This is number of types and coercions are expected to match to CoAxiomRule
  -- (i.e., the CoAxiomRules are always fully saturated)
  | TcAxiomRuleCo CoAxiomRule [TcType] [TcCoercion]
  | TcPhantomCo TcCoercion TcType TcType
  | TcSymCo TcCoercion
  | TcTransCo TcCoercion TcCoercion
  | TcNthCo Int TcCoercion
  | TcLRCo LeftOrRight TcCoercion
  | TcSubCo TcCoercion
  | TcCastCo TcCoercion TcCoercion     -- co1 |> co2
  | TcCoherenceCo TcCoercion Coercion
  | TcKindCo TcCoercion
  | TcKindAppCo TcCoercion
  | TcLetCo TcEvBinds TcCoercion
  | TcCoercion CoercionArg             -- embed a Core Coercion
  deriving (Data.Data, Data.Typeable)

isEqVar :: Var -> Bool 
-- Is lifted coercion variable (only!)
isEqVar v = case tyConAppTyCon_maybe (varType v) of
               Just tc -> tc `hasKey` eqTyConKey
               Nothing -> False

isTcReflCo_maybe :: TcCoercion -> Maybe TcType
isTcReflCo_maybe (TcRefl _ ty) = Just ty
isTcReflCo_maybe _             = Nothing

isTcReflCo :: TcCoercion -> Bool
isTcReflCo (TcRefl {}) = True
isTcReflCo _           = False

getTcCoVar_maybe :: TcCoercion -> Maybe CoVar
getTcCoVar_maybe (TcCoVarCo v) = Just v
getTcCoVar_maybe _             = Nothing

mkTcReflCo :: Role -> TcType -> TcCoercion
mkTcReflCo = TcRefl

mkTcNomReflCo :: TcType -> TcCoercion
mkTcNomReflCo = TcRefl Nominal

mkTcRepReflCo :: TcType -> TcCoercion
mkTcRepReflCo = TcRefl Representational

mkTcFunCo :: Role -> TcCoercion -> TcCoercion -> TcCoercion
mkTcFunCo role co1 co2 = mkTcTyConAppCo role funTyCon [co1, co2]

mkTcTyConAppCo :: Role -> TyCon -> [TcCoercion] -> TcCoercion
mkTcTyConAppCo role tc cos -- No need to expand type synonyms
                           -- See Note [TcCoercions]
  | Just tys <- traverse isTcReflCo_maybe cos 
  = TcRefl role (mkTyConApp tc tys)  -- See Note [Refl invariant]

  | otherwise = TcTyConAppCo role tc cos

-- input coercion is Nominal
-- mkSubCo will do some normalisation. We do not do it for TcCoercions, but
-- defer that to desugaring; just to reduce the code duplication a little bit
mkTcSubCo :: TcCoercion -> TcCoercion
mkTcSubCo co = ASSERT2( tcCoercionRole co == Nominal, ppr co)
               TcSubCo co

-- See Note [Role twiddling functions] in Coercion
-- | Change the role of a 'TcCoercion'. Returns 'Nothing' if this isn't
-- a downgrade.
tcDowngradeRole_maybe :: Role   -- desired role
                      -> Role   -- current role
                      -> TcCoercion -> Maybe TcCoercion
tcDowngradeRole_maybe Representational Nominal = Just . mkTcSubCo
tcDowngradeRole_maybe Nominal Representational = const Nothing
tcDowngradeRole_maybe Phantom _
  = panic "tcDowngradeRole_maybe Phantom"
    -- not supported (not needed at the moment)
tcDowngradeRole_maybe _ Phantom                = const Nothing
tcDowngradeRole_maybe _ _                      = Just

-- See Note [Role twiddling functions] in Coercion
-- | Change the role of a 'TcCoercion'. Panics if this isn't a downgrade.
tcDowngradeRole :: Role  -- ^ desired role
                -> Role  -- ^ current role
                -> TcCoercion -> TcCoercion
tcDowngradeRole r1 r2 co
  = case tcDowngradeRole_maybe r1 r2 co of
      Just co' -> co'
      Nothing  -> pprPanic "tcDowngradeRole" (ppr r1 <+> ppr r2 <+> ppr co)

-- | If the EqRel is ReprEq, makes a TcSubCo; otherwise, does nothing.
-- Note that the input coercion should always be nominal.
maybeTcSubCo :: EqRel -> TcCoercion -> TcCoercion
maybeTcSubCo NomEq  = id
maybeTcSubCo ReprEq = mkTcSubCo

mkTcAxInstCo :: Role -> CoAxiom br -> Int -> [TcType] -> TcCoercion
mkTcAxInstCo role ax index tys = mkTcCoercion $ mkAxInstCo role ax index tys

mkTcAxiomRuleCo :: CoAxiomRule -> [TcType] -> [TcCoercion] -> TcCoercion
mkTcAxiomRuleCo = TcAxiomRuleCo

mkTcUnbranchedAxInstCo :: Role -> CoAxiom Unbranched -> [TcType] -> TcCoercion
mkTcUnbranchedAxInstCo role ax tys
  = mkTcAxInstCo role ax 0 tys

mkTcAppCo :: TcCoercion -> TcCoercion -> TcCoercion -> TcCoercion
-- No need to deal with TyConApp on the left; see Note [TcCoercions]
-- Third coercion *must* be nominal; other two must match roles
mkTcAppCo (TcRefl r ty1) _ (TcRefl _ ty2) = TcRefl r (mkAppTy ty1 ty2)
mkTcAppCo co1 h co2                       = TcAppCo co1 h co2

mkTcSymCo :: TcCoercion -> TcCoercion
mkTcSymCo co@(TcRefl {})  = co
mkTcSymCo    (TcSymCo co) = co
mkTcSymCo co              = TcSymCo co

mkTcTransCo :: TcCoercion -> TcCoercion -> TcCoercion
mkTcTransCo (TcRefl {}) co = co
mkTcTransCo co (TcRefl {}) = co
mkTcTransCo co1 co2        = TcTransCo co1 co2

mkTcNthCo :: Int -> TcCoercion -> TcCoercion
mkTcNthCo n (TcRefl r ty) = TcRefl (nthRole r tc n) (args `getNth` n)
  where (tc, args) = splitTyConApp ty
mkTcNthCo n co            = TcNthCo n co

mkTcLRCo :: LeftOrRight -> TcCoercion -> TcCoercion
mkTcLRCo lr (TcRefl r ty) = TcRefl r (pickLR lr (tcSplitAppTy ty))
mkTcLRCo lr co            = TcLRCo lr co

mkTcPhantomCo :: TcCoercion -> TcType -> TcType -> TcCoercion
mkTcPhantomCo = TcPhantomCo

mkTcAppCos :: TcCoercion -> [(TcCoercion, TcCoercion)] -> TcCoercion
mkTcAppCos co1 tys = foldl (uncurry2 mkTcAppCo) co1 tys

mkTcForAllCo :: TyCoVar -> TcCoercion -> TcCoercion
-- note that a TyVar or CoVar should be used here, not a TcTyVar
mkTcForAllCo tv (TcRefl r ty) = TcRefl r (mkNamedForAllTy tv Invisible ty)  -- TODO (RAE): Check.
mkTcForAllCo tv  co           = TcForAllCo tv co

mkTcForAllCos :: [TyCoVar] -> TcCoercion -> TcCoercion
mkTcForAllCos tvs (TcRefl r ty) = TcRefl r (mkInvForAllTys tvs ty)  -- TODO (RAE): Check.
mkTcForAllCos tvs co            = foldr TcForAllCo co tvs

mkTcCoVarCo :: EqVar -> TcCoercion
-- ipv :: s ~ t  (the boxed equality type) or Coercible s t (the boxed representational equality type)
mkTcCoVarCo ipv = TcCoVarCo ipv
  -- Previously I checked for (ty ~ ty) and generated Refl,
  -- but in fact ipv may not even (visibly) have a (t1 ~ t2) type, because
  -- the constraint solver does not substitute in the types of
  -- evidence variables as it goes.  In any case, the optimisation
  -- will be done in the later zonking phase

-- | Cast the left type in a coercion. The second coercion must be
-- Representational.
mkTcCoherenceLeftCo :: TcCoercion -> Coercion -> TcCoercion
mkTcCoherenceLeftCo co g = TcCoherenceCo co g

-- | Cast the right type in a coercion. The second coercion must be
-- Representational.
mkTcCoherenceRightCo :: TcCoercion -> Coercion -> TcCoercion
mkTcCoherenceRightCo c1 c2 = mkTcSymCo (mkTcCoherenceLeftCo (mkTcSymCo c1) c2)

-- | Cast both types in a coercion. The second and third coercions must be
-- Representational.
castTcCoercionKind :: TcCoercion -> Coercion -> Coercion -> TcCoercion
castTcCoercionKind g h1 h2
  = g `mkTcCoherenceLeftCo` h1 `mkTcCoherenceRightCo` h2

mkTcKindCo :: TcCoercion -> TcCoercion
mkTcKindCo = TcKindCo

mkTcKindAppCo :: TcCoercion -> TcCoercion
mkTcKindAppCo = TcKindAppCo

-- | Convert a Coercion to a TcCoercion.
mkTcCoercion :: Coercion -> TcCoercion
mkTcCoercion co
  | Just (ty, r) <- isReflCo_maybe co = TcRefl r ty
  | otherwise                         = TcCoercion (mkTyCoArg co)

-- | Convert a CoercionArg to a TcCoercion
mkTcCoercionArg :: CoercionArg -> TcCoercion
mkTcCoercionArg co
  | Just ty <- isReflLike_maybe co = TcRefl (coercionArgRole co) ty
  | otherwise                      = TcCoercion co

tcCoercionKind :: TcCoercion -> Pair Type
tcCoercionKind co = go co 
  where 
    go (TcRefl _ ty)          = Pair ty ty
    go (TcLetCo _ co)         = go co
    go (TcCastCo _ co)        = case getEqPredTys (pSnd (go co)) of
                                   (ty1,ty2) -> Pair ty1 ty2
    go (TcCoherenceCo co g)   = pLiftFst (`mkCastTy` g) (go co)
    go (TcKindCo co)          = typeKind <$> go co
    go (TcKindAppCo co)       = typeKind <$> (snd <$> (splitAppTy <$> go co))
    go (TcTyConAppCo _ tc cos)= mkTyConApp tc <$> (sequenceA $ map go cos)
    go (TcAppCo co1 _ co2)    = mkAppTy <$> go co1 <*> go co2
    go (TcForAllCo tv co)     = mkNamedForAllTy tv Invisible <$> go co
       -- TODO (RAE): Check above.
    go (TcCoVarCo cv)         = eqVarKind cv
    go (TcAxiomInstCo ax ind cos)
      = let branch = coAxiomNthBranch ax ind
            tvs = coAxBranchTyCoVars branch
            Pair tys1 tys2 = sequenceA (map go cos)
        in ASSERT( cos `equalLength` tvs )
           Pair (substTyWith tvs tys1 (coAxNthLHS ax ind))
                (substTyWith tvs tys2 (coAxBranchRHS branch))
    go (TcPhantomCo _ ty1 ty2)= Pair ty1 ty2
    go (TcSymCo co)           = swap (go co)
    go (TcTransCo co1 co2)    = Pair (pFst (go co1)) (pSnd (go co2))
    go (TcNthCo d co)         = tyConAppArgN d <$> go co
    go (TcLRCo lr co)         = (pickLR lr . tcSplitAppTy) <$> go co
    go (TcSubCo co)           = go co
    go (TcAxiomRuleCo ax ts cs) =
       case coaxrProves ax ts (map tcCoercionKind cs) of
         Just res -> res
         Nothing -> panic "tcCoercionKind: malformed TcAxiomRuleCo"
    go (TcCoercion co)        = coercionArgKind co

eqVarRole :: EqVar -> Role
eqVarRole cv = getEqPredRole (varType cv)

eqVarKind :: EqVar -> Pair Type
eqVarKind cv
 | Just (tc, [_kind,ty1,ty2]) <- split_ty
 = ASSERT(tc `hasKey` eqTyConKey || tc `hasKey` coercibleTyConKey)
   Pair ty1 ty2
 | Just (tc, [_k1, _k2, ty1, ty2]) <- split_ty
 = ASSERT(tc `hasKey` eqPrimTyConKey || tc `hasKey` eqReprPrimTyConKey)
   Pair ty1 ty2
 | otherwise = pprPanic "eqVarKind, non coercion variable" (ppr cv <+> dcolon <+> ppr (varType cv))
  where
    split_ty = tcSplitTyConApp_maybe (varType cv)

tcCoercionRole :: TcCoercion -> Role
tcCoercionRole = go
  where
    go (TcRefl r _)           = r
    go (TcTyConAppCo r _ _)   = r
    go (TcAppCo co _ _)       = go co
    go (TcForAllCo _ co)      = go co
    go (TcCoVarCo cv)         = eqVarRole cv
    go (TcAxiomInstCo ax _ _) = coAxiomRole ax
    go (TcPhantomCo _ _ _)    = Phantom
    go (TcSymCo co)           = go co
    go (TcTransCo co1 _)      = go co1 -- same as go co2
    go (TcNthCo n co)         = let Pair ty1 _ = tcCoercionKind co
                                    (tc, _) = tcSplitTyConApp ty1
                                in nthRole (go co) tc n
    go (TcLRCo _ _)           = Nominal
    go (TcSubCo _)            = Representational
    go (TcAxiomRuleCo c _ _)  = coaxrRole c
    go (TcCastCo c _)         = go c
    go (TcCoherenceCo co _)   = go co
    go (TcKindCo _)           = Representational
    go (TcKindAppCo co)       = go co
    go (TcLetCo _ c)          = go c
    go (TcCoercion co)        = coercionArgRole co

tyCoVarsOfTcCo :: TcCoercion -> VarSet
tyCoVarsOfTcCo = go
  where
    go (TcRefl _ t)              = tyCoVarsOfType t
    go (TcTyConAppCo _ _ cos)    = mapUnionVarSet go cos
    go (TcAppCo co1 h co2)       = go co1 `unionVarSet` go h `unionVarSet` go co2
    go (TcCastCo co1 co2)        = go co1 `unionVarSet` go co2
    go (TcCoherenceCo co g)      = go co `unionVarSet` tyCoVarsOfCo g
    go (TcKindCo co)             = go co
    go (TcKindAppCo co)          = go co
    go (TcForAllCo _ co)         = go co
    go (TcCoVarCo v)             = unitVarSet v
    go (TcAxiomInstCo _ _ cos)   = mapUnionVarSet go cos
    go (TcPhantomCo h t1 t2)     = unionVarSets [ go h
                                                , tyCoVarsOfType t1
                                                , tyCoVarsOfType t2 ]
    go (TcSymCo co)              = go co
    go (TcTransCo co1 co2)       = go co1 `unionVarSet` go co2
    go (TcNthCo _ co)            = go co
    go (TcLRCo  _ co)            = go co
    go (TcSubCo co)              = go co
    go (TcLetCo (EvBinds bs) co) = foldrBag (unionVarSet . go_bind) (go co) bs
                                   `minusVarSet` evBindsVars bs
    go (TcLetCo {}) = emptyVarSet    -- Harumph. This does legitimately happen in the call
                                     -- to evVarsOfTerm in the DEBUG check of setEvBind
    go (TcAxiomRuleCo _ _ cos)   = mapUnionVarSet go cos
    go (TcCoercion co)           = tyCoVarsOfCoArg co

    -- We expect only coercion bindings, so use evTermCoercion 
    go_bind :: EvBind -> VarSet
    go_bind (EvBind { evb_term = tm }) = go (evTermCoercion tm)

coVarsOfTcCo :: TcCoercion -> VarSet
-- Only works on *zonked* coercions, because of TcLetCo
coVarsOfTcCo tc_co
  = go tc_co
  where
    go (TcRefl _ t)              = coVarsOfType t
    go (TcTyConAppCo _ _ cos)    = mapUnionVarSet go cos
    go (TcAppCo co1 h co2)       = go co1 `unionVarSet` go h `unionVarSet` go co2
    go (TcCastCo co1 co2)        = go co1 `unionVarSet` go co2
    go (TcCoherenceCo co g)      = go co `unionVarSet` coVarsOfCo g
    go (TcKindCo co)             = go co
    go (TcKindAppCo co)          = go co
    go (TcForAllCo _ co)         = go co
    go (TcCoVarCo v)             = unitVarSet v
    go (TcAxiomInstCo _ _ cos)   = mapUnionVarSet go cos
    go (TcPhantomCo h t1 t2)     = go h `unionVarSet`
                                   coVarsOfType t1 `unionVarSet` coVarsOfType t2
    go (TcSymCo co)              = go co
    go (TcTransCo co1 co2)       = go co1 `unionVarSet` go co2
    go (TcNthCo _ co)            = go co
    go (TcLRCo  _ co)            = go co
    go (TcSubCo co)              = go co
    go (TcLetCo (EvBinds bs) co) = foldrBag (unionVarSet . go_bind) (go co) bs
                                   `minusVarSet` evBindsVars bs
    go (TcLetCo {}) = emptyVarSet    -- Harumph. This does legitimately happen in the call
                                     -- to evVarsOfTerm in the DEBUG check of setEvBind
    go (TcAxiomRuleCo _ _ cos)   = mapUnionVarSet go cos
    go (TcCoercion co)           = coVarsOfCoArg co

    -- We expect only coercion bindings, so use evTermCoercion 
    go_bind :: EvBind -> VarSet
    go_bind (EvBind { evb_term = tm }) = go (evTermCoercion tm)

-- | Converts a TcCoercion to a Coercion, substituting for covars as it goes.
-- All covars in the TcCoercion must be mapped for this to succeed, as covars
-- in a TcCoercion are different than those in a Coercion. A covar might not
-- be mapped if, for example, there is an unsolved equality constraint, so
-- failure here shouldn't be a panic.
tcCoercionToCoercion :: TCvSubst -> TcCoercion -> Maybe Coercion
-- If the incoming TcCoercion if of type (a ~ b)   (resp.  Coercible a b)
--                 the result is of type (a ~# b)  (reps.  a ~# b)
tcCoercionToCoercion subst tc_co
  = go tc_co
  where
    go (TcRefl r ty)            = Just $ mkReflCo r (Type.substTy subst ty)
    go (TcTyConAppCo r tc cos)  = mkTyConAppCo r tc <$> mapM go_arg cos
    go (TcAppCo co1 h co2)      = mkAppCo <$> go co1 <*> go h <*> go_arg co2
    go co@(TcForAllCo {})       = go_forall [] co
    go (TcAxiomInstCo ax ind cos)
                                = mkAxiomInstCo ax ind <$> mapM go_arg cos
    go (TcPhantomCo h ty1 ty2)  = mkPhantomCo <$> go h <*> pure (substTy subst ty1)
                                                       <*> pure (substTy subst ty2)
    go (TcSymCo co)             = mkSymCo <$> go co
    go (TcTransCo co1 co2)      = mkTransCo <$> go co1 <*> go co2
    go (TcNthCo n co)           = mkNthCo n <$> go co
    go (TcLRCo lr co)           = mkLRCo lr <$> go co
    go (TcSubCo co)             = mkSubCo <$> go co
    go (TcLetCo bs co)          = tcCoercionToCoercion (ds_co_binds bs) co
    go (TcCastCo co1 co2)       = mkCoCast <$> go co1 <*> go co2
    go (TcCoherenceCo tco1 co2) = mkCoherenceCo <$> go tco1 <*> pure (substCo subst co2)
    go (TcKindCo co)            = mkKindCo <$> go co
    go (TcKindAppCo co)         = mkKindAppCo <$> go co
    go (TcCoVarCo v)            = lookupCoVar subst v
    go (TcAxiomRuleCo co ts cs) = mkAxiomRuleCo co (map (Type.substTy subst) ts) <$> (mapM go cs)
    go (TcCoercion co)          = stripTyCoArg <$> Just (substCoArg subst co)

    go_arg (TcCoercion arg)     = Just (substCoArg subst arg)
    go_arg tc_co                = mkTyCoArg <$> go tc_co

    go_forall tvs (TcForAllCo tv co) = go_forall (tv:tvs) co
    go_forall tvs co = foldr mkForAllCo <$> tcCoercionToCoercion subst' co
                                        <*> pure cobndrs'
      where
        role               = tcCoercionRole co  -- TODO (RAE): make more efficient?
        in_scope           = mkInScopeSet $ tyCoVarsOfTcCo co
        (_, cobndrs)       = mapAccumL mk_cobndr in_scope tvs
        (subst', cobndrs') = mapAccumL substForAllCoBndr subst (reverse cobndrs)
        
        mk_cobndr is tv = (is', cobndr)
          where cobndr = mkHomoCoBndr is role tv
                is'    = is `extendInScopeSetList` coBndrVars cobndr

    ds_co_binds :: TcEvBinds -> TCvSubst
    ds_co_binds (EvBinds bs)      = evBindsSubstX subst bs
    ds_co_binds eb@(TcEvBinds {}) = pprPanic "ds_co_binds" (ppr eb)

-- Pretty printing

instance Outputable TcCoercion where
  ppr = pprTcCo

pprTcCo, pprParendTcCo :: TcCoercion -> SDoc
pprTcCo       co = ppr_co TopPrec   co
pprParendTcCo co = ppr_co TyConPrec co

ppr_co :: TyPrec -> TcCoercion -> SDoc
ppr_co _ (TcRefl r ty) = angleBrackets (ppr ty) <> ppr_role r

ppr_co p co@(TcTyConAppCo _ tc [_,_])
  | tc `hasKey` funTyConKey = ppr_fun_co p co

ppr_co p (TcTyConAppCo r tc cos) = pprTcApp   p ppr_co tc cos <> ppr_role r
ppr_co p (TcLetCo bs co)         = maybeParen p TopPrec $
                                   sep [ptext (sLit "let") <+> braces (ppr bs), ppr co]
ppr_co p (TcAppCo co1 _ co2)     = maybeParen p TyConPrec $
                                   pprTcCo co1 <+> ppr_co TyConPrec co2
                                   -- TODO (RAE): Printing TcCastCo like this is terrible.
ppr_co p (TcCastCo co1 co2)      = maybeParen p FunPrec $
                                   ppr_co FunPrec co1 <+> ptext (sLit "|>") <+> ppr_co FunPrec co2
ppr_co p (TcCoherenceCo co g)    = maybeParen p FunPrec $
                                   ppr_co FunPrec co <+> text "|>>" <+> ppr g
ppr_co p (TcKindCo co)           = maybeParen p FunPrec $
                                   text "kind" <+> ppr_co FunPrec co
ppr_co p (TcKindAppCo co)        = maybeParen p FunPrec $
                                   text "kapp" <+> ppr_co FunPrec co
ppr_co p co@(TcForAllCo {})      = ppr_forall_co p co
                     
ppr_co _ (TcCoVarCo cv)          = parenSymOcc (getOccName cv) (ppr cv)

ppr_co p (TcAxiomInstCo con ind cos)
  = pprPrefixApp p (ppr (getName con) <> brackets (ppr ind)) (map pprParendTcCo cos)

ppr_co p (TcTransCo co1 co2) = maybeParen p FunPrec $
                               ppr_co FunPrec co1
                               <+> ptext (sLit ";")
                               <+> ppr_co FunPrec co2
ppr_co p (TcPhantomCo _ t1 t2)= pprPrefixApp p (ptext (sLit "PhantomCo")) [pprParendType t1, pprParendType t2]
ppr_co p (TcSymCo co)         = pprPrefixApp p (ptext (sLit "Sym")) [pprParendTcCo co]
ppr_co p (TcNthCo n co)       = pprPrefixApp p (ptext (sLit "Nth:") <+> int n) [pprParendTcCo co]
ppr_co p (TcLRCo lr co)       = pprPrefixApp p (ppr lr) [pprParendTcCo co]
ppr_co p (TcSubCo co)         = pprPrefixApp p (ptext (sLit "Sub")) [pprParendTcCo co]
ppr_co p (TcAxiomRuleCo co ts ps) = maybeParen p TopPrec
                                  $ ppr_tc_axiom_rule_co co ts ps
ppr_co p (TcCoercion co)      = pprPrefixApp p (text "Core co:") [ppr co]

ppr_tc_axiom_rule_co :: CoAxiomRule -> [TcType] -> [TcCoercion] -> SDoc
ppr_tc_axiom_rule_co co ts ps = ppr (coaxrName co) <> ppTs ts $$ nest 2 (ppPs ps)
  where
  ppTs []   = Outputable.empty
  ppTs [t]  = ptext (sLit "@") <> pprType t
  ppTs ts   = ptext (sLit "@") <>
                parens (hsep $ punctuate comma $ map pprType ts)

  ppPs []   = Outputable.empty
  ppPs [p]  = pprParendTcCo p
  ppPs (p : ps) = ptext (sLit "(") <+> pprTcCo p $$
                  vcat [ ptext (sLit ",") <+> pprTcCo q | q <- ps ] $$
                  ptext (sLit ")")

ppr_role :: Role -> SDoc
ppr_role r = underscore <> pp_role
  where pp_role = case r of
                    Nominal          -> char 'N'
                    Representational -> char 'R'
                    Phantom          -> char 'P'

ppr_fun_co :: TyPrec -> TcCoercion -> SDoc
ppr_fun_co p co = pprArrowChain p (split co)
  where
    split :: TcCoercion -> [SDoc]
    split (TcTyConAppCo _ f [arg,res])
      | f `hasKey` funTyConKey
      = ppr_co FunPrec arg : split res
    split co = [ppr_co TopPrec co]

ppr_forall_co :: TyPrec -> TcCoercion -> SDoc
ppr_forall_co p ty
  = maybeParen p FunPrec $
    sep [pprForAllImplicit tvs, ppr_co TopPrec rho]
  where
    (tvs,  rho) = split1 [] ty
    split1 tvs (TcForAllCo tv ty) = split1 (tv:tvs) ty
    split1 tvs ty                 = (reverse tvs, ty)

{-
%************************************************************************
%*                                                                      *
                  HsWrapper
*                                                                      *
************************************************************************
-}

data HsWrapper
  = WpHole                      -- The identity coercion

  | WpCompose HsWrapper HsWrapper
       -- (wrap1 `WpCompose` wrap2)[e] = wrap1[ wrap2[ e ]]
       --
       -- Hence  (\a. []) `WpCompose` (\b. []) = (\a b. [])
       -- But    ([] a)   `WpCompose` ([] b)   = ([] b a)

  | WpFun HsWrapper HsWrapper TcType TcType
       -- (WpFun wrap1 wrap2 t1 t2)[e] = \(x:t1). wrap2[ e wrap1[x] ] :: t2
       -- So note that if  wrap1 :: exp_arg <= act_arg
       --                  wrap2 :: act_res <= exp_res
       --           then   WpFun wrap1 wrap2 : (act_arg -> arg_res) <= (exp_arg -> exp_res)
       -- This isn't the same as for mkTcFunCo, but it has to be this way
       -- because we can't use 'sym' to flip around these HsWrappers

  | WpCast TcCoercion         -- A cast:  [] `cast` co
                              -- Guaranteed not the identity coercion
                              -- At role Representational

        -- Evidence abstraction and application
        -- (both dictionaries and coercions)
  | WpEvLam EvVar               -- \d. []       the 'd' is an evidence variable
  | WpEvApp EvTerm              -- [] d         the 'd' is evidence for a constraint
  | WpEvPrimApp TcCoercion      -- [] @~ d      the 'd' will be an *unboxed* coercion
    
        -- Kind and Type abstraction and application
  | WpTyLam TyVar       -- \a. []  the 'a' is a type/kind variable (not coercion var)
  | WpTyApp KindOrType  -- [] t    the 't' is a type (not coercion)


  | WpLet TcEvBinds             -- Non-empty (or possibly non-empty) evidence bindings,
                                -- so that the identity coercion is always exactly WpHole
  deriving (Data.Data, Data.Typeable)


(<.>) :: HsWrapper -> HsWrapper -> HsWrapper
WpHole <.> c = c
c <.> WpHole = c
c1 <.> c2    = c1 `WpCompose` c2

mkWpFun :: HsWrapper -> HsWrapper -> TcType -> TcType -> HsWrapper
mkWpFun WpHole       WpHole       _  _  = WpHole
mkWpFun WpHole       (WpCast co2) t1 _  = WpCast (mkTcFunCo Representational (mkTcRepReflCo t1) co2)
mkWpFun (WpCast co1) WpHole       _  t2 = WpCast (mkTcFunCo Representational (mkTcSymCo co1) (mkTcRepReflCo t2))
mkWpFun (WpCast co1) (WpCast co2) _  _  = WpCast (mkTcFunCo Representational (mkTcSymCo co1) co2)
mkWpFun co1          co2          t1 t2 = WpFun co1 co2 t1 t2

mkWpCast :: TcCoercion -> HsWrapper
mkWpCast co
  | isTcReflCo co = WpHole
  | otherwise     = ASSERT2(tcCoercionRole co == Representational, ppr co)
                    WpCast co

-- | Make a wrapper from the list of types returned by a tcInstTyCoVars. This
-- list of types contains only type and coercion variables.
mkWpTyEvApps :: [Type] -> HsWrapper
mkWpTyEvApps tys = mk_co_app_fn wp_ty_or_ev_app tys
  where wp_ty_or_ev_app ty
          | Just co <- isCoercionTy_maybe ty
          = WpEvPrimApp (mkTcCoercion co)

          | otherwise
          = WpTyApp ty

mkWpTyApps :: [Type] -> HsWrapper
mkWpTyApps tys = mk_co_app_fn WpTyApp tys

mkWpEvApps :: [Boxity] -> [EvTerm] -> HsWrapper
mkWpEvApps boxities args = mk_co_app_fn wp_ev_app (zip (map isBoxed boxities) args)

wp_ev_app :: (Bool, EvTerm) -> HsWrapper
wp_ev_app (True,  evterm) = WpEvApp evterm
wp_ev_app (False, evterm) = WpEvPrimApp (evTermCoercion evterm)

mkWpEvVarApps :: [EvVar] -> HsWrapper
mkWpEvVarApps vs = mk_co_app_fn wp_ev_app (zip (map (not . isUnLiftedType . varType) vs)
                                               (map EvId vs))

mkWpTyLams :: [TyVar] -> HsWrapper
mkWpTyLams ids = mk_co_lam_fn WpTyLam ids

mkWpLams :: [Var] -> HsWrapper
mkWpLams ids = mk_co_lam_fn WpEvLam ids

mkWpLet :: TcEvBinds -> HsWrapper
-- This no-op is a quite a common case
mkWpLet (EvBinds b) | isEmptyBag b = WpHole
mkWpLet ev_binds                   = WpLet ev_binds

mk_co_lam_fn :: (a -> HsWrapper) -> [a] -> HsWrapper
mk_co_lam_fn f as = foldr (\x wrap -> f x <.> wrap) WpHole as

mk_co_app_fn :: (a -> HsWrapper) -> [a] -> HsWrapper
-- For applications, the *first* argument must
-- come *last* in the composition sequence
mk_co_app_fn f as = foldr (\x wrap -> wrap <.> f x) WpHole as

idHsWrapper :: HsWrapper
idHsWrapper = WpHole

isIdHsWrapper :: HsWrapper -> Bool
isIdHsWrapper WpHole = True
isIdHsWrapper _      = False

{-
************************************************************************
*                                                                      *
                  Evidence bindings
*                                                                      *
************************************************************************
-}

data TcEvBinds
  = TcEvBinds           -- Mutable evidence bindings
       EvBindsVar       -- Mutable because they are updated "later"
                        --    when an implication constraint is solved

  | EvBinds             -- Immutable after zonking
       (Bag EvBind)

  deriving( Data.Typeable )

data EvBindsVar = EvBindsVar (IORef EvBindMap) Unique
     -- The Unique is for debug printing and the ability to roll back
     -- changes in tryTcS

instance Data.Data TcEvBinds where
  -- Placeholder; we can't travers into TcEvBinds
  toConstr _   = abstractConstr "TcEvBinds"
  gunfold _ _  = error "gunfold"
  dataTypeOf _ = Data.mkNoRepType "TcEvBinds"

-----------------
newtype EvBindMap 
  = EvBindMap { 
       ev_bind_varenv :: VarEnv EvBind
    }       -- Map from evidence variables to evidence terms

emptyEvBindMap :: EvBindMap
emptyEvBindMap = EvBindMap { ev_bind_varenv = emptyVarEnv }

extendEvBinds :: EvBindMap -> EvVar -> EvTerm -> CtLoc -> EvBindMap
extendEvBinds bs v t l
  = EvBindMap { ev_bind_varenv = extendVarEnv (ev_bind_varenv bs) v
                                              (EvBind { evb_var  = v
                                                      , evb_term = t
                                                      , evb_loc  = l}) }

dropEvBind :: EvBindMap -> EvVar -> EvBindMap
dropEvBind bs v
  = EvBindMap { ev_bind_varenv = delVarEnv (ev_bind_varenv bs) v }

lookupEvBind :: EvBindMap -> EvVar -> Maybe EvBind
lookupEvBind bs = lookupVarEnv (ev_bind_varenv bs)

evBindMapBinds :: EvBindMap -> Bag EvBind
evBindMapBinds bs 
  = foldVarEnv consBag emptyBag (ev_bind_varenv bs)

-----------------
-- All evidence is bound by EvBinds; no side effects
data EvBind = EvBind { evb_var  :: EvVar
                     , evb_term :: EvTerm
                     , evb_loc  :: CtLoc }

evBindVar :: EvBind -> EvVar
evBindVar = evb_var

data EvTerm
  = EvId EvId                    -- Any sort of evidence Id, including coercions

  | EvCoercion TcCoercion        -- (Boxed) coercion bindings
                                 -- See Note [Coercion evidence terms]

  | EvCast EvTerm TcCoercion     -- d |> co, the coercion being at role representational

  | EvDFunApp DFunId             -- Dictionary instance application
       [Type] [EvTerm]

  | EvTupleSel EvTerm  Int       -- n'th component of the tuple, 0-indexed

  | EvTupleMk [EvTerm]           -- tuple built from this stuff

  | EvDelayedError Type FastString  -- Used with Opt_DeferTypeErrors
                               -- See Note [Deferring coercion errors to runtime]
                               -- in TcSimplify

  | EvSuperClass EvTerm Int      -- n'th superclass. Used for both equalities and
                                 -- dictionaries, even though the former have no
                                 -- selector Id.  We count up from _0_

  | EvLit EvLit       -- Dictionary for KnownNat and KnownSymbol classes.
                      -- Note [KnownNat & KnownSymbol and EvLit]

  deriving( Data.Data, Data.Typeable)


data EvLit
  = EvNum Integer
  | EvStr FastString
    deriving( Data.Data, Data.Typeable)

{-
Note [Coercion evidence terms]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A "coercion evidence term" takes one of these forms
   co_tm ::= EvId v           where v :: t1 ~ t2
           | EvCoercion co
           | EvCast co_tm co

We do quite often need to get a TcCoercion from an EvTerm; see
'evTermCoercion'.

INVARIANT: The evidence for any constraint with type (t1~t2) is 
a coercion evidence term.  Consider for example
    [G] d :: F Int a
If we have
    ax7 a :: F Int a ~ (a ~ Bool)
then we do NOT generate the constraint
    [G] (d |> ax7 a) :: a ~ Bool
because that does not satisfy the invariant (d is not a coercion variable).  
Instead we make a binding
    g1 :: a~Bool = g |> ax7 a
and the constraint
    [G] g1 :: a~Bool
See Trac [7238] and Note [Bind new Givens immediately] in TcSMonad

Note [EvBinds/EvTerm]
~~~~~~~~~~~~~~~~~~~~~
How evidence is created and updated. Bindings for dictionaries,
and coercions and implicit parameters are carried around in TcEvBinds
which during constraint generation and simplification is always of the
form (TcEvBinds ref). After constraint simplification is finished it
will be transformed to t an (EvBinds ev_bag).

Evidence for coercions *SHOULD* be filled in using the TcEvBinds
However, all EvVars that correspond to *wanted* coercion terms in
an EvBind must be mutable variables so that they can be readily
inlined (by zonking) after constraint simplification is finished.

Conclusion: a new wanted coercion variable should be made mutable.
[Notice though that evidence variables that bind coercion terms
 from super classes will be "given" and hence rigid]


Note [KnownNat & KnownSymbol and EvLit]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A part of the type-level literals implementation are the classes
"KnownNat" and "KnownSymbol", which provide a "smart" constructor for
defining singleton values.  Here is the key stuff from GHC.TypeLits

  class KnownNat (n :: Nat) where
    natSing :: SNat n

  newtype SNat (n :: Nat) = SNat Integer

Conceptually, this class has infinitely many instances:

  instance KnownNat 0       where natSing = SNat 0
  instance KnownNat 1       where natSing = SNat 1
  instance KnownNat 2       where natSing = SNat 2
  ...

In practice, we solve `KnownNat` predicates in the type-checker
(see typecheck/TcInteract.hs) because we can't have infinately many instances.
The evidence (aka "dictionary") for `KnownNat` is of the form `EvLit (EvNum n)`.

We make the following assumptions about dictionaries in GHC:
  1. The "dictionary" for classes with a single method---like `KnownNat`---is
     a newtype for the type of the method, so using a evidence amounts
     to a coercion, and
  2. Newtypes use the same representation as their definition types.

So, the evidence for `KnownNat` is just a value of the representation type,
wrapped in two newtype constructors: one to make it into a `SNat` value,
and another to make it into a `KnownNat` dictionary.

Also note that `natSing` and `SNat` are never actually exposed from the
library---they are just an implementation detail.  Instead, users see
a more convenient function, defined in terms of `natSing`:

  natVal :: KnownNat n => proxy n -> Integer

The reason we don't use this directly in the class is that it is simpler
and more efficient to pass around an integer rather than an entier function,
especialy when the `KnowNat` evidence is packaged up in an existential.

The story for kind `Symbol` is analogous:
  * class KnownSymbol
  * newtype SSymbol
  * Evidence: EvLit (EvStr n)
-}

mkEvCast :: EvTerm -> TcCoercion -> EvTerm
mkEvCast ev lco
  | ASSERT2(tcCoercionRole lco == Representational, (vcat [ptext (sLit "Coercion of wrong role passed to mkEvCast:"), ppr ev, ppr lco]))
    isTcReflCo lco = ev
  | otherwise      = EvCast ev lco

emptyTcEvBinds :: TcEvBinds
emptyTcEvBinds = EvBinds emptyBag

isEmptyTcEvBinds :: TcEvBinds -> Bool
isEmptyTcEvBinds (EvBinds b)    = isEmptyBag b
isEmptyTcEvBinds (TcEvBinds {}) = panic "isEmptyTcEvBinds"


evTermCoercion :: EvTerm -> TcCoercion
-- Applied only to EvTerms of type (s~t)
-- See Note [Coercion evidence terms]
evTermCoercion (EvId v)        = mkTcCoVarCo v
evTermCoercion (EvCoercion co) = co
evTermCoercion (EvCast tm co)  = TcCastCo (evTermCoercion tm) co
evTermCoercion tm = pprPanic "evTermCoercion" (ppr tm)

evVarsOfTerm :: EvTerm -> VarSet
evVarsOfTerm (EvId v)             = unitVarSet v
evVarsOfTerm (EvCoercion co)      = coVarsOfTcCo co
evVarsOfTerm (EvDFunApp _ _ evs)  = evVarsOfTerms evs
evVarsOfTerm (EvTupleSel v _)     = evVarsOfTerm v
evVarsOfTerm (EvSuperClass v _)   = evVarsOfTerm v
evVarsOfTerm (EvCast tm co)       = evVarsOfTerm tm `unionVarSet` coVarsOfTcCo co
evVarsOfTerm (EvTupleMk evs)      = evVarsOfTerms evs
evVarsOfTerm (EvDelayedError _ _) = emptyVarSet
evVarsOfTerm (EvLit _)            = emptyVarSet

evVarsOfTerms :: [EvTerm] -> VarSet
evVarsOfTerms = mapUnionVarSet evVarsOfTerm

-- | Do SCC analysis on a bag of 'EvBind's.
sccEvBinds :: Bag EvBind -> [SCC EvBind]
sccEvBinds bs = stronglyConnCompFromEdgedVertices edges
  where
    edges :: [(EvBind, EvVar, [EvVar])]
    edges = foldrBag ((:) . mk_node) [] bs 

    mk_node :: EvBind -> (EvBind, EvVar, [EvVar])
    mk_node b@(EvBind { evb_var = var, evb_term = term })
      = (b, var, varSetElems (evVarsOfTerm term `unionVarSet`
                              coVarsOfType (varType var)))

-- | Get the set of EvVars bound in a bag of EvBinds.
evBindsVars :: Bag EvBind -> VarSet
evBindsVars = foldrBag (\ (EvBind { evb_var = b }) bs -> extendVarSet bs b)
                       emptyVarSet 

-- | Create a coercion substitution from a bunch of EvBinds.
evBindsSubst :: Bag EvBind -> TCvSubst
evBindsSubst = evBindsSubstX emptyTCvSubst

-- | Extends a coercion substitution from a bunch of EvBinds. For EvBinds
-- that don't map to a coercion, just don't include the mapping.
evBindsSubstX :: TCvSubst -> Bag EvBind -> TCvSubst
evBindsSubstX subst = foldl combine subst . sccEvBinds
  where
    combine env (AcyclicSCC (EvBind { evb_var = v, evb_term = ev_term }))
      | Just co <- convert env ev_term
      = extendTCvSubstAndInScope env v (mkCoercionTy co)
    combine env _
      = env

    convert env (EvCoercion tc_co) = tcCoercionToCoercion env tc_co
    convert env (EvId v)
      | Just co <- lookupCoVar env v = Just co
      | isCoVar v                    = Just $ mkCoVarCo v
      | otherwise                    = Nothing
    convert env (EvCast tm1 tc_co2)
      | Just co1 <- convert env tm1
      = mkCoCast co1 <$> tcCoercionToCoercion env tc_co2
      | otherwise
      = Nothing
    convert _ _ = Nothing  -- this can happen with superclass equalities!

-- | Get a mapping from covars to coercions induced by an EvBinds
evBindsCvSubstEnv :: Bag EvBind -> CvSubstEnv
evBindsCvSubstEnv = getCvSubstEnv . evBindsSubst

{-
************************************************************************
*                                                                      *
                  Pretty printing
*                                                                      *
************************************************************************
-}

instance Outputable HsWrapper where
  ppr co_fn = pprHsWrapper (ptext (sLit "<>")) co_fn

pprHsWrapper :: SDoc -> HsWrapper -> SDoc
-- In debug mode, print the wrapper
-- otherwise just print what's inside
pprHsWrapper doc wrap
  = getPprStyle (\ s -> if (dumpStyle s && debugIsOn) || debugStyle s
                        then (help (add_parens doc) wrap False)
                        else doc )
  where
    help :: (Bool -> SDoc) -> HsWrapper -> Bool -> SDoc
    -- True  <=> appears in function application position
    -- False <=> appears as body of let or lambda
    help it WpHole             = it
    help it (WpCompose f1 f2)  = help (help it f2) f1
    help it (WpFun f1 f2 t1 _) = add_parens $ ptext (sLit "\\(x") <> dcolon <> ppr t1 <> ptext (sLit ").") <+>
                                              help (\_ -> it True <+> help (\_ -> ptext (sLit "x")) f1 True) f2 False
    help it (WpCast co)   = add_parens $ sep [it False, nest 2 (ptext (sLit "|>")
                                              <+> pprParendTcCo co)]
    help it (WpEvApp id)    = no_parens  $ sep [it True, nest 2 (ppr id)]
    help it (WpEvPrimApp co)= no_parens  $ sep [it True, text "@~" <+> nest 2 (ppr co)]
    help it (WpTyApp ty)    = no_parens  $ sep [it True, ptext (sLit "@") <+> pprParendType ty]
    help it (WpEvLam id)    = add_parens $ sep [ ptext (sLit "\\") <> pp_bndr id, it False]
    help it (WpTyLam tv)    = add_parens $ sep [ptext (sLit "/\\") <> pp_bndr tv, it False]
    help it (WpLet binds)   = add_parens $ sep [ptext (sLit "let") <+> braces (ppr binds), it False]

    pp_bndr v = pprBndr LambdaBind v <> dot

    add_parens, no_parens :: SDoc -> Bool -> SDoc
    add_parens d True  = parens d
    add_parens d False = d
    no_parens d _ = d

instance Outputable TcEvBinds where
  ppr (TcEvBinds v) = ppr v
  ppr (EvBinds bs)  = ptext (sLit "EvBinds") <> braces (vcat (map ppr (bagToList bs)))

instance Outputable EvBindsVar where
  ppr (EvBindsVar _ u) = ptext (sLit "EvBindsVar") <> angleBrackets (ppr u)

instance Uniquable EvBindsVar where
  getUnique (EvBindsVar _ u) = u

instance Outputable EvBind where
  ppr (EvBind { evb_var = v, evb_term = e })
    = sep [ ppr v, nest 2 $ equals <+> ppr e ]
   -- We cheat a bit and pretend EqVars are CoVars for the purposes of pretty printing

instance Outputable EvTerm where
  ppr (EvId v)           = ppr v
  ppr (EvCast v co)      = ppr v <+> (ptext (sLit "`cast`")) <+> pprParendTcCo co
  ppr (EvCoercion co)    = ptext (sLit "CO") <+> ppr co
  ppr (EvTupleSel v n)   = ptext (sLit "tupsel") <> parens (ppr (v,n))
  ppr (EvTupleMk vs)     = ptext (sLit "tupmk") <+> ppr vs
  ppr (EvSuperClass d n) = ptext (sLit "sc") <> parens (ppr (d,n))
  ppr (EvDFunApp df tys ts) = ppr df <+> sep [ char '@' <> ppr tys, ppr ts ]
  ppr (EvLit l)          = ppr l
  ppr (EvDelayedError ty msg) =     ptext (sLit "error") 
                                <+> sep [ char '@' <> ppr ty, ppr msg ]

instance Outputable EvLit where
  ppr (EvNum n) = integer n
  ppr (EvStr s) = text (show s)
