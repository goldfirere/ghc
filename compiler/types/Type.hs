-- (c) The University of Glasgow 2006
-- (c) The GRASP/AQUA Project, Glasgow University, 1998
--
-- Type - public interface

{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Main functions for manipulating types and type-related things
module Type (
        -- Note some of this is just re-exports from TyCon..

        -- * Main data types representing Types
        -- $type_classification

        -- $representation_types
        TyThing(..), Type, VisibilityFlag(..), KindOrType, PredType, ThetaType,
        Var, TyVar, isTyVar, TyCoVar, Binder, TyLit(..),

        -- ** Constructing and deconstructing types
        mkOnlyTyVarTy, mkOnlyTyVarTys, getTyVar, getTyVar_maybe, repGetTyVar_maybe,
        getCastedTyVar_maybe,
        getTyCoVar_maybe, mkTyCoVarTy, mkTyCoVarTys,

        mkAppTy, mkAppTys, splitAppTy, splitAppTys,
        splitAppTy_maybe, repSplitAppTy_maybe,

        mkFunTy, mkFunTys, splitFunTy, splitFunTy_maybe,
        splitFunTys, splitFunTysN,
        funResultTy, funArgTy,

        mkTyConApp, mkTyConTy,
        tyConAppTyCon_maybe, tyConAppTyConPicky_maybe,
        tyConAppArgs_maybe, tyConAppTyCon, tyConAppArgs,
        splitTyConApp_maybe, splitTyConApp, tyConAppArgN, nextRole,

        mkForAllTy, mkForAllTys, mkInvForAllTys, mkVisForAllTys,
        mkNamedForAllTy,
        splitForAllTy_maybe, splitForAllTys, splitForAllTy,
        splitNamedForAllTys, splitNamedForAllTysB,
        mkPiType, mkPiTypes, mkPiTypesNoTv, mkPiTypesPreferFunTy,
        piResultTy, piResultTys,
        applyTys, applyTysD, applyTysX, isForAllTy, dropForAlls,

        mkNumLitTy, isNumLitTy,
        mkStrLitTy, isStrLitTy,

        mkCastTy, splitCastTy_maybe, mkCoercionTy,

        coAxNthLHS,
        stripCoercionTy, splitCoercionType_maybe,

        splitForAllTysInvisible, filterInvisibles,
        synTyConResKind,
        tyConBinders,

        -- Analyzing types
        analyzeType, TypeAnalysis(..),
        TyCoMapper(..), mapType, mapCoercion, mapCoercionArg,
        
        -- (Newtypes)
        newTyConInstRhs,

        -- Pred types
        mkFamilyTyConApp,
        isDictLikeTy,
        mkEqPred, mkCoerciblePred, mkEqPredRole,
        mkPrimEqPred, mkReprPrimEqPred, mkPrimEqPredRole,
        equalityTyCon,
        mkHeteroPrimEqPred, mkHeteroReprPrimEqPred,
        mkClassPred,
        isClassPred, isEqPred, isNomEqPred,
        isIPPred, isIPPred_maybe, isIPTyCon, isIPClass,

        -- Deconstructing predicate types
        PredTree(..), EqRel(..), eqRelRole, classifyPredType,
        getClassPredTys, getClassPredTys_maybe,
        getEqPredTys, getEqPredTys_maybe, getEqPredRole,
        isEqPredLifted, getEqPredBoxity, predTypeEqRel,

        -- ** Binders
        mkNamedBinder, mkAnonBinder, isNamedBinder, isAnonBinder,
        isIdLikeBinder, binderVisibility, binderVar_maybe,
        binderVar, binderRelevantType_maybe, caseBinder,
        partitionBinders, partitionBindersIntoBinders,
        binderType, isVisibleBinder, isInvisibleBinder,
        
        -- ** Common type constructors
        funTyCon,

        -- ** Predicates on types
        isTyCoVarTy, allDistinctTyVars,
        isTyVarTy, isFunTy, isDictTy, isPredTy, isVoidTy, isCoercionTy,
        isCoercionTy_maybe, isCoercionType, isNamedForAllTy,

        -- (Lifting and boxity)
        isUnLiftedType, isUnboxedTupleType, isAlgType, isClosedAlgType,
        isPrimitiveType, isStrictType, isLevityTy, isLevityVar, getLevity,

        -- * Main data types representing Kinds
        Kind,

        -- ** Finding the kind of a type
        typeKind,

        -- ** Common Kinds
        liftedTypeKind, unliftedTypeKind,
        constraintKind,

        -- ** Common Kind type constructors
        liftedTypeKindTyCon, unliftedTypeKindTyCon,
        constraintKindTyCon,

        -- * Type free variables
        tyCoVarsOfType, tyCoVarsOfTypes, coVarsOfType,
        coVarsOfTypes, closeOverKinds,
        splitDepVarsOfType, splitDepVarsOfTypes,
        expandTypeSynonyms,
        typeSize, varSetElemsWellScoped,

        -- * Type comparison
        eqType, eqTypeX, eqTypes, cmpType, cmpTypes, cmpTypeX, cmpTypesX, cmpTc,
        eqTyCoVarBndrs, eraseType, EType(..), EKind, EBinder(..),

        -- * Forcing evaluation of types
        seqType, seqTypes,

        -- * Other views onto Types
        coreView, coreViewOneStarKind, tcView,

        UnaryType, RepType(..), flattenRepType, repType,
        tyConsOfType,

        -- * Type representation for the code generator
        typePrimRep, typeRepArity,

        -- * Main type substitution data types
        TvSubstEnv,     -- Representation widely visible
        TCvSubst(..),    -- Representation visible to a few friends

        -- ** Manipulating type substitutions
        emptyTvSubstEnv, emptyTCvSubst, mkEmptyTCvSubst,

        mkTCvSubst, mkOpenTCvSubst, zipOpenTCvSubst, zipTopTCvSubst, mkTopTCvSubst,
        notElemTCvSubst,
        getTvSubstEnv, setTvSubstEnv,
        zapTCvSubst, getTCvInScope,
        extendTCvInScope, extendTCvInScopeList,
        extendTCvSubst, extendTCvSubstList,
        isInScope, composeTCvSubstEnv, composeTCvSubst, zipTyCoEnv,
        isEmptyTCvSubst, unionTCvSubst,

        -- ** Performing substitution on types and kinds
        substTy, substTys, substTyWith, substTysWith, substTheta,
        substTyCoVar, substTyCoVars, substTyVarBndr, substTyCoVarBndr,
        cloneTyVarBndr, lookupTyVar, lookupVar, substTelescope,

        -- * Pretty-printing
        pprType, pprParendType, pprTypeApp, pprTyThingCategory, pprTyThing,
        pprTCvBndr, pprTCvBndrs, pprForAll, pprForAllImplicit, pprUserForAll,
        pprSigmaType,
        pprTheta, pprThetaArrowTy, pprClassPred,
        pprKind, pprParendKind, pprSourceTyCon,
        TyPrec(..), maybeParen, pprSigmaTypeExtraCts,
        pprTcApp, pprPrefixApp, pprArrowChain,

        -- * Tidying type related things up for printing
        tidyType,      tidyTypes,
        tidyOpenType,  tidyOpenTypes,
        tidyOpenKind,
        tidyTyCoVarBndr, tidyTyCoVarBndrs, tidyFreeTyCoVars,
        tidyOpenTyCoVar, tidyOpenTyCoVars,
        tidyTyVarOcc,
        tidyTopType,
        tidyKind
    ) where

#include "HsVersions.h"

-- We import the representation and primitive functions from TyCoRep.
-- Many things are reexported, but not the representation!

import Kind
import TyCoRep

-- friends:
import Var
import VarEnv
import VarSet
import NameEnv

import Class
import TyCon
import TysPrim
import {-# SOURCE #-} TysWiredIn ( eqTyCon, coercibleTyCon, typeNatKind, typeSymbolKind )
import PrelNames
import CoAxiom
import {-# SOURCE #-} Coercion

-- others
import BasicTypes       ( Arity, RepArity, Boxity(..) )
import Util
import Outputable
import FastString
import Pair
import ListSetOps

import Data.List        ( partition, sortBy, mapAccumL )
import Maybes           ( orElse )
import Data.Maybe       ( isJust )
import Control.Monad    ( guard, liftM )
import Control.Applicative ( (<$>) )
import Control.Arrow    ( first, second )

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ( Applicative, (<*>) )
#endif

-- $type_classification
-- #type_classification#
--
-- Types are one of:
--
-- [Unboxed]            Iff its representation is other than a pointer
--                      Unboxed types are also unlifted.
--
-- [Lifted]             Iff it has bottom as an element.
--                      Closures always have lifted types: i.e. any
--                      let-bound identifier in Core must have a lifted
--                      type. Operationally, a lifted object is one that
--                      can be entered.
--                      Only lifted types may be unified with a type variable.
--
-- [Algebraic]          Iff it is a type with one or more constructors, whether
--                      declared with @data@ or @newtype@.
--                      An algebraic type is one that can be deconstructed
--                      with a case expression. This is /not/ the same as
--                      lifted types, because we also include unboxed
--                      tuples in this classification.
--
-- [Data]               Iff it is a type declared with @data@, or a boxed tuple.
--
-- [Primitive]          Iff it is a built-in type that can't be expressed in Haskell.
--
-- Currently, all primitive types are unlifted, but that's not necessarily
-- the case: for example, @Int@ could be primitive.
--
-- Some primitive types are unboxed, such as @Int#@, whereas some are boxed
-- but unlifted (such as @ByteArray#@).  The only primitive types that we
-- classify as algebraic are the unboxed tuples.
--
-- Some examples of type classifications that may make this a bit clearer are:
--
-- @
-- Type         primitive       boxed           lifted          algebraic
-- -----------------------------------------------------------------------------
-- Int#         Yes             No              No              No
-- ByteArray#   Yes             Yes             No              No
-- (\# a, b \#)   Yes             No              No              Yes
-- (  a, b  )   No              Yes             Yes             Yes
-- [a]          No              Yes             Yes             Yes
-- @

-- $representation_types
-- A /source type/ is a type that is a separate type as far as the type checker is
-- concerned, but which has a more low-level representation as far as Core-to-Core
-- passes and the rest of the back end is concerned.
--
-- You don't normally have to worry about this, as the utility functions in
-- this module will automatically convert a source into a representation type
-- if they are spotted, to the best of it's abilities. If you don't want this
-- to happen, use the equivalent functions from the "TcType" module.

{-
************************************************************************
*                                                                      *
                Type representation
*                                                                      *
************************************************************************
-}

{-# INLINE coreView #-}
coreView :: Type -> Maybe Type
-- ^ In Core, we \"look through\" type synonyms: this
-- function tries to obtain a different view of the supplied type given this
--
-- Strips off the /top layer only/ of a type to give
-- its underlying representation type.
-- Returns Nothing if there is nothing to look through.
--
-- By being non-recursive and inlined, this case analysis gets efficiently
-- joined onto the case analysis that the caller is already doing
coreView (TyConApp tc tys)
  | Just (tenv, rhs, tys') <- coreExpandTyCon_maybe tc tys
  = Just (mkAppTys (substTy (mkTopTCvSubst tenv) rhs) tys')
               -- Its important to use mkAppTys, rather than (foldl AppTy),
               -- because the function part might well return a
               -- partially-applied type constructor; indeed, usually will!
coreView _                 = Nothing

-- | Like 'coreView', but it also "expands" @Constraint@ and @BOX@ to become
-- @TYPE Lifted@.
coreViewOneStarKind :: Type -> Maybe Type
coreViewOneStarKind = go Nothing
  where
    go _ t | Just t' <- coreView t                    = go (Just t') t'
    go _ (TyConApp tc []) | isStarKindSynonymTyCon tc = go (Just t') t'
      where t' = liftedTypeKind
    go res _ = res

-----------------------------------------------
{-# INLINE tcView #-}
tcView :: Type -> Maybe Type
-- ^ Similar to 'coreView', but for the type checker, which just looks through synonyms
tcView (TyConApp tc tys) | Just (tenv, rhs, tys') <- tcExpandTyCon_maybe tc tys
                         = Just (mkAppTys (substTy (mkTopTCvSubst tenv) rhs) tys')
tcView _                 = Nothing
  -- You might think that tcView belows in TcType rather than Type, but unfortunately
  -- it is needed by Unify, which is turn imported by Coercion (for MatchEnv and matchList).
  -- So we will leave it here to avoid module loops.

-----------------------------------------------
expandTypeSynonyms :: Type -> Type
-- ^ Expand out all type synonyms.  Actually, it'd suffice to expand out
-- just the ones that discard type variables (e.g.  type Funny a = Int)
-- But we don't know which those are currently, so we just expand all.
expandTypeSynonyms ty
  = go (mkEmptyTCvSubst (mkTyCoInScopeSet [ty] [])) ty
  where
    go subst (TyConApp tc tys)
      | Just (tenv, rhs, tys') <- tcExpandTyCon_maybe tc tys
      = let subst' = unionTCvSubst subst (mkTopTCvSubst tenv) in
        go subst' (mkAppTys rhs tys')
      | otherwise
      = TyConApp tc (map (go subst) tys)
    go _     (LitTy l)     = LitTy l
    go subst (TyVarTy tv)  = substTyVar subst tv
    go subst (AppTy t1 t2) = mkAppTy (go subst t1) (go subst t2)
    go subst (ForAllTy (Anon arg) res)
      = mkFunTy (go subst arg) (go subst res) 
    go subst (ForAllTy (Named tv vis) t)
      = let (subst', tv') = substTyVarBndrCallback go subst tv in
        ForAllTy (Named tv' vis) (go subst' t)
    go subst (CastTy ty co)  = mkCastTy (go subst ty) (go_co subst co)
    go subst (CoercionTy co) = mkCoercionTy (go_co subst co)

    go_co subst (Refl r ty)
      = mkReflCo r (go subst ty)
       -- NB: coercions are always expanded upon creation
    go_co subst (TyConAppCo r tc args)
      = mkTyConAppCo r tc (map (go_arg subst) args)
    go_co subst (AppCo co h arg)
      = mkAppCo (go_co subst co) (go_co subst h) (go_arg subst arg)
    go_co subst (ForAllCo cobndr co)
      = let (subst', cobndr') = go_cobndr subst cobndr in
        mkForAllCo cobndr' (go_co subst' co)
    go_co subst (CoVarCo cv)
      = substCoVar subst cv
    go_co subst (AxiomInstCo ax ind args)
      = mkAxiomInstCo ax ind (map (go_arg subst) args)
    go_co subst (PhantomCo h t1 t2)
      = mkPhantomCo (go_co subst h) (go subst t1) (go subst t2)
    go_co subst (UnsafeCo s r ty1 ty2)
      = mkUnsafeCo s r (go subst ty1) (go subst ty2)
    go_co subst (SymCo co)
      = mkSymCo (go_co subst co)
    go_co subst (TransCo co1 co2)
      = mkTransCo (go_co subst co1) (go_co subst co2)
    go_co subst (NthCo n co)
      = mkNthCo n (go_co subst co)
    go_co subst (LRCo lr co)
      = mkLRCo lr (go_co subst co)
    go_co subst (InstCo co arg)
      = mkInstCo (go_co subst co) (go_arg subst arg)
    go_co subst (CoherenceCo co1 co2)
      = mkCoherenceCo (go_co subst co1) (go_co subst co2)
    go_co subst (KindCo co)
      = mkKindCo (go_co subst co)
    go_co subst (KindAppCo co)
      = mkKindAppCo (go_co subst co)
    go_co subst (SubCo co)
      = mkSubCo (go_co subst co)
    go_co subst (AxiomRuleCo ax ts cs)
      = AxiomRuleCo ax (map (go subst) ts) (map (go_co subst) cs)

    go_arg subst (TyCoArg co)
      = TyCoArg (go_co subst co)
    go_arg subst (CoCoArg r h co1 co2)
      = CoCoArg r (go_co subst h) (go_co subst co1) (go_co subst co2)

      -- the "False" and "const" are to accommodate the type of
      -- substForAllCoBndrCallback, which is general enough to
      -- handle coercion optimization (which sometimes swaps the
      -- order of a coercion)
    go_cobndr = substForAllCoBndrCallback False go (const go_co)

{-
************************************************************************
*                                                                      *
   Analyzing types
*                                                                      *
************************************************************************

Use these definitions instead of doing a case-split on types. This allows
us to enforce the fact that any two types equal according to `eqType` are
treated the same.

-}

-- | This structure gives instructions for how to analyze a type, producing
-- a result of type @r@.
data TypeAnalysis r
  = TypeAnalysis
      { ta_tyvar    :: TyVar -> r
      , ta_tyconapp :: TyCon -> [Type] -> r  -- ^ does not include (->)!
      , ta_fun      :: Type -> Type -> r
      , ta_app      :: Type -> Type -> r     -- ^ first type is not a tycon
      , ta_forall   :: TyVar -> VisibilityFlag -> Type -> r
           -- ^ Only named foralls. Anon foralls are in ta_tyconapp
      , ta_lit      :: TyLit -> r
      , ta_cast     :: Type -> Coercion -> r
      , ta_coercion :: Coercion -> r
      }

analyzeType :: TypeAnalysis r -> Type -> r
analyzeType (TypeAnalysis { ta_tyvar    = tyvar
                          , ta_tyconapp = tyconapp
                          , ta_fun      = fun
                          , ta_app      = app
                          , ta_forall   = forall
                          , ta_lit      = lit
                          , ta_cast     = cast
                          , ta_coercion = coercion })
  = go
  where
    go ty | Just ty' <- coreView ty    = go ty'
    go (TyVarTy tv)                    = tyvar tv
    go (AppTy t1 t2)                   = app t1 t2
    go (TyConApp tc tys)               = tyconapp tc tys
    go (ForAllTy (Anon arg) res)       = fun arg res
    go (ForAllTy (Named tv vis) inner) = forall tv vis inner
    go (LitTy tylit)                   = lit tylit
    go (CastTy ty co)                  = cast ty co
    go (CoercionTy co)                 = coercion co

-- | This describes how a "map" operation over a type/coercion should behave
data TyCoMapper env m
  = TyCoMapper
      { tcm_smart :: Bool -- ^ Should the new type be created with smart
                         -- constructors?
      , tcm_tyvar :: env -> TyVar -> m Type
      , tcm_covar :: env -> CoVar -> m Coercion

      , tcm_tycobinder :: env -> TyCoVar -> VisibilityFlag -> m (env, TyCoVar)
          -- ^ The returned env is used in the extended scope
      }

mapType :: (Applicative m, Monad m) => TyCoMapper env m -> env -> Type -> m Type
mapType mapper@(TyCoMapper { tcm_smart = smart, tcm_tyvar = tyvar
                           , tcm_tycobinder = tybinder })
        env ty
  = go ty
  where
    go (TyVarTy tv) = tyvar env tv
    go (AppTy t1 t2) = mkappty <$> go t1 <*> go t2
    go (TyConApp tc tys) = mktyconapp tc <$> mapM go tys
    go (ForAllTy (Anon arg) res) = mkfunty <$> go arg <*> go res
    go (ForAllTy (Named tv vis) inner)
      = do { (env', tv') <- tybinder env tv vis
           ; inner' <- mapType mapper env' inner
           ; return $ ForAllTy (Named tv' vis) inner' }
    go ty@(LitTy {}) = return ty
    go (CastTy ty co) = mkcastty <$> go ty <*> mapCoercion mapper env co
    go (CoercionTy co) = CoercionTy <$> mapCoercion mapper env co

    (mktyconapp, mkappty, mkcastty, mkfunty)
      | smart     = (mkTyConApp, mkAppTy, mkCastTy, mkFunTy)
      | otherwise = (TyConApp,   AppTy,   CastTy,   ForAllTy . Anon)

mapCoercion :: (Applicative m, Monad m)
            => TyCoMapper env m -> env -> Coercion -> m Coercion
mapCoercion mapper@(TyCoMapper { tcm_smart = smart, tcm_covar = covar
                               , tcm_tycobinder = tycobinder })
            env co
  = go co
  where
    go (Refl r ty) = Refl r <$> mapType mapper env ty
    go (TyConAppCo r tc args)
      = mktyconappco r tc <$> mapM (mapCoercionArg mapper env) args
    go (AppCo c1 h c2) = mkappco <$> go c1
                                 <*> go h
                                 <*> mapCoercionArg mapper env c2
    go (ForAllCo cobndr co)
      = do { (env', cobndr') <- go_cobndr cobndr
           ; co' <- mapCoercion mapper env' co
           ; return $ mkforallco cobndr' co' }
    go (CoVarCo cv) = covar env cv
    go (AxiomInstCo ax i args)
      = mkaxiominstco ax i <$> mapM (mapCoercionArg mapper env) args
    go (PhantomCo co t1 t2)
      = mkphantomco <$> go co <*> mapType mapper env t1
                              <*> mapType mapper env t2
    go (UnsafeCo prov r t1 t2) = mkunsafeco prov r <$> mapType mapper env t1
                                                   <*> mapType mapper env t2
    go (SymCo co) = mksymco <$> go co
    go (TransCo c1 c2) = mktransco <$> go c1 <*> go c2
    go (AxiomRuleCo rule tys cos)
      = AxiomRuleCo rule <$> mapM (mapType mapper env) tys
                         <*> mapM go cos
    go (NthCo i co)        = mknthco i <$> go co
    go (LRCo lr co)        = mklrco lr <$> go co
    go (InstCo co arg)     = mkinstco <$> go co <*> mapCoercionArg mapper env arg
    go (CoherenceCo c1 c2) = mkcoherenceco <$> go c1 <*> go c2
    go (KindCo co)         = mkkindco <$> go co
    go (KindAppCo co)      = mkkindappco <$> go co
    go (SubCo co)          = mksubco <$> go co

    go_cobndr (ForAllCoBndr h tv1 tv2 m_cv)
      = do { h' <- go h
           ; (env1, tv1')  <-   tycobinder env  tv1  Invisible
           ; (env2, tv2')  <-   tycobinder env1 tv2  Invisible
           ; (env3, m_cv') <- m_tycobinder env2 m_cv Invisible
           ; return (env3, ForAllCoBndr h' tv1' tv2' m_cv') }
    m_tycobinder env Nothing  _   = return (env, Nothing)
    m_tycobinder env (Just v) vis = liftM (second Just) $ tycobinder env v vis
    
    ( mktyconappco, mkappco, mkaxiominstco, mkphantomco, mkunsafeco
      , mksymco, mktransco, mknthco, mklrco, mkinstco, mkcoherenceco
      , mkkindco, mkkindappco, mksubco, mkforallco)
      | smart
      = ( mkTyConAppCo, mkAppCo, mkAxiomInstCo, mkPhantomCo, mkUnsafeCo
        , mkSymCo, mkTransCo, mkNthCo, mkLRCo, mkInstCo, mkCoherenceCo
        , mkKindCo, mkKindAppCo, mkSubCo, mkForAllCo )
      | otherwise
      = ( TyConAppCo, AppCo, AxiomInstCo, PhantomCo, UnsafeCo
        , SymCo, TransCo, NthCo, LRCo, InstCo, CoherenceCo
        , KindCo, KindAppCo, SubCo, ForAllCo )

mapCoercionArg :: (Applicative m, Monad m)
               => TyCoMapper env m -> env -> CoercionArg -> m CoercionArg
mapCoercionArg mapper env (TyCoArg co) = TyCoArg <$> mapCoercion mapper env co
mapCoercionArg mapper env (CoCoArg r h c1 c2)
  = CoCoArg r <$> mapCoercion mapper env h
              <*> mapCoercion mapper env c1 <*> mapCoercion mapper env c2

{-
************************************************************************
*                                                                      *
\subsection{Constructor-specific functions}
*                                                                      *
************************************************************************


---------------------------------------------------------------------
                                TyVarTy
                                ~~~~~~~
-}

-- | Attempts to obtain the type variable underlying a 'Type', and panics with the
-- given message if this is not a type variable type. See also 'getTyVar_maybe'
getTyVar :: String -> Type -> TyVar
getTyVar msg ty = case getTyVar_maybe ty of
                    Just tv -> tv
                    Nothing -> panic ("getTyVar: " ++ msg)

isTyVarTy :: Type -> Bool
isTyVarTy ty = isJust (getTyVar_maybe ty)

isTyCoVarTy :: Type -> Bool
isTyCoVarTy ty = isJust (getTyCoVar_maybe ty)

-- | Attempts to obtain the type variable underlying a 'Type'
getTyVar_maybe :: Type -> Maybe TyVar
getTyVar_maybe ty | Just ty' <- coreView ty = getTyVar_maybe ty'
                  | otherwise               = repGetTyVar_maybe ty

-- | If the type is a tyvar, possibly under a cast, returns it, along
-- with the coercion. Thus, the co is :: kind tv ~R kind type
getCastedTyVar_maybe :: Type -> Maybe (TyVar, Coercion)
getCastedTyVar_maybe ty | Just ty' <- coreView ty = getCastedTyVar_maybe ty'
getCastedTyVar_maybe (CastTy (TyVarTy tv) co)     = Just (tv, co)
getCastedTyVar_maybe (TyVarTy tv)
  = Just (tv, mkReflCo Representational (tyVarKind tv))
getCastedTyVar_maybe _                            = Nothing

-- | Attempts to obtain the type variable underlying a 'Type', without
-- any expansion
repGetTyVar_maybe :: Type -> Maybe TyVar
repGetTyVar_maybe (TyVarTy tv) = Just tv
repGetTyVar_maybe _            = Nothing

-- | Attempts to obtain the type or coercion variable underlying a 'Type'
getTyCoVar_maybe :: Type -> Maybe TyCoVar
getTyCoVar_maybe ty | Just ty' <- coreView ty = getTyCoVar_maybe ty'
getTyCoVar_maybe (TyVarTy tv)                 = Just tv
getTyCoVar_maybe (CoercionTy (CoVarCo cv))    = Just cv
getTyCoVar_maybe _                            = Nothing

allDistinctTyVars :: [KindOrType] -> Bool
allDistinctTyVars tkvs = go emptyVarSet tkvs
  where
    go _      [] = True
    go so_far (ty : tys)
       = case getTyVar_maybe ty of
             Nothing -> False
             Just tv | tv `elemVarSet` so_far -> False
                     | otherwise -> go (so_far `extendVarSet` tv) tys

{-
---------------------------------------------------------------------
                                AppTy
                                ~~~~~
We need to be pretty careful with AppTy to make sure we obey the
invariant that a TyConApp is always visibly so.  mkAppTy maintains the
invariant: use it.
-}

-- | Applies a type to another, as in e.g. @k a@
mkAppTy :: Type -> Type -> Type
mkAppTy (TyConApp tc tys) ty2 = mkTyConApp tc (tys ++ [ty2])
mkAppTy ty1               ty2 = AppTy ty1 ty2
        -- Note that the TyConApp could be an
        -- under-saturated type synonym.  GHC allows that; e.g.
        --      type Foo k = k a -> k a
        --      type Id x = x
        --      foo :: Foo Id -> Foo Id
        --
        -- Here Id is partially applied in the type sig for Foo,
        -- but once the type synonyms are expanded all is well

mkAppTys :: Type -> [Type] -> Type
mkAppTys ty1                []   = ty1
mkAppTys (TyConApp tc tys1) tys2 = mkTyConApp tc (tys1 ++ tys2)
mkAppTys ty1                tys2 = foldl AppTy ty1 tys2

-------------
splitAppTy_maybe :: Type -> Maybe (Type, Type)
-- ^ Attempt to take a type application apart, whether it is a
-- function, type constructor, or plain type application. Note
-- that type family applications are NEVER unsaturated by this!
splitAppTy_maybe ty | Just ty' <- coreView ty
                    = splitAppTy_maybe ty'
splitAppTy_maybe ty = repSplitAppTy_maybe ty

-------------
repSplitAppTy_maybe :: Type -> Maybe (Type,Type)
-- ^ Does the AppTy split as in 'splitAppTy_maybe', but assumes that
-- any Core view stuff is already done
repSplitAppTy_maybe (ForAllTy (Anon ty1) ty2)
  = Just (TyConApp funTyCon [ty1], ty2)
repSplitAppTy_maybe (AppTy ty1 ty2)   = Just (ty1, ty2)
repSplitAppTy_maybe (TyConApp tc tys)
  | isDecomposableTyCon tc || tys `lengthExceeds` tyConArity tc
  , Just (tys', ty') <- snocView tys
  = Just (TyConApp tc tys', ty')    -- Never create unsaturated type family apps!
repSplitAppTy_maybe _other = Nothing
-------------
splitAppTy :: Type -> (Type, Type)
-- ^ Attempts to take a type application apart, as in 'splitAppTy_maybe',
-- and panics if this is not possible
splitAppTy ty = case splitAppTy_maybe ty of
                Just pr -> pr
                Nothing -> panic "splitAppTy"

-------------
splitAppTys :: Type -> (Type, [Type])
-- ^ Recursively splits a type as far as is possible, leaving a residual
-- type being applied to and the type arguments applied to it. Never fails,
-- even if that means returning an empty list of type applications.
splitAppTys ty = split ty ty []
  where
    split orig_ty ty args | Just ty' <- coreView ty = split orig_ty ty' args
    split _       (AppTy ty arg)        args = split ty ty (arg:args)
    split _       (TyConApp tc tc_args) args
      = let -- keep type families saturated
            n | isDecomposableTyCon tc = 0
              | otherwise              = tyConArity tc
            (tc_args1, tc_args2) = splitAt n tc_args
        in
        (TyConApp tc tc_args1, tc_args2 ++ args)
    split _   (ForAllTy (Anon ty1) ty2) args = ASSERT( null args )
                                               (TyConApp funTyCon [], [ty1,ty2])
    split orig_ty _                     args = (orig_ty, args)

{-
                      LitTy
                      ~~~~~
-}

mkNumLitTy :: Integer -> Type
mkNumLitTy n = LitTy (NumTyLit n)

-- | Is this a numeric literal. We also look through type synonyms.
isNumLitTy :: Type -> Maybe Integer
isNumLitTy ty | Just ty1 <- tcView ty = isNumLitTy ty1
isNumLitTy (LitTy (NumTyLit n)) = Just n
isNumLitTy _                    = Nothing

mkStrLitTy :: FastString -> Type
mkStrLitTy s = LitTy (StrTyLit s)

-- | Is this a symbol literal. We also look through type synonyms.
isStrLitTy :: Type -> Maybe FastString
isStrLitTy ty | Just ty1 <- tcView ty = isStrLitTy ty1
isStrLitTy (LitTy (StrTyLit s)) = Just s
isStrLitTy _                    = Nothing

{-
---------------------------------------------------------------------
                                FunTy
                                ~~~~~

Function types are represented with (ForAllTy (Anon ...) ...)
-}

mkFunTys :: [Type] -> Type -> Type
-- more efficient than foldr mkFunTy because of the InScopeSet business
-- We must be careful here to respect the invariant that all covars are
-- dependently quantified. See Note [Equality-constrained types] in
-- TyCoRep
mkFunTys args ty = mkForAllTys (snd $ mapAccumL to_binder in_scope args) ty
  where
    in_scope = mkInScopeSet $ tyCoVarsOfType ty

    to_binder :: InScopeSet -> PredType -> (InScopeSet, Binder)
    to_binder is ty
      | isCoercionType ty
      = let cv = mkFreshCoVarOfType is ty in
        (is `extendInScopeSet` cv, Named cv Invisible)
          -- we don't really need to extend in_scope, but we don't
          -- want lots of name shadowing later
      | otherwise
      = (is, Anon ty)

isFunTy :: Type -> Bool
isFunTy ty = isJust (splitFunTy_maybe ty)

splitFunTy :: Type -> (Type, Type)
-- ^ Attempts to extract the argument and result types from a type, and
-- panics if that is not possible. See also 'splitFunTy_maybe'
splitFunTy ty | Just ty' <- coreView ty = splitFunTy ty'
splitFunTy (ForAllTy (Anon arg) res)    = (arg, res)
splitFunTy other                        = pprPanic "splitFunTy" (ppr other)

splitFunTy_maybe :: Type -> Maybe (Type, Type)
-- ^ Attempts to extract the argument and result types from a type
splitFunTy_maybe ty | Just ty' <- coreView ty = splitFunTy_maybe ty'
splitFunTy_maybe (ForAllTy (Anon arg) res) = Just (arg, res)
splitFunTy_maybe _                         = Nothing

splitFunTys :: Type -> ([Type], Type)
splitFunTys ty = split [] ty ty
  where
    split args orig_ty ty | Just ty' <- coreView ty = split args orig_ty ty'
    split args _       (ForAllTy (Anon arg) res) = split (arg:args) res res
    split args orig_ty _                         = (reverse args, orig_ty)

splitFunTysN :: Int -> Type -> ([Type], Type)
-- ^ Split off exactly the given number argument types, and panics if that is not possible
splitFunTysN 0 ty = ([], ty)
splitFunTysN n ty = ASSERT2( isFunTy ty, int n <+> ppr ty )
                    case splitFunTy ty of { (arg, res) ->
                    case splitFunTysN (n-1) res of { (args, res) ->
                    (arg:args, res) }}

funResultTy :: Type -> Type
-- ^ Extract the function result type and panic if that is not possible
funResultTy ty = piResultTy ty (pprPanic "funResultTy" (ppr ty))

-- | Essentially 'funResultTy' on kinds handling pi-types too
piResultTy :: Type -> Type -> Type
piResultTy ty arg | Just ty' <- coreView ty = piResultTy ty' arg
piResultTy (ForAllTy (Anon _) res)     _   = res
piResultTy (ForAllTy (Named tv _) res) arg = substTyWith [tv] [arg] res
piResultTy ty arg                          = pprPanic "piResultTy"
                                                 (ppr ty $$ ppr arg)

-- | Fold 'piResultTy' over many types
piResultTys :: Type -> [Type] -> Type
piResultTys = foldl piResultTy

funArgTy :: Type -> Type
-- ^ Extract the function argument type and panic if that is not possible
funArgTy ty | Just ty' <- coreView ty = funArgTy ty'
funArgTy (ForAllTy (Anon arg) _res) = arg
funArgTy ty                         = pprPanic "funArgTy" (ppr ty)

{-
---------------------------------------------------------------------
                                TyConApp
                                ~~~~~~~~
-}

-- | A key function: builds a 'TyConApp' or 'FunTy' as appropriate to
-- its arguments.  Applies its arguments to the constructor from left to right.
mkTyConApp :: TyCon -> [Type] -> Type
mkTyConApp tycon tys
  | isFunTyCon tycon, [ty1,ty2] <- tys
  = ForAllTy (Anon ty1) ty2

  | otherwise
  = TyConApp tycon tys

-- splitTyConApp "looks through" synonyms, because they don't
-- mean a distinct type, but all other type-constructor applications
-- including functions are returned as Just ..

-- | Retrieve the tycon heading this type, if there is one. Does /not/
-- look through synonyms.
tyConAppTyConPicky_maybe :: Type -> Maybe TyCon
tyConAppTyConPicky_maybe (TyConApp tc _)       = Just tc
tyConAppTyConPicky_maybe (ForAllTy (Anon _) _) = Just funTyCon
tyConAppTyConPicky_maybe _                     = Nothing


-- | The same as @fst . splitTyConApp@
tyConAppTyCon_maybe :: Type -> Maybe TyCon
tyConAppTyCon_maybe ty | Just ty' <- coreView ty = tyConAppTyCon_maybe ty'
tyConAppTyCon_maybe (TyConApp tc _)       = Just tc
tyConAppTyCon_maybe (ForAllTy (Anon _) _) = Just funTyCon
tyConAppTyCon_maybe _                     = Nothing

tyConAppTyCon :: Type -> TyCon
tyConAppTyCon ty = tyConAppTyCon_maybe ty `orElse` pprPanic "tyConAppTyCon" (ppr ty)

-- | The same as @snd . splitTyConApp@
tyConAppArgs_maybe :: Type -> Maybe [Type]
tyConAppArgs_maybe ty | Just ty' <- coreView ty = tyConAppArgs_maybe ty'
tyConAppArgs_maybe (TyConApp _ tys)          = Just tys
tyConAppArgs_maybe (ForAllTy (Anon arg) res) = Just [arg,res]
tyConAppArgs_maybe _                         = Nothing

tyConAppArgs :: Type -> [Type]
tyConAppArgs ty = tyConAppArgs_maybe ty `orElse` pprPanic "tyConAppArgs" (ppr ty)

tyConAppArgN :: Int -> Type -> Type
-- Executing Nth
tyConAppArgN n ty
  = case tyConAppArgs_maybe ty of
      Just tys -> ASSERT2( n < length tys, ppr n <+> ppr tys ) tys `getNth` n
      Nothing  -> pprPanic "tyConAppArgN" (ppr n <+> ppr ty)

-- | Attempts to tease a type apart into a type constructor and the application
-- of a number of arguments to that constructor. Panics if that is not possible.
-- See also 'splitTyConApp_maybe'
splitTyConApp :: Type -> (TyCon, [Type])
splitTyConApp ty = case splitTyConApp_maybe ty of
                   Just stuff -> stuff
                   Nothing    -> pprPanic "splitTyConApp" (ppr ty)

-- | Attempts to tease a type apart into a type constructor and the application
-- of a number of arguments to that constructor
splitTyConApp_maybe :: Type -> Maybe (TyCon, [Type])
splitTyConApp_maybe ty | Just ty' <- coreView ty = splitTyConApp_maybe ty'
splitTyConApp_maybe (TyConApp tc tys)         = Just (tc, tys)
splitTyConApp_maybe (ForAllTy (Anon arg) res) = Just (funTyCon, [arg,res])
splitTyConApp_maybe _                         = Nothing

-- | What is the role assigned to the next parameter of this type? Usually,
-- this will be 'Nominal', but if the type is a 'TyConApp', we may be able to
-- do better. The type does *not* have to be well-kinded when applied for this
-- to work!
nextRole :: Type -> Role
nextRole ty
  | Just (tc, tys) <- splitTyConApp_maybe ty
  , let num_tys = length tys
  , num_tys < tyConArity tc
  = tyConRoles tc `getNth` num_tys

  | otherwise
  = Nominal

newTyConInstRhs :: TyCon -> [Type] -> Type
-- ^ Unwrap one 'layer' of newtype on a type constructor and its
-- arguments, using an eta-reduced version of the @newtype@ if possible.
-- This requires tys to have at least @newTyConInstArity tycon@ elements.
newTyConInstRhs tycon tys
    = ASSERT2( tvs `leLength` tys, ppr tycon $$ ppr tys $$ ppr tvs )
      applyTysX tvs rhs tys
  where
    (tvs, rhs) = newTyConEtadRhs tycon

{-
---------------------------------------------------------------------
                           CastTy
                           ~~~~~~
A casted type has its *kind* casted into something new.

Note [Weird typing rule for ForAllTy]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Here is the (truncated) typing rule for the dependent ForAllTy:

inner : kind
------------------------------------
ForAllTy (Named tv vis) inner : kind

Note that neither the inner type nor for ForAllTy itself have to have
kind *! But, it means that we should push any kind casts through the
ForAllTy. The only trouble is avoiding capture.

-}

-- | Make a 'CastTy'. The Coercion must be representational.
mkCastTy :: Type -> Coercion -> Type
-- Running example:
--   T :: forall k1. k1 -> forall k2. k2 -> Bool -> Maybe k1 -> *
--   co :: * ~R X    (maybe X is a newtype around *)
--   ty = T Nat 3 Symbol "foo" True (Just 2)
--
-- We wish to "push" the cast down as far as possible. See also
-- Note [Pushing down casts] in TyCoRep. Here is where we end
-- up:
--
--   (T Nat 3 Symbol |> <Symbol> -> <Bool> -> <Maybe Nat> -> co)
--      "foo" True (Just 2)
--
-- General approach:
-- 
mkCastTy ty (Refl {}) = ty
mkCastTy (CastTy ty co1) co2 = mkCastTy ty (co1 `mkTransCo` co2)
-- See Note [Weird typing rule for ForAllTy]
mkCastTy (ForAllTy (Named tv vis) inner_ty) co
  = -- have to make sure that pushing the co in doesn't capture the bound var!
    let fvs = tyCoVarsOfCo co
        empty_subst = mkEmptyTCvSubst (mkInScopeSet fvs)
        (subst, tv') = substTyCoVarBndr empty_subst tv
    in
    ForAllTy (Named tv' vis) (substTy subst inner_ty `mkCastTy` co)
mkCastTy ty co = -- NB: don't check if the coercion "from" type matches here;
                 -- there may be unzonked variables about!
                 let result = split_apps [] ty co in
                 ASSERT2( CastTy ty co `eqType` result
                        , ppr ty <+> dcolon <+> ppr (typeKind ty) $$
                          ppr co <+> dcolon <+> ppr (coercionKind co) $$
                          ppr result <+> dcolon <+> ppr (typeKind result) )
                 result
  where
    -- split_apps breaks apart any type applications, so we can see how far down
    -- to push the cast
    split_apps args (AppTy t1 t2) co
      = split_apps (t2:args) t1 co
    split_apps args (TyConApp tc tc_args) co
      | isDecomposableTyCon tc
      = affix_co (tyConKind tc) (mkTyConTy tc) (tc_args `chkAppend` args) co
      | otherwise -- not decomposable... but it may still be oversaturated
      = let (non_decomp_args, decomp_args) = splitAt (tyConArity tc) tc_args
            saturated_tc = mkTyConApp tc non_decomp_args
        in
        affix_co (typeKind saturated_tc) saturated_tc (decomp_args `chkAppend` args) co
            
    split_apps args (ForAllTy (Anon arg) res) co
      = affix_co (tyConKind funTyCon) (mkTyConTy funTyCon)
                 (arg : res : args) co
    split_apps args ty co
      = affix_co (typeKind ty) ty args co

    -- having broken everything apart, this figures out the point at which there
    -- are no more dependent quantifications, and puts the cast there
    affix_co _ ty [] co = no_double_casts ty co
    affix_co kind ty args co
      -- if kind contains any dependent quantifications, we can't push.
      -- apply arguments until it doesn't
      = let (bndrs, _inner_ki) = splitForAllTys kind
            (some_dep_bndrs, no_dep_bndrs) = span_from_end isAnonBinder bndrs
            (some_dep_args, rest_args) = splitAtList some_dep_bndrs args
            dep_subst = zipOpenTCvSubstBinders some_dep_bndrs some_dep_args
            used_no_dep_bndrs = takeList rest_args no_dep_bndrs
            rest_arg_tys = substTys dep_subst (map binderType used_no_dep_bndrs)
            co' = mkFunCos Representational
                           (map (mkReflCo Representational) rest_arg_tys)
                           co
        in
        ((ty `mkAppTys` some_dep_args) `no_double_casts` co') `mkAppTys` rest_args

    no_double_casts (CastTy ty co1) co2 = CastTy ty (co1 `mkTransCo` co2)
    no_double_casts ty              co  = CastTy ty co

    -- TODO (RAE): Make more efficient
    span_from_end :: (a -> Bool) -> [a] -> ([a], [a])
    span_from_end p as = let (xs, ys) = span p (reverse as) in
                         (reverse ys, reverse xs)

splitCastTy_maybe :: Type -> Maybe (Type, Coercion)
splitCastTy_maybe ty | Just ty' <- coreView ty = splitCastTy_maybe ty'
splitCastTy_maybe (CastTy ty co) = Just (ty, co)
splitCastTy_maybe _              = Nothing

{-
--------------------------------------------------------------------
                            CoercionTy
                            ~~~~~~~~~~
CoercionTy allows us to inject coercions into types. A CoercionTy
should appear only in the right-hand side of an application.
-}

mkCoercionTy :: Coercion -> Type
mkCoercionTy = CoercionTy

isCoercionTy :: Type -> Bool
isCoercionTy (CoercionTy _) = True
isCoercionTy _              = False

isCoercionTy_maybe :: Type -> Maybe Coercion
isCoercionTy_maybe (CoercionTy co) = Just co
isCoercionTy_maybe _               = Nothing

stripCoercionTy :: Type -> Coercion
stripCoercionTy (CoercionTy co) = co
stripCoercionTy ty              = pprPanic "stripCoercionTy" (ppr ty)

{-
---------------------------------------------------------------------
                                SynTy
                                ~~~~~

Notes on type synonyms
~~~~~~~~~~~~~~~~~~~~~~
The various "split" functions (splitFunTy, splitRhoTy, splitForAllTy) try
to return type synonyms wherever possible. Thus

        type Foo a = a -> a

we want
        splitFunTys (a -> Foo a) = ([a], Foo a)
not                                ([a], a -> a)

The reason is that we then get better (shorter) type signatures in
interfaces.  Notably this plays a role in tcTySigs in TcBinds.lhs.


                Representation types
                ~~~~~~~~~~~~~~~~~~~~

Note [Nullary unboxed tuple]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We represent the nullary unboxed tuple as the unary (but void) type
Void#.  The reason for this is that the ReprArity is never
less than the Arity (as it would otherwise be for a function type like
(# #) -> Int).

As a result, ReprArity is always strictly positive if Arity is. This
is important because it allows us to distinguish at runtime between a
thunk and a function takes a nullary unboxed tuple as an argument!
-}

type UnaryType = Type

data RepType = UbxTupleRep [UnaryType] -- INVARIANT: never an empty list (see Note [Nullary unboxed tuple])
             | UnaryRep UnaryType

instance Outputable RepType where
  ppr (UbxTupleRep tys) = ptext (sLit "UbxTupleRep") <+> ppr tys
  ppr (UnaryRep ty)     = ptext (sLit "UnaryRep")    <+> ppr ty

flattenRepType :: RepType -> [UnaryType]
flattenRepType (UbxTupleRep tys) = tys
flattenRepType (UnaryRep ty)     = [ty]

-- | Looks through:
--
--      1. For-alls
--      2. Synonyms
--      3. Predicates
--      4. All newtypes, including recursive ones, but not newtype families
--      5. Casts
--
-- It's useful in the back end of the compiler.
repType :: Type -> RepType
repType ty
  = go initRecTc ty
  where
    go :: RecTcChecker -> Type -> RepType
    go rec_nts ty                       -- Expand predicates and synonyms
      | Just ty' <- coreView ty
      = go rec_nts ty'

    go rec_nts ty@(ForAllTy (Named tv _) ty2)  -- Drop type foralls
      | isTyVar tv
      = go rec_nts ty2
      | otherwise
      = -- abstractions over coercions exist in the representation
        UnaryRep ty

    go rec_nts (TyConApp tc tys)        -- Expand newtypes
      | isNewTyCon tc
      , tys `lengthAtLeast` tyConArity tc
      , Just rec_nts' <- checkRecTc rec_nts tc   -- See Note [Expanding newtypes] in TyCon
      = go rec_nts' (newTyConInstRhs tc tys)

      | isUnboxedTupleTyCon tc
      = if null tys
         then UnaryRep voidPrimTy -- See Note [Nullary unboxed tuple]
         else UbxTupleRep (concatMap (flattenRepType . go rec_nts) non_levity_tys)
      where
          -- See Note [Unboxed tuple levity vars] in TyCon
        non_levity_tys = drop (length tys `div` 2) tys

    go rec_nts (CastTy ty _)
      = go rec_nts ty

    go _ ty@(CoercionTy _)
      = pprPanic "repType" (ppr ty)

    go _ ty = UnaryRep ty

-- ToDo: this could be moved to the code generator, using splitTyConApp instead
-- of inspecting the type directly.

-- | Discovers the primitive representation of a more abstract 'UnaryType'
typePrimRep :: UnaryType -> PrimRep
typePrimRep ty
  = case repType ty of
      UbxTupleRep _ -> pprPanic "typePrimRep: UbxTupleRep" (ppr ty)
      UnaryRep rep -> go rep
    where go (TyConApp tc _)   = tyConPrimRep tc
          go (ForAllTy _ _)    = PtrRep
          go (AppTy _ _)       = PtrRep      -- See Note [AppTy rep]
          go (TyVarTy _)       = PtrRep
          go (CastTy ty _)     = go ty
          go _                 = pprPanic "typePrimRep: UnaryRep" (ppr ty)

typeRepArity :: Arity -> Type -> RepArity
typeRepArity 0 _ = 0
typeRepArity n ty = case repType ty of
  UnaryRep (ForAllTy bndr ty) -> length (flattenRepType (repType (binderType bndr))) + typeRepArity (n - 1) ty
  _                           -> pprPanic "typeRepArity: arity greater than type can handle" (ppr (n, ty, repType ty))

isVoidTy :: Type -> Bool
-- True if the type has zero width
isVoidTy ty = case repType ty of
                UnaryRep (TyConApp tc _) -> isVoidRep (tyConPrimRep tc)
                _                        -> False

{-
Note [AppTy rep]
~~~~~~~~~~~~~~~~
Types of the form 'f a' must be of kind *, not #, so we are guaranteed
that they are represented by pointers.  The reason is that f must have
kind (kk -> kk) and kk cannot be unlifted; see Note [The kind invariant]
in TyCoRep.

---------------------------------------------------------------------
                                ForAllTy
                                ~~~~~~~~
-}

mkForAllTy :: Binder -> Type -> Type
mkForAllTy = ForAllTy 

-- | Make a dependent forall.
mkNamedForAllTy :: TyVar -> VisibilityFlag -> Type -> Type
mkNamedForAllTy tv vis = ForAllTy (Named tv vis)

-- | Wraps foralls over the type using the provided 'TyVar's from left to right
mkForAllTys :: [Binder] -> Type -> Type
mkForAllTys tyvars ty = foldr ForAllTy ty tyvars

-- | Like mkForAllTys, but assumes all variables are dependent and invisible,
-- a common case
mkInvForAllTys :: [TyCoVar] -> Type -> Type
mkInvForAllTys tvs = mkForAllTys (map (flip Named Invisible) tvs)

-- | Like mkForAllTys, but assumes all variables are dependent and visible
mkVisForAllTys :: [TyCoVar] -> Type -> Type
mkVisForAllTys tvs = mkForAllTys (map (flip Named Visible) tvs)

  -- TODO (RAE): should these ever produce Explicit?
mkPiType  :: Var -> Type -> Type
-- ^ Makes a @(->)@ type or an implicit forall type, depending
-- on whether it is given a type variable or a term variable.
-- This is used, for example, when producing the type of a lambda.
mkPiTypes :: [Var] -> Type -> Type
-- ^ 'mkPiType' for multiple type or value arguments

mkPiType v ty
   |  isTyVar v
   || isCoVar v = mkForAllTy (Named v Invisible) ty
   | otherwise  = mkForAllTy (Anon (varType v)) ty

mkPiTypes vs ty = foldr mkPiType ty vs

-- | Given a list of type-level vars, makes ForAllTys, preferring
-- anonymous binders if the variable is, in fact, not dependent.
-- All non-coercion binders are /visible/.
-- This used to
-- be @mkPiKinds@.
mkPiTypesPreferFunTy :: [TyCoVar] -> Type -> Type
mkPiTypesPreferFunTy vars inner_ty = fst $ go vars inner_ty
  where
    go :: [TyCoVar] -> Type -> (Type, VarSet) -- also returns the free vars
    go [] ty = (ty, tyCoVarsOfType ty)
    go (v:vs) ty
      | isTyVar v
      = if v `elemVarSet` fvs
        then ( mkForAllTy (Named v Visible) qty
             , fvs `delVarSet` v `unionVarSet` kind_vars )
        else ( mkForAllTy (Anon (tyVarKind v)) qty
             , fvs `unionVarSet` kind_vars )
      | otherwise
      = ASSERT( isCoVar v )
        ( mkForAllTy (Named v Invisible) qty
        , fvs `delVarSet` v `unionVarSet` kind_vars )
      where
        (qty, fvs) = go vs ty
        kind_vars  = tyCoVarsOfType $ tyVarKind v

-- | Given a list of kinds, makes either FunTys or ForAllTys (quantified
-- over a wild card) as appropriate. (A ForAllTy is used only when the type
-- is a coercion type.) An invariant on @Type@ forbids using anonymous
-- binders over coercions.
mkPiTypesNoTv :: [Type] -> Type -> Type
mkPiTypesNoTv [] ty = ty
mkPiTypesNoTv (k:ks) ty
  = let binder
          | isCoercionType k = Named (mkCoVar wildCardName k) Invisible
          | otherwise        = Anon k
        result = mkPiTypesNoTv ks ty in
    mkForAllTy binder result

-- | Take a ForAllTy apart, returning the list of binders and the result type.
-- This always succeeds, even if it returns only an empty list. Note that the
-- result type returned may have free variables that were bound by a forall.
splitForAllTys :: Type -> ([Binder], Type)
splitForAllTys ty = split ty ty []
  where
    split orig_ty ty bndrs | Just ty' <- coreView ty = split orig_ty ty' bndrs
    split _       (ForAllTy bndr ty) bndrs = split ty ty (bndr:bndrs)
    split orig_ty _                  bndrs = (reverse bndrs, orig_ty)
    
-- | Like 'splitForAllTys' but split off only /named/ binders, returning
-- only the tycovars.
splitNamedForAllTys :: Type -> ([TyCoVar], Type)
splitNamedForAllTys ty = first (map $ binderVar "splitNamedForAllTys") $
                         splitNamedForAllTysB ty

-- | Like 'splitForAllTys' but split off only /named/ binders.
splitNamedForAllTysB :: Type -> ([Binder], Type)
splitNamedForAllTysB ty = split ty ty []
  where
    split orig_ty ty bs | Just ty' <- coreView ty = split orig_ty ty' bs
    split _       (ForAllTy b@(Named {}) res) bs  = split res res (b:bs)
    split orig_ty _                           bs  = (reverse bs, orig_ty)

isForAllTy :: Type -> Bool
isForAllTy (ForAllTy {})  = True
isForAllTy _              = False

-- | Is this a 'ForAllTy' with a named binder?
isNamedForAllTy :: Type -> Bool
isNamedForAllTy (ForAllTy (Named {}) _) = True
isNamedForAllTy _                       = False

-- | Take a forall type apart, or panics if that is not possible.
splitForAllTy :: Type -> (Binder, Type)
splitForAllTy ty
  | Just answer <- splitForAllTy_maybe ty = answer
  | otherwise                             = pprPanic "splitForAllTy" (ppr ty)

-- | Attempts to take a forall type apart
splitForAllTy_maybe :: Type -> Maybe (Binder, Type)
splitForAllTy_maybe ty = splitFAT_m ty
  where
    splitFAT_m ty | Just ty' <- coreView ty = splitFAT_m ty'
    splitFAT_m (ForAllTy bndr ty) = Just (bndr, ty)
    splitFAT_m _                  = Nothing

-- | Drops all non-anonymous ForAllTys
dropForAlls :: Type -> Type
dropForAlls ty | Just ty' <- coreView ty = dropForAlls ty'
               | otherwise = go ty
  where
    go (ForAllTy (Named {}) res) = go res
    go res                       = res

-- | Given a tycon and its arguments, filters out any invisible arguments
filterInvisibles :: TyCon -> [a] -> [a]
  -- TODO (RAE): This is wrong wrong wrong. What if a substitution would expose
  -- more arrow types, thus changing the splitForAllTys result? If length xs
  -- is <= length bndrs, we're OK, but we need to do substitution in the
  -- oversaturated case.
filterInvisibles tc xs = [ x | (x, bndr) <- zip xs bndrs
                             , isVisibleBinder bndr ]
  where
    (bndrs, _) = splitForAllTys (tyConKind tc)

-- like splitForAllTys, but returns only *invisible* binders, including constraints
splitForAllTysInvisible :: Type -> ([Binder], Type)
splitForAllTysInvisible ty = split ty ty []
   where
     split orig_ty ty bndrs
       | Just ty' <- coreView ty = split orig_ty ty' bndrs
     split _       (ForAllTy bndr ty) bndrs
       |  isInvisibleBinder bndr
       || isPredTy (binderType bndr)
       = split ty ty (bndr:bndrs)

     split orig_ty _ bndrs
       = (reverse bndrs, orig_ty)

tyConBinders :: TyCon -> [Binder]
tyConBinders = fst . splitForAllTys . tyConKind

{-
applyTys
~~~~~~~~~~~~~~~~~
-}

applyTys :: Type -> [KindOrType] -> Type
-- ^ This function is interesting because:
--
--      1. The function may have more for-alls than there are args
--
--      2. Less obviously, it may have fewer for-alls
--
-- For case 2. think of:
--
-- > applyTys (forall a.a) [forall b.b, Int]
--
-- This really can happen, but only (I think) in situations involving
-- undefined.  For example:
--       undefined :: forall a. a
-- Term: undefined @(forall b. b->b) @Int
-- This term should have type (Int -> Int), but notice that
-- there are more type args than foralls in 'undefined's type.

-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
applyTys ty args = applyTysD empty ty args

applyTysD :: SDoc -> Type -> [Type] -> Type     -- Debug version
applyTysD _   orig_fun_ty []      = orig_fun_ty
applyTysD doc orig_fun_ty arg_tys
  | n_bndrs == n_args     -- The vastly common case
  = substTyWithBinders bndrs arg_tys rho_ty
  | n_bndrs > n_args      -- Too many for-alls
  = substTyWithBinders (take n_args bndrs) arg_tys
                       (mkForAllTys (drop n_args bndrs) rho_ty)
  | otherwise           -- Too many type args
  = ASSERT2( n_bndrs > 0, doc $$ ppr orig_fun_ty $$ ppr arg_tys )       -- Zero case gives infinite loop!
    applyTysD doc (substTyWithBinders bndrs (take n_bndrs arg_tys) rho_ty)
                  (drop n_bndrs arg_tys)
  where
    (bndrs, rho_ty) = splitForAllTys orig_fun_ty
    n_bndrs = length bndrs
    n_args  = length arg_tys

applyTysX :: [TyVar] -> Type -> [Type] -> Type
-- applyTyxX beta-reduces (/\tvs. body_ty) arg_tys
applyTysX tvs body_ty arg_tys
  = ASSERT2( length arg_tys >= n_tvs, ppr tvs $$ ppr body_ty $$ ppr arg_tys )
    mkAppTys (substTyWith tvs (take n_tvs arg_tys) body_ty)
             (drop n_tvs arg_tys)
  where
    n_tvs = length tvs

{-
%************************************************************************
%*                                                                      *
   Binders
%*                                                                      *
%************************************************************************
-}

-- | Make a named binder
mkNamedBinder :: Var -> VisibilityFlag -> Binder
mkNamedBinder = Named

-- | Make an anonymous binder
mkAnonBinder :: Type -> Binder
mkAnonBinder = Anon

isNamedBinder :: Binder -> Bool
isNamedBinder (Named {}) = True
isNamedBinder _          = False

isAnonBinder :: Binder -> Bool
isAnonBinder (Anon {}) = True
isAnonBinder _         = False

-- | Does this binder bind a variable that is /not/ erased? Returns
-- 'True' for anonymous binders and coercion binders.
isIdLikeBinder :: Binder -> Bool
isIdLikeBinder (Named cv _) = isCoVar cv
isIdLikeBinder (Anon {})    = True

-- | Does this type, when used to the left of an arrow, require
-- a visible argument? This checks to see if the kind of the type
-- is constraint.
isVisibleType :: Type -> Bool
isVisibleType = not . isConstraintKind . typeKind

binderVisibility :: Binder -> VisibilityFlag
binderVisibility (Named _ vis) = vis
binderVisibility (Anon ty)
  | isVisibleType ty = Visible
  | otherwise        = Invisible

-- | Extract a bound variable in a binder, if any
binderVar_maybe :: Binder -> Maybe Var
binderVar_maybe (Named v _) = Just v
binderVar_maybe (Anon {})   = Nothing

-- | Extract a bound variable in a binder, or panics
binderVar :: String   -- ^ printed if there is a panic
          -> Binder -> Var
binderVar _ (Named v _) = v
binderVar e (Anon t)    = pprPanic ("binderVar (" ++ e ++ ")") (ppr t)

-- | Extract a relevant type, if there is one.
binderRelevantType_maybe :: Binder -> Maybe Type
binderRelevantType_maybe (Named {}) = Nothing
binderRelevantType_maybe (Anon ty)  = Just ty

-- | Like 'maybe', but for binders.
caseBinder :: Binder      -- ^ binder to scrutinize
           -> (Var -> a)  -- ^ named case
           -> (Type -> a) -- ^ anonymous case
           -> a
caseBinder (Named v _) f _ = f v
caseBinder (Anon t) _ d    = d t

-- | Break apart a list of binders into ty/co vars and anonymous types.
partitionBinders :: [Binder] -> ([TyCoVar], [Type])
partitionBinders = partitionWith named_or_anon
  where
    named_or_anon bndr = caseBinder bndr Left Right

-- | Break apart a list of binders into a list of named binders and
-- a list of anonymous types.
partitionBindersIntoBinders :: [Binder] -> ([Binder], [Type])
partitionBindersIntoBinders = partitionWith named_or_anon
  where
    named_or_anon bndr = caseBinder bndr (\_ -> Left bndr) Right

{-
%************************************************************************
%*                                                                      *
                         Pred
*                                                                      *
************************************************************************

Predicates on PredType
-}

-- | Is the type suitable to classify a given/wanted in the typechecker?
isPredTy :: Type -> Bool
  -- NB: isPredTy is used when printing types, which can happen in debug printing
  --     during type checking of not-fully-zonked types.  So it's not cool to say
  --     isConstraintKind (typeKind ty) because absent zonking the type might
  --     be ill-kinded, and typeKind crashes
  --     Hence the rather tiresome story here
  --
  -- NB: This must return "True" to *unlifted* coercions, which are not
  --     of kind Constraint!
isPredTy ty = go ty []
  where
    go :: Type -> [KindOrType] -> Bool
    go (AppTy ty1 ty2)   args = go ty1 (ty2 : args)
    go (TyConApp tc tys) args
      | tc `hasKey` eqPrimTyConKey || tc `hasKey` eqReprPrimTyConKey
      , [_,_,_,_] <- all_args
      = True

      | otherwise
      = go_k (tyConKind tc) all_args
      where
        all_args = tys ++ args
    go (TyVarTy tv)      args = go_k (tyVarKind tv) args
    go _                 _    = False

    go_k :: Kind -> [KindOrType] -> Bool
    -- True <=> kind is k1 -> .. -> kn -> Constraint
    go_k k [] = isConstraintKind k
    go_k (ForAllTy bndr k1) (arg:args)
      = go_k (substTyWithBinders [bndr] [arg] k1) args
    go_k _ _ = False                  -- Typeable * Int :: Constraint

isClassPred, isEqPred, isNomEqPred, isIPPred :: PredType -> Bool
isClassPred ty = case tyConAppTyCon_maybe ty of
    Just tyCon | isClassTyCon tyCon -> True
    _                               -> False
isEqPred ty = case tyConAppTyCon_maybe ty of
    Just tyCon -> tyCon `hasKey` eqTyConKey
               || tyCon `hasKey` eqPrimTyConKey
               || tyCon `hasKey` coercibleTyConKey
               || tyCon `hasKey` eqReprPrimTyConKey
    _          -> False

isNomEqPred ty = case tyConAppTyCon_maybe ty of
    Just tyCon -> tyCon `hasKey` eqTyConKey
               || tyCon `hasKey` eqPrimTyConKey
    _          -> False

isIPPred ty = case tyConAppTyCon_maybe ty of
    Just tc -> isIPTyCon tc
    _       -> False

isIPTyCon :: TyCon -> Bool
isIPTyCon tc = tc `hasKey` ipClassNameKey

isIPClass :: Class -> Bool
isIPClass cls = cls `hasKey` ipClassNameKey
  -- Class and it corresponding TyCon have the same Unique

isIPPred_maybe :: Type -> Maybe (FastString, Type)
isIPPred_maybe ty =
  do (tc,[t1,t2]) <- splitTyConApp_maybe ty
     guard (isIPTyCon tc)
     x <- isStrLitTy t1
     return (x,t2)

{-
Make PredTypes

--------------------- Equality types ---------------------------------
-}

-- | Creates a type equality predicate
mkEqPred :: Type -> Type -> PredType
mkEqPred ty1 ty2
  = WARN( not (k `eqType` typeKind ty2), ppr ty1 $$ ppr ty2 $$ ppr k $$ ppr (typeKind ty2) )
    TyConApp eqTyCon [k, ty1, ty2]
  where
    k = typeKind ty1

mkCoerciblePred :: Type -> Type -> PredType
mkCoerciblePred ty1 ty2
  = WARN( not (k `eqType` typeKind ty2), ppr ty1 $$ ppr ty2 $$ ppr k $$ ppr (typeKind ty2) )
    TyConApp coercibleTyCon [k, ty1, ty2]
  where
    k = typeKind ty1

-- | Makes a lifted equality predicate at the given role
mkEqPredRole :: Role -> Type -> Type -> PredType
mkEqPredRole Nominal          = mkEqPred
mkEqPredRole Representational = mkCoerciblePred
mkEqPredRole Phantom          = panic "mkEqPredRole phantom"

-- | Makes a lifted equality predicate at the given role
mkPrimEqPredRole :: Role -> Type -> Type -> PredType
mkPrimEqPredRole Nominal          = mkPrimEqPred
mkPrimEqPredRole Representational = mkReprPrimEqPred
mkPrimEqPredRole Phantom          = panic "mkPrimEqPredRole phantom"

-- | Creates a primitive type equality predicate.
-- Invariant: the types are not Coercions
mkPrimEqPred :: Type -> Type -> Type
mkPrimEqPred ty1 ty2
  = TyConApp eqPrimTyCon [k1, k2, ty1, ty2]
  where
    k1 = typeKind ty1
    k2 = typeKind ty2

-- | Creates a primite type equality predicate with explicit kinds
mkHeteroPrimEqPred :: Kind -> Kind -> Type -> Type -> Type
mkHeteroPrimEqPred k1 k2 ty1 ty2 = TyConApp eqPrimTyCon [k1, k2, ty1, ty2]

-- | Creates a primitive representational type equality predicate
-- with explicit kinds
mkHeteroReprPrimEqPred :: Kind -> Kind -> Type -> Type -> Type
mkHeteroReprPrimEqPred k1 k2 ty1 ty2
  = TyConApp eqReprPrimTyCon [k1, k2, ty1, ty2]

-- | Try to split up a coercion type into the types that it coerces
splitCoercionType_maybe :: Type -> Maybe (Type, Type)
splitCoercionType_maybe ty
  = do { (tc, [_, _, ty1, ty2]) <- splitTyConApp_maybe ty
       ; guard $ tc `hasKey` eqPrimTyConKey
       ; return (ty1, ty2) }

mkReprPrimEqPred :: Type -> Type -> Type
mkReprPrimEqPred ty1  ty2
  = TyConApp eqReprPrimTyCon [k1, k2, ty1, ty2]
  where
    k1 = typeKind ty1
    k2 = typeKind ty2

equalityTyCon :: Role -> TyCon
equalityTyCon Nominal          = eqPrimTyCon
equalityTyCon Representational = eqReprPrimTyCon
equalityTyCon Phantom          = eqPhantPrimTyCon

-- --------------------- Dictionary types ---------------------------------

mkClassPred :: Class -> [Type] -> PredType
mkClassPred clas tys = TyConApp (classTyCon clas) tys

isDictTy :: Type -> Bool
isDictTy = isClassPred

isDictLikeTy :: Type -> Bool
-- Note [Dictionary-like types]
isDictLikeTy ty | Just ty' <- coreView ty = isDictLikeTy ty'
isDictLikeTy ty = case splitTyConApp_maybe ty of
        Just (tc, tys) | isClassTyCon tc -> True
                       | isTupleTyCon tc -> all isDictLikeTy tys
        _other                           -> False

{-
Note [Dictionary-like types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Being "dictionary-like" means either a dictionary type or a tuple thereof.
In GHC 6.10 we build implication constraints which construct such tuples,
and if we land up with a binding
    t :: (C [a], Eq [a])
    t = blah
then we want to treat t as cheap under "-fdicts-cheap" for example.
(Implication constraints are normally inlined, but sadly not if the
occurrence is itself inside an INLINE function!  Until we revise the
handling of implication constraints, that is.)  This turned out to
be important in getting good arities in DPH code.  Example:

    class C a
    class D a where { foo :: a -> a }
    instance C a => D (Maybe a) where { foo x = x }

    bar :: (C a, C b) => a -> b -> (Maybe a, Maybe b)
    {-# INLINE bar #-}
    bar x y = (foo (Just x), foo (Just y))

Then 'bar' should jolly well have arity 4 (two dicts, two args), but
we ended up with something like
   bar = __inline_me__ (\d1,d2. let t :: (D (Maybe a), D (Maybe b)) = ...
                                in \x,y. <blah>)

This is all a bit ad-hoc; eg it relies on knowing that implication
constraints build tuples.


Decomposing PredType
-}

-- | A choice of equality relation. This is separate from the type 'Role'
-- because 'Phantom' does not define a (non-trivial) equality relation.
data EqRel = NomEq | ReprEq
  deriving (Eq, Ord)

instance Outputable EqRel where
  ppr NomEq  = text "nominal equality"
  ppr ReprEq = text "representational equality"

eqRelRole :: EqRel -> Role
eqRelRole NomEq  = Nominal
eqRelRole ReprEq = Representational

data PredTree = ClassPred Class [Type]
              | EqPred EqRel Type Type
              | TuplePred [PredType]
              | IrredPred PredType

classifyPredType :: PredType -> PredTree
classifyPredType ev_ty = case splitTyConApp_maybe ev_ty of
    Just (tc, tys)
      | tc `hasKey` coercibleTyConKey
      , let [_, ty1, ty2] = tys           -> EqPred ReprEq ty1 ty2

      | tc `hasKey` eqReprPrimTyConKey
      , let [_, _, ty1, ty2] = tys        -> EqPred ReprEq ty1 ty2

      | tc `hasKey` eqTyConKey
      , let [_, ty1, ty2] = tys           -> EqPred NomEq ty1 ty2

      | tc `hasKey` eqPrimTyConKey
      , let [_, _, ty1, ty2] = tys        -> EqPred NomEq ty1 ty2

     -- NB: Coercible is also a class, so this check must come *after*
     -- the Coercible check
      | Just clas <- tyConClass_maybe tc  -> ClassPred clas tys

      | isTupleTyCon tc                   -> TuplePred tys

    _                                     -> IrredPred ev_ty

getClassPredTys :: PredType -> (Class, [Type])
getClassPredTys ty = case getClassPredTys_maybe ty of
        Just (clas, tys) -> (clas, tys)
        Nothing          -> pprPanic "getClassPredTys" (ppr ty)

getClassPredTys_maybe :: PredType -> Maybe (Class, [Type])
getClassPredTys_maybe ty = case splitTyConApp_maybe ty of
        Just (tc, tys) | Just clas <- tyConClass_maybe tc -> Just (clas, tys)
        _ -> Nothing

getEqPredTys :: PredType -> (Type, Type)
getEqPredTys ty
  = case splitTyConApp_maybe ty of
      Just (tc, [_, ty1, ty2])
        |  tc `hasKey` eqTyConKey
        || tc `hasKey` coercibleTyConKey -> (ty1, ty2)
      Just (tc, [_, _, ty1, ty2])
        |  tc `hasKey` eqPrimTyConKey
        || tc `hasKey` eqReprPrimTyConKey -> (ty1, ty2)
      _ -> pprPanic "getEqPredTys" (ppr ty)

getEqPredTys_maybe :: PredType -> Maybe (Boxity, Role, Type, Type)
getEqPredTys_maybe ty
  = case splitTyConApp_maybe ty of
      Just (tc, [_, ty1, ty2])
        | tc `hasKey` eqTyConKey        -> Just (Boxed, Nominal, ty1, ty2)
        | tc `hasKey` coercibleTyConKey -> Just (Boxed, Representational, ty1, ty2)
      Just (tc, [_, _, ty1, ty2])
        | tc `hasKey` eqPrimTyConKey    -> Just (Unboxed, Nominal, ty1, ty2)
        | tc `hasKey` eqReprPrimTyConKey -> Just (Unboxed, Representational, ty1, ty2)
      _ -> Nothing

getEqPredRole :: PredType -> Role
getEqPredRole ty
  = case splitTyConApp_maybe ty of
      Just (tc, _)
        | tc `hasKey` eqTyConKey -> Nominal
        | tc `hasKey` eqPrimTyConKey -> Nominal
        | tc `hasKey` coercibleTyConKey -> Representational
        | tc `hasKey` eqReprPrimTyConKey -> Representational  -- TODO (RAE): Remove?
      _ -> pprPanic "getEqPredRole" (ppr ty)

-- | Assuming the type provided is an EqPred, is it lifted?
isEqPredLifted :: PredType -> Bool
isEqPredLifted ty
  = case splitTyConApp_maybe ty of
      Just (tc, _) -> not (tc `hasKey` eqPrimTyConKey)
                   && not (tc `hasKey` eqReprPrimTyConKey)
      _ -> pprPanic "isEqPredLifted" (ppr ty)

-- | Assuming the type provided is an EqPred, return its boxity
getEqPredBoxity :: PredType -> Boxity
getEqPredBoxity ty
  | isEqPredLifted ty = Boxed
  | otherwise         = Unboxed

-- | Get the equality relation relevant for a pred type.
predTypeEqRel :: PredType -> EqRel
predTypeEqRel ty
  | Just (tc, _) <- splitTyConApp_maybe ty
  , tc `hasKey` coercibleTyConKey || tc `hasKey` eqReprPrimTyConKey
  = ReprEq
  | otherwise
  = NomEq

{-
%************************************************************************
%*                                                                      *
                   Size
*                                                                      *
************************************************************************
-}

-- NB: This function does not respect `eqType`, in that two types that
-- are `eqType` may return different sizes. This is OK, because this
-- function is used only in reporting, not decision-making.
typeSize :: Type -> Int
typeSize (LitTy {})       = 1
typeSize (TyVarTy {})     = 1
typeSize (AppTy t1 t2)    = typeSize t1 + typeSize t2
typeSize (ForAllTy b t)   = typeSize (binderType b) + typeSize t
typeSize (TyConApp _ ts)  = 1 + sum (map typeSize ts)
typeSize (CastTy ty co)   = typeSize ty + coercionSize co
typeSize (CoercionTy co)  = coercionSize co

-- no promises that this is the most efficient, but it will do the job
-- TODO (RAE): make better.
-- Works on all kinds of Vars, including Ids.
type DepEnv = VarEnv VarSet

-- | Extract a well-scoped list of variables from a set of variables.
-- This prefers putting 'Id's after other vars, when it has the choice.
varSetElemsWellScoped :: VarSet -> [Var]
varSetElemsWellScoped set
  = build_list [] (varSetElems set)
  where
    deps = foldVarSet add_dep emptyVarEnv set

    add_dep :: Var -> DepEnv -> DepEnv
    add_dep v env = extendVarEnv env v (dep_set v emptyVarSet)

    dep_set :: Var -> VarSet -> VarSet
    dep_set v s = let free_vars = tyCoVarsOfType (varType v) `intersectVarSet` set in
                    foldVarSet dep_set free_vars free_vars `unionVarSet` s

    get_deps :: Var -> VarSet
    get_deps v = lookupVarEnv_NF deps v

    build_list :: [TyCoVar] -- vars in scope
               -> [TyCoVar] -- vars not yet sorted
               -> [TyCoVar]
    build_list scoped [] = scoped
    build_list scoped unsorted
      = let (new_scoped, unsorted') = partition (well_scoped scoped) unsorted in
        ASSERT( not $ null new_scoped )
        build_list (scoped ++ sortBy put_ids_later new_scoped) unsorted'

    well_scoped scoped var = get_deps var `subVarSet` (mkVarSet scoped)
    put_ids_later v1 v2
      = (isId v1 `compare` isId v2) `thenCmp` (v1 `compare` v2)
          -- NB: True > False!

{-
************************************************************************
*                                                                      *
\subsection{Type families}
*                                                                      *
************************************************************************
-}

mkFamilyTyConApp :: TyCon -> [Type] -> Type
-- ^ Given a family instance TyCon and its arg types, return the
-- corresponding family type.  E.g:
--
-- > data family T a
-- > data instance T (Maybe b) = MkT b
--
-- Where the instance tycon is :RTL, so:
--
-- > mkFamilyTyConApp :RTL Int  =  T (Maybe Int)
mkFamilyTyConApp tc tys
  | Just (fam_tc, fam_tys) <- tyConFamInst_maybe tc
  , let tvs = tyConTyVars tc
        fam_subst = ASSERT2( length tvs == length tys, ppr tc <+> ppr tys )
                    zipTopTCvSubst tvs tys
  = mkTyConApp fam_tc (substTys fam_subst fam_tys)
  | otherwise
  = mkTyConApp tc tys

-- | Get the type on the LHS of a coercion induced by a type/data
-- family instance.
coAxNthLHS :: CoAxiom br -> Int -> Type
coAxNthLHS ax ind =
  mkTyConApp (coAxiomTyCon ax) (coAxBranchLHS (coAxiomNthBranch ax ind))

-- | Pretty prints a 'TyCon', using the family instance in case of a
-- representation tycon.  For example:
--
-- > data T [a] = ...
--
-- In that case we want to print @T [a]@, where @T@ is the family 'TyCon'
pprSourceTyCon :: TyCon -> SDoc
pprSourceTyCon tycon
  | Just (fam_tc, tys) <- tyConFamInst_maybe tycon
  = ppr $ fam_tc `TyConApp` tys        -- can't be FunTyCon
  | otherwise
  = ppr tycon

{-
************************************************************************
*                                                                      *
\subsection{Liftedness}
*                                                                      *
************************************************************************
-}

-- | See "Type#type_classification" for what an unlifted type is
isUnLiftedType :: Type -> Bool
        -- isUnLiftedType returns True for forall'd unlifted types:
        --      x :: forall a. Int#
        -- I found bindings like these were getting floated to the top level.
        -- They are pretty bogus types, mind you.  It would be better never to
        -- construct them

isUnLiftedType ty | Just ty' <- coreView ty = isUnLiftedType ty'
isUnLiftedType (ForAllTy (Named tv _) ty)
  | isTyVar tv                      = isUnLiftedType ty
  | otherwise {- co var -}          = False
isUnLiftedType (TyConApp tc _)      = isUnLiftedTyCon tc
isUnLiftedType _                    = False

-- | Extract the levity classifier of a type. Panics if this is not possible.
getLevity :: String   -- ^ Printed in case of an error
          -> Type -> Type
getLevity err ty = go (typeKind ty)
  where
    go k | Just k' <- coreViewOneStarKind k = go k'
    go k
      | Just (tc, [arg]) <- splitTyConApp_maybe k
      , tc `hasKey` tYPETyConKey
      = arg
    go k = pprPanic "getLevity" (text err $$
                                 ppr ty <+> dcolon <+> ppr k
                                        <+> dcolon <+> ppr (typeKind k))

isUnboxedTupleType :: Type -> Bool
isUnboxedTupleType ty = case tyConAppTyCon_maybe ty of
                           Just tc -> isUnboxedTupleTyCon tc
                           _       -> False

-- | See "Type#type_classification" for what an algebraic type is.
-- Should only be applied to /types/, as opposed to e.g. partially
-- saturated type constructors
isAlgType :: Type -> Bool
isAlgType ty
  = case splitTyConApp_maybe ty of
      Just (tc, ty_args) -> ASSERT( ty_args `lengthIs` tyConArity tc )
                            isAlgTyCon tc
      _other             -> False

-- | See "Type#type_classification" for what an algebraic type is.
-- Should only be applied to /types/, as opposed to e.g. partially
-- saturated type constructors. Closed type constructors are those
-- with a fixed right hand side, as opposed to e.g. associated types
isClosedAlgType :: Type -> Bool
isClosedAlgType ty
  = case splitTyConApp_maybe ty of
      Just (tc, ty_args) | isAlgTyCon tc && not (isFamilyTyCon tc)
             -> ASSERT2( ty_args `lengthIs` tyConArity tc, ppr ty ) True
      _other -> False

-- | Computes whether an argument (or let right hand side) should
-- be computed strictly or lazily, based only on its type.
-- Currently, it's just 'isUnLiftedType'.

isStrictType :: Type -> Bool
isStrictType = isUnLiftedType

isPrimitiveType :: Type -> Bool
-- ^ Returns true of types that are opaque to Haskell.
isPrimitiveType ty = case splitTyConApp_maybe ty of
                        Just (tc, ty_args) -> ASSERT( ty_args `lengthIs` tyConArity tc )
                                              isPrimTyCon tc
                        _                  -> False

{-
************************************************************************
*                                                                      *
\subsection{Sequencing on types}
*                                                                      *
************************************************************************
-}

seqType :: Type -> ()
seqType (LitTy n)            = n `seq` ()
seqType (TyVarTy tv)         = tv `seq` ()
seqType (AppTy t1 t2)        = seqType t1 `seq` seqType t2
seqType (TyConApp tc tys)    = tc `seq` seqTypes tys
seqType (ForAllTy bndr ty)   = seqType (binderType bndr) `seq` seqType ty
seqType (CastTy ty co)       = seqType ty `seq` seqCo co
seqType (CoercionTy co)      = seqCo co

seqTypes :: [Type] -> ()
seqTypes []       = ()
seqTypes (ty:tys) = seqType ty `seq` seqTypes tys

{-
************************************************************************
*                                                                      *
                Comparison for types
        (We don't use instances so that we know where it happens)
*                                                                      *
************************************************************************
-}

eqType :: Type -> Type -> Bool
-- ^ Type equality on source types. Does not look through @newtypes@ or
-- 'PredType's, but it does look through type synonyms.
-- See also Note [Non-trivial definitional equality] in TyCoRep.
eqType t1 t2 = isEqual $ cmpType t1 t2

-- | Compare types with respect to a (presumably) non-empty 'RnEnv2'.
eqTypeX :: RnEnv2 -> Type -> Type -> Bool
eqTypeX env t1 t2 = isEqual $ cmpTypeX env t1 t2

-- | Type equality on lists of types, looking through type synonyms
-- but not newtypes.
eqTypes :: [Type] -> [Type] -> Bool
eqTypes tys1 tys2 = isEqual $ cmpTypes tys1 tys2

eqTyCoVarBndrs :: RnEnv2 -> [TyCoVar] -> [TyCoVar] -> Maybe RnEnv2
-- Check that the tyvar lists are the same length
-- and have matching kinds; if so, extend the RnEnv2
-- Returns Nothing if they don't match
eqTyCoVarBndrs env [] []
 = Just env
eqTyCoVarBndrs env (tv1:tvs1) (tv2:tvs2)
 | eqTypeX env (tyVarKind tv1) (tyVarKind tv2)
 = eqTyCoVarBndrs (rnBndr2 env tv1 tv2) tvs1 tvs2
eqTyCoVarBndrs _ _ _= Nothing

-- Now here comes the real worker

cmpType :: Type -> Type -> Ordering
cmpType t1 t2
  -- we know k1 and k2 have the same kind, because they both have kind *.
  = cmpTypeX rn_env t1 t2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfType t1 `unionVarSet` tyCoVarsOfType t2))

cmpTypes :: [Type] -> [Type] -> Ordering
cmpTypes ts1 ts2 = cmpTypesX rn_env ts1 ts2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfTypes ts1 `unionVarSet` tyCoVarsOfTypes ts2))

cmpTypeX :: RnEnv2 -> Type -> Type -> Ordering  -- Main workhorse
    -- See Note [Non-trivial definitional equality] in TyCoRep
cmpTypeX env t1 t2 = go env (coreEraseType k1) (coreEraseType k2) `thenCmp`
                     go env (coreEraseType t1) (coreEraseType t2)
  where
    k1 = typeKind t1
    k2 = typeKind t2

    -- NB: It's tempting just to do a straightforward descent into the types,
    -- ignoring casts. However, this might end up comparing an AppTy to a
    -- TyConApp and getting confused. There may be a more efficient approach
    -- than erasing and comparing, but I don't feel like succumbing to evil
    -- premature optimization at the moment. TODO (RAE): Optimize when not
    -- premature!
   
    -- We expand predicate types, because in Core-land we have
    -- lots of definitions like
    --      fOrdBool :: Ord Bool
    --      fOrdBool = D:Ord .. .. ..
    -- So the RHS has a data type

    go env (ETyVarTy tv1)       (ETyVarTy tv2)
      = rnOccL env tv1 `compare` rnOccR env tv2
    go env (EForAllTy (ENamed tv1 k1 _) t1) (EForAllTy (ENamed tv2 k2 _) t2)
      = go env k1 k2 `thenCmp` go (rnBndr2 env tv1 tv2) t1 t2
    go env (EAppTy s1 k1 t1)    (EAppTy s2 k2 t2)
      = go env s1 s2 `thenCmp` go env k1 k2 `thenCmp` go env t1 t2
    go env (EForAllTy (EAnon s1) t1) (EForAllTy (EAnon s2) t2)
      = go env s1 s2 `thenCmp` go env t1 t2
    go env (ETyConApp tc1 tys1) (ETyConApp tc2 tys2)
      = (tc1 `cmpTc` tc2) `thenCmp` gos env tys1 tys2
    go _   (ELitTy l1)          (ELitTy l2)          = compare l1 l2
    go _   ECoercionTy          ECoercionTy          = EQ

        -- Deal with the rest: TyVarTy < CoercionTy < CastTy < AppTy < LitTy < TyConApp < ForAllTy
    go _ ty1 ty2
      = (get_rank ty1) `compare` (get_rank ty2)
      where get_rank :: EType -> Int
            get_rank (ETyVarTy {})             = 0
            get_rank (ECoercionTy {})          = 1
            get_rank (EAppTy {})               = 3
            get_rank (ELitTy {})               = 4
            get_rank (ETyConApp {})            = 5
            get_rank (EForAllTy (EAnon {}) _)  = 6
            get_rank (EForAllTy (ENamed {}) _) = 7

    gos _   []         []         = EQ
    gos _   []         _          = LT
    gos _   _          []         = GT
    gos env (ty1:tys1) (ty2:tys2) = go env ty1 ty2 `thenCmp` gos env tys1 tys2

-------------
cmpTypesX :: RnEnv2 -> [Type] -> [Type] -> Ordering
cmpTypesX _   []        []        = EQ
cmpTypesX env (t1:tys1) (t2:tys2) = cmpTypeX env t1 t2 `thenCmp` cmpTypesX env tys1 tys2
cmpTypesX _   []        _         = LT
cmpTypesX _   _         []        = GT

-------------
-- | Compare two 'TyCon's. NB: This should /never/ see the "star synonyms",
-- as recognized by Kind.isStarKindSynonymTyCon. See Note
-- [Kind Constraint and kind *] in Kind.
cmpTc :: TyCon -> TyCon -> Ordering
cmpTc tc1 tc2
  = ASSERT( not (isStarKindSynonymTyCon tc1) && not (isStarKindSynonymTyCon tc2) )
    u1 `compare` u2
  where
    u1  = tyConUnique tc1
    u2  = tyConUnique tc2

----------------
-- | This is used when doing the non-trivial definitional equality check.
-- If differs from 'Type' in that it annotates all AppTys with the kind
-- of the argument.
-- See Note [Non-trivial definitional equality] in TyCoRep
data EType
  = ETyVarTy TyVar
  | EAppTy EType EKind EType
  | ETyConApp TyCon [EType]
  | EForAllTy EBinder EType
  | ELitTy TyLit
  | ECoercionTy
type EKind = EType

data EBinder
  = EAnon EType
  | ENamed TyVar EType VisibilityFlag  -- don't ask for the tyvar's kind!

instance Outputable EType where
  ppr (ETyVarTy tv)       = ppr tv
  ppr (EAppTy t1 k2 t2)   = ppr t1 <+> parens (ppr t2 <+> dcolon <+> ppr k2)
  ppr (ETyConApp tc tys)  = ppr tc <+> sep (map (parens . ppr) tys)
  ppr (EForAllTy bndr ty) = text "forall" <+> ppr bndr <> dot <+> ppr ty
  ppr (ELitTy lit)        = ppr lit
  ppr ECoercionTy         = text "<<co>>"

instance Outputable EBinder where
  ppr (EAnon ty)        = text "[anon]" <+> ppr ty
  ppr (ENamed tv k vis) = parens (ppr tv <+> dcolon <+> ppr k <+> ppr vis)

-- | Remove all casts from a type, and use the given "view" function to
-- unwrap synonyms as we go. This will yield an ill-kinded type, so
-- use with caution.
eraseType :: (Type -> Maybe Type) -> Type -> EType
eraseType view_fun = go
  where
    go :: Type -> EType
    go t | Just t' <- view_fun t = go t'
    
    go (TyVarTy tv1)      = ETyVarTy tv1 -- comparison doesn't recur into tv kinds
      -- NB: use mkAppTy, as erasing may expose a TyCon!
    go t@(AppTy {})       = go_app t []
    go (TyConApp tc tys)  = ETyConApp tc (map go tys)
    go (ForAllTy bndr ty) = EForAllTy (go_bndr bndr) (go ty)
    go (LitTy lit)        = ELitTy lit
    go (CastTy t _)       = go t
    go (CoercionTy {})    = ECoercionTy

      -- doing it this way turns a quadratic algorithm into a linear one!
    go_app (AppTy t1 t2) args = go_app t1 (t2 : args)
    go_app other_ty      args = mk_app_tys (go other_ty) args

    mk_app_tys :: EType -> [Type] -> EType
    mk_app_tys ty1                 []         = ty1
    mk_app_tys (ETyConApp tc tys1) tys2
      = mk_ty_con_app tc (tys1 ++ map go tys2)
    mk_app_tys ty1                 (ty2:tys2)
      = mk_app_tys (EAppTy ty1 (go (typeKind ty2)) (go ty2)) tys2

    mk_ty_con_app :: TyCon -> [EType] -> EType
    mk_ty_con_app tycon tys
      | isFunTyCon tycon
      , [ty1, ty2] <- tys
      = EForAllTy (EAnon ty1) ty2
      | otherwise
      = ETyConApp tycon tys

    go_bndr :: Binder -> EBinder
    go_bndr (Anon ty)      = EAnon (go ty)
    go_bndr (Named tv vis) = ENamed tv (go (tyVarKind tv)) vis

-- | Remove all casts, all type synonyms, and make Constraint and *
-- look the same. Note that the result type will likely be ill-kinded,
-- so proceed with caution.
coreEraseType :: Type -> EType
coreEraseType = eraseType coreViewOneStarKind

{-
************************************************************************
*                                                                      *
        The kind of a type
*                                                                      *
************************************************************************
-}

typeKind :: Type -> Kind
typeKind (TyConApp tc tys)     = piResultTys (tyConKind tc) tys
typeKind (AppTy fun arg)       = piResultTy (typeKind fun) arg
typeKind (LitTy l)             = typeLiteralKind l
typeKind (ForAllTy (Anon _) _) = liftedTypeKind
typeKind (ForAllTy _ ty)       = typeKind ty
typeKind (TyVarTy tyvar)       = tyVarKind tyvar
typeKind (CastTy _ty co)       = pSnd $ coercionKind co
typeKind (CoercionTy co)       = coercionType co

typeLiteralKind :: TyLit -> Kind
typeLiteralKind l =
  case l of
    NumTyLit _ -> typeNatKind
    StrTyLit _ -> typeSymbolKind

{-
%************************************************************************
%*                                                                      *
        Miscellaneous functions
%*                                                                      *
%************************************************************************

-}
-- | All type constructors occurring in the type; looking through type
--   synonyms, but not newtypes.
--  When it finds a Class, it returns the class TyCon.
tyConsOfType :: Type -> NameEnv TyCon
tyConsOfType ty
  = go ty
  where
     go :: Type -> NameEnv TyCon  -- The NameEnv does duplicate elim
     go ty | Just ty' <- tcView ty = go ty'
     go (TyVarTy {})               = emptyNameEnv
     go (LitTy {})                 = emptyNameEnv
     go (TyConApp tc tys)          = go_tc tc `plusNameEnv` go_s tys
     go (AppTy a b)                = go a `plusNameEnv` go b
     go (ForAllTy (Anon a) b)      = go a `plusNameEnv` go b `plusNameEnv` go_tc funTyCon
     go (ForAllTy (Named tv _) ty) = go ty `plusNameEnv` go (tyVarKind tv)
     go (CastTy ty co)             = go ty `plusNameEnv` go_co co
     go (CoercionTy co)            = go_co co

     go_co (Refl _ ty)             = go ty
     go_co (TyConAppCo _ tc args)  = go_tc tc `plusNameEnv` go_args args
     go_co (AppCo co h arg)        = go_co co `plusNameEnv`
                                     go_co h `plusNameEnv` go_arg arg
     go_co (ForAllCo cobndr co)
       = go_co (coBndrKindCo cobndr) `plusNameEnv` var_names `plusNameEnv` go_co co
       where var_names = go_s (snd (coBndrVarsKinds cobndr))
     go_co (CoVarCo {})            = emptyNameEnv
     go_co (AxiomInstCo ax _ args) = go_ax ax `plusNameEnv` go_args args
     go_co (PhantomCo h t1 t2)     = go_co h `plusNameEnv` go t1 `plusNameEnv` go t2
     go_co (UnsafeCo _ _ ty1 ty2)  = go ty1 `plusNameEnv` go ty2
     go_co (SymCo co)              = go_co co
     go_co (TransCo co1 co2)       = go_co co1 `plusNameEnv` go_co co2
     go_co (NthCo _ co)            = go_co co
     go_co (LRCo _ co)             = go_co co
     go_co (InstCo co arg)         = go_co co `plusNameEnv` go_arg arg
     go_co (CoherenceCo co1 co2)   = go_co co1 `plusNameEnv` go_co co2
     go_co (KindCo co)             = go_co co
     go_co (KindAppCo co)          = go_co co
     go_co (SubCo co)              = go_co co
     go_co (AxiomRuleCo _ ts cs)   = go_s ts `plusNameEnv` go_cos cs

     go_arg (TyCoArg co)           = go_co co
     go_arg (CoCoArg _ h co1 co2)  = go_co h `plusNameEnv`
                                     go_co co1 `plusNameEnv` go_co co2

     go_s tys     = foldr (plusNameEnv . go)     emptyNameEnv tys
     go_cos cos   = foldr (plusNameEnv . go_co)  emptyNameEnv cos
     go_args args = foldr (plusNameEnv . go_arg) emptyNameEnv args

     go_tc tc = unitNameEnv (tyConName tc) tc
     go_ax ax = go_tc $ coAxiomTyCon ax

-- | Find the result 'Kind' of a type synonym, 
-- after applying it to its 'arity' number of type variables
-- Actually this function works fine on data types too, 
-- but they'd always return '*', so we never need to ask
synTyConResKind :: TyCon -> Kind
synTyConResKind tycon = piResultTys (tyConKind tycon) (mkOnlyTyVarTys (tyConTyVars tycon))

-- | Retrieve the free variables in this type, splitting them based
-- on whether the variable was used in a dependent context. It's possible
-- for a variable to be reported twice, if it's used both dependently
-- and non-dependently. (This isn't the most precise analysis, because
-- it's used in the typechecking knot. It might list some dependent
-- variables as also non-dependent.)
splitDepVarsOfType :: Type -> (TyCoVarSet, TyCoVarSet)
splitDepVarsOfType = go
  where
    go (TyVarTy tv)              = (tyCoVarsOfType $ tyVarKind tv, unitVarSet tv)
    go (AppTy t1 t2)             = combine [go t1, go t2]
    go (TyConApp _ tys)          = combine (map go tys)
    go (ForAllTy (Anon arg) res) = combine [go arg, go res]
    go (ForAllTy (Named tv _) ty)
      = let (kvs, tvs) = go ty in
        ( kvs `delVarSet` tv `unionVarSet` tyCoVarsOfType (tyVarKind tv)
        , tvs `delVarSet` tv )
    go (LitTy {})                = combine []
    go (CastTy ty co)            = combine [go ty, (tyCoVarsOfCo co, emptyVarSet)]
    go (CoercionTy co)           = go_co co

    go_co co = let Pair ty1 ty2 = coercionKind co in
               combine [go ty1, go ty2]

    combine [] = (emptyVarSet, emptyVarSet)
    combine ((kvs, tvs) : rest) = let (kvs', tvs') = combine rest in
                                  (kvs `unionVarSet` kvs', tvs `unionVarSet` tvs')

-- | Like 'splitDepVarsOfType', but over a list of types
splitDepVarsOfTypes :: [Type] -> (TyCoVarSet, TyCoVarSet)
splitDepVarsOfTypes tys
  = let (kvss, tvss) = mapAndUnzip splitDepVarsOfType tys in
    (unionVarSets kvss, unionVarSets tvss)
