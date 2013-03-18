%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1998
%

Type - public interface

\begin{code}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

-- | Main functions for manipulating types and type-related things
module Type (
	-- Note some of this is just re-exports from TyCon..

        -- * Main data types representing Types
	-- $type_classification
	
        -- $representation_types
        TyThing(..), Type, KindOrType, PredType, ThetaType,
        Var, TyVar, isTyVar, TyCoVar,

        -- ** Constructing and deconstructing types
        mkOnlyTyVarTy, mkOnlyTyVarTys, getTyVar, getTyVar_maybe, repGetTyVar_maybe,
        getTyCoVar_maybe, mkTyCoVarTy, mkTyCoVarTys,

	mkAppTy, mkAppTys, mkNakedAppTys, splitAppTy, splitAppTys, 
	splitAppTy_maybe, repSplitAppTy_maybe,

	mkFunTy, mkFunTys, splitFunTy, splitFunTy_maybe, 
	splitFunTys, splitFunTysN,
	funResultTy, funArgTy, zipFunTys, 

	mkTyConApp, mkTyConTy,
	tyConAppTyCon_maybe, tyConAppArgs_maybe, tyConAppTyCon, tyConAppArgs, 
	splitTyConApp_maybe, splitTyConApp, tyConAppArgN,

        mkForAllTy, mkForAllTys, splitForAllTy_maybe, splitForAllTys,
        splitForAllTy,
        mkPiKinds, mkPiType, mkPiTypes, mkPiTypesNoTv, piResultTy,
        splitPiTypes, applyTy, applyTys, applyTysD, isForAllTy, dropForAlls,

        mkNumLitTy, isNumLitTy,
        mkStrLitTy, isStrLitTy,

        mkCastTy, mkCoercionTy,

        coAxNthLHS,

        stripCoercionTy, splitCoercionType_maybe,
	
	-- (Newtypes)
	newTyConInstRhs, 
	
	-- Pred types
        mkFamilyTyConApp,
	isDictLikeTy,
        mkEqPred, mkPrimEqPred, mkHeteroPrimEqPred,
        mkClassPred,
        noParenPred, isClassPred, isEqPred, 
        isIPPred, isIPPred_maybe, isIPTyCon, isIPClass,
        
        -- Deconstructing predicate types
        PredTree(..), classifyPredType,
        getClassPredTys, getClassPredTys_maybe,
        getEqPredTys, getEqPredTys_maybe,

	-- ** Common type constructors
        funTyCon,

        -- ** Predicates on types
        isTypeVar, isKindVar, isTyCoVarTy,
        isTyVarTy, isFunTy, isDictTy, isPredTy, isKindTy, isCoercionTy,
        isCoercionTy_maybe, isCoercionType,

	-- (Lifting and boxity)
	isUnLiftedType, isUnboxedTupleType, isAlgType, isClosedAlgType,
	isPrimitiveType, isStrictType,

	-- * Main data types representing Kinds
	-- $kind_subtyping
        Kind, SimpleKind, MetaKindVar,

        -- ** Finding the kind of a type
        typeKind,
        
        -- ** Common Kinds and SuperKinds
        anyKind, liftedTypeKind, unliftedTypeKind, openTypeKind,
        constraintKind, superKind, 

        -- ** Common Kind type constructors
        liftedTypeKindTyCon, openTypeKindTyCon, unliftedTypeKindTyCon,
        constraintKindTyCon, anyKindTyCon,

	-- * Type free variables
	tyCoVarsOfType, tyCoVarsOfTypes,
	expandTypeSynonyms, 
	typeSize, varSetElemsWellScoped, 

	-- * Type comparison
        eqType, eqTypeX, eqTypes, cmpType, cmpTypes, cmpTypeX, cmpTc,
	eqPred, eqPredX, cmpPred, eqKind, eqTyCoVarBndrs,

	-- * Forcing evaluation of types
        seqType, seqTypes,

        -- * Other views onto Types
        coreView, tcView, 

        UnaryType, RepType(..), flattenRepType, repType,

	-- * Type representation for the code generator
	typePrimRep, typeRepArity,

	-- * Main type substitution data types
	TvSubstEnv,	-- Representation widely visible
	TCvSubst(..), 	-- Representation visible to a few friends
	
	-- ** Manipulating type substitutions
	emptyTvSubstEnv, emptyTCvSubst, mkEmptyTCvSubst,
	
	mkTCvSubst, mkOpenTCvSubst, zipOpenTCvSubst, zipTopTCvSubst,
        mkTopTCvSubst, notElemTCvSubst,
        getTvSubstEnv, setTvSubstEnv,
        zapTCvSubst, getTCvInScope,
        extendTCvInScope, extendTCvInScopeList,
 	extendTCvSubst, extendTCvSubstList,
        isInScope, composeTCvSubstEnv, zipTyCoEnv,
        isEmptyTCvSubst, unionTCvSubst,

	-- ** Performing substitution on types and kinds
	substTy, substTys, substTyWith, substTysWith, substTheta, 
        substTyCoVar, substTyCoVars, substTyVarBndr, substTyCoVarBndr,
        cloneTyVarBndr, lookupTyVar, lookupVar,
        substKiWith, substKisWith,

	-- * Pretty-printing
	pprType, pprParendType, pprTypeApp, pprTyThingCategory, pprTyThing, 
        pprTCvBndr, pprTCvBndrs, pprForAll, pprSigmaType,
	pprEqPred, pprTheta, pprThetaArrowTy, pprClassPred, 
        pprKind, pprParendKind, pprSourceTyCon,

        -- * Tidying type related things up for printing
        tidyType,      tidyTypes,
        tidyOpenType,  tidyOpenTypes,
        tidyOpenKind,
        tidyTyCoVarBndr, tidyTyCoVarBndrs, tidyFreeTyCoVars,
        tidyOpenTyCoVar, tidyOpenTyCoVars,
        tidyTyVarOcc,
        tidyTopType,
        tidyKind, 

        -- * Miscellaneous
        tcTyConsOfType
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

import Class
import TyCon
import TysPrim
import {-# SOURCE #-} TysWiredIn ( eqTyCon, typeNatKind, typeSymbolKind )
import PrelNames
import CoAxiom
import {-# SOURCE #-} Coercion

-- others
import BasicTypes	( Arity, RepArity )
import NameSet
import StaticFlags
import Util
import Outputable
import FastString
import Pair
import NameEnv

import Data.List        ( partition )
import Maybes		( orElse )
import Data.Maybe	( isJust )
import Control.Monad    ( guard )

infixr 3 `mkFunTy`	-- Associates to the right
\end{code}

\begin{code}
-- $type_classification
-- #type_classification#
-- 
-- Types are one of:
-- 
-- [Unboxed]            Iff its representation is other than a pointer
-- 			Unboxed types are also unlifted.
-- 
-- [Lifted]             Iff it has bottom as an element.
-- 			Closures always have lifted types: i.e. any
-- 			let-bound identifier in Core must have a lifted
-- 			type. Operationally, a lifted object is one that
-- 			can be entered.
-- 			Only lifted types may be unified with a type variable.
-- 
-- [Algebraic]          Iff it is a type with one or more constructors, whether
-- 			declared with @data@ or @newtype@.
-- 			An algebraic type is one that can be deconstructed
-- 			with a case expression. This is /not/ the same as 
--			lifted types, because we also include unboxed
-- 			tuples in this classification.
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
\end{code}

%************************************************************************
%*									*
		Type representation
%*									*
%************************************************************************

\begin{code}
{-# INLINE coreView #-}
coreView :: Type -> Maybe Type
-- ^ In Core, we \"look through\" non-recursive newtypes and 'PredTypes': this
-- function tries to obtain a different view of the supplied type given this
--
-- Strips off the /top layer only/ of a type to give 
-- its underlying representation type. 
-- Returns Nothing if there is nothing to look through.
--
-- By being non-recursive and inlined, this case analysis gets efficiently
-- joined onto the case analysis that the caller is already doing
coreView (TyConApp tc tys) | Just (tenv, rhs, tys') <- coreExpandTyCon_maybe tc tys 
              = Just (mkAppTys (substTy (mkTopTCvSubst tenv) rhs) tys')
               -- Its important to use mkAppTys, rather than (foldl AppTy),
               -- because the function part might well return a 
               -- partially-applied type constructor; indeed, usually will!
coreView _                 = Nothing

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
  = go ty
  where
    go (TyConApp tc tys)
      | Just (tenv, rhs, tys') <- tcExpandTyCon_maybe tc tys 
      = go (mkAppTys (substTy (mkTopTCvSubst tenv) rhs) tys')
      | otherwise
      = TyConApp tc (map go tys)
    go (LitTy l)       = LitTy l
    go (TyVarTy tv)    = TyVarTy tv
    go (AppTy t1 t2)   = mkAppTy (go t1) (go t2)
    go (FunTy t1 t2)   = FunTy (go t1) (go t2)
    go (ForAllTy tv t) = ForAllTy tv (go t)
    go (CastTy ty co)  = mkCastTy (go ty) (go_co co)
    go (CoercionTy co) = mkCoercionTy (go_co co)

    go_co (Refl ty)                 = mkReflCo (go ty)
    go_co (TyConAppCo tc args)
      | Just (cenv, rhs, args') <- tcExpandTyCon_maybe tc args
      = go_co (mkAppCos (liftCoSubst cenv rhs) args')
      | otherwise
      = mkTyConAppCo tc (map go_arg args)
    go_co (AppCo co arg)            = mkAppCo (go_co co) (go_arg arg)
    go_co (ForAllCo cobndr co)      = mkForAllCo cobndr (go_co co)
    go_co (CoVarCo cv)              = mkCoVarCo cv
    go_co (AxiomInstCo ax ind args) = mkAxiomInstCo ax ind (map go_arg args)
    go_co (UnsafeCo ty1 ty2)        = mkUnsafeCo (go ty1) (go ty2)
    go_co (SymCo co)                = mkSymCo (go_co co)
    go_co (TransCo co1 co2)         = mkTransCo (go_co co1) (go_co co2)
    go_co (NthCo n co)              = mkNthCo n (go_co co)
    go_co (LRCo lr co)              = mkLRCo lr (go_co co)
    go_co (InstCo co arg)           = mkInstCo (go_co co) (go_arg arg)
    go_co (CoherenceCo co1 co2)     = mkCoherenceCo (go_co co1) (go_co co2)
    go_co (KindCo co)               = mkKindCo (go_co co)

    go_arg (TyCoArg co)      = TyCoArg (go_co co)
    go_arg (CoCoArg co1 co2) = CoCoArg (go_co co1) (go_co co2)
\end{code}


%************************************************************************
%*									*
\subsection{Constructor-specific functions}
%*									*
%************************************************************************


---------------------------------------------------------------------
				TyVarTy
				~~~~~~~
\begin{code}
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

\end{code}


---------------------------------------------------------------------
				AppTy
				~~~~~
We need to be pretty careful with AppTy to make sure we obey the 
invariant that a TyConApp is always visibly so.  mkAppTy maintains the
invariant: use it.

\begin{code}
-- | Applies a type to another, as in e.g. @k a@
mkAppTy :: Type -> Type -> Type
mkAppTy (TyConApp tc tys) ty2 = mkTyConApp tc (tys ++ [ty2])
mkAppTy ty1               ty2 = AppTy ty1 ty2
	-- Note that the TyConApp could be an 
	-- under-saturated type synonym.  GHC allows that; e.g.
	--	type Foo k = k a -> k a
	--	type Id x = x
	--	foo :: Foo Id -> Foo Id
	--
	-- Here Id is partially applied in the type sig for Foo,
	-- but once the type synonyms are expanded all is well

mkAppTys :: Type -> [Type] -> Type
mkAppTys ty1                []	 = ty1
mkAppTys (TyConApp tc tys1) tys2 = mkTyConApp tc (tys1 ++ tys2)
mkAppTys ty1                tys2 = foldl AppTy ty1 tys2

mkNakedAppTys :: Type -> [Type] -> Type
mkNakedAppTys ty1           []	 = ty1
mkNakedAppTys (TyConApp tc tys1) tys2 = mkNakedTyConApp tc (tys1 ++ tys2)
mkNakedAppTys ty1                tys2 = foldl AppTy ty1 tys2

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
repSplitAppTy_maybe (FunTy ty1 ty2)   = Just (TyConApp funTyCon [ty1], ty2)
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
    split _       (FunTy ty1 ty2)       args = ASSERT( null args )
					       (TyConApp funTyCon [], [ty1,ty2])
    split orig_ty _                     args = (orig_ty, args)

\end{code}


                      LitTy
                      ~~~~~

\begin{code}
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

\end{code}


---------------------------------------------------------------------
				FunTy
				~~~~~

\begin{code}
mkFunTy :: Type -> Type -> Type
-- ^ Creates a function type from the given argument and result type
mkFunTy arg res = FunTy arg res

mkFunTys :: [Type] -> Type -> Type
mkFunTys tys ty = foldr mkFunTy ty tys

isFunTy :: Type -> Bool 
isFunTy ty = isJust (splitFunTy_maybe ty)

splitFunTy :: Type -> (Type, Type)
-- ^ Attempts to extract the argument and result types from a type, and
-- panics if that is not possible. See also 'splitFunTy_maybe'
splitFunTy ty | Just ty' <- coreView ty = splitFunTy ty'
splitFunTy (FunTy arg res)   = (arg, res)
splitFunTy other	     = pprPanic "splitFunTy" (ppr other)

splitFunTy_maybe :: Type -> Maybe (Type, Type)
-- ^ Attempts to extract the argument and result types from a type
splitFunTy_maybe ty | Just ty' <- coreView ty = splitFunTy_maybe ty'
splitFunTy_maybe (FunTy arg res)   = Just (arg, res)
splitFunTy_maybe _                 = Nothing

splitFunTys :: Type -> ([Type], Type)
splitFunTys ty = split [] ty ty
  where
    split args orig_ty ty | Just ty' <- coreView ty = split args orig_ty ty'
    split args _       (FunTy arg res)   = split (arg:args) res res
    split args orig_ty _                 = (reverse args, orig_ty)

splitFunTysN :: Int -> Type -> ([Type], Type)
-- ^ Split off exactly the given number argument types, and panics if that is not possible
splitFunTysN 0 ty = ([], ty)
splitFunTysN n ty = ASSERT2( isFunTy ty, int n <+> ppr ty )
                    case splitFunTy ty of { (arg, res) ->
		    case splitFunTysN (n-1) res of { (args, res) ->
		    (arg:args, res) }}

-- | Splits off argument types from the given type and associating
-- them with the things in the input list from left to right. The
-- final result type is returned, along with the resulting pairs of
-- objects and types, albeit with the list of pairs in reverse order.
-- Panics if there are not enough argument types for the input list.
zipFunTys :: Outputable a => [a] -> Type -> ([(a, Type)], Type)
zipFunTys orig_xs orig_ty = split [] orig_xs orig_ty orig_ty
  where
    split acc []     nty _                 = (reverse acc, nty)
    split acc xs     nty ty 
	  | Just ty' <- coreView ty 	   = split acc xs nty ty'
    split acc (x:xs) _   (FunTy arg res)   = split ((x,arg):acc) xs res res
    split _   _      _   _                 = pprPanic "zipFunTys" (ppr orig_xs <+> ppr orig_ty)
    
funResultTy :: Type -> Type
-- ^ Extract the function result type and panic if that is not possible
funResultTy ty = piResultTy ty (pprPanic "funResultTy" (ppr ty))

-- | Essentially 'funResultTy' on kinds handling pi-types too
piResultTy :: Type -> Type -> Type
piResultTy ty arg | Just ty' <- coreView ty = piResultTy ty' arg
piResultTy (FunTy _arg res) _    = res
piResultTy (ForAllTy tv res) arg = substTyWith [tv] [arg] res
piResultTy ty _                  = pprPanic "piResultTy" (ppr ty)

funArgTy :: Type -> Type
-- ^ Extract the function argument type and panic if that is not possible
funArgTy ty | Just ty' <- coreView ty = funArgTy ty'
funArgTy (FunTy arg _res)  = arg
funArgTy ty                = pprPanic "funArgTy" (ppr ty)
\end{code}

---------------------------------------------------------------------
				TyConApp
				~~~~~~~~

\begin{code}
-- | A key function: builds a 'TyConApp' or 'FunTy' as apppropriate to 
-- its arguments.  Applies its arguments to the constructor from left to right.
mkTyConApp :: TyCon -> [Type] -> Type
mkTyConApp tycon tys
  | isFunTyCon tycon, [ty1,ty2] <- tys
  = FunTy ty1 ty2

  | otherwise
  = TyConApp tycon tys

-- splitTyConApp "looks through" synonyms, because they don't
-- mean a distinct type, but all other type-constructor applications
-- including functions are returned as Just ..

-- | The same as @fst . splitTyConApp@
tyConAppTyCon_maybe :: Type -> Maybe TyCon
tyConAppTyCon_maybe ty | Just ty' <- coreView ty = tyConAppTyCon_maybe ty'
tyConAppTyCon_maybe (TyConApp tc _) = Just tc
tyConAppTyCon_maybe (FunTy {})      = Just funTyCon
tyConAppTyCon_maybe _               = Nothing

tyConAppTyCon :: Type -> TyCon
tyConAppTyCon ty = tyConAppTyCon_maybe ty `orElse` pprPanic "tyConAppTyCon" (ppr ty)

-- | The same as @snd . splitTyConApp@
tyConAppArgs_maybe :: Type -> Maybe [Type]
tyConAppArgs_maybe ty | Just ty' <- coreView ty = tyConAppArgs_maybe ty'
tyConAppArgs_maybe (TyConApp _ tys) = Just tys
tyConAppArgs_maybe (FunTy arg res)  = Just [arg,res]
tyConAppArgs_maybe _                = Nothing


tyConAppArgs :: Type -> [Type]
tyConAppArgs ty = tyConAppArgs_maybe ty `orElse` pprPanic "tyConAppArgs" (ppr ty)

tyConAppArgN :: Int -> Type -> Type
-- Executing Nth
tyConAppArgN n ty 
  = case tyConAppArgs_maybe ty of
      Just tys -> ASSERT2( n < length tys, ppr n <+> ppr tys ) tys !! n
      Nothing  -> pprPanic "tyConAppArgN" (ppr n <+> ppr ty)

-- | Attempts to tease a type apart into a type constructor and the application
-- of a number of arguments to that constructor. Panics if that is not possible.
-- See also 'splitTyConApp_maybe'
splitTyConApp :: Type -> (TyCon, [Type])
splitTyConApp ty = case splitTyConApp_maybe ty of
			Just stuff -> stuff
			Nothing	   -> pprPanic "splitTyConApp" (ppr ty)

-- | Attempts to tease a type apart into a type constructor and the application
-- of a number of arguments to that constructor
splitTyConApp_maybe :: Type -> Maybe (TyCon, [Type])
splitTyConApp_maybe ty | Just ty' <- coreView ty = splitTyConApp_maybe ty'
splitTyConApp_maybe (TyConApp tc tys) = Just (tc, tys)
splitTyConApp_maybe (FunTy arg res)   = Just (funTyCon, [arg,res])
splitTyConApp_maybe _                 = Nothing

newTyConInstRhs :: TyCon -> [Type] -> Type
-- ^ Unwrap one 'layer' of newtype on a type constructor and its arguments, using an 
-- eta-reduced version of the @newtype@ if possible
newTyConInstRhs tycon tys 
    = ASSERT2( equalLength tvs tys1, ppr tycon $$ ppr tys $$ ppr tvs )
      mkAppTys (substTyWith tvs tys1 ty) tys2
  where
    (tvs, ty)    = newTyConEtadRhs tycon
    (tys1, tys2) = splitAtList tvs tys
\end{code}

---------------------------------------------------------------------
                           CastTy
                           ~~~~~~
A casted type has its *kind* casted into something new.

Why not ignore Refl coercions? See Note [Optimising Refl] in OptCoercion.
\begin{code}
mkCastTy :: Type -> Coercion -> Type
mkCastTy = CastTy
\end{code}

--------------------------------------------------------------------
                            CoercionTy
                            ~~~~~~~~~~
CoercionTy allows us to inject coercions into types. A CoercionTy
should appear only in the right-hand side of an application.

\begin{code}
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
\end{code}

---------------------------------------------------------------------
				SynTy
				~~~~~

Notes on type synonyms
~~~~~~~~~~~~~~~~~~~~~~
The various "split" functions (splitFunTy, splitRhoTy, splitForAllTy) try
to return type synonyms whereever possible. Thus

	type Foo a = a -> a

we want 
	splitFunTys (a -> Foo a) = ([a], Foo a)
not			           ([a], a -> a)

The reason is that we then get better (shorter) type signatures in 
interfaces.  Notably this plays a role in tcTySigs in TcBinds.lhs.


Note [Expanding newtypes]
~~~~~~~~~~~~~~~~~~~~~~~~~
When expanding a type to expose a data-type constructor, we need to be
careful about newtypes, lest we fall into an infinite loop. Here are
the key examples:

  newtype Id  x = MkId x
  newtype Fix f = MkFix (f (Fix f))
  newtype T     = MkT (T -> T) 
  
  Type	         Expansion
 --------------------------
  T		 T -> T
  Fix Maybe      Maybe (Fix Maybe)
  Id (Id Int)    Int
  Fix Id         NO NO NO

Notice that we can expand T, even though it's recursive.
And we can expand Id (Id Int), even though the Id shows up
twice at the outer level.  

So, when expanding, we keep track of when we've seen a recursive
newtype at outermost level; and bale out if we see it again.


		Representation types
		~~~~~~~~~~~~~~~~~~~~

Note [Nullary unboxed tuple]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We represent the nullary unboxed tuple as the unary (but void) type
State# RealWorld.  The reason for this is that the ReprArity is never
less than the Arity (as it would otherwise be for a function type like
(# #) -> Int).

As a result, ReprArity is always strictly positive if Arity is. This
is important because it allows us to distinguish at runtime between a
thunk and a function takes a nullary unboxed tuple as an argument!

\begin{code}
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
--	1. For-alls
--	2. Synonyms
--	3. Predicates
--	4. All newtypes, including recursive ones, but not newtype families
--      5. Casts
--
-- It's useful in the back end of the compiler.
repType :: Type -> RepType
repType ty
  = go emptyNameSet ty
  where
    go :: NameSet -> Type -> RepType
    go rec_nts ty    	  		-- Expand predicates and synonyms
      | Just ty' <- coreView ty
      = go rec_nts ty'

    go rec_nts ty@(ForAllTy tv ty2)		-- Drop type foralls
      | isTyVar tv
      = go rec_nts ty2
      | otherwise
      = -- abstractions over coercions exist in the representation
        UnaryRep ty

    go rec_nts (TyConApp tc tys)	-- Expand newtypes
      | isNewTyCon tc
      , tys `lengthAtLeast` tyConArity tc
      , let tc_name = tyConName tc
            rec_nts' | isRecursiveTyCon tc = addOneToNameSet rec_nts tc_name
	             | otherwise	   = rec_nts
      , not (tc_name `elemNameSet` rec_nts)  -- See Note [Expanding newtypes]
      = go rec_nts' (newTyConInstRhs tc tys)

      | isUnboxedTupleTyCon tc
      = if null tys
         then UnaryRep realWorldStatePrimTy -- See Note [Nullary unboxed tuple]
         else UbxTupleRep (concatMap (flattenRepType . go rec_nts) tys)

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
    where go (TyConApp tc _) = tyConPrimRep tc
          go (ForAllTy _v _) = ASSERT( isCoVar _v ) PtrRep
          go (FunTy _ _)     = PtrRep
          go (AppTy _ _)     = PtrRep      -- See Note [AppTy rep] 
          go (TyVarTy _)     = PtrRep
          go (CastTy ty _)   = go ty  
          go _               = pprPanic "typePrimRep: UnaryRep" (ppr ty)

typeRepArity :: Arity -> Type -> RepArity
typeRepArity 0 _ = 0
typeRepArity n ty = case repType ty of
  UnaryRep (ForAllTy cv ty) -> length (flattenRepType (repType (varType cv))) + typeRepArity (n - 1) ty
  UnaryRep (FunTy ty1 ty2)  -> length (flattenRepType (repType ty1)) + typeRepArity (n - 1) ty2
  _                         -> pprPanic "typeRepArity: arity greater than type can handle" (ppr (n, ty, repType ty))
\end{code}

Note [AppTy rep]
~~~~~~~~~~~~~~~~
Types of the form 'f a' must be of kind *, not #, so we are guaranteed
that they are represented by pointers.  The reason is that f must have
kind (kk -> kk) and kk cannot be unlifted; see Note [The kind invariant] 
in TyCoRep.

Note [mkPiKinds vs mkPiTypes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If kinds and types are the same, why have separate mkPiKinds and mkPiTypes?
Because kinds and types are most certainly *not* the same, in source Haskell.
And, because 'Type's are shared between the levels, we need to maintain that
distinction down here. mkPiKinds is used to create the kind for user-visible
TyCons.

---------------------------------------------------------------------
				ForAllTy
				~~~~~~~~

\begin{code}
mkForAllTy :: TyVar -> Type -> Type
mkForAllTy tyvar ty
  = ForAllTy tyvar ty

-- | Wraps foralls over the type using the provided 'TyVar's from left to right
mkForAllTys :: [TyVar] -> Type -> Type
mkForAllTys tyvars ty = foldr ForAllTy ty tyvars

-- See Note [mkPiKinds vs mkPiTypes]
mkPiKinds :: [TyVar] -> Kind -> Kind
-- mkPiKinds [k1, k2, (a:k1 -> *)] k2
-- returns forall k1 k2. (k1 -> *) -> k2
mkPiKinds [] res = res
mkPiKinds (tv:tvs) res 
  | isKindVar tv = ForAllTy tv          (mkPiKinds tvs res)
  | otherwise    = FunTy (tyVarKind tv) (mkPiKinds tvs res)

mkPiType  :: Var -> Type -> Type
-- ^ Makes a @(->)@ type or a forall type, depending
-- on whether it is given a type variable or a term variable.
mkPiTypes :: [Var] -> Type -> Type
-- ^ 'mkPiType' for multiple type or value arguments

mkPiType v ty
   |  isTyVar v
   || isCoVar v = mkForAllTy v ty
   | otherwise  = mkFunTy (varType v) ty

mkPiTypes vs ty = foldr mkPiType ty vs

-- | Given a list of kinds, makes either FunTys or ForAllTys (quantified
-- over a wild card) as appropriate. (A ForAllTy is used only when the type
-- is a coercion type.)
mkPiTypesNoTv :: [Type] -> Type -> Type
mkPiTypesNoTv [] ty = ty
mkPiTypesNoTv (k:ks) ty
  = let result = mkPiTypesNoTv ks ty in
    if isCoercionType k
    then mkForAllTy (mkCoVar wildCardName k) result
    else mkFunTy k result

-- | Take a pi type (that is, either a ForAllTy or a FunTy) apart, returning
-- the list of argument types and the result type. This always succeeds, even
-- if it returns only an empty list. Note that the second type returned may
-- have free variables that were bound by a forall.
splitPiTypes :: Type -> ([Type], Type)
splitPiTypes ty | Just ty' <- coreView ty = splitPiTypes ty'
splitPiTypes (FunTy arg res)              = let (args, res') = splitPiTypes res in
                                            (arg:args, res')
splitPiTypes (ForAllTy tv ty)             = let (args, res') = splitPiTypes ty in
                                            (tyVarKind tv : args, res')
splitPiTypes ty                           = ([], ty)

isForAllTy :: Type -> Bool
isForAllTy (ForAllTy _ _) = True
isForAllTy _              = False

-- | Take a forall type apart, or panics if that is not possible.
splitForAllTy :: Type -> (TyCoVar, Type)
splitForAllTy ty
  | Just (tv, ty') <- splitForAllTy_maybe ty = (tv, ty')
  | otherwise                                = pprPanic "splitForAllTy" (ppr ty)

-- | Attempts to take a forall type apart, returning the bound type variable
-- and the remainder of the type
splitForAllTy_maybe :: Type -> Maybe (TyCoVar, Type)
splitForAllTy_maybe ty = splitFAT_m ty
  where
    splitFAT_m ty | Just ty' <- coreView ty = splitFAT_m ty'
    splitFAT_m (ForAllTy tyvar ty)	    = Just(tyvar, ty)
    splitFAT_m _			    = Nothing

-- | Attempts to take a forall type apart, returning all the immediate such bound
-- type variables and the remainder of the type. Always suceeds, even if that means
-- returning an empty list of 'TyVar's
splitForAllTys :: Type -> ([TyCoVar], Type)
splitForAllTys ty = split ty ty []
   where
     split orig_ty ty tvs | Just ty' <- coreView ty = split orig_ty ty' tvs
     split _       (ForAllTy tv ty)  tvs = split ty ty (tv:tvs)
     split orig_ty _                 tvs = (reverse tvs, orig_ty)

-- | Equivalent to @snd . splitForAllTys@
dropForAlls :: Type -> Type
dropForAlls ty = snd (splitForAllTys ty)
\end{code}

-- (mkPiType now in CoreUtils)

applyTy, applyTys
~~~~~~~~~~~~~~~~~

\begin{code}
-- | Instantiate a forall type with one or more type arguments.
-- Used when we have a polymorphic function applied to type args:
--
-- > f t1 t2
--
-- We use @applyTys type-of-f [t1,t2]@ to compute the type of the expression.
-- Panics if no application is possible.
applyTy :: Type -> KindOrType -> Type
applyTy ty arg | Just ty' <- coreView ty = applyTy ty' arg
applyTy (ForAllTy tv ty) arg = substTyWith [tv] [arg] ty
applyTy _                _   = panic "applyTy"

applyTys :: Type -> [KindOrType] -> Type
-- ^ This function is interesting because:
--
--	1. The function may have more for-alls than there are args
--
--	2. Less obviously, it may have fewer for-alls
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

applyTysD :: SDoc -> Type -> [Type] -> Type	-- Debug version
applyTysD _   orig_fun_ty []      = orig_fun_ty
applyTysD doc orig_fun_ty arg_tys 
  | n_tvs == n_args 	-- The vastly common case
  = substTyWith tvs arg_tys rho_ty
  | n_tvs > n_args 	-- Too many for-alls
  = substTyWith (take n_args tvs) arg_tys 
		(mkForAllTys (drop n_args tvs) rho_ty)
  | otherwise		-- Too many type args
  = ASSERT2( n_tvs > 0, doc $$ ppr orig_fun_ty )	-- Zero case gives infnite loop!
    applyTysD doc (substTyWith tvs (take n_tvs arg_tys) rho_ty)
	          (drop n_tvs arg_tys)
  where
    (tvs, rho_ty) = splitForAllTys orig_fun_ty 
    n_tvs = length tvs
    n_args = length arg_tys     
\end{code}


%************************************************************************
%*									*
                         Pred
%*									*
%************************************************************************

Predicates on PredType

\begin{code}
noParenPred :: PredType -> Bool
-- A predicate that can appear without parens before a "=>"
--       C a => a -> a
--       a~b => a -> b
-- But   (?x::Int) => Int -> Int
noParenPred p = not (isIPPred p) && isClassPred p || isEqPred p

isPredTy :: Type -> Bool
isPredTy ty
  | isSuperKind ty = False
  | otherwise = isConstraintKind (typeKind ty)

isKindTy :: Type -> Bool
isKindTy = isSuperKind . typeKind

isClassPred, isEqPred, isIPPred :: PredType -> Bool
isClassPred ty = case tyConAppTyCon_maybe ty of
    Just tyCon | isClassTyCon tyCon -> True
    _                               -> False
isEqPred ty = case tyConAppTyCon_maybe ty of
    Just tyCon -> tyCon `hasKey` eqTyConKey
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
\end{code}

Make PredTypes

--------------------- Equality types ---------------------------------
\begin{code}
-- | Creates a type equality predicate
mkEqPred :: Type -> Type -> PredType
mkEqPred ty1 ty2
  = WARN( not (k `eqKind` typeKind ty2), ppr ty1 $$ ppr ty2 $$ ppr k $$ ppr (typeKind ty2) )
    TyConApp eqTyCon [k, ty1, ty2]
  where 
    k = typeKind ty1

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

-- | Try to split up a coercion type into the types that it coerces
splitCoercionType_maybe :: Type -> Maybe (Type, Type)
splitCoercionType_maybe ty
  = do { (tc, [_, _, ty1, ty2]) <- splitTyConApp_maybe ty
       ; guard $ tc `hasKey` eqPrimTyConKey
       ; return (ty1, ty2) }

\end{code}

--------------------- Dictionary types ---------------------------------
\begin{code}
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
\end{code}

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

\begin{code}
data PredTree = ClassPred Class [Type]
              | EqPred Type Type
              | TuplePred [PredType]
              | IrredPred PredType

classifyPredType :: PredType -> PredTree
classifyPredType ev_ty = case splitTyConApp_maybe ev_ty of
    Just (tc, tys) | Just clas <- tyConClass_maybe tc
                   -> ClassPred clas tys
    Just (tc, tys) | tc `hasKey` eqTyConKey
                   , let [_, ty1, ty2] = tys
                   -> EqPred ty1 ty2
    Just (tc, tys) | isTupleTyCon tc
                   -> TuplePred tys
    _ -> IrredPred ev_ty
\end{code}

\begin{code}
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
      Just (tc, (_ : ty1 : ty2 : tys)) -> ASSERT( tc `hasKey` eqTyConKey && null tys )
                                          (ty1, ty2)
      _ -> pprPanic "getEqPredTys" (ppr ty)

getEqPredTys_maybe :: PredType -> Maybe (Type, Type)
getEqPredTys_maybe ty 
  = case splitTyConApp_maybe ty of 
      Just (tc, [_, ty1, ty2]) | tc `hasKey` eqTyConKey -> Just (ty1, ty2)
      _ -> Nothing
\end{code}

%************************************************************************
%*									*
                   Size									
%*									*
%************************************************************************

\begin{code}
typeSize :: Type -> Int
typeSize (LitTy {})      = 1
typeSize (TyVarTy {})    = 1
typeSize (AppTy t1 t2)   = typeSize t1 + typeSize t2
typeSize (FunTy t1 t2)   = typeSize t1 + typeSize t2
typeSize (ForAllTy _ t)  = 1 + typeSize t
typeSize (TyConApp _ ts) = 1 + sum (map typeSize ts)
typeSize (CastTy ty co)  = 1 + typeSize ty + coercionSize co
typeSize (CoercionTy co) = 1 + coercionSize co

-- no promises that this is the most efficient, but it will do the job
type DepEnv = VarEnv VarSet
varSetElemsWellScoped :: VarSet -> [TyCoVar]
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
      = let (scoped', unsorted') = partition (well_scoped scoped) unsorted in
        build_list (scoped ++ scoped') unsorted'

    well_scoped scoped var = get_deps var `subVarSet` (mkVarSet scoped)

\end{code}


%************************************************************************
%*									*
\subsection{Type families}
%*									*
%************************************************************************

\begin{code}
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
  = ppr $ fam_tc `TyConApp` tys	       -- can't be FunTyCon
  | otherwise
  = ppr tycon
\end{code}

%************************************************************************
%*									*
\subsection{Liftedness}
%*									*
%************************************************************************

\begin{code}
-- | See "Type#type_classification" for what an unlifted type is
isUnLiftedType :: Type -> Bool
	-- isUnLiftedType returns True for forall'd unlifted types:
	--	x :: forall a. Int#
	-- I found bindings like these were getting floated to the top level.
	-- They are pretty bogus types, mind you.  It would be better never to
	-- construct them

isUnLiftedType ty | Just ty' <- coreView ty = isUnLiftedType ty'
isUnLiftedType (ForAllTy tv ty)  
  | isTyVar tv                      = isUnLiftedType ty
  | otherwise {- co var -}          = False
isUnLiftedType (TyConApp tc _)      = isUnLiftedTyCon tc
isUnLiftedType _                    = False

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
      _other	         -> False

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
\end{code}

\begin{code}
-- | Computes whether an argument (or let right hand side) should
-- be computed strictly or lazily, based only on its type.
-- Works just like 'isUnLiftedType', except that it has a special case 
-- for dictionaries (i.e. does not work purely on representation types)

-- Since it takes account of class 'PredType's, you might think
-- this function should be in 'TcType', but 'isStrictType' is used by 'DataCon',
-- which is below 'TcType' in the hierarchy, so it's convenient to put it here.
--
-- We may be strict in dictionary types, but only if it 
-- has more than one component.
--
-- (Being strict in a single-component dictionary risks
--  poking the dictionary component, which is wrong.)
isStrictType :: Type -> Bool
isStrictType ty | Just ty' <- coreView ty = isStrictType ty'
isStrictType (ForAllTy _ ty)   = isStrictType ty
isStrictType (TyConApp tc _)
 | isUnLiftedTyCon tc               = True
 | isClassTyCon tc, opt_DictsStrict = True
isStrictType _                      = False
\end{code}

\begin{code}
isPrimitiveType :: Type -> Bool
-- ^ Returns true of types that are opaque to Haskell.
-- Most of these are unlifted, but now that we interact with .NET, we
-- may have primtive (foreign-imported) types that are lifted
isPrimitiveType ty = case splitTyConApp_maybe ty of
			Just (tc, ty_args) -> ASSERT( ty_args `lengthIs` tyConArity tc )
					      isPrimTyCon tc
			_                  -> False
\end{code}


%************************************************************************
%*									*
\subsection{Sequencing on types}
%*									*
%************************************************************************

\begin{code}
seqType :: Type -> ()
seqType (LitTy n)         = n `seq` ()
seqType (TyVarTy tv) 	  = tv `seq` ()
seqType (AppTy t1 t2) 	  = seqType t1 `seq` seqType t2
seqType (FunTy t1 t2) 	  = seqType t1 `seq` seqType t2
seqType (TyConApp tc tys) = tc `seq` seqTypes tys
seqType (ForAllTy tv ty)  = seqType (tyVarKind tv) `seq` seqType ty
seqType (CastTy ty co)    = seqType ty `seq` seqCo co
seqType (CoercionTy co)   = seqCo co

seqTypes :: [Type] -> ()
seqTypes []       = ()
seqTypes (ty:tys) = seqType ty `seq` seqTypes tys
\end{code}


%************************************************************************
%*									*
		Comparision for types 
	(We don't use instances so that we know where it happens)
%*									*
%************************************************************************

\begin{code}
eqKind :: Kind -> Kind -> Bool
eqKind = eqType

eqType :: Type -> Type -> Bool
-- ^ Type equality on source types. Does not look through @newtypes@ or 
-- 'PredType's, but it does look through type synonyms.
eqType t1 t2 = isEqual $ cmpType t1 t2

eqTypeX :: RnEnv2 -> Type -> Type -> Bool
eqTypeX env t1 t2 = isEqual $ cmpTypeX env t1 t2

eqTypes :: [Type] -> [Type] -> Bool
eqTypes tys1 tys2 = isEqual $ cmpTypes tys1 tys2

eqPred :: PredType -> PredType -> Bool
eqPred = eqType

eqPredX :: RnEnv2 -> PredType -> PredType -> Bool
eqPredX env p1 p2 = isEqual $ cmpTypeX env p1 p2

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
\end{code}

Now here comes the real worker

\begin{code}
cmpType :: Type -> Type -> Ordering
cmpType t1 t2 = cmpTypeX rn_env t1 t2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfType t1 `unionVarSet` tyCoVarsOfType t2))

cmpTypes :: [Type] -> [Type] -> Ordering
cmpTypes ts1 ts2 = cmpTypesX rn_env ts1 ts2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfTypes ts1 `unionVarSet` tyCoVarsOfTypes ts2))

cmpPred :: PredType -> PredType -> Ordering
cmpPred p1 p2 = cmpTypeX rn_env p1 p2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfType p1 `unionVarSet` tyCoVarsOfType p2))

cmpTypeX :: RnEnv2 -> Type -> Type -> Ordering	-- Main workhorse
cmpTypeX env t1 t2 | Just t1' <- coreView t1 = cmpTypeX env t1' t2
		   | Just t2' <- coreView t2 = cmpTypeX env t1 t2'
-- We expand predicate types, because in Core-land we have
-- lots of definitions like
--      fOrdBool :: Ord Bool
--      fOrdBool = D:Ord .. .. ..
-- So the RHS has a data type

cmpTypeX env (TyVarTy tv1)       (TyVarTy tv2)       = rnOccL env tv1 `compare` rnOccR env tv2
cmpTypeX env (ForAllTy tv1 t1)   (ForAllTy tv2 t2)   = cmpTypeX env (tyVarKind tv1) (tyVarKind tv1)
                                                       `thenCmp` cmpTypeX (rnBndr2 env tv1 tv2) t1 t2
cmpTypeX env (AppTy s1 t1)       (AppTy s2 t2)       = cmpTypeX env s1 s2 `thenCmp` cmpTypeX env t1 t2
cmpTypeX env (FunTy s1 t1)       (FunTy s2 t2)       = cmpTypeX env s1 s2 `thenCmp` cmpTypeX env t1 t2
cmpTypeX env (TyConApp tc1 tys1) (TyConApp tc2 tys2) = (tc1 `cmpTc` tc2) `thenCmp` cmpTypesX env tys1 tys2
cmpTypeX _   (LitTy l1)          (LitTy l2)          = compare l1 l2
cmpTypeX env (CastTy t1 c1)      (CastTy t2 c2)      = cmpTypeX env t1 t2 `thenCmp` cmpCoercionX env c1 c2
cmpTypeX env (CoercionTy c1)     (CoercionTy c2)     = cmpCoercionX env c1 c2

    -- Deal with the rest: TyVarTy < CoercionTy < CastTy < AppTy < FunTy < LitTy < TyConApp < ForAllTy
cmpTypeX _ ty1 ty2
  = (get_rank ty1) `compare` (get_rank ty2)
  where get_rank :: Type -> Int
        get_rank (TyVarTy {})    = 0
        get_rank (CoercionTy {}) = 1
        get_rank (CastTy {})     = 2
        get_rank (AppTy {})      = 3
        get_rank (FunTy {})      = 4
        get_rank (LitTy {})      = 5
        get_rank (TyConApp {})   = 6
        get_rank (ForAllTy {})   = 7

-------------
cmpTypesX :: RnEnv2 -> [Type] -> [Type] -> Ordering
cmpTypesX _   []        []        = EQ
cmpTypesX env (t1:tys1) (t2:tys2) = cmpTypeX env t1 t2 `thenCmp` cmpTypesX env tys1 tys2
cmpTypesX _   []        _         = LT
cmpTypesX _   _         []        = GT

-------------
cmpTc :: TyCon -> TyCon -> Ordering
-- Here we treat BOX, *, and Constraint as equal
-- See Note [Kind Constraint and kind *] and Note [SuperKind] in Kinds.lhs
cmpTc tc1 tc2 = nu1 `compare` nu2
  where
    u1  = tyConUnique tc1
    nu1 = if isStarKindCon tc1 then liftedTypeKindTyConKey else u1
    u2  = tyConUnique tc2
    nu2 = if isStarKindCon tc2 then liftedTypeKindTyConKey else u2
\end{code}

Note [cmpTypeX]
~~~~~~~~~~~~~~~

When we compare foralls, we should look at the kinds. But if we do so,
we get a corelint error like the following (in
libraries/ghc-prim/GHC/PrimopWrappers.hs):

    Binder's type: forall (o_abY :: *).
                   o_abY
                   -> GHC.Prim.State# GHC.Prim.RealWorld
                   -> GHC.Prim.State# GHC.Prim.RealWorld
    Rhs type: forall (a_12 :: ?).
              a_12
              -> GHC.Prim.State# GHC.Prim.RealWorld
              -> GHC.Prim.State# GHC.Prim.RealWorld

This is why we don't look at the kind. Maybe we should look if the
kinds are compatible.

-- cmpTypeX env (ForAllTy tv1 t1)   (ForAllTy tv2 t2)
--   = cmpTypeX env (tyVarKind tv1) (tyVarKind tv2) `thenCmp`
--     cmpTypeX (rnBndr2 env tv1 tv2) t1 t2

----------------------------------------------------
-- Kind Stuff

Kinds
~~~~~

For the description of subkinding in GHC, see
  http://hackage.haskell.org/trac/ghc/wiki/Commentary/Compiler/TypeType#Kinds

\begin{code}
type MetaKindVar = TyVar  -- invariant: MetaKindVar will always be a
                          -- TcTyVar with details MetaTv TauTv ...
-- meta kind var constructors and functions are in TcType

type SimpleKind = Kind
\end{code}

%************************************************************************
%*                                                                      *
        The kind of a type
%*                                                                      *
%************************************************************************

\begin{code}
typeKind :: Type -> Kind
typeKind (TyConApp tc tys)
  = kindAppResult (tyConKind tc) tys

typeKind (AppTy fun arg)      = kindAppResult (typeKind fun) [arg]
typeKind (LitTy l)            = typeLiteralKind l
typeKind (ForAllTy _ ty)      = typeKind ty
typeKind (TyVarTy tyvar)      = tyVarKind tyvar
typeKind _ty@(FunTy _arg res)
    -- Hack alert.  The kind of (Int -> Int#) is liftedTypeKind (*), 
    --              not unliftedTypKind (#)
    -- The only things that can be after a function arrow are
    --   (a) types (of kind openTypeKind or its sub-kinds)
    --   (b) kinds (of super-kind TY) (e.g. * -> (* -> *))
    | isSuperKind k         = k
    | otherwise             = ASSERT2( isSubOpenTypeKind k, ppr _ty $$ ppr k ) liftedTypeKind
    where
      k = typeKind res
typeKind (CastTy _ty co)    = pSnd $ coercionKind co
typeKind (CoercionTy co)    = coercionType co

typeLiteralKind :: TyLit -> Kind
typeLiteralKind l =
  case l of
    NumTyLit _ -> typeNatKind
    StrTyLit _ -> typeSymbolKind
\end{code}

Kind inference
~~~~~~~~~~~~~~
During kind inference, a kind variable unifies only with 
a "simple kind", sk
	sk ::= * | sk1 -> sk2
For example 
	data T a = MkT a (T Int#)
fails.  We give T the kind (k -> *), and the kind variable k won't unify
with # (the kind of Int#).

Type inference
~~~~~~~~~~~~~~
When creating a fresh internal type variable, we give it a kind to express 
constraints on it.  E.g. in (\x->e) we make up a fresh type variable for x, 
with kind ??.  

During unification we only bind an internal type variable to a type
whose kind is lower in the sub-kind hierarchy than the kind of the tyvar.

When unifying two internal type variables, we collect their kind constraints by
finding the GLB of the two.  Since the partial order is a tree, they only
have a glb if one is a sub-kind of the other.  In that case, we bind the
less-informative one to the more informative one.  Neat, eh?


%************************************************************************
%*                                                                      *
        Miscellaneous functions
%*                                                                      *
%************************************************************************


\begin{code}
tcTyConsOfType :: Type -> [TyCon]
-- tcTyConsOfType looks through all synonyms, but not through any newtypes.
-- When it finds a Class, it returns the class TyCon.  The reaons it's here
-- (not in Type.lhs) is because it is newtype-aware.
tcTyConsOfType ty
  = nameEnvElts (go ty)
  where
     go :: Type -> NameEnv TyCon  -- The NameEnv does duplicate elim
     go ty | Just ty' <- tcView ty = go ty'
     go (TyVarTy {})               = emptyNameEnv
     go (LitTy {})                 = emptyNameEnv
     go (TyConApp tc tys)          = go_tc tc `plusNameEnv` go_s tys
     go (AppTy a b)                = go a `plusNameEnv` go b
     go (FunTy a b)                = go a `plusNameEnv` go b
     go (ForAllTy tv ty)           = go ty `plusNameEnv` go (tyVarKind tv)
     go (CastTy ty co)             = go ty `plusNameEnv` go_co co
     go (CoercionTy co)            = go_co co

     go_co (Refl ty)               = go ty
     go_co (TyConAppCo tc args)    = go_tc tc `plusNameEnv` go_args args
     go_co (AppCo co arg)          = go_co co `plusNameEnv` go_arg arg
     go_co (ForAllCo cobndr co)
       | Just (h, _, _) <- splitHeteroCoBndr_maybe cobndr
       = go_co h `plusNameEnv` var_names `plusNameEnv` go_co co
       | otherwise
       = var_names `plusNameEnv` go_co co
       where var_names = go_s (snd (coBndrVarsKinds cobndr))
     go_co (CoVarCo {})            = emptyNameEnv
     go_co (AxiomInstCo ax _ args) = go_ax ax `plusNameEnv` go_args args
     go_co (UnsafeCo ty1 ty2)      = go ty1 `plusNameEnv` go ty2
     go_co (SymCo co)              = go_co co
     go_co (TransCo co1 co2)       = go_co co1 `plusNameEnv` go_co co2
     go_co (NthCo _ co)            = go_co co
     go_co (LRCo _ co)             = go_co co
     go_co (InstCo co arg)         = go_co co `plusNameEnv` go_arg arg
     go_co (CoherenceCo co1 co2)   = go_co co1 `plusNameEnv` go_co co2
     go_co (KindCo co)             = go_co co

     go_arg (TyCoArg co)           = go_co co
     go_arg (CoCoArg co1 co2)      = go_co co1 `plusNameEnv` go_co co2

     go_s tys = foldr (plusNameEnv . go) emptyNameEnv tys
     go_args args = foldr (plusNameEnv . go_arg) emptyNameEnv args

     go_tc tc = unitNameEnv (tyConName tc) tc
     go_ax ax = go_tc $ coAxiomTyCon ax
\end{code}
