-- (c) The University of Glasgow 2006-2012

{-# LANGUAGE CPP #-}
module Kind (
        -- * Main data type
        Kind, typeKind,

        -- ** Predicates on Kinds
        isLiftedTypeKind, isUnliftedTypeKind,
        isConstraintKind,
        returnsTyCon, returnsConstraintKind,
        isConstraintKindCon,
        okArrowArgKind, okArrowResultKind,

        classifiesTypeWithValues,
        isStarKind, isStarKindSynonymTyCon,
        isKindLevPoly
       ) where

#include "HsVersions.h"

import {-# SOURCE #-} Type       ( typeKind, coreViewOneStarKind )

import TyCoRep
import TyCon
import PrelNames

import Outputable
import Util

{-
************************************************************************
*                                                                      *
        Functions over Kinds
*                                                                      *
************************************************************************

Note [Kind Constraint and kind *]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The kind Constraint is the kind of classes and other type constraints.
The special thing about types of kind Constraint is that
 * They are displayed with double arrow:
     f :: Ord a => a -> a
 * They are implicitly instantiated at call sites; so the type inference
   engine inserts an extra argument of type (Ord a) at every call site
   to f.

However, once type inference is over, there is *no* distinction between
Constraint and *.  Indeed we can have coercions between the two. Consider
   class C a where
     op :: a -> a
For this single-method class we may generate a newtype, which in turn
generates an axiom witnessing
    C a ~ (a -> a)
so on the left we have Constraint, and on the right we have *.
See Trac #7451.

Bottom line: although '*' and 'Constraint' are distinct TyCons, with
distinct uniques, they are treated as equal at all times except
during type inference.
-}

isConstraintKind :: Kind -> Bool
isConstraintKindCon :: TyCon -> Bool

isConstraintKindCon   tc = tyConUnique tc == constraintKindTyConKey

isConstraintKind (TyConApp tc _) = isConstraintKindCon tc
isConstraintKind _               = False

-- | Does the given type "end" in the given tycon? For example @k -> [a] -> *@
-- ends in @*@ and @Maybe a -> [a]@ ends in @[]@.
returnsTyCon :: Unique -> Type -> Bool
returnsTyCon tc_u (ForAllTy _ ty)  = returnsTyCon tc_u ty
returnsTyCon tc_u (FunTy    _ ty)  = returnsTyCon tc_u ty
returnsTyCon tc_u (TyConApp tc' _) = tc' `hasKey` tc_u
returnsTyCon _  _                  = False

returnsConstraintKind :: Kind -> Bool
returnsConstraintKind = returnsTyCon constraintKindTyConKey

-- | Tests whether the given kind (which should look like "TYPE ...")
-- has any free variables
isKindLevPoly :: Kind -> Bool
isKindLevPoly k = ASSERT2( isStarKind k ||  -- necessary b/c of Constraint
                           case k of
                             TyConApp typ [_] | typ `hasKey` tYPETyConKey -> True
                             _                                            -> False
                         , ppr k )
                  not $ noFreeVarsOfType k

--------------------------------------------
--            Kinding for arrow (->)
-- Says when a kind is acceptable on lhs or rhs of an arrow
--     arg -> res
--
-- See Note [Levity polymorphism]

okArrowArgKind, okArrowResultKind :: Kind -> Bool
okArrowArgKind    = classifiesTypeWithValues
okArrowResultKind = classifiesTypeWithValues

-----------------------------------------
--              Subkinding
-- The tc variants are used during type-checking, where ConstraintKind
-- is distinct from all other kinds
-- After type-checking (in core), Constraint and liftedTypeKind are
-- indistinguishable

-- | Does this classify a type allowed to have values? Responds True to things
-- like *, #, TYPE Lifted, TYPE v, Constraint.
classifiesTypeWithValues :: Kind -> Bool
-- ^ True of any sub-kind of OpenTypeKind
classifiesTypeWithValues t | Just t' <- coreViewOneStarKind t = classifiesTypeWithValues t'
classifiesTypeWithValues (TyConApp tc [_]) = tc `hasKey` tYPETyConKey
classifiesTypeWithValues _ = False

-- | Is this kind equivalent to *?
isStarKind :: Kind -> Bool
isStarKind k | Just k' <- coreViewOneStarKind k = isStarKind k'
isStarKind (TyConApp tc [TyConApp ptr_rep []])
  =  tc      `hasKey` tYPETyConKey
  && ptr_rep `hasKey` ptrRepLiftedDataConKey
isStarKind _ = False
                              -- See Note [Kind Constraint and kind *]

-- | Is the tycon @Constraint@?
isStarKindSynonymTyCon :: TyCon -> Bool
isStarKindSynonymTyCon tc = tc `hasKey` constraintKindTyConKey


{- Note [Levity polymorphism]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Is this type legal?
   (a :: TYPE rep) -> Int
   where 'rep :: RuntimeRep'

You might think not, because no lambda can have a
runtime-rep-polymorphic binder.  So no lambda has the
above type.  BUT here's a way it can be useful (taken from
Trac #12708):

  data T rep (a :: TYPE rep)
     = MkT (a -> Int)

  x1 :: T LiftedPtrRep Int
  x1 =  MkT LiftedPtrRep Int  (\x::Int -> 3)

  x2 :: T IntRep Int#
  x2 = MkT IntRep Int# (\x:Int# -> 3)

Note that the lambdas are just fine!

Hence, okArrowArgKind and okArrowResultKind both just
check that the type is of the form (TYPE r) for some
representation type r.
-}
