-- (c) The University of Glasgow 2006

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}

module Unify ( 
        -- Matching of types: 
        --      the "tc" prefix indicates that matching always
        --      respects newtypes (rather than looking through them)
        MatchEnv(..),

        tcMatchTy, tcMatchTys, tcMatchTyX, 
        ruleMatchTyX,

        typesCantMatch,

        -- Side-effect free unification
        tcUnifyTy, tcUnifyTys, BindFlag(..),
        UnifyResult, UnifyResultM(..),

        -- Matching a type against a lifted type (coercion)
        liftCoMatch,

        tcUnifyTysFG
   ) where

#include "HsVersions.h"

import Var
import VarEnv
import VarSet
import Kind
import Type hiding ( getTvSubstEnv )
import Coercion
import TyCon
import TyCoRep hiding ( getTvSubstEnv, getCvSubstEnv )
import Util
import Pair
import Outputable
import FastString
import Unique

import Control.Monad
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative (Applicative(..), Alternative(..))
#else
import Control.Applicative (Alternative(..))
#endif

{-
************************************************************************
*                                                                      *
                Matching
*                                                                      *
************************************************************************


Matching is much tricker than you might think.

1. The substitution we generate binds the *template type variables*
   which are given to us explicitly.

2. We want to match in the presence of foralls; 
        e.g     (forall a. t1) ~ (forall b. t2)

   That is what the RnEnv2 is for; it does the alpha-renaming
   that makes it as if a and b were the same variable.
   Initialising the RnEnv2, so that it can generate a fresh
   binder when necessary, entails knowing the free variables of
   both types.

3. We must be careful not to bind a template type variable to a
   locally bound variable.  E.g.
        (forall a. x) ~ (forall b. b)
   where x is the template type variable.  Then we do not want to
   bind x to a/b!  This is a kind of occurs check.
   The necessary locals accumulate in the RnEnv2.
-}

-- avoid rewriting boilerplate by overloading:
class Unifiable t where
  match :: MatchEnv -> TvSubstEnv -> CvSubstEnv
        -> t -> t -> Maybe (TvSubstEnv, CvSubstEnv)
  unify :: t -> t -> UM ()
  tyCoVarsOf   :: t -> TyCoVarSet
  tyCoVarsOf_s :: [t] -> TyCoVarSet

instance Unifiable Type where
  match = match_ty
  unify = unify_ty
  tyCoVarsOf = tyCoVarsOfType
  tyCoVarsOf_s = tyCoVarsOfTypes

instance Unifiable Coercion where
  match = match_co
  unify = unify_co
  tyCoVarsOf = tyCoVarsOfCo
  tyCoVarsOf_s = tyCoVarsOfCos

instance Unifiable CoercionArg where
  match = match_co_arg
  unify = unify_co_arg
  tyCoVarsOf = tyCoVarsOfCoArg
  tyCoVarsOf_s = tyCoVarsOfCoArgs

data MatchEnv
  = ME  { me_tmpls :: VarSet    -- Template variables
        , me_env   :: RnEnv2    -- Renaming envt for nested foralls
        }                       --   In-scope set includes template variables
    -- Nota Bene: MatchEnv isn't specific to Types.  It is used
    --            for matching terms and coercions as well as types

tcMatch :: Unifiable t
        => TyCoVarSet     -- Template tyvars
        -> t              -- Template
        -> t              -- Target
        -> Maybe TCvSubst -- One-shot; in principle the template
                          -- variables could be free in the target

tcMatch tmpls ty1 ty2
  = case match menv emptyTvSubstEnv emptyCvSubstEnv ty1 ty2 of
        Just (tv_env, cv_env) -> Just (TCvSubst in_scope tv_env cv_env)
        Nothing               -> Nothing
  where
    menv     = ME { me_tmpls = tmpls, me_env = mkRnEnv2 in_scope }
    in_scope = mkInScopeSet (tmpls `unionVarSet` tyCoVarsOf ty2)
        -- We're assuming that all the interesting 
        -- tyvars in ty1 are in tmpls

-- | @tcMatchTy tys t1 t2@ produces a substitution (over a subset of
-- the variables @tys@) @s@ such that the erasure of @s(t1)@ equals
-- the erasure of @t2@. Note that @s(t1)@ might /not/ equal @t2@!
-- If you're concerned about this, check out 'Coercion.buildCoherenceCo'.
tcMatchTy :: TyCoVarSet -> Type -> Type -> Maybe TCvSubst
tcMatchTy = tcMatch

tcMatches :: Unifiable t
          => TyCoVarSet     -- Template tyvars
          -> [t]            -- Template
          -> [t]            -- Target
          -> Maybe TCvSubst -- One-shot; in principle the template
                            -- variables could be free in the target

tcMatches tmpls tys1 tys2
  = case match_list menv emptyTvSubstEnv emptyCvSubstEnv tys1 tys2 of
        Just (tv_env, cv_env) -> Just (TCvSubst in_scope tv_env cv_env)
        Nothing               -> Nothing
  where
    menv     = ME { me_tmpls = tmpls, me_env = mkRnEnv2 in_scope }
    in_scope = mkInScopeSet (tmpls `unionVarSet` tyCoVarsOf_s tys2)
        -- We're assuming that all the interesting 
        -- tyvars in tys1 are in tmpls

-- | Like 'tcMatchTy' but over a list of types.
tcMatchTys :: TyCoVarSet -> [Type] -> [Type] -> Maybe TCvSubst
tcMatchTys = tcMatches

-- This is similar, but extends a substitution
tcMatchX :: Unifiable t
         => TyCoVarSet          -- Template tyvars
         -> TCvSubst            -- Substitution to extend
         -> t                   -- Template
         -> t                   -- Target
         -> Maybe TCvSubst
tcMatchX tmpls (TCvSubst in_scope tv_env cv_env) ty1 ty2
  = case match menv tv_env cv_env ty1 ty2 of
        Just (tv_env, cv_env) -> Just (TCvSubst in_scope tv_env cv_env)
        Nothing               -> Nothing
  where
    menv = ME {me_tmpls = tmpls, me_env = mkRnEnv2 in_scope}

tcMatchTyX :: TyCoVarSet -> TCvSubst -> Type -> Type -> Maybe TCvSubst
tcMatchTyX = tcMatchX

tcMatchCoX :: TyCoVarSet -> TCvSubst -> Coercion -> Coercion -> Maybe TCvSubst
tcMatchCoX = tcMatchX

-- This one is called from the expression matcher, which already has a MatchEnv in hand
ruleMatchTyX :: MatchEnv 
         -> TvSubstEnv          -- type substitution to extend
         -> CvSubstEnv          -- coercion substitution to extend
         -> Type                -- Template
         -> Type                -- Target
         -> Maybe (TvSubstEnv, CvSubstEnv)
ruleMatchTyX env tenv cenv tmpl target
  | Just result <- match env tenv cenv tmpl target
  , let subst = mkOpenTCvSubst tenv cenv
  , substTy subst tmpl `eqType` target   -- we want exact matching here
  = Just result
     -- TODO (RAE): This should probably work with inexact matching too;
     -- otherwise, various rules won't fire when they should

  | otherwise
  = Nothing

-- Rename for export

-- Now the internals of matching

-- | Workhorse matching function.  Our goal is to find a substitution
-- on all of the template variables (specified by @me_tmpls menv@) such
-- that the erased versions of @ty1@ and @ty2@ match under the substituion.
-- This substitution is accumulated in @subst@.
-- If a variable is not a template variable, we don't attempt to find a
-- substitution for it; it must match exactly on both sides.  Furthermore,
-- only @ty1@ can have template variables.
--
-- This function handles binders, see 'RnEnv2' for more details on
-- how that works.
match_ty :: MatchEnv    -- For the most part this is pushed downwards
         -> TvSubstEnv     -- Substitution so far:
                           --   Domain is subset of template tyvars
                           --   Free vars of range is subset of 
                           --      in-scope set of the RnEnv2
         -> CvSubstEnv
         -> Type -> Type   -- Template and target respectively
         -> Maybe (TvSubstEnv, CvSubstEnv, Coercion)  -- co :: substed lhs ~ rhs
match_ty menv tsubst csubst ty1 ty2
  | Just ty1' <- coreView ty1 = match_ty menv tsubst csubst ty1' ty2
  | Just ty2' <- coreView ty2 = match_ty menv tsubst csubst ty1 ty2'

match_ty menv tsubst csubst (TyVarTy tv1) ty2
  | Just ty1' <- lookupVarEnv tsubst tv1'       -- tv1' is already bound
  = do { co <- buildCoherenceCoX (nukeRnEnvL rn_env) ty1' ty2
        -- ty1 has no locally-bound variables, hence nukeRnEnvL
       ; return (tsubst, csubst, co) }

  | tv1' `elemVarSet` me_tmpls menv -- RAE was here
  = if any (inRnEnvR rn_env) (varSetElems (tyCoVarsOfType ty2))
    then Nothing        -- Occurs check
                        -- ezyang: Is this really an occurs check?  It seems
                        -- to just reject matching \x. A against \x. x (maintaining
                        -- the invariant that the free vars of the range of @subst@
                        -- are a subset of the in-scope set in @me_env menv@.)
    else do { (tsubst1, csubst1, co_kind)
                <- match_kind menv tsubst csubst (tyVarKind tv1') (typeKind ty2)
            ; return (extendVarEnv tsubst1 tv1' (ty2 `mkCastTyOrRefl` , csubst1) }

   | otherwise  -- tv1 is not a template tyvar
   = case ty2 of
        TyVarTy tv2 | tv1' == rnOccR rn_env tv2 -> Just (tsubst, csubst)
        _                                       -> Nothing
  where
    rn_env = me_env menv
    tv1' = rnOccL rn_env tv1

match_ty menv tsubst csubst (ForAllTy (Named tv1 _) ty1) (ForAllTy (Named tv2 _) ty2) 
  = do { (tsubst', csubst') <- match_kind menv tsubst csubst (tyVarKind tv1) (tyVarKind tv2)
       ; match_ty menv' tsubst' csubst' ty1 ty2 }
  where         -- Use the magic of rnBndr2 to go under the binders
    menv' = menv { me_env = rnBndr2 (me_env menv) tv1 tv2 }

match_ty menv tsubst csubst (TyConApp tc1 tys1) (TyConApp tc2 tys2) 
  | tc1 == tc2 = match_list menv tsubst csubst tys1 tys2
match_ty menv tsubst csubst (ForAllTy (Anon ty1a) ty1b) (ForAllTy (Anon ty2a) ty2b) 
  = do { (tsubst', csubst') <- match_ty menv tsubst csubst ty1a ty2a
       ; match_ty menv tsubst' csubst' ty1b ty2b }
match_ty menv tsubst csubst (AppTy ty1a ty1b) ty2
  | Just (ty2a, ty2b) <- repSplitAppTy_maybe ty2
        -- 'repSplit' used because the tcView stuff is done above
  = do { (tsubst', csubst') <- match_ty menv tsubst csubst ty1a ty2a
       ; match_ty menv tsubst' csubst' ty1b ty2b }

match_ty _ tsubst csubst (LitTy x) (LitTy y) | x == y  = return (tsubst, csubst)

match_ty menv tsubst csubst (CastTy ty1 co1) (CastTy ty2 co2)
  = do { (tsubst', csubst') <- match_ty menv tsubst csubst ty1 ty2
       ; match_co menv tsubst' csubst' co1 co2 }

match_ty menv tsubst csubst (CoercionTy co1) (CoercionTy co2)
  = match_co menv tsubst csubst co1 co2

match_ty _ _ _ _ _
  = Nothing



--------------
match_kind :: MatchEnv -> TvSubstEnv -> CvSubstEnv -> Kind -> Kind -> Maybe (TvSubstEnv, CvSubstEnv)
-- Match the kind of the template tyvar with the kind of Type
match_kind menv tsubst csubst k1 k2
  | k2 `eqType` k1
  = return (tsubst, csubst)

  | otherwise
  = match menv tsubst csubst k1 k2

{-
Note [Unifying with Refl]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Because of Refl invariant #2 (see Note [Refl invariant]), any reflexive
coercion must be constructed with Refl. This means that any of the smart
constructors for Coercions check for reflexivity and produce Refl in that
case. Because the substitution operation uses these smart constructors, *any*
coercion might become Refl after substitution. So, when matching, we must
allow for this possibility. We do so by, when the target coercion is a Refl,
trying to match the kind of the coercion with the kind of the Refl. If these
match, then the substitution produced will indeed make the substituted
coercion become Refl, as desired.

But, what to do when a CoVarCo is matched with a Refl? There are two ways a
CoVarCo can become a Refl under substitution: the underlying CoVar can be
mapped to a Refl coercion; or the types of the CoVar can end up becoming the
same, triggering the Refl invariant. This matching algorithm therefore has a
choice. If a CoVarCo is matched with a Refl, do we make a mapping from the
CoVar, or do we just unify the kinds? This choice is apparent in the ordering
of the first two clauses of match_co below. It seems that taking the second
option -- just unifying the kinds -- means strictly less work, so that is the
route I have taken. This means that the final substitution will not contain a
mapping for the CoVar in question, but that should be OK.

Note [Coercion optimizations and match_co]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The algorithm in match_co must be kept carefully in sync with the
optimizations and simplifications done in the smart constructors of coercions.
We want this property: if Just subst = match co1 co2, then subst(co1) = co2.
And, we want this one: if Nothing = match co1 co2, then there exists no such
possible substitution. Because substitution uses the smart constructors,
we must account for the possibility that the structure of a coercion changes
during substitution. This isn't that hard to do, but we still must be careful
about it. For example, mkUnsafeCo sometimes produces a TyConAppCo, *not* an
UnsafeCo. So, we must allow for the possibility that an UnsafeCo will become
a TyConAppCo after substitution, and check for this case in matching.
-}

--------------
-- See Note [Coercion optimizations and match_co]
match_co :: MatchEnv -> TvSubstEnv -> CvSubstEnv
         -> Coercion -> Coercion -> Maybe (TvSubstEnv, CvSubstEnv)

 -- There are no "unification role varialbles", so if the roles don't match,
 -- fail eagerly.
match_co _ _ _ co1 co2
  | coercionRole co1 /= coercionRole co2
  = Nothing

-- From now on, assume that the roles match!

-- See Note [Unifying with Refl]
-- any coercion shape can become a refl under certain conditions:
match_co menv tsubst csubst co1 (Refl _ ty2)
  = do { let Pair tyl1 tyr1 = coercionKind co1
       ; (tsubst', csubst') <- match_ty menv tsubst csubst tyl1 ty2
       ; match_ty menv tsubst' csubst' tyr1 ty2 }

-- See Note [Unifying with Refl]
match_co menv tsubst csubst (CoVarCo cv1) co2
  | Just co1' <- lookupVarEnv csubst cv1'   -- cv1' is already bound
  = if eqCoercionX (nukeRnEnvL rn_env) co1' co2
          -- co1' has no locally-bound variables, hence nukeRnEnvL
    then Just (tsubst, csubst)
    else Nothing -- co2 doesn't match

  | cv1' `elemVarSet` me_tmpls menv
  = if any (inRnEnvR rn_env) (varSetElems (tyCoVarsOfCo co2))
    then Nothing -- occurs check
    else do { (tsubst1, csubst1) <- match_ty menv tsubst csubst (coVarKind cv1')
                                                                (coercionType co2)
            ; return (tsubst1, extendVarEnv csubst1 cv1' co2) }

  | otherwise -- cv1 is not a template covar
  = case co2 of
      CoVarCo cv2 | cv1' == rnOccR rn_env cv2 -> Just (tsubst, csubst)
      _                                       -> Nothing
  where
    rn_env = me_env menv
    cv1' = rnOccL rn_env cv1

-- Refl case already handled:
match_co menv tsubst csubst (TyConAppCo _ tc1 args1) (TyConAppCo _ tc2 args2)
  | tc1 == tc2 = match_list menv tsubst csubst args1 args2

match_co menv tsubst csubst (AppCo co1 arg1) co2
  | Just (co2, arg2) <- splitAppCo_maybe co2
  = do { (tsubst', csubst') <- match_co menv tsubst csubst co1 co2
       ; match_co_arg menv tsubst' csubst' arg1 arg2 }

match_co menv tsubst csubst (ForAllCo cobndr1 co1) (ForAllCo cobndr2 co2)
  | TyHomo tv1 <- cobndr1
  , TyHomo tv2 <- cobndr2
  = do { (tsubst', csubst') <- match_kind menv tsubst csubst (tyVarKind tv1)
                                                             (tyVarKind tv2)
       ; let menv' = menv { me_env = rnBndr2 (me_env menv) tv1 tv2 }
       ; match_co menv' tsubst' csubst' co1 co2 }
  
  | TyHetero eta1 tvl1 tvr1 cv1 <- cobndr1
  , TyHomo tv2 <- cobndr2
  = do { let eta_role = coercionRole eta1  -- TODO (RAE): This seems inefficient.
       ; (tsubst1, csubst1) <- match_co menv tsubst csubst 
                                        eta1 (mkReflCo eta_role (tyVarKind tv2))
       ; (tsubst2, csubst2) <- match_kind menv tsubst1 csubst1 (tyVarKind tvl1)
                                                               (tyVarKind tvr1)
       ; let rn_env = me_env menv
             in_scope = rnInScopeSet rn_env
             homogenized = substCoWithIS in_scope
                                         [tvr1,               cv1]
                                         [mkOnlyTyVarTy tvl1, mkCoercionTy $
                                                              mkReflCo Nominal (mkOnlyTyVarTy tvl1)]
                                         co1
             menv' = menv { me_env = rnBndr2 rn_env tvl1 tv2 }
       ; match_co menv' tsubst2 csubst2 homogenized co2 }

  | TyHetero eta1 tvl1 tvr1 cv1 <- cobndr1
  , TyHetero eta2 tvl2 tvr2 cv2 <- cobndr2
  = do { (tsubst1, csubst1) <- match_co menv tsubst csubst eta1 eta2
       ; (tsubst2, csubst2) <- match_kind menv tsubst1 csubst1 (tyVarKind tvl1)
                                                               (tyVarKind tvl2)
       ; (tsubst3, csubst3) <- match_kind menv tsubst2 csubst2 (tyVarKind tvr1)
                                                               (tyVarKind tvr2)
       ; let menv' = menv { me_env = rnBndrs2 (me_env menv) [tvl1, tvr1, cv1]
                                                            [tvl2, tvr2, cv2] }
       ; match_co menv' tsubst3 csubst3 co1 co2 }

  | CoHomo cv1 <- cobndr1
  , CoHomo cv2 <- cobndr2
  = do { (tsubst', csubst') <- match_ty menv tsubst csubst (coVarKind cv1)
                                                           (coVarKind cv2)
       ; let menv' = menv { me_env = rnBndr2 (me_env menv) cv1 cv2 }
       ; match_co menv' tsubst' csubst' co1 co2 }

  | CoHetero eta1 cvl1 cvr1 <- cobndr1
  , CoHomo cv2 <- cobndr2
  = do { let role = coercionRole eta1  -- TODO (RAE): This seems inefficient.
       ; (tsubst1, csubst1) <- match_co menv tsubst csubst
                                        eta1 (mkReflCo role (coVarKind cv2))
       ; (tsubst2, csubst2) <- match_ty menv tsubst1 csubst1 (coVarKind cvl1)
                                                             (coVarKind cvr1)
       ; let rn_env = me_env menv
             in_scope = rnInScopeSet rn_env
             homogenized = substCoWithIS in_scope
                                         [cvr1] [mkCoercionTy $ mkCoVarCo cvl1] co1
             menv' = menv { me_env = rnBndr2 rn_env cvl1 cv2 }
       ; match_co menv' tsubst2 csubst2 homogenized co2 }

  | CoHetero eta1 cvl1 cvr1 <- cobndr1
  , CoHetero eta2 cvl2 cvr2 <- cobndr2
  = do { (tsubst1, csubst1) <- match_co menv tsubst csubst eta1 eta2
       ; (tsubst2, csubst2) <- match_ty menv tsubst1 csubst1 (coVarKind cvl1)
                                                             (coVarKind cvl2)
       ; (tsubst3, csubst3) <- match_ty menv tsubst2 csubst2 (coVarKind cvr1)
                                                             (coVarKind cvr2)
       ; let menv' = menv { me_env = rnBndrs2 (me_env menv) [cvl1, cvr1]
                                                            [cvl2, cvr2] }
       ; match_co menv' tsubst3 csubst3 co1 co2 }

  -- TyHomo can't match with TyHetero, and same for Co

match_co menv tsubst csubst (AxiomInstCo ax1 ind1 args1)
                            (AxiomInstCo ax2 ind2 args2)
  | ax1 == ax2
  , ind1 == ind2
  = match_list menv tsubst csubst args1 args2

match_co menv tsubst csubst (PhantomCo h1 tyl1 tyr1) (PhantomCo h2 tyl2 tyr2)
  = do { (tsubst1, csubst1) <- match_co menv tsubst  csubst  h1   h2
       ; (tsubst2, csubst2) <- match_ty menv tsubst1 csubst1 tyl1 tyl2
       ; match_ty menv tsubst2 csubst2 tyr1 tyr2 }

match_co menv tsubst csubst (UnsafeCo _ _ tyl1 tyr1) (UnsafeCo _ _ tyl2 tyr2)
  = do { (tsubst', csubst') <- match_ty menv tsubst csubst tyl1 tyl2
       ; match_ty menv tsubst' csubst' tyr1 tyr2 }
match_co menv tsubst csubst (UnsafeCo _ _ lty1 rty1) co2@(TyConAppCo _ _ _)
  = do { let Pair lty2 rty2 = coercionKind co2
       ; (tsubst', csubst') <- match_ty menv tsubst csubst lty1 lty2
       ; match_ty menv tsubst' csubst' rty1 rty2 }

-- it's safe to do these in order because there is never a SymCo (SymCo ...)
-- or a SymCo (UnsafeCo ...)
match_co menv tsubst csubst (SymCo co1) (SymCo co2)
  = match_co menv tsubst csubst co1 co2
match_co menv tsubst csubst (SymCo co1) (UnsafeCo s r lty2 rty2)
  = match_co menv tsubst csubst co1 (UnsafeCo s r rty2 lty2)
match_co menv tsubst csubst (SymCo co1) co2
  = match_co menv tsubst csubst co1 (SymCo co2)

match_co menv tsubst csubst (TransCo col1 cor1) (TransCo col2 cor2)
  = do { (tsubst', csubst') <- match_co menv tsubst csubst col1 col2
       ; match_co menv tsubst' csubst' cor1 cor2 }

match_co menv tsubst csubst (NthCo n1 co1) (NthCo n2 co2)
  | n1 == n2
  = match_co menv tsubst csubst co1 co2

match_co menv tsubst csubst (LRCo lr1 co1) (LRCo lr2 co2)
  | lr1 == lr2
  = match_co menv tsubst csubst co1 co2

match_co menv tsubst csubst (InstCo co1 arg1) (InstCo co2 arg2)
  = do { (tsubst', csubst') <- match_co menv tsubst csubst co1 co2
       ; match_co_arg menv tsubst' csubst' arg1 arg2 }

match_co menv tsubst csubst (CoherenceCo lco1 rco1) (CoherenceCo lco2 rco2)
  = do { (tsubst', csubst') <- match_co menv tsubst csubst lco1 lco2
       ; match_co menv tsubst' csubst' rco1 rco2 }

match_co menv tsubst csubst (KindCo co1) (KindCo co2)
  = match_co menv tsubst csubst co1 co2

match_co menv tsubst csubst (SubCo co1) (SubCo co2)
  = match_co menv tsubst csubst co1 co2
match_co menv tsubst csubst (SubCo co1) co2@(TyConAppCo _ _ _)
  = match_co menv tsubst csubst co1 co2
match_co menv tsubst csubst (SubCo co1) (UnsafeCo s Representational ty1 ty2)
  = match_co menv tsubst csubst co1 (UnsafeCo s Nominal ty1 ty2)

match_co menv tsubst csubst (AxiomRuleCo ax1 ts1 cs1) (AxiomRuleCo ax2 ts2 cs2)
  | ax1 == ax2
  = do { (tsubst', csubst') <- match_list menv tsubst csubst ts1 ts2
       ; match_list menv tsubst' csubst' cs1 cs2 }

match_co _ _ _ _ _
  = Nothing


match_co_arg :: MatchEnv -> TvSubstEnv -> CvSubstEnv
             -> CoercionArg -> CoercionArg -> Maybe (TvSubstEnv, CvSubstEnv)
match_co_arg menv tsubst csubst (TyCoArg co1) (TyCoArg co2)
  = match_co menv tsubst csubst co1 co2
match_co_arg menv tsubst csubst (CoCoArg r1 lco1 rco1) (CoCoArg r2 lco2 rco2)
  | r1 == r2
  = do { (tsubst', csubst') <- match_co menv tsubst csubst lco1 lco2
       ; match_co menv tsubst' csubst' rco1 rco2 }
match_co_arg _ _ _ _ _ = Nothing

-------------

match_list :: Unifiable t => MatchEnv -> TvSubstEnv -> CvSubstEnv -> [t] -> [t]
           -> Maybe (TvSubstEnv, CvSubstEnv)
match_list _    tenv cenv []     []     = Just (tenv, cenv)
match_list menv tenv cenv (a:as) (b:bs) = do { (tenv', cenv') <- match menv tenv cenv a b
                                             ; match_list menv tenv' cenv' as bs }
match_list _    _    _    _      _      = Nothing

{-
%************************************************************************
%*                                                                      *
        Matching monad
%*                                                                      *
%************************************************************************
-}

newtype MatchM a = MM { unMM :: MatchEnv -> TvSubstEnv -> CvSubstEnv
                             -> Maybe ((TvSubstEnv, CvSubstEnv), a) }

instance Functor MatchM where
      fmap = liftM

instance Applicative MatchM where
      pure = return
      (<*>) = ap

instance Monad MatchM where
  return x = MM $ \_ tsubst csubst -> Just ((tsubst, csubst), x)
  fail _   = MM $ \_ _ _ -> Nothing

  a >>= f = MM $ \menv tsubst csubst -> case unMM a menv tsubst csubst of
    Just ((tsubst', csubst'), a') -> unMM (f a') menv tsubst' csubst'
    Nothing                       -> Nothing

_runMatchM :: MatchM a -> MatchEnv -> TvSubstEnv -> CvSubstEnv
          -> Maybe (TvSubstEnv, CvSubstEnv)
_runMatchM mm menv tsubst csubst
  -- in the Maybe monad
  = do { ((tsubst', csubst'), _) <- unMM mm menv tsubst csubst
       ; return (tsubst', csubst') }

_getRnEnv :: MatchM RnEnv2
_getRnEnv = MM $ \menv tsubst csubst -> Just ((tsubst, csubst), me_env menv)

_withRnEnv :: RnEnv2 -> MatchM a -> MatchM a
_withRnEnv rn_env mm = MM $ \menv tsubst csubst
                           -> unMM mm (menv { me_env = rn_env }) tsubst csubst

{-
************************************************************************
*                                                                      *
                GADTs
*                                                                      *
************************************************************************

Note [Pruning dead case alternatives]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider        data T a where
                   T1 :: T Int
                   T2 :: T a

                newtype X = MkX Int
                newtype Y = MkY Char

                type family F a
                type instance F Bool = Int

Now consider    case x of { T1 -> e1; T2 -> e2 }

The question before the house is this: if I know something about the type
of x, can I prune away the T1 alternative?

Suppose x::T Char.  It's impossible to construct a (T Char) using T1, 
        Answer = YES we can prune the T1 branch (clearly)

Suppose x::T (F a), where 'a' is in scope.  Then 'a' might be instantiated
to 'Bool', in which case x::T Int, so
        ANSWER = NO (clearly)

Suppose x::T X.  Then *in Haskell* it's impossible to construct a (non-bottom) 
value of type (T X) using T1.  But *in FC* it's quite possible.  The newtype
gives a coercion
        CoX :: X ~ Int
So (T CoX) :: T X ~ T Int; hence (T1 `cast` sym (T CoX)) is a non-bottom value
of type (T X) constructed with T1.  Hence
        ANSWER = NO we can't prune the T1 branch (surprisingly)

Furthermore, this can even happen; see Trac #1251.  GHC's newtype-deriving
mechanism uses a cast, just as above, to move from one dictionary to another,
in effect giving the programmer access to CoX.

Finally, suppose x::T Y.  Then *even in FC* we can't construct a
non-bottom value of type (T Y) using T1.  That's because we can get
from Y to Char, but not to Int.


Here's a related question.      data Eq a b where EQ :: Eq a a
Consider
        case x of { EQ -> ... }

Suppose x::Eq Int Char.  Is the alternative dead?  Clearly yes.

What about x::Eq Int a, in a context where we have evidence that a~Char.
Then again the alternative is dead.   


                        Summary

We are really doing a test for unsatisfiability of the type
constraints implied by the match. And that is clearly, in general, a
hard thing to do.  

However, since we are simply dropping dead code, a conservative test
suffices.  There is a continuum of tests, ranging from easy to hard, that
drop more and more dead code.

For now we implement a very simple test: type variables match
anything, type functions (incl newtypes) match anything, and only
distinct data types fail to match.  We can elaborate later.
-}

typesCantMatch :: [(Type,Type)] -> Bool
typesCantMatch prs = any (\(s,t) -> cant_match s t) prs
  where
    cant_match :: Type -> Type -> Bool
    cant_match t1 t2
        | Just t1' <- coreView t1 = cant_match t1' t2
        | Just t2' <- coreView t2 = cant_match t1 t2'

    cant_match (ForAllTy (Anon a1) r1) (ForAllTy (Anon a2) r2)
        = cant_match a1 a2 || cant_match r1 r2

    cant_match (TyConApp tc1 tys1) (TyConApp tc2 tys2)
        | isDistinctTyCon tc1 && isDistinctTyCon tc2
        = tc1 /= tc2 || typesCantMatch (zipEqual "typesCantMatch" tys1 tys2)

    cant_match (ForAllTy (Anon _) _) (TyConApp tc _) = isDistinctTyCon tc
    cant_match (TyConApp tc _) (ForAllTy (Anon _) _) = isDistinctTyCon tc
        -- tc can't be FunTyCon by invariant

    cant_match (AppTy f1 a1) ty2
        | Just (f2, a2) <- repSplitAppTy_maybe ty2
        = cant_match f1 f2 || cant_match a1 a2
    cant_match ty1 (AppTy f2 a2)
        | Just (f1, a1) <- repSplitAppTy_maybe ty1
        = cant_match f1 f2 || cant_match a1 a2

    cant_match (LitTy x) (LitTy y) = x /= y

    cant_match _ _ = False      -- Safe!

-- Things we could add;
--      foralls
--      look through newtypes
--      take account of tyvar bindings (EQ example above)

{-
************************************************************************
*                                                                      *
             Unification
*                                                                      *
************************************************************************

Note [Fine-grained unification]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Do the types (x, x) and ([y], y) unify? The answer is seemingly "no" --
no substitution to finite types makes these match. But, a substitution to
*infinite* types can unify these two types: [x |-> [[[...]]], y |-> [[[...]]] ].
Why do we care? Consider these two type family instances:

type instance F x x   = Int
type instance F [y] y = Bool

If we also have

type instance Looper = [Looper]

then the instances potentially overlap. The solution is to use unification
over infinite terms. This is possible (see [1] for lots of gory details), but
a full algorithm is a little more power than we need. Instead, we make a
conservative approximation and just omit the occurs check.

[1]: http://research.microsoft.com/en-us/um/people/simonpj/papers/ext-f/axioms-extended.pdf

tcUnifyTys considers an occurs-check problem as the same as general unification
failure.

tcUnifyTysFG ("fine-grained") returns one of three results: success, occurs-check
failure ("MaybeApart"), or general failure ("SurelyApart").

See also Trac #8162.

It's worth noting that unification in the presence of infinite types is not
complete. This means that, sometimes, a closed type family does not reduce
when it should. See test case indexed-types/should_fail/Overlap15 for an
example.

Note [The substitution in MaybeApart]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The constructor MaybeApart carries data with it, typically a TvSubstEnv. Why?
Because consider unifying these:

(a, a, Int) ~ (b, [b], Bool)

If we go left-to-right, we start with [a |-> b]. Then, on the middle terms, we
apply the subst we have so far and discover that we need [b |-> [b]]. Because
this fails the occurs check, we say that the types are MaybeApart (see above
Note [Fine-grained unification]). But, we can't stop there! Because if we
continue, we discover that Int is SurelyApart from Bool, and therefore the
types are apart. This has practical consequences for the ability for closed
type family applications to reduce. See test case
indexed-types/should_compile/Overlap14.

Note [Unifying with skolems]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we discover that two types unify if and only if a skolem variable is
substituted, we can't properly unify the types. But, that skolem variable
may later be instantiated with a unifyable type. So, we return maybeApart
in these cases.

Note [Apartness and coercions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
What does it mean for two coercions to be apart? It has to mean that the
types coerced between are apart. In cannot mean that there is no unification
from one coercion to another. The problem is that, in general, there are
many shapes a coercion might take. Any two coercions that coerce between
the same two types are fully equivalent. Even with wildly different
structures, it would be folly to say that they are "apart". So, a failure
to unify two coercions can yield surelyApart if and only if the types
coerced between are surelyApart. Otherwise, two coercions either unify or
are maybeApart.

Note [Lists of different lengths are MaybeApart]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It is unusual to call tcUnifyTys or tcUnifyTysFG with lists of different
lengths. The place where we know this can happen is from compatibleBranches in
FamInstEnv, when checking data family instances. Data family instances may be
eta-reduced; see Note [Eta reduction for data family axioms] in TcInstDcls.

We wish to say that

  D :: * -> * -> *
  axDF1 :: D Int ~ DFInst1
  axDF2 :: D Int Bool ~ DFInst2

overlap. If we conclude that lists of different lengths are SurelyApart, then
it will look like these do *not* overlap, causing disaster. See Trac #9371.

In usages of tcUnifyTys outside of family instances, we always use tcUnifyTys,
which can't tell the difference between MaybeApart and SurelyApart, so those
usages won't notice this design choice.
-}

tcUnifyTy :: Type -> Type       -- All tyvars are bindable
          -> Maybe TCvSubst     -- A regular one-shot (idempotent) substitution
-- Simple unification of two types; all type variables are bindable
tcUnifyTy t1 t2 = tcUnifyTys (const BindMe) [t1] [t2]

-----------------
tcUnifyTys :: (TyCoVar -> BindFlag)
           -> [Type] -> [Type]
           -> Maybe TCvSubst    -- ^ A regular one-shot (idempotent) substitution
                                -- that unifies the erased types. See comments
                                -- for 'tcUnifyTysFG'
              
-- The two types may have common type variables, and indeed do so in the
-- second call to tcUnifyTys in FunDeps.checkClsFD
tcUnifyTys bind_fn tys1 tys2
  = case tcUnifyTysFG bind_fn tys1 tys2 of
      Unifiable subst -> Just subst
      _               -> Nothing

-- This type does double-duty. It is used in the UM (unifier monad) and to
-- return the final result. See Note [Fine-grained unification]
type UnifyResult = UnifyResultM TCvSubst
data UnifyResultM a = Unifiable a        -- the subst that unifies the types
                    | MaybeApart a       -- the subst has as much as we know
                                         -- it must be part of an most general unifier
                                         -- See Note [The substitution in MaybeApart]
                    | SurelyApart

-- | @tcUnifyTysFG bind_tv tys1 tys2@ attepts to find a substitution @s@ (whose
-- domain elements all respond 'BindMe' to @bind_tv@) such that the erasure of
-- @s(tys1)@ and that of @s(tys2)@ are equal. If we want the types themselves
-- to be equal, see 'Coercion.buildCoherenceCo' for a way forward.
-- See also Note [Fine-grained unification].
tcUnifyTysFG :: (TyCoVar -> BindFlag)
             -> [Type] -> [Type]
             -> UnifyResult
tcUnifyTysFG bind_fn tys1 tys2
  = initUM bind_fn vars $
    do { unifyList tys1 tys2
       ; tsubst <- getTvSubstEnv
       ; csubst <- getCvSubstEnv

       ; return (niFixTCvSubst tsubst csubst) }
  where
    vars = tyCoVarsOfTypes tys1 `unionVarSet` tyCoVarsOfTypes tys2

{-
************************************************************************
*                                                                      *
                Non-idempotent substitution
*                                                                      *
************************************************************************

Note [Non-idempotent substitution]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
During unification we use a TvSubstEnv/CvSubstEnv pair that is
  (a) non-idempotent
  (b) loop-free; ie repeatedly applying it yields a fixed point

Note [Finding the substitution fixpoint]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Finding the fixpoint of a non-idempotent substitution arising from a
unification is harder than it looks, because of kinds.  Consider
   T k (H k (f:k)) ~ T * (g:*)
If we unify, we get the substitution
   [ k -> *
   , g -> H k (f:k) ]
To make it idempotent we don't want to get just
   [ k -> *
   , g -> H * (f:k) ]
We also want to substitute inside f's kind, to get
   [ k -> *
   , g -> H k (f:*) ]
If we don't do this, we may apply the substitition to something,
and get an ill-formed type, i.e. one where typeKind will fail.
This happened, for example, in Trac #9106.

This is the reason for extending env with [f:k -> f:*], in the
definition of env' in niFixTvSubst
-}

niFixTCvSubst :: TvSubstEnv -> CvSubstEnv -> TCvSubst
-- Find the idempotent fixed point of the non-idempotent substitution
-- See Note [Finding the substitution fixpoint]
-- ToDo: use laziness instead of iteration?
niFixTCvSubst tenv cenv = f tenv cenv
  where
    f tenv cenv
        | not_fixpoint = f (mapVarEnv (substTy subst') tenv)
                           (mapVarEnv (substCo subst') cenv)
        | otherwise    = subst
        where
          not_fixpoint  = foldVarSet ((||) . in_domain) False all_range_tvs
          in_domain tv  = tv `elemVarEnv` tenv || tv `elemVarEnv` cenv

          range_tvs     = foldVarEnv (unionVarSet . tyCoVarsOfType) emptyVarSet tenv
          range_cvs     = foldVarEnv (unionVarSet . tyCoVarsOfCo) emptyVarSet cenv
          all_range_tvs = range_tvs `unionVarSet` range_cvs
          subst         = mkTCvSubst (mkInScopeSet all_range_tvs) (tenv, cenv)

             -- env' extends env by replacing any free type with 
             -- that same tyvar with a substituted kind
             -- See note [Finding the substitution fixpoint]
          tenv'         = extendVarEnvList tenv [ (rtv, mkOnlyTyVarTy $ setTyVarKind rtv $
                                                        substTy subst $ tyVarKind rtv)
                                                | rtv <- varSetElems range_tvs
                                                , not (in_domain rtv) ]
          subst'        = mkTCvSubst (mkInScopeSet all_range_tvs) (tenv', cenv)

niSubstTvSet :: TvSubstEnv -> CvSubstEnv -> TyCoVarSet -> TyCoVarSet
-- Apply the non-idempotent substitution to a set of type variables,
-- remembering that the substitution isn't necessarily idempotent
-- This is used in the occurs check, before extending the substitution
niSubstTvSet tsubst csubst tvs
  = foldVarSet (unionVarSet . get) emptyVarSet tvs
  where
    get tv
      | isTyVar tv
      = case lookupVarEnv tsubst tv of
               Nothing -> unitVarSet tv
               Just ty -> niSubstTvSet tsubst csubst (tyCoVarsOfType ty)
      | otherwise
      = case lookupVarEnv csubst tv of
               Nothing -> unitVarSet tv
               Just co -> niSubstTvSet tsubst csubst (tyCoVarsOfCo co)

{-
************************************************************************
*                                                                      *
                The workhorse
*                                                                      *
************************************************************************

Note [unify_co SymCo case]
~~~~~~~~~~~~~~~~~~~~~~~~~~
mkSymCo says that mkSymCo (SymCo co) = co. So, it is, in general, possible
for a SymCo to unify with any other coercion. For example, if we have
(SymCo c) (for a coercion variable c), that unifies with any coercion co
with [c |-> SymCo co]. Now, consider a unification problem: we wish to unify
(SymCo co1) with co2. If co2 is not a SymCo or an UnsafeCo (the two other
possible outcomes of mkSymCo) then we should try to unify co1 with (SymCo co2).
The problem is that, if that also fails, a naive algorithm would then try
pushing the SymCo back onto co1. What we need is to make sure we swap the SymCo
only once, prevent infinite recursion. This is done in unify_co_sym with the
SymFlag parameter.

Note [Unifying casted types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We must be careful when unifying casted types. Say (t :: *). On the one hand,
we must consider (t) and (t |> <*>) to be distinct types inhabited by distinct
sets of terms. These types are *not* equal. See Note [Optimising Refl] in
OptCoercion. But, it is wrong to say these types are "apart", by the definition
of apartness: two types are apart only when they are not coercible, even after
arbitrary substitutions. After all, the coercion (sym (<t> |> <*>)) witnesses
the equality of these two types.

So, what do we do? If we're unifying (t1 |> g1) and (t2 |> g2):

1. We first go ahead and try straightforward unification. If that works (i.e., there is a
unifying substitution), hooray. Stop.

2. Now, we try just to unify t1 and t2. If that succeeds, then we've shown
that (t1 |> g1) and (t2 |> g2) are not apart, because we can build a coercion
between a type that appears after applying a substitution to these types.
However, we can't just return Unifiable, because they're not unifiable! So, we
conclude MaybeApart, which is a safe fallback.

This logic is remarkably easy to implement. We simply do this:
  do { unify_ty t1 t2
     ; unify_co g1 g2 }
If they both succeed: perfect. If unify_ty fails, the whole thing fails for the same
reason: perfect. If unify_ty succeeds but unify_co fails, the whole thing fails with
MaybeApart, by the definition of unify_co: perfect. So, easy implementation, somewhat
involved reasoning behind it. For example, reversing the order of the statements would
*not* be correct!

Now, what do we do when unifying (t1 |> g1) and t2, where t2 is not headed by a
cast operation? Clearly, these types do not unify, but they might or might not be
apart. So, we try to unify t1 and t2. If this fails, we fail for the same reason.
If this succeeds, we fail with MaybeApart. Once again, the types aren't apart, but
we can't say NotApart when the types don't unify.
-}

-- TODO (RAE): Currently, requires an exact match. Relax to respect erasure.
unify_ty :: Type -> Type   -- Types to be unified
         -> UM ()
-- We do not require the incoming substitution to be idempotent,
-- nor guarantee that the outgoing one is.  That's fixed up by
-- the wrappers.

-- Respects newtypes, PredTypes

-- in unify, any NewTcApps/Preds should be taken at face value
unify_ty (TyVarTy tv1) ty2  = uVar tv1 ty2
unify_ty ty1 (TyVarTy tv2)  = umSwapRn $ uVar tv2 ty1

unify_ty ty1 ty2
  | Just ty1' <- tcView ty1 = unify_ty ty1' ty2
  | Just ty2' <- tcView ty2 = unify_ty ty1 ty2'

-- See Note [Unifying casted types]
unify_ty (CastTy ty1 co1) (CastTy ty2 co2)
  = do { unify_ty ty1 ty2
       ; unify_co co1 co2 }
unify_ty (CastTy ty1 _co1) ty2
  = dontUnify $ unify_ty ty1 ty2
unify_ty ty1 (CastTy ty2 _co2)
  = dontUnify $ unify_ty ty1 ty2

unify_ty (TyConApp tyc1 tys1) (TyConApp tyc2 tys2)
  | tyc1 == tyc2                                   
  = unify_tys tys1 tys2

unify_ty (ForAllTy (Anon ty1a) ty1b) (ForAllTy (Anon ty2a) ty2b) 
  = do  { unify_ty ty1a ty2a
        ; unify_ty ty1b ty2b }

        -- Applications need a bit of care!
        -- They can match FunTy and TyConApp, so use splitAppTy_maybe
        -- NB: we've already dealt with type variables and Notes,
        -- so if one type is an App the other one jolly well better be too
unify_ty (AppTy ty1a ty1b) ty2
  | Just (ty2a, ty2b) <- repSplitAppTy_maybe ty2
  = do  { unify_ty ty1a ty2a
        ; unify_ty ty1b ty2b }

unify_ty ty1 (AppTy ty2a ty2b)
  | Just (ty1a, ty1b) <- repSplitAppTy_maybe ty1
  = do  { unify_ty ty1a ty2a
        ; unify_ty ty1b ty2b }

unify_ty (LitTy x) (LitTy y) | x == y = return ()

unify_ty (ForAllTy (Named tv1 _) ty1) (ForAllTy (Named tv2 _) ty2)
  = do { unify_ty (tyVarKind tv1) (tyVarKind tv2)
       ; umRnBndr2 tv1 tv2 $ unify_ty ty1 ty2 }

unify_ty (CoercionTy co1) (CoercionTy co2)
  = unify_co co1 co2

unify_ty _ _ = surelyApart

unify_tys :: [Type] -> [Type] -> UM ()
unify_tys = unifyList

-----------------------------------------
unify_co :: Coercion -> Coercion -> UM ()
-- See Note [Coercion optimizations and match_co]. It applies here too.
-- See Note [Apartness and coercions]
unify_co co1 co2
  = do { let role1 = coercionRole co1
             role2 = coercionRole co2
             Pair tyl1 tyr1 = coercionKind co1
             Pair tyl2 tyr2 = coercionKind co2
       ; guard (role1 == role2)
       ; unify_ty tyl1 tyl2
       ; unify_ty tyr1 tyr2
       ; dontBeSoSure $ unify_co' co1 co2 }

-- Unify two Coercions with unified kinds
unify_co' :: Coercion -> Coercion -> UM ()

-- in the Refl case, the kinds are already unified, so there is no more work.
-- See Note [Unifying with Refl]
unify_co' (Refl _ _) _ = return ()
unify_co' _ (Refl _ _) = return ()

unify_co' (CoVarCo cv1) co2 = uVar cv1 co2
unify_co' co1 (CoVarCo cv2) = umSwapRn $ uVar cv2 co1

unify_co' (TyConAppCo _ tc1 args1) (TyConAppCo _ tc2 args2)
 | tc1 == tc2 = unifyList args1 args2

unify_co' g1@(ForAllCo cobndr1 co1) g2@(ForAllCo cobndr2 co2)
 | Just v1 <- getHomoVar_maybe cobndr1
 , Just v2 <- getHomoVar_maybe cobndr2
 = do { unify_ty (varType v1) (varType v2)
      ; umRnBndr2 v1 v2 $ unify_co co1 co2 }

 | Just (eta1, lv1, rv1) <- splitHeteroCoBndr_maybe cobndr1
 , Just (eta2, lv2, rv2) <- splitHeteroCoBndr_maybe cobndr2
 = do { unify_co eta1 eta2
      ; unify_ty (varType lv1) (varType lv2)
      ; unify_ty (varType rv1) (varType rv2)
      ; let rnCoVar :: UM () -> UM ()
            rnCoVar
              = case cobndr1 of
                { TyHetero _ _ _ cv1 -> case cobndr2 of
                  { TyHetero _ _ _ cv2 -> umRnBndr2 cv1 cv2
                  ; _                  -> \_ -> maybeApart } -- one is Ty, one is Co
                ; _                  -> id }
      ; umRnBndr2 lv1 lv2 $
        umRnBndr2 rv1 rv2 $
        rnCoVar $
        unify_co co1 co2 }

  -- mixed Homo/Hetero case. Ugh. Only handle where 1 is hetero and 2 is homo;
  -- otherwise, flip 1 and 2
  | Just _ <- getHomoVar_maybe cobndr1
  , Just _ <- splitHeteroCoBndr_maybe cobndr2
  = umSwapRn $ unify_co' g2 g1

  | Just (eta1, lv1, rv1) <- splitHeteroCoBndr_maybe cobndr1
  , Just v2               <- getHomoVar_maybe cobndr2
  = do { let eta_role = coercionRole eta1
       ; unify_co eta1 (mkReflCo eta_role (varType v2))
       ; unify_ty (varType lv1) (varType rv1)
       ; homogenize $ \co1' ->
         umRnBndr2 lv1 v2 $
         unify_co co1' co2 }
  where
    homogenize :: (Coercion -> UM a) -> UM a
    homogenize thing
      = do { in_scope <- getInScope
           ; let co1' = case cobndr1 of
                        { TyHetero _ ltv1 rtv1 cv1
                            -> let lty = mkOnlyTyVarTy ltv1 in
                               substCoWithIS in_scope [rtv1, cv1]
                                                      [lty,  mkCoercionTy $ mkReflCo Nominal lty] co1
                        ; CoHetero _ lcv1 rcv1
                            -> let lco = mkCoVarCo lcv1 in
                               substCoWithIS in_scope [rcv1] [mkCoercionTy lco] co1
                        ; _ -> pprPanic "unify_co'#homogenize" (ppr g1) }
           ; thing co1' }

unify_co' (AxiomInstCo ax1 ind1 args1) (AxiomInstCo ax2 ind2 args2)
  | ax1 == ax2
  , ind1 == ind2
  = unifyList args1 args2

unify_co' (PhantomCo h1 tyl1 tyr1) (PhantomCo h2 tyl2 tyr2)
  = do { unify_co h1   h2
       ; unify_ty tyl1 tyl2
       ; unify_ty tyr1 tyr2 }

unify_co' (UnsafeCo _ _ tyl1 tyr1) (UnsafeCo _ _ tyl2 tyr2)
  = do { unify_ty tyl1 tyl2
       ; unify_ty tyr1 tyr2 }
unify_co' (UnsafeCo _ _ lty1 rty1) co2@(TyConAppCo _ _ _)
  = do { let Pair lty2 rty2 = coercionKind co2
       ; unify_ty lty1 lty2
       ; unify_ty rty1 rty2 }
unify_co' co1@(TyConAppCo _ _ _) (UnsafeCo _ _ lty2 rty2)
  = do { let Pair lty1 rty1 = coercionKind co1
       ; unify_ty lty1 lty2
       ; unify_ty rty1 rty2 }

-- see Note [unify_co SymCo case]
unify_co' co1@(SymCo _) co2
  = unify_co_sym TrySwitchingSym co1 co2
unify_co' co1 co2@(SymCo _)
  = unify_co_sym TrySwitchingSym co1 co2

unify_co' (TransCo col1 cor1) (TransCo col2 cor2)
  = do { unify_co col1 col2
       ; unify_co cor1 cor2 }

unify_co' (NthCo n1 co1) (NthCo n2 co2)
  | n1 == n2
  = unify_co' co1 co2

unify_co' (LRCo lr1 co1) (LRCo lr2 co2)
  | lr1 == lr2
  = unify_co' co1 co2

unify_co' (InstCo co1 arg1) (InstCo co2 arg2)
  = do { unify_co co1 co2
       ; unify_co_arg arg1 arg2 }

unify_co' (CoherenceCo lco1 rco1) (CoherenceCo lco2 rco2)
  = do { unify_co lco1 lco2
       ; unify_co rco1 rco2 }

unify_co' (KindCo co1) (KindCo co2)
  = unify_co' co1 co2

unify_co' _ _ = maybeApart

-- See Note [unify_co SymCo case]
data SymFlag = TrySwitchingSym
             | DontTrySwitchingSym

unify_co_sym :: SymFlag -> Coercion -> Coercion -> UM ()
unify_co_sym _ (SymCo co1) (SymCo co2)
  = unify_co' co1 co2
unify_co_sym _ (SymCo co1) (UnsafeCo s r lty2 rty2)
  = unify_co' co1 (UnsafeCo s r rty2 lty2)
unify_co_sym _ (UnsafeCo s r lty1 rty1) (SymCo co2)
  = unify_co' (UnsafeCo s r rty1 lty1) co2

-- note that neither co1 nor co2 can be Refl, so we don't have to worry
-- about missing that catchall case in unify_co'
unify_co_sym TrySwitchingSym (SymCo co1) co2
  = unify_co_sym DontTrySwitchingSym co1 (SymCo co2)
unify_co_sym TrySwitchingSym co1 (SymCo co2)
  = unify_co_sym DontTrySwitchingSym (SymCo co1) co2
unify_co_sym _ _ _ = maybeApart

unify_co_arg :: CoercionArg -> CoercionArg -> UM ()
unify_co_arg (TyCoArg co1) (TyCoArg co2) = unify_co co1 co2
unify_co_arg (CoCoArg r1 lco1 rco1) (CoCoArg r2 lco2 rco2)
  | r1 == r2
  = do { unify_co lco1 lco2
       ; unify_co rco1 rco2 }
unify_co_arg _ _ = surelyApart

unifyList :: Unifiable tyco => [tyco] -> [tyco] -> UM ()
unifyList orig_xs orig_ys
  = go orig_xs orig_ys
  where
    go []     []     = return ()
    go (x:xs) (y:ys) = do { unify x y
                          ; go xs ys }
    go _ _ = maybeApart  -- See Note [Lists of different lengths are MaybeApart]

---------------------------------
uVar :: TyOrCo tyco
     => TyCoVar           -- Variable to be unified
     -> tyco              -- with this tyco
     -> UM ()

uVar tv1 ty
 = do { -- Check to see whether tv1 is refined by the substitution
        subst <- getSubstEnv
      ; case (lookupVarEnv subst tv1) of
          Just ty' -> unify ty' ty        -- Yes, call back into unify
          Nothing  -> uUnrefined tv1 ty ty } -- No, continue

uUnrefined :: forall tyco. TyOrCo tyco
           => TyCoVar             -- variable to be unified
           -> tyco                -- with this tyco
           -> tyco                -- (version w/ expanded synonyms)
           -> UM ()

-- We know that tv1 isn't refined

uUnrefined tv1 ty2 ty2'
  | Just ty2'' <- tycoTcView ty2'
  = uUnrefined tv1 ty2 ty2''    -- Unwrap synonyms
                -- This is essential, in case we have
                --      type Foo a = a
                -- and then unify a ~ Foo a

uUnrefined tv1 ty2 ty2'
  | Just tv2 <- getVar_maybe ty2'
  = do { tv1' <- umRnOccL tv1
       ; tv2' <- umRnOccR tv2
       ; when (tv1' /= tv2') $ do -- when they are equal, success: do nothing
       { subst <- (getSubstEnv :: UM (VarEnv tyco))
          -- Check to see whether tv2 is refined     
       ; case lookupVarEnv subst tv2 of
         {  Just ty' -> uUnrefined tv1 ty' ty'
         ;  Nothing  -> do
       {   -- So both are unrefined
         when (mustUnifyKind ty2) $ unify_ty (tyVarKind tv1) (tyVarKind tv2)

           -- And then bind one or the other, 
           -- depending on which is bindable
           -- NB: unlike TcUnify we do not have an elaborate sub-kinding 
           --     story.  That is relevant only during type inference, and
           --     (I very much hope) is not relevant here.
       ; b1 <- tvBindFlag tv1
       ; b2 <- tvBindFlag tv2
       ; let ty1 = (mkVar tv1 :: tyco)
       ; case (b1, b2) of
           (Skolem, Skolem) -> maybeApart -- See Note [Unification with skolems]
           (BindMe, _)      -> do { checkRnEnvR ty2 -- make sure ty2 is not a local
                                  ; extendEnv tv1 ty2 }
           (_, BindMe)      -> do { checkRnEnvL ty1 -- ditto for ty1
                                  ; extendEnv tv2 ty1 }}}}}

uUnrefined tv1 ty2 ty2' -- ty2 is not a type variable
  = do { occurs <- elemNiSubstSet tv1 (tyCoVarsOf ty2')
       ; if occurs 
         then maybeApart               -- Occurs check, see Note [Fine-grained unification]
         else do
       { unify k1 k2
        -- Note [Kinds Containing Only Literals]
       ; bindTv tv1 ty2 }}      -- Bind tyvar to the synonym if poss
  where
    k1 = tyVarKind tv1
    k2 = getKind ty2'

elemNiSubstSet :: TyCoVar -> TyCoVarSet -> UM Bool
elemNiSubstSet v set
  = do { tsubst <- getTvSubstEnv
       ; csubst <- getCvSubstEnv
       ; return $ v `elemVarSet` niSubstTvSet tsubst csubst set }

bindTv :: TyOrCo tyco => TyCoVar -> tyco -> UM ()
bindTv tv ty    -- ty is not a variable
  = do  { checkRnEnvR ty -- make sure ty mentions no local variables
        ; b <- tvBindFlag tv
        ; case b of
            Skolem -> maybeApart  -- See Note [Unification with skolems]
            BindMe -> extendEnv tv ty
        }

{-
%************************************************************************
%*                                                                      *
                TyOrCo class
%*                                                                      *
%************************************************************************
-}

class Unifiable tyco => TyOrCo tyco where
  getSubstEnv   :: UM (VarEnv tyco)
  tycoTcView    :: tyco -> Maybe tyco
  getVar_maybe  :: tyco -> Maybe TyCoVar
  mkVar         :: TyCoVar -> tyco
  extendEnv     :: TyCoVar -> tyco -> UM ()
  getKind       :: tyco -> Type
  mustUnifyKind :: tyco -> Bool -- the parameter is really a type proxy

instance TyOrCo Type where
  getSubstEnv     = getTvSubstEnv
  tycoTcView      = tcView
  getVar_maybe    = repGetTyVar_maybe
  mkVar           = mkOnlyTyVarTy
  extendEnv       = extendTvEnv
  getKind         = typeKind
  mustUnifyKind _ = True

instance TyOrCo Coercion where
  getSubstEnv     = getCvSubstEnv
  tycoTcView _    = Nothing
  getVar_maybe    = getCoVar_maybe
  mkVar           = mkCoVarCo
  extendEnv       = extendCvEnv
  getKind         = coercionType -- not coercionKind!
  mustUnifyKind _ = False -- done in unify_co, don't need in unify_co'

{-
%************************************************************************
%*                                                                      *
                Binding decisions
*                                                                      *
************************************************************************
-}

data BindFlag 
  = BindMe      -- A regular type variable

  | Skolem      -- This type variable is a skolem constant
                -- Don't bind it; it only matches itself

{-
************************************************************************
*                                                                      *
                Unification monad
*                                                                      *
************************************************************************
-}

newtype UM a = UM { unUM :: (TyVar -> BindFlag) -- the user-supplied BingFlag function
                         -> RnEnv2              -- the renaming env for local variables
                         -> TyCoVarSet          -- set of all local variables
                         -> TvSubstEnv -> CvSubstEnv -- substitutions
                         -> UnifyResultM ((TvSubstEnv, CvSubstEnv), a) }

instance Functor UM where
      fmap = liftM

instance Applicative UM where
      pure = return
      (<*>) = ap

instance Monad UM where
  return a = UM (\_ _ _ tsubst csubst -> Unifiable ((tsubst, csubst), a))
  fail _   = UM (\_ _ _ _ _ -> SurelyApart) -- failed pattern match
  m >>= k  = UM (\tvs rn_env locals tsubst csubst ->
                 case unUM m tvs rn_env locals tsubst csubst of
                   Unifiable ((tsubst', csubst'), v)
                     -> unUM (k v) tvs rn_env locals tsubst' csubst'
                   MaybeApart ((tsubst', csubst'), v)
                     -> case unUM (k v) tvs rn_env locals tsubst' csubst' of
                          Unifiable result -> MaybeApart result
                          other            -> other
                   SurelyApart -> SurelyApart)

-- TODO (RAE): Is this right?
instance Alternative UM where
  empty = mzero
  (<|>) = mplus

  -- need this instance because of a use of 'guard' above
instance MonadPlus UM where
  mzero = UM (\_ _ _ _ _ -> SurelyApart)

    -- This function should never be called, but it has a sensible implementation,
    -- so why not?
  mplus m1 m2 = UM (\tvs rn_env locals tsubst csubst ->
                     let res2 = unUM m2 tvs rn_env locals tsubst csubst in
                     case unUM m1 tvs rn_env locals tsubst csubst of
                       res1@(Unifiable _)  -> res1
                       res1@(MaybeApart _) -> case res2 of
                                                  Unifiable _ -> res2
                                                  _           -> res1
                       SurelyApart         -> res2)

initUM :: (TyVar -> BindFlag)
       -> TyCoVarSet  -- set of variables in scope
       -> UM a -> UnifyResultM a
initUM badtvs vars um
  = case unUM um badtvs rn_env emptyVarSet emptyTvSubstEnv emptyCvSubstEnv of
      Unifiable (_, subst)  -> Unifiable subst
      MaybeApart (_, subst) -> MaybeApart subst
      SurelyApart           -> SurelyApart
  where
    rn_env = mkRnEnv2 (mkInScopeSet vars)

tvBindFlag :: TyVar -> UM BindFlag
tvBindFlag tv = UM $ \tv_fn _ locals tsubst csubst ->
  Unifiable ((tsubst, csubst), if tv `elemVarSet` locals then Skolem else tv_fn tv)

getTvSubstEnv :: UM TvSubstEnv
getTvSubstEnv = UM $ \_ _ _ tsubst csubst -> Unifiable ((tsubst, csubst), tsubst)

extendTvEnv :: TyVar -> Type -> UM ()
extendTvEnv tv ty = UM $ \_ _ _ tsubst csubst ->
  let tsubst' = extendVarEnv tsubst tv ty in
  Unifiable ((tsubst', csubst), ())

getCvSubstEnv :: UM CvSubstEnv
getCvSubstEnv = UM $ \_ _ _ tsubst csubst -> Unifiable ((tsubst, csubst), csubst)

extendCvEnv :: CoVar -> Coercion -> UM ()
extendCvEnv cv co = UM $ \_ _ _ tsubst csubst ->
  let csubst' = extendVarEnv csubst cv co in
  Unifiable ((tsubst, csubst'), ())

getInScope :: UM InScopeSet
getInScope = UM $ \_ rn_env _ tsubst csubst -> Unifiable ((tsubst, csubst), rnInScopeSet rn_env)

umRnBndr2 :: TyCoVar -> TyCoVar -> UM a -> UM a
umRnBndr2 v1 v2 thing = UM $ \tv_fn rn_env locals tsubst csubst ->
  let (rn_env', v3) = rnBndr2_var rn_env v1 v2
      locals'       = extendVarSetList locals [v1, v2, v3]
  in unUM thing tv_fn rn_env' locals' tsubst csubst

checkRnEnv :: TyOrCo tyco => (RnEnv2 -> Var -> Bool) -> tyco -> UM ()
checkRnEnv inRnEnv tyco = UM $ \_ rn_env _ tsubst csubst ->
  let varset = tyCoVarsOf tyco in
  if any (inRnEnv rn_env) (varSetElems varset)
  then MaybeApart ((tsubst, csubst), ())
  else Unifiable ((tsubst, csubst), ())

checkRnEnvR :: TyOrCo tyco => tyco -> UM ()
checkRnEnvR = checkRnEnv inRnEnvR

checkRnEnvL :: TyOrCo tyco => tyco -> UM ()
checkRnEnvL = checkRnEnv inRnEnvL

umRnOccL :: TyCoVar -> UM TyCoVar
umRnOccL v = UM $ \_ rn_env _ tsubst csubst ->
  Unifiable ((tsubst, csubst), rnOccL rn_env v)

umRnOccR :: TyCoVar -> UM TyCoVar
umRnOccR v = UM $ \_ rn_env _ tsubst csubst ->
  Unifiable ((tsubst, csubst), rnOccR rn_env v)

umSwapRn :: UM a -> UM a
umSwapRn thing = UM $ \tv_fn rn_env locals tsubst csubst ->
  let rn_env' = rnSwap rn_env in
  unUM thing tv_fn rn_env' locals tsubst csubst

dontBeSoSure :: UM () -> UM ()
dontBeSoSure thing = UM $ \ty_fn rn_env locals tsubst csubst ->
  case unUM thing ty_fn rn_env locals tsubst csubst of
    SurelyApart -> MaybeApart ((tsubst, csubst), ())
    other       -> other

dontUnify :: UM a -> UM a
dontUnify thing = UM $ \ty_fn rn_env locals tsubst csubst ->
  case unUM thing ty_fn rn_env locals tsubst csubst of
    Unifiable result  -> MaybeApart result
    MaybeApart result -> MaybeApart result
    SurelyApart       -> SurelyApart

maybeApart :: UM ()
maybeApart = UM (\_ _ _ tsubst csubst -> MaybeApart ((tsubst, csubst), ()))

surelyApart :: UM a
surelyApart = UM (\_ _ _ _ _ -> SurelyApart)

{-
%************************************************************************
%*                                                                      *
            Matching a (lifted) type against a coercion
%*                                                                      *
%************************************************************************

This section defines essentially an inverse to liftCoSubst. It is defined
here to avoid a dependency from Coercion on this module.

Note [zipLiftCoEnv incomplete]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
zipLiftCoEnv attempts to take two TCvSubsts (one for the left side and one for
the right side) and zip them together into a LiftCoEnv. The problem is that,
whenever the two substs disagree on a type mapping, the LiftCoEnv must use a
coercion between the two types. We could theoretically have some pile of
available coercions and sift through them trying to make the right coercion,
but that's a much harder problem than just matching, which is where this is
used. Because this matching is currently (Jan 2013) used only for coercion
optimization, I'm not implementing full coercion inference.

When the two substs disagree on a coercion mapping, though, there is no
problem: we don't need evidence showing coercions agree. We just make the
CoCoArg and carry on.

If the two substs have different sets of bindings, we have a different
problem. Ideally, we would create a new matchable variable for the missing
binding and keep working, but it does not seem worth it to implement this now.
Shout (at Richard Eisenberg, eir@cis.upenn.edu) if this is a problem for you.

Note [Heterogeneous type matching]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Say we have the following in our LiftCoEnv:

[a |-> g]
where g :: k1 ~ k2

Now, we are matching the following:

forall a:k.t <-> forall_g (a1:k1, a2:k2, c:a1~a2).h

We can't just use RnEnv2 the normal way, because there are a different
number of binders on either side. What we want to ensure is that, while
matching t and h, any appearance of a in t is replaced by an appearance
of c in h. So, we just add all the variables separately to the appropriate
sides of the RnEnv2. Then, we augment the substitution to link the renamed
'a' to its lifted coercion, the renamed 'c'. After matching, we then
want to remove this mapping from the substitution before returning.

But, what about the kind of c? Won't its new kind be wrong? Sure, it
will be, but that's OK. If the kind of c ever matters, the occurs check
in the TyVarTy case will fail, because the kind of c mentions local
variables.

The coercion cases follow a similar logic.

Note [ty_co_match CastTy case]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We essentially need to reverse engineer a castCoercionKind to get this to
work. But, the result of the castCoercionKind might, potentially, have been
restructured. So, instead of deconstructing it directly, we just add
more casts to cancel out the ones already there. To have a hope of this
working, though, we want the new casts to cancel out the old ones. If we
just use castCoercionKind again, it does not simplify. (Try it!) On the
other hand, if we use mkCoherenceRightCo *before* mkCoherenceLeftCo, the
optimizations in the mk...Co functions almost do the right thing. The one
problem is the missing optimization in mkCoherenceCo, as described in
Note [Don't optimize mkCoherenceCo]. So, we use the function opt_coh to
implement that optimization in exactly the special case that we need to
cancel out all the coercions. It's a little fiddly, but because there can
be many equivalent coercions, I don't see an easier way.
-}

zipLiftCoEnv :: RnEnv2 -> LiftCoEnv
             -> TCvSubst -> TCvSubst -> Maybe LiftCoEnv
zipLiftCoEnv rn_env lc_env
             (TCvSubst _ l_tenv l_cenv) (TCvSubst _ r_tenv r_cenv)
  = do { lc_env1 <- go_ty lc_env  r_tenv (varEnvKeys l_tenv)
       ;            go_co lc_env1 r_cenv (varEnvKeys l_cenv) }
  where
    go_ty :: LiftCoEnv -> TvSubstEnv -> [Unique] -> Maybe LiftCoEnv
    go_ty env r_tenv []
      | isEmptyVarEnv r_tenv
      = Just env
      
      | otherwise -- leftover bindings in renv, but not in lenv
      = Nothing -- See Note [zipLiftCoEnv incomplete]

    go_ty env r_tenv (u:us)
      | Just _ <- lookupVarEnv_Directly env u
      = go_ty env (delVarEnv_Directly r_tenv u) us

      | Just tyl <- lookupVarEnv_Directly l_tenv u
      , Just tyr <- lookupVarEnv_Directly r_tenv u
      , eqTypeX rn_env tyl tyr
      = go_ty (extendVarEnv_Directly env u (TyCoArg (mkReflCo Nominal tyr)))
              (delVarEnv_Directly r_tenv u) us

      | otherwise
      = Nothing -- See Note [zipLiftCoEnv incomplete]

    go_co :: LiftCoEnv -> CvSubstEnv -> [Unique] -> Maybe LiftCoEnv
    go_co env r_cenv []
      | isEmptyVarEnv r_cenv
      = Just env

      | otherwise
      = Nothing -- See Note [zipLifCoEnv incomplete]

    go_co env r_cenv (u:us)
      | Just _ <- lookupVarEnv_Directly env u
      = go_co env (delVarEnv_Directly r_cenv u) us

      | Just col <- lookupVarEnv_Directly l_cenv u
      , Just cor <- lookupVarEnv_Directly r_cenv u
      = go_co (extendVarEnv_Directly env u (CoCoArg Nominal col cor))
              (delVarEnv_Directly r_cenv u) us

      | otherwise
      = Nothing -- See Note [zipLiftCoEnv incomplete]

-- | 'liftCoMatch' is sort of inverse to 'liftCoSubst'.  In particular, if
--   @liftCoMatch vars ty co == Just s@, then @tyCoSubst s ty == co@.
--   That is, it matches a type against a coercion of the same
--   "shape", and returns a lifting substitution which could have been
--   used to produce the given coercion from the given type.
--   Note that this function is incomplete -- it might return Nothing
--   when there does indeed exist a possible lifting context.
--   See Note [zipLiftCoEnv incomplete]
--
-- The lifting context produced doesn't have to be exacting in the roles
-- of the mappings. This is because any use of the lifting context will
-- also require a desired role. Thus, this algorithm prefers mapping to
-- nominal coercions where it can do so.
liftCoMatch :: TyCoVarSet -> Type -> Coercion -> Maybe LiftingContext
liftCoMatch tmpls ty co 
  = case ty_co_match menv emptyVarEnv ty co of
      Just cenv -> Just (LC in_scope cenv)
      Nothing   -> Nothing
  where
    menv     = ME { me_tmpls = tmpls, me_env = mkRnEnv2 in_scope }
    in_scope = mkInScopeSet (tmpls `unionVarSet` tyCoVarsOfCo co)
    -- Like tcMatchTy, assume all the interesting variables 
    -- in ty are in tmpls

-- | 'ty_co_match' does all the actual work for 'liftCoMatch'.
ty_co_match :: MatchEnv -> LiftCoEnv -> Type -> Coercion -> Maybe LiftCoEnv
ty_co_match menv subst ty co
  | Just ty' <- coreView ty = ty_co_match menv subst ty' co

  -- handle Refl case:
  | tyCoVarsOfType ty `isNotInDomainOf` subst
  , Just (ty', _) <- isReflCo_maybe co
  , eqTypeX (me_env menv) ty ty'
  = Just subst

  where
    isNotInDomainOf :: VarSet -> VarEnv a -> Bool
    isNotInDomainOf set env
      = noneSet (\v -> elemVarEnv v env) set

    noneSet :: (Var -> Bool) -> VarSet -> Bool
    noneSet f = foldVarSet (\v rest -> rest && (not $ f v)) True

  -- Match a type variable against a non-refl coercion
ty_co_match menv subst (TyVarTy tv1) co
  | Just (TyCoArg co1') <- lookupVarEnv subst tv1' -- tv1' is already bound to co1
  = if eqCoercionX (nukeRnEnvL rn_env) co1' co
    then Just subst
    else Nothing       -- no match since tv1 matches two different coercions

  | tv1' `elemVarSet` me_tmpls menv           -- tv1' is a template var
  = if any (inRnEnvR rn_env) (varSetElems (tyCoVarsOfCo co))
    then Nothing      -- occurs check failed
    else do { subst1 <- ty_co_match menv subst (tyVarKind tv1') (promoteCoercion co)
            ; return (extendVarEnv subst1 tv1' (TyCoArg co)) }

  | otherwise
  = Nothing

  where
    rn_env = me_env menv
    tv1' = rnOccL rn_env tv1

  -- just look through SubCo's. We don't really care about roles here.
ty_co_match menv subst ty (SubCo co)
  = ty_co_match menv subst ty co

ty_co_match menv subst (AppTy ty1 ty2) co
  | Just (co1, arg2) <- splitAppCo_maybe co     -- c.f. Unify.match on AppTy
  = do { subst' <- ty_co_match menv subst ty1 co1 
       ; ty_co_match_arg menv subst' ty2 arg2 }

ty_co_match menv subst (TyConApp tc1 tys) (TyConAppCo _ tc2 cos)
  | tc1 == tc2 = ty_co_match_args menv subst tys cos

ty_co_match menv subst (ForAllTy (Anon ty1) ty2) (TyConAppCo _ tc cos)
  | tc == funTyCon = ty_co_match_args menv subst [ty1, ty2] cos

ty_co_match menv subst (ForAllTy (Named tv _) ty) (ForAllCo cobndr co)
  | TyHomo tv2 <- cobndr
  = ASSERT( isTyVar tv )
    do { subst1 <- ty_co_match menv subst (tyVarKind tv)
                                          (mkReflCo Nominal $ tyVarKind tv2)
       ; let menv1 = menv { me_env = rnBndr2 (me_env menv) tv tv2 }
       ; ty_co_match menv1 subst1 ty co }

  | TyHetero co1 tvl tvr cv <- cobndr
  = ASSERT( isTyVar tv )
    do { subst1 <- ty_co_match menv subst (tyVarKind tv) co1
         -- See Note [Heterogeneous type matching]
       ; let rn_env0 = me_env menv
             (rn_env1, tv')  = rnBndrL rn_env0 tv
             (rn_env2, _)    = rnBndrR rn_env1 tvl
             (rn_env3, _)    = rnBndrR rn_env2 tvr
             (rn_env4, cv')  = rnBndrR rn_env3 cv
             menv' = menv { me_env = rn_env4 }
             subst2 = extendVarEnv subst1 tv' (TyCoArg (mkCoVarCo cv'))
       ; subst3 <- ty_co_match menv' subst2 ty co
       ; return $ delVarEnv subst3 tv' }

  | CoHomo cv <- cobndr
  = ASSERT( isCoVar tv )
    do { subst1 <- ty_co_match menv subst (coVarKind tv)
                                          (mkReflCo Nominal $ coVarKind cv)
       ; let rn_env0 = me_env menv
             (rn_env1, tv') = rnBndrL rn_env0 tv
             (rn_env2, cv') = rnBndrR rn_env1 cv
             menv' = menv { me_env = rn_env2 }
             subst2 = extendVarEnv subst1 tv' (mkCoArgForVar cv')
       ; subst3 <- ty_co_match menv' subst2 ty co
       ; return $ delVarEnv subst3 tv' }

  | CoHetero co1 cvl cvr <- cobndr
  = ASSERT( isCoVar tv )
    do { subst1 <- ty_co_match menv subst (coVarKind tv) co1
       ; let rn_env0 = me_env menv
             (rn_env1, tv')  = rnBndrL rn_env0 tv
             (rn_env2, cvl') = rnBndrR rn_env1 cvl
             (rn_env3, cvr') = rnBndrR rn_env2 cvr
             menv' = menv { me_env = rn_env3 }
             subst2 = extendVarEnv subst1 tv' (CoCoArg Nominal (mkCoVarCo cvl') (mkCoVarCo cvr'))
       ; subst3 <- ty_co_match menv' subst2 ty co
       ; return $ delVarEnv subst3 tv' }

ty_co_match menv subst (CastTy ty1 co1) co
  | Pair (CastTy _ col) (CastTy _ cor) <- coercionKind co
  = do { subst1 <- ty_co_match_lr menv subst co1 col cor
         -- don't use castCoercionKind! See Note [ty_co_match CastTy case]
       ; ty_co_match menv subst1 ty1
                     (opt_coh (co `mkCoherenceRightCo` (mkSymCo cor)
                                  `mkCoherenceLeftCo` (mkSymCo col))) }
  where
    -- in a very limited number of cases, optimize CoherenceCo
    -- see Note [ty_co_match CastTy case]
    mk_coh co1 (Refl {}) = co1
    mk_coh co1 co2       = mkCoherenceCo co1 co2

    opt_coh (SymCo co) = mkSymCo (opt_coh co)
    opt_coh (CoherenceCo (CoherenceCo co1 co2) co3)
      = mk_coh co1 (mkTransCo co2 co3)
    opt_coh (CoherenceCo co1 co2) = mk_coh (opt_coh co1) co2
    opt_coh co = co

ty_co_match _ _ (CoercionTy co) _
  = pprPanic "ty_co_match" (ppr co)

ty_co_match menv subst ty co
  | Just co' <- pushRefl co = ty_co_match menv subst ty co'
  | otherwise               = Nothing

ty_co_match_args :: MatchEnv -> LiftCoEnv -> [Type] -> [CoercionArg]
                 -> Maybe LiftCoEnv
ty_co_match_args _    subst []       []         = Just subst
ty_co_match_args menv subst (ty:tys) (arg:args) = do { subst' <- ty_co_match_arg menv subst ty arg
                                                    ; ty_co_match_args menv subst' tys args }
ty_co_match_args _    _     _        _          = Nothing

ty_co_match_arg :: MatchEnv -> LiftCoEnv -> Type -> CoercionArg -> Maybe LiftCoEnv
ty_co_match_arg menv subst ty arg
  | TyCoArg co <- arg
  = ty_co_match menv subst ty co
  | CoercionTy co1 <- ty
  , CoCoArg _ col cor <- arg
  = ty_co_match_lr menv subst co1 col cor
  | otherwise
  = pprPanic "ty_co_match_arg" (ppr ty <+> ptext (sLit "<->") <+> ppr arg)

ty_co_match_lr :: MatchEnv -> LiftCoEnv
               -> Coercion -> Coercion -> Coercion -> Maybe LiftCoEnv
ty_co_match_lr menv subst co1 col cor
  = do { let subst_left  = liftEnvSubstLeft  in_scope subst
             subst_right = liftEnvSubstRight in_scope subst
       ; tcvsubst1 <- tcMatchCoX tmpl_vars subst_left  co1 col
       ; tcvsubst2 <- tcMatchCoX tmpl_vars subst_right co1 cor
       ; zipLiftCoEnv rn_env subst tcvsubst1 tcvsubst2 }
  where
    ME { me_tmpls = tmpl_vars
       , me_env   = rn_env } = menv
    in_scope = rnInScopeSet rn_env
  
pushRefl :: Coercion -> Maybe Coercion
pushRefl (Refl Nominal (AppTy ty1 ty2))
  = Just (AppCo (Refl Nominal ty1) (liftSimply Nominal ty2))
pushRefl (Refl r (ForAllTy (Anon ty1) ty2))
  = Just (TyConAppCo r funTyCon [liftSimply r ty1, liftSimply r ty2])
pushRefl (Refl r (TyConApp tc tys))
  = Just (TyConAppCo r tc (zipWith liftSimply (tyConRolesX r tc) tys))
pushRefl (Refl r (ForAllTy (Named tv _) ty))
  | isTyVar tv                    = Just (ForAllCo (TyHomo tv) (Refl r ty))
  | otherwise                     = Just (ForAllCo (CoHomo tv) (Refl r ty))
pushRefl (Refl r (CastTy ty co))  = Just (castCoercionKind (Refl r ty) co co)
pushRefl _                        = Nothing

