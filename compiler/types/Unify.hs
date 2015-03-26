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
        tcUnifyTy, tcUnifyTys, 
        tcUnifyTysFG,
        BindFlag(..),
        UnifyResult, UnifyResultM(..),

        -- Matching a type against a lifted type (coercion)
        liftCoMatch
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

import Control.Monad
import Maybes
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ( Applicative(..) )
import Data.Traversable    ( traverse )
#endif
import Control.Applicative ( Alternative(..), (<$>) )

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

Note [Lazy coercions in Unify]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
After the internal matching algorithm is done running, we use
buildCoherenceCo to create a coercion between the input and the output.

This operation should always succeed after a successful match. But,
many times, we just care if the match succeeded or not. (That is,
many calls to tcMatchTy are wrapped in `isJust`). We don't want to
build the coercion at all in this case. So, we're careful to be lazy
in the return value from buildCoherenceCo.

Note [Kind coercions in Unify]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We wish to match/unify while ignoring casts. But, we can't just ignore
them completely, or we'll end up with ill-kinded substitutions. For example,
say we're matching `a` with `ty |> co`. If we just drop the cast, we'll
return [a |-> ty], but `a` and `ty` might have different kinds. We can't
just match/unify their kinds, either, because this might gratuitously
fail. After all, `co` is the witness that the kinds are the same -- they
may look nothing alike.

So, we pass a kind coercion to the match/unify worker. This coercion witnesses
the equality between the substed kind of the left-hand type and the substed
kind of the right-hand type. To get this coercion, we first have to match/unify
the kinds before looking at the types. Happily, we need look only one level
up, as all kinds are guaranteed to have kind *.

-}

data MatchEnv
  = ME  { me_tmpls :: VarSet    -- ^ Template variables
        , me_env   :: RnEnv2    -- ^ Renaming envt for nested foralls
        }                       --   In-scope set includes template variables

-- | @tcMatchTy tys t1 t2@ produces a substitution (over a subset of
-- the variables @tys@) @s@ such that @s(t1)@ equals @t2@, as witnessed
-- by the returned coercion. That coercion will be reflexive whenever the
-- kinds of @s(t1)@ and @t2) are the same.
tcMatchTy :: TyCoVarSet -> Type -> Type -> Maybe (TCvSubst, Coercion)
tcMatchTy tmpls ty1 ty2
    -- See Note [Lazy coercions in Unify]
  = do { (subst, ~[~(TyCoArg co)]) <- tcMatchTys tmpls [ty1] [ty2]
       ; return (subst, co) }

-- | This is similar to 'tcMatchTy', but extends a substitution
tcMatchTyX :: TyCoVarSet          -- ^ Template tyvars
           -> TCvSubst            -- ^ Substitution to extend
           -> Type                -- ^ Template
           -> Type                -- ^ Target
           -> Maybe (TCvSubst, Coercion)
tcMatchTyX tmpls subst ty1 ty2
    -- See Note [Lazy coercions in Unify]
  = do { (subst, ~[~(TyCoArg co)]) <- tcMatchTysX tmpls subst [ty1] [ty2]
       ; return (subst, co) }

-- | Like 'tcMatchTy' but over a list of types.
tcMatchTys :: TyCoVarSet     -- ^ Template tyvars
           -> [Type]         -- ^ Template
           -> [Type]         -- ^ Target
           -> Maybe (TCvSubst, [CoercionArg])
                             -- ^ One-shot; in principle the template
                             -- variables could be free in the target
tcMatchTys tmpls tys1 tys2
  = tcMatchTysX tmpls (mkEmptyTCvSubst in_scope) tys1 tys2
  where
    in_scope = mkInScopeSet (tmpls `unionVarSet` tyCoVarsOfTypes tys2)
        -- We're assuming that all the interesting 
        -- tyvars in tys1 are in tmpls

-- | Like 'tcMatchTys', but extending a substitution
tcMatchTysX :: TyCoVarSet     -- ^ Template tyvars
            -> TCvSubst       -- ^ Substitution to extend
            -> [Type]         -- ^ Template
            -> [Type]         -- ^ Target
            -> Maybe (TCvSubst, [CoercionArg])  -- ^ One-shot substitution
tcMatchTysX tmpls (TCvSubst in_scope tv_env cv_env) tys1 tys2
-- See Note [Kind coercions in Unify]
  = do { tv_env1 <- match_tys menv tv_env kis1 kis2
                              (repeat (mkRepReflCoArg liftedTypeKind))
             -- it must be that subst(kis1) `eqTypes` kis2, because
             -- all kinds have kind *
       ; tv_env2 <- match_tys menv tv_env1 tys1 tys2
                                           (map mkRepReflCoArg kis2)
       ; let subst = TCvSubst in_scope tv_env2 cv_env
                 -- See Note [Lazy coercions in Unify]
       ; return (subst, map (expectJust "tcMatchTysX types") $
                        zipWith buildCoherenceCoArg
                                (substTys subst tys1) tys2) }
  where
    kis1 = map typeKind tys1
    kis2 = map typeKind tys2
    menv = ME {me_tmpls = tmpls, me_env = mkRnEnv2 in_scope}

-- | This one is called from the expression matcher,
-- which already has a MatchEnv in hand
ruleMatchTyX :: MatchEnv 
         -> TvSubstEnv          -- ^ type substitution to extend
         -> CvSubstEnv          -- ^ coercion substitution to extend
         -> Type                -- ^ Template
         -> Type                -- ^ Target
         -> Maybe (TvSubstEnv, CvSubstEnv)
ruleMatchTyX env tenv cenv tmpl target
-- See Note [Kind coercions in Unify]
  = do { let target_ki = typeKind target
       ; tenv1 <- match_ty env tenv (typeKind tmpl) target_ki
                                    (mkRepReflCo liftedTypeKind)
       ; tenv2 <- match_ty env tenv1 tmpl target
                                     (mkRepReflCo target_ki)
       ; let subst = mkOpenTCvSubst tenv2 cenv
       ; guard (substTy subst tmpl `eqType` target) -- we want exact matching here
       ; return (tenv2, cenv) }
     -- TODO (RAE): This should probably work with inexact matching too;
     -- otherwise, various rules won't fire when they should

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
match_ty :: MatchEnv    -- ^ For the most part this is pushed downwards
         -> TvSubstEnv     -- ^ Substitution so far:
                           --   Domain is subset of template tyvars
                           --   Free vars of range is subset of 
                           --      in-scope set of the RnEnv2
         -> Type -> Type   -- ^ Template and target respectively
         -> Coercion       -- ^ :: kind of template ~R kind of target
                           -- See Note [Kind coercions in Unify]
         -> Maybe TvSubstEnv

match_ty menv tsubst ty1 ty2 kco
  | Just ty1' <- coreViewOneStarKind ty1 = match_ty menv tsubst ty1' ty2 kco
  | Just ty2' <- coreViewOneStarKind ty2 = match_ty menv tsubst ty1 ty2' kco

  | CastTy ty1' co <- ty1 = match_ty menv tsubst ty1' ty2 (co `mkTransCo` kco)
  | CastTy ty2' co <- ty2 = match_ty menv tsubst ty1 ty2'
                                                 (kco `mkTransCo` mkSymCo co)

match_ty menv tsubst (TyVarTy tv1) ty2 kco
  | Just ty1' <- lookupVarEnv tsubst tv1'       -- tv1' is already bound
  = do { _ <- buildCoherenceCoX (nukeRnEnvL rn_env) ty1' ty2
        -- ty1 has no locally-bound variables, hence nukeRnEnvL
       ; return tsubst }

  | tv1' `elemVarSet` me_tmpls menv
  = if any (inRnEnvR rn_env) (varSetElems (tyCoVarsOfType ty2))
    then Nothing        -- Occurs check
                        -- ezyang: Is this really an occurs check?  It seems
                        -- to just reject matching \x. A against \x. x (maintaining
                        -- the invariant that the free vars of the range of @subst@
                        -- are a subset of the in-scope set in @me_env menv@.)
    else Just $ extendVarEnv tsubst tv1' (ty2 `mkCastTy` mkSymCo kco)

   | otherwise  -- tv1 is not a template tyvar
   = case ty2 of
        TyVarTy tv2 | tv1' == rnOccR rn_env tv2 -> Just tsubst
        _                                       -> Nothing
  where
    rn_env = me_env menv
    tv1' = rnOccL rn_env tv1

match_ty menv tsubst (ForAllTy (Named tv1 _) ty1) (ForAllTy (Named tv2 _) ty2) kco
  = do { tsubst' <- match_ty menv tsubst (tyVarKind tv1) (tyVarKind tv2)
                                         (mkRepReflCo liftedTypeKind)
       ; match_ty menv' tsubst' ty1 ty2 kco }
  where         -- Use the magic of rnBndr2 to go under the binders
    menv' = menv { me_env = rnBndr2 (me_env menv) tv1 tv2 }

match_ty menv tsubst (TyConApp tc1 tys1) (TyConApp tc2 tys2) _kco
  | tc1 == tc2 = match_tys menv tsubst tys1 tys2
                           (map (mkRepReflCoArg . typeKind) tys2)
         -- if any of the kinds of the tys don't match up, there has to be
         -- an earlier, dependent parameter of the tycon that *also* doesn't
         -- match. So, we'll never look at any bogus kind coercions made on
         -- the line above.
match_ty menv tsubst (ForAllTy (Anon ty1a) ty1b) (ForAllTy (Anon ty2a) ty2b) _kco
-- NB: The types here may be of kind #. Note that if the kinds don't match
-- up, neither will the types, so we don't have to unify the kinds first.
-- A bogus coercion passed in won't hurt us.
  = do { tsubst' <- match_ty menv tsubst ty1a ty2a (mkRepReflCo (typeKind ty1a))
       ; match_ty menv tsubst' ty1b ty2b (mkRepReflCo (typeKind ty1b)) }
    
match_ty menv tsubst (AppTy ty1a ty1b) ty2 _kco
  | Just (ty2a, ty2b) <- repSplitAppTy_maybe ty2
        -- 'repSplit' used because the tcView stuff is done above
  = match_ty_app menv tsubst ty1a ty1b ty2a ty2b
match_ty menv tsubst ty1 (AppTy ty2a ty2b) _kco
  | Just (ty1a, ty1b) <- repSplitAppTy_maybe ty1
  = match_ty_app menv tsubst ty1a ty1b ty2a ty2b

match_ty _ tsubst (LitTy x) (LitTy y) _kco
  | x == y
  = return tsubst

match_ty _ tsubst (CoercionTy {}) (CoercionTy {}) _kco = return tsubst

match_ty _ _ _ _ _
  = Nothing

match_ty_app :: MatchEnv -> TvSubstEnv
             -> Type -> Type
             -> Type -> Type
             -> Maybe TvSubstEnv
match_ty_app menv tsubst ty1a ty1b ty2a ty2b
  = do { -- we painfully can't decompose kco here.
         -- TODO (RAE): Fix this exponential behavior.
         tsubst1 <- match_ty menv tsubst  ki1a ki2a (mkRepReflCo liftedTypeKind)
       ; let ki_a = mkRepReflCo ki2a
       ; tsubst2 <- match_ty menv tsubst1 ty1a ty2a ki_a
       ; match_ty menv tsubst2 ty1b ty2b (mkNthCo 0 ki_a) }
  where
    ki1a = typeKind ty1a
    ki2a = typeKind ty2a

match_tys :: MatchEnv -> TvSubstEnv -> [Type] -> [Type] -> [CoercionArg]
          -> Maybe TvSubstEnv
match_tys _    tenv []     []     _ = Just tenv
match_tys menv tenv (a:as) (b:bs) (c:cs)
  = do { tenv' <- match_ty menv tenv a b (stripTyCoArg c)
             -- the stripTyCoArg should fail iff a b are CoercionTys, in which
             -- case it's never inspected
       ; match_tys menv tenv' as bs cs }
match_tys _    _    _    _      _      = Nothing

{-
%************************************************************************
%*                                                                      *
        Matching monad
%*                                                                      *
%************************************************************************
-}

-- TODO (RAE): Use this monad!
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
typesCantMatch prs = any (uncurry cant_match) prs
  where
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
--      more smarts around casts/coercions

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
          -> Maybe (TCvSubst, Coercion)
                       -- A regular one-shot (idempotent) substitution
-- Simple unification of two types; all type variables are bindable
tcUnifyTy t1 t2
   -- See Note [Lazy coercions in Unify]
  = do { (subst, ~[~(TyCoArg co)]) <- tcUnifyTys (const BindMe) [t1] [t2]
       ; return (subst, co) }

-----------------
tcUnifyTys :: (TyCoVar -> BindFlag)
           -> [Type] -> [Type]
           -> Maybe (TCvSubst, [CoercionArg])
                                -- ^ A regular one-shot (idempotent) substitution
                                -- that unifies the erased types. See comments
                                -- for 'tcUnifyTysFG'
              
-- The two types may have common type variables, and indeed do so in the
-- second call to tcUnifyTys in FunDeps.checkClsFD
tcUnifyTys bind_fn tys1 tys2
  = case tcUnifyTysFG bind_fn tys1 tys2 of
      Unifiable result -> Just result
      _                -> Nothing

-- This type does double-duty. It is used in the UM (unifier monad) and to
-- return the final result. See Note [Fine-grained unification]
type UnifyResult = UnifyResultM (TCvSubst, [CoercionArg])
data UnifyResultM a = Unifiable a        -- the subst that unifies the types
                    | MaybeApart a       -- the subst has as much as we know
                                         -- it must be part of an most general unifier
                                         -- See Note [The substitution in MaybeApart]
                    | SurelyApart

-- | @tcUnifyTysFG bind_tv tys1 tys2@ attepts to find a substitution @s@ (whose
-- domain elements all respond 'BindMe' to @bind_tv@) such that
-- @s(tys1)@ and that of @s(tys2)@ are equal, as witnessed by the returned
-- CoercionArgs.
tcUnifyTysFG :: (TyCoVar -> BindFlag)
             -> [Type] -> [Type]
             -> UnifyResult
tcUnifyTysFG bind_fn tys1 tys2
  = initUM bind_fn vars $
    do { unify_tys kis1 kis2
       ; unify_tys tys1 tys2
       ; subst <- getTCvSubst
       ; return (subst, map (expectJust "tcUnifyTysFG") $
                        zipWith buildCoherenceCoArg
                                (substTys subst tys1)
                                (substTys subst tys2)) }
  where
    vars = tyCoVarsOfTypes tys1 `unionVarSet` tyCoVarsOfTypes tys2
    kis1 = map typeKind tys1
    kis2 = map typeKind tys2

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

niFixTCvSubst :: TvSubstEnv -> TCvSubst
-- Find the idempotent fixed point of the non-idempotent substitution
-- See Note [Finding the substitution fixpoint]
-- ToDo: use laziness instead of iteration?
niFixTCvSubst tenv = f tenv
  where
    f tenv
        | not_fixpoint = f (mapVarEnv (substTy subst') tenv)
        | otherwise    = subst
        where
          not_fixpoint  = foldVarSet ((||) . in_domain) False range_tvs
          in_domain tv  = tv `elemVarEnv` tenv

          range_tvs     = foldVarEnv (unionVarSet . tyCoVarsOfType) emptyVarSet tenv
          subst         = mkTCvSubst (mkInScopeSet range_tvs)
                                     (tenv, emptyCvSubstEnv)

             -- env' extends env by replacing any free type with 
             -- that same tyvar with a substituted kind
             -- See note [Finding the substitution fixpoint]
          tenv'         = extendVarEnvList tenv [ (rtv, mkOnlyTyVarTy $
                                                        setTyVarKind rtv $
                                                        substTy subst $
                                                        tyVarKind rtv)
                                                | rtv <- varSetElems range_tvs
                                                , not (in_domain rtv) ]
          subst'        = mkTCvSubst (mkInScopeSet range_tvs)
                                     (tenv', emptyCvSubstEnv)

niSubstTvSet :: TvSubstEnv -> TyCoVarSet -> TyCoVarSet
-- Apply the non-idempotent substitution to a set of type variables,
-- remembering that the substitution isn't necessarily idempotent
-- This is used in the occurs check, before extending the substitution
niSubstTvSet tsubst tvs
  = foldVarSet (unionVarSet . get) emptyVarSet tvs
  where
    get tv
      | Just ty <- lookupVarEnv tsubst tv
      = niSubstTvSet tsubst (tyCoVarsOfType ty)

      | otherwise
      = unitVarSet tv

{-
************************************************************************
*                                                                      *
                The workhorse
*                                                                      *
************************************************************************

-}

unify_ty :: Type -> Type -> Coercion   -- Types to be unified and a co
                                       -- between their kinds
         -> UM ()
-- We do not require the incoming substitution to be idempotent,
-- nor guarantee that the outgoing one is.  That's fixed up by
-- the wrappers.

unify_ty ty1 ty2 kco
  | Just ty1' <- coreViewOneStarKind ty1 = unify_ty ty1' ty2 kco
  | Just ty2' <- coreViewOneStarKind ty2 = unify_ty ty1 ty2' kco
  | CastTy ty1' co <- ty1                = unify_ty ty1' ty2 (co `mkTransCo` kco)
  | CastTy ty2' co <- ty2                = unify_ty ty1 ty2'
                                                    (kco `mkTransCo` mkSymCo co)

-- Respects newtypes, PredTypes

unify_ty (TyVarTy tv1) ty2 kco = uVar tv1 ty2 kco
unify_ty ty1 (TyVarTy tv2) kco = umSwapRn $ uVar tv2 ty1 (mkSymCo kco)

unify_ty (TyConApp tyc1 tys1) (TyConApp tyc2 tys2) _kco
  | tyc1 == tyc2                                   
  = unify_tys tys1 tys2 

unify_ty (ForAllTy (Anon ty1a) ty1b) (ForAllTy (Anon ty2a) ty2b) _kco
  = do  { unify_ty ty1a ty2a (mkRepReflCo (typeKind ty1a))
        ; unify_ty ty1b ty2b (mkRepReflCo (typeKind ty1b)) }

        -- Applications need a bit of care!
        -- They can match FunTy and TyConApp, so use splitAppTy_maybe
        -- NB: we've already dealt with type variables,
        -- so if one type is an App the other one jolly well better be too
unify_ty (AppTy ty1a ty1b) ty2 _kco
  | Just (ty2a, ty2b) <- repSplitAppTy_maybe ty2
  = unify_ty_app ty1a ty1b ty2a ty2b 

unify_ty ty1 (AppTy ty2a ty2b) _kco
  | Just (ty1a, ty1b) <- repSplitAppTy_maybe ty1
  = unify_ty_app ty1a ty1b ty2a ty2b

unify_ty (LitTy x) (LitTy y) _kco | x == y = return ()

unify_ty (ForAllTy (Named tv1 _) ty1) (ForAllTy (Named tv2 _) ty2) kco
  = do { unify_ty (tyVarKind tv1) (tyVarKind tv2) (mkRepReflCo liftedTypeKind)
       ; umRnBndr2 tv1 tv2 $ unify_ty ty1 ty2 kco }

unify_ty (CoercionTy {}) (CoercionTy {}) _kco = return ()

unify_ty _ _ _ = surelyApart

unify_ty_app :: Type -> Type -> Type -> Type -> UM ()
unify_ty_app ty1a ty1b ty2a ty2b
  = do { -- TODO (RAE): Remove this exponential behavior.
         let ki1a = typeKind ty1a
             ki2a = typeKind ty2a
       ; unify_ty ki1a ki2a (mkRepReflCo liftedTypeKind)
       ; subst <- getTCvSubst
       ; let kind_co = mkRepReflCo (substTy subst ki1a)
       ; unify_ty ty1a ty2a kind_co
       ; unify_ty ty1b ty2b (mkNthCo 0 kind_co) }

unify_tys :: [Type] -> [Type] -> UM ()
unify_tys orig_xs orig_ys
  = go orig_xs orig_ys
  where
    go []     []     = return ()
    go (x:xs) (y:ys)
      = do { subst <- getTCvSubst
           ; unify_ty x y (mkRepReflCo $ substTy subst $ typeKind x)
           ; go xs ys }
    go _ _ = maybeApart  -- See Note [Lists of different lengths are MaybeApart]

---------------------------------
uVar :: TyCoVar           -- Variable to be unified
     -> Type              -- with this Type
     -> Coercion          -- :: kind tv ~N kind ty
     -> UM ()

uVar tv1 ty kco
 = do { -- Check to see whether tv1 is refined by the substitution
        subst <- getTvSubstEnv
      ; case (lookupVarEnv subst tv1) of
          Just ty' -> unify_ty ty' ty kco        -- Yes, call back into unify
          Nothing  -> uUnrefined tv1 ty ty kco } -- No, continue

uUnrefined :: TyCoVar             -- variable to be unified
           -> Type                -- with this Type
           -> Type                -- (version w/ expanded synonyms)
           -> Coercion            -- :: kind tv ~N kind ty
           -> UM ()

-- We know that tv1 isn't refined

uUnrefined tv1 ty2 ty2' kco
  | Just ty2'' <- coreViewOneStarKind ty2'
  = uUnrefined tv1 ty2 ty2'' kco    -- Unwrap synonyms
                -- This is essential, in case we have
                --      type Foo a = a
                -- and then unify a ~ Foo a

  | TyVarTy tv2 <- ty2'
  = do { tv1' <- umRnOccL tv1
       ; tv2' <- umRnOccR tv2
       ; when (tv1' /= tv2') $ do -- when they are equal, success: do nothing
       { subst <- getTvSubstEnv
          -- Check to see whether tv2 is refined     
       ; case lookupVarEnv subst tv2 of
         {  Just ty' -> uUnrefined tv1 ty' ty' kco
         ;  Nothing  -> do
       {   -- So both are unrefined

           -- And then bind one or the other, 
           -- depending on which is bindable
       ; b1 <- tvBindFlag tv1
       ; b2 <- tvBindFlag tv2
       ; let ty1 = mkOnlyTyVarTy tv1
       ; case (b1, b2) of
           (Skolem, Skolem) -> maybeApart -- See Note [Unification with skolems]
           (BindMe, _)      -> do { checkRnEnvR ty2 -- make sure ty2 is not a local
                                  ; extendTvEnv tv1 (ty2 `mkCastTy` kco) }
           (_, BindMe)      -> do { checkRnEnvL ty1 -- ditto for ty1
                                  ; extendTvEnv tv2 (ty1 `mkCastTy` mkSymCo kco)
  }}}}}

uUnrefined tv1 ty2 ty2' kco -- ty2 is not a type variable
  = do { occurs <- elemNiSubstSet tv1 (tyCoVarsOfType ty2')
       ; if occurs 
         then maybeApart               -- Occurs check, see Note [Fine-grained unification]
         else do bindTv tv1 (ty2 `mkCastTy` mkSymCo kco) }
            -- Bind tyvar to the synonym if poss

elemNiSubstSet :: TyCoVar -> TyCoVarSet -> UM Bool
elemNiSubstSet v set
  = do { tsubst <- getTvSubstEnv
       ; return $ v `elemVarSet` niSubstTvSet tsubst set }

bindTv :: TyCoVar -> Type -> UM ()
bindTv tv ty    -- ty is not a variable
  = do  { checkRnEnvR ty -- make sure ty mentions no local variables
        ; b <- tvBindFlag tv
        ; case b of
            Skolem -> maybeApart  -- See Note [Unification with skolems]
            BindMe -> extendTvEnv tv ty
        }

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
                         -> TvSubstEnv          -- substitutions
                         -> UnifyResultM (TvSubstEnv, a) }

instance Functor UM where
      fmap = liftM

instance Applicative UM where
      pure = return
      (<*>) = ap

instance Monad UM where
  return a = UM (\_ _ _ tsubst -> Unifiable (tsubst, a))
  fail _   = UM (\_ _ _ _ -> SurelyApart) -- failed pattern match
  m >>= k  = UM (\tvs rn_env locals tsubst ->
                 case unUM m tvs rn_env locals tsubst of
                   Unifiable (tsubst', v)
                     -> unUM (k v) tvs rn_env locals tsubst'
                   MaybeApart (tsubst', v)
                     -> case unUM (k v) tvs rn_env locals tsubst' of
                          Unifiable result -> MaybeApart result
                          other            -> other
                   SurelyApart -> SurelyApart)

-- TODO (RAE): Is this right?
instance Alternative UM where
  empty = mzero
  (<|>) = mplus

  -- need this instance because of a use of 'guard' above
instance MonadPlus UM where
  mzero = UM (\_ _ _ _ -> SurelyApart)

    -- This function should never be called, but it has a sensible implementation,
    -- so why not?
  mplus m1 m2 = UM (\tvs rn_env locals tsubst ->
                     let res2 = unUM m2 tvs rn_env locals tsubst in
                     case unUM m1 tvs rn_env locals tsubst of
                       res1@(Unifiable _)  -> res1
                       res1@(MaybeApart _) -> case res2 of
                                                  Unifiable _ -> res2
                                                  _           -> res1
                       SurelyApart         -> res2)

initUM :: (TyVar -> BindFlag)
       -> TyCoVarSet  -- set of variables in scope
       -> UM a -> UnifyResultM a
initUM badtvs vars um
  = case unUM um badtvs rn_env emptyVarSet emptyTvSubstEnv of
      Unifiable (_, subst)  -> Unifiable subst
      MaybeApart (_, subst) -> MaybeApart subst
      SurelyApart           -> SurelyApart
  where
    rn_env = mkRnEnv2 (mkInScopeSet vars)

tvBindFlag :: TyVar -> UM BindFlag
tvBindFlag tv = UM $ \tv_fn _ locals tsubst ->
  Unifiable (tsubst, if tv `elemVarSet` locals then Skolem else tv_fn tv)

getTvSubstEnv :: UM TvSubstEnv
getTvSubstEnv = UM $ \_ _ _ tsubst -> Unifiable (tsubst, tsubst)

getTCvSubst :: UM TCvSubst
getTCvSubst = UM $ \_ _ _ tsubst -> Unifiable (tsubst, niFixTCvSubst tsubst)

extendTvEnv :: TyVar -> Type -> UM ()
extendTvEnv tv ty = UM $ \_ _ _ tsubst ->
  Unifiable (extendVarEnv tsubst tv ty, ())

umRnBndr2 :: TyCoVar -> TyCoVar -> UM a -> UM a
umRnBndr2 v1 v2 thing = UM $ \tv_fn rn_env locals tsubst ->
  let (rn_env', v3) = rnBndr2_var rn_env v1 v2
      locals'       = extendVarSetList locals [v1, v2, v3]
  in unUM thing tv_fn rn_env' locals' tsubst

checkRnEnv :: (RnEnv2 -> Var -> Bool) -> Type -> UM ()
checkRnEnv inRnEnv ty = UM $ \_ rn_env _ tsubst ->
  let varset = tyCoVarsOfType ty in
  if any (inRnEnv rn_env) (varSetElems varset)
  then MaybeApart (tsubst, ())
  else Unifiable (tsubst, ())

checkRnEnvR :: Type -> UM ()
checkRnEnvR = checkRnEnv inRnEnvR

checkRnEnvL :: Type -> UM ()
checkRnEnvL = checkRnEnv inRnEnvL

umRnOccL :: TyVar -> UM TyVar
umRnOccL v = UM $ \_ rn_env _ tsubst ->
  Unifiable (tsubst, rnOccL rn_env v)

umRnOccR :: TyVar -> UM TyVar
umRnOccR v = UM $ \_ rn_env _ tsubst ->
  Unifiable (tsubst, rnOccR rn_env v)

umSwapRn :: UM a -> UM a
umSwapRn thing = UM $ \tv_fn rn_env locals tsubst ->
  let rn_env' = rnSwap rn_env in
  unUM thing tv_fn rn_env' locals tsubst

maybeApart :: UM ()
maybeApart = UM (\_ _ _ tsubst -> MaybeApart (tsubst, ()))

surelyApart :: UM a
surelyApart = UM (\_ _ _ _ -> SurelyApart)

{-
%************************************************************************
%*                                                                      *
            Matching a (lifted) type against a coercion
%*                                                                      *
%************************************************************************

This section defines essentially an inverse to liftCoSubst. It is defined
here to avoid a dependency from Coercion on this module.

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

-}

-- | 'liftCoMatch' is sort of inverse to 'liftCoSubst'.  In particular, if
--   @liftCoMatch vars ty co == Just s@, then @tyCoSubst s ty == co@,
--   where @==@ there means that the result of tyCoSubst has the same
--   type as the original co; but may be different under the hood.
--   That is, it matches a type against a coercion of the same
--   "shape", and returns a lifting substitution which could have been
--   used to produce the given coercion from the given type.
--   Note that this function is incomplete -- it might return Nothing
--   when there does indeed exist a possible lifting context.
--
-- This function is incomplete in that it doesn't respect the equality
-- in `eqType`. That is, it's possible that this will succeed for t1 and
-- fail for t2, even when t1 `eqType` t2. That's because it depends on
-- there being a very similar structure between the type and the coercion.
-- This incompleteness shouldn't be all that surprising, especially because
-- it depends on the structure of the coercion, which is a silly thing to do.
--
-- The lifting context produced doesn't have to be exacting in the roles
-- of the mappings. This is because any use of the lifting context will
-- also require a desired role. Thus, this algorithm prefers mapping to
-- nominal coercions where it can do so.
liftCoMatch :: TyCoVarSet -> Type -> Coercion -> Maybe LiftingContext
liftCoMatch tmpls ty co 
  = do { cenv1 <- ty_co_match menv emptyVarEnv ki ki_co ki_ki_co ki_ki_co
       ; cenv2 <- ty_co_match menv cenv1       ty co
                              (mkRepReflCo co_lkind) (mkRepReflCo co_rkind)
       ; return (LC in_scope cenv2) }
  where
    menv     = ME { me_tmpls = tmpls, me_env = mkRnEnv2 in_scope }
    in_scope = mkInScopeSet (tmpls `unionVarSet` tyCoVarsOfCo co)
    -- Like tcMatchTy, assume all the interesting variables 
    -- in ty are in tmpls

    ki       = typeKind ty
    ki_co    = promoteCoercion co
    ki_ki_co = mkRepReflCo liftedTypeKind

    Pair co_lkind co_rkind = coercionKind ki_co

-- | 'ty_co_match' does all the actual work for 'liftCoMatch'.
ty_co_match :: MatchEnv   -- ^ ambient helpful info
            -> LiftCoEnv  -- ^ incoming subst
            -> Type       -- ^ ty, type to match
            -> Coercion   -- ^ co, coercion to match against
            -> Coercion   -- ^ :: kind of L type of substed ty ~R L kind of co
            -> Coercion   -- ^ :: kind of R type of substed ty ~R R kind of co
            -> Maybe LiftCoEnv
ty_co_match menv subst ty co lkco rkco
  | Just ty' <- coreViewOneStarKind ty = ty_co_match menv subst ty' co lkco rkco

  -- handle Refl case:
  | tyCoVarsOfType ty `isNotInDomainOf` subst
  , Just (ty', _) <- isReflCo_maybe co
  , Just _ <- buildCoherenceCoX (me_env menv) ty ty'
  = Just subst

  where
    isNotInDomainOf :: VarSet -> VarEnv a -> Bool
    isNotInDomainOf set env
      = noneSet (\v -> elemVarEnv v env) set

    noneSet :: (Var -> Bool) -> VarSet -> Bool
    noneSet f = foldVarSet (\v rest -> rest && (not $ f v)) True

ty_co_match menv subst ty co lkco rkco
  | CastTy ty' co' <- ty
  = ty_co_match menv subst ty' co (co' `mkTransCo` lkco) (co' `mkTransCo` rkco)

  | CoherenceCo co1 co2 <- co
  = ty_co_match menv subst ty co1 (lkco `mkTransCo` mkSymCo co2) rkco

  | SymCo co' <- co
  = swapLiftCoEnv <$> ty_co_match menv (swapLiftCoEnv subst) ty co' rkco lkco

  -- Match a type variable against a non-refl coercion
ty_co_match menv subst (TyVarTy tv1) co lkco rkco
  | Just (TyCoArg co1') <- lookupVarEnv subst tv1' -- tv1' is already bound to co1
  = if eqCoercionX (nukeRnEnvL rn_env) co1' co
    then Just subst
    else Nothing       -- no match since tv1 matches two different coercions

  | tv1' `elemVarSet` me_tmpls menv           -- tv1' is a template var
  = if any (inRnEnvR rn_env) (varSetElems (tyCoVarsOfCo co))
    then Nothing      -- occurs check failed
    else Just $ extendVarEnv subst tv1' $
                TyCoArg (castCoercionKind co (mkSymCo lkco) (mkSymCo rkco))

  | otherwise
  = Nothing

  where
    rn_env = me_env menv
    tv1' = rnOccL rn_env tv1

  -- just look through SubCo's. We don't really care about roles here.
ty_co_match menv subst ty (SubCo co) lkco rkco
  = ty_co_match menv subst ty co lkco rkco

ty_co_match menv subst (AppTy ty1a ty1b) co _lkco _rkco
  | Just (co2, _, arg2) <- splitAppCo_maybe co     -- c.f. Unify.match on AppTy
  = ty_co_match_app menv subst ty1a ty1b co2 arg2
ty_co_match menv subst ty1 (AppCo co2 _ arg2) _lkco _rkco
  | Just (ty1a, ty1b) <- repSplitAppTy_maybe ty1
  = ty_co_match_app menv subst ty1a ty1b co2 arg2

ty_co_match menv subst (TyConApp tc1 tys) (TyConAppCo _ tc2 cos) _lkco _rkco
  = ty_co_match_tc menv subst tc1 tys tc2 cos
ty_co_match menv subst (ForAllTy (Anon ty1) ty2) (TyConAppCo _ tc cos) _lkco _rkco
  = ty_co_match_tc menv subst funTyCon [ty1, ty2] tc cos

ty_co_match menv subst (ForAllTy (Named tv _) ty)
                       (ForAllCo (ForAllCoBndr co1 tvl tvr m_cv) co)
                       lkco rkco
  = do { subst1 <- ty_co_match menv subst (tyVarKind tv) co1 ki_ki_co ki_ki_co
         -- See Note [Heterogeneous type matching]
       ; let rn_env0 = me_env menv
             (rn_env1, tv')   = rnBndrL rn_env0 tv
             (rn_env2, tvl')  = rnBndrR rn_env1 tvl
             (rn_env3, tvr')  = rnBndrR rn_env2 tvr
             (rn_env4, m_cv') = maybeSecond rnBndrR rn_env3 m_cv
             menv' = menv { me_env = rn_env4 }
             witness = coBndrWitness (mkForAllCoBndr co1 tvl' tvr' m_cv')
             subst2  = extendVarEnv subst1 tv' witness
       ; subst3 <- ty_co_match menv' subst2 ty co lkco rkco
       ; return $ delVarEnv subst3 tv' }
  where
    ki_ki_co = mkRepReflCo liftedTypeKind

ty_co_match _ _ (CoercionTy co) _ _ _
  = pprPanic "ty_co_match" (ppr co)

ty_co_match menv subst ty co lkco rkco
  | Just co' <- pushRefl co = ty_co_match menv subst ty co' lkco rkco
  | otherwise               = Nothing

ty_co_match_tc :: MatchEnv -> LiftCoEnv
               -> TyCon -> [Type]
               -> TyCon -> [CoercionArg]
               -> Maybe LiftCoEnv
ty_co_match_tc menv subst tc1 tys1 tc2 cos2
  = do { guard (tc1 == tc2)
       ; ty_co_match_args menv subst tys1 cos2 lkcos rkcos }
  where
    Pair lkcos rkcos
      = traverse (fmap mkRepReflCo . coercionArgKind) cos2

ty_co_match_app :: MatchEnv -> LiftCoEnv
                -> Type -> Type -> Coercion -> CoercionArg
                -> Maybe LiftCoEnv
ty_co_match_app menv subst ty1a ty1b co2a co2b
  = do { -- TODO (RAE): Remove this exponential behavior.
         subst1 <- ty_co_match menv subst  ki1a ki2a ki_ki_co ki_ki_co
       ; let Pair lkco rkco = mkRepReflCo <$> coercionKind ki2a
       ; subst2 <- ty_co_match menv subst1 ty1a co2a lkco rkco
       ; ty_co_match_arg menv subst2 ty1b co2b
                         (mkNthCo 0 lkco) (mkNthCo 0 rkco) }
  where
    ki1a = typeKind ty1a
    ki2a = promoteCoercion co2a
    ki_ki_co = mkRepReflCo liftedTypeKind

ty_co_match_args :: MatchEnv -> LiftCoEnv -> [Type]
                 -> [CoercionArg] -> [Coercion] -> [Coercion]
                 -> Maybe LiftCoEnv
ty_co_match_args _    subst []       []         _ _ = Just subst
ty_co_match_args menv subst (ty:tys) (arg:args) (lkco:lkcos) (rkco:rkcos)
  = do { subst' <- ty_co_match_arg menv subst ty arg lkco rkco
       ; ty_co_match_args menv subst' tys args lkcos rkcos }
ty_co_match_args _    _     _        _          _ _ = Nothing

ty_co_match_arg :: MatchEnv -> LiftCoEnv -> Type
                -> CoercionArg -> Coercion -> Coercion -> Maybe LiftCoEnv
ty_co_match_arg menv subst ty arg lkco rkco
  | TyCoArg co <- arg
  = ty_co_match menv subst ty co lkco rkco
  | CoercionTy {} <- ty
  , CoCoArg {} <- arg
  = Just subst  -- don't inspect coercions!
  | otherwise
  = pprPanic "ty_co_match_arg" (ppr ty <+> ptext (sLit "<->") <+> ppr arg)

pushRefl :: Coercion -> Maybe Coercion
pushRefl (Refl Nominal (AppTy ty1 ty2))
  = Just (AppCo (Refl Nominal ty1) (Refl Nominal (typeKind ty2))
                                   (mkNomReflCoArg ty2))
pushRefl (Refl r (ForAllTy (Anon ty1) ty2))
  = Just (TyConAppCo r funTyCon [mkReflCoArg r ty1, mkReflCoArg r ty2])
pushRefl (Refl r (TyConApp tc tys))
  = Just (TyConAppCo r tc (zipWith mkReflCoArg (tyConRolesX r tc) tys))
pushRefl (Refl r (ForAllTy (Named tv _) ty))
  = let in_scope = mkInScopeSet $ tyCoVarsOfType ty in
    Just (ForAllCo (mkHomoCoBndr in_scope r tv) (Refl r ty))
pushRefl (Refl r (CastTy ty co))  = Just (castCoercionKind (Refl r ty) co co)
pushRefl _                        = Nothing

