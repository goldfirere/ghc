-- (c) The University of Glasgow 2006

{-# LANGUAGE CPP #-}

module OptCoercion ( optCoercion, checkAxInstCo ) where 

#include "HsVersions.h"

import TyCoRep
import Coercion
import Type hiding( substTyVarBndr, substTy, extendTCvSubst )
import TcType       ( exactTyCoVarsOfType )
import TyCon
import CoAxiom
import Var
import VarSet
import VarEnv
import StaticFlags      ( opt_NoOptCoercion )
import Outputable
import FamInstEnv ( flattenTys )
import Pair
import ListSetOps ( getNth )
import FastString
import Util
import Unify
import InstEnv
import Maybes
import Control.Monad   ( zipWithM )

{-
%************************************************************************
%*                                                                      *
                 Optimising coercions                                                                   
%*                                                                      *
%************************************************************************

Note [ForAllCo case for opt_trans_rule]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Hold onto your hat, because this is messy.

Say we have the following four coercions to hand:

  h1 :: k1 ~ k2
  h2 :: k2 ~ k3
  a1:k1, a2:k2, c1:a1~a2 |- g1 :: s1 ~ s2
  b2:k2, b3:k3, c2:b2~b3 |- g2 :: s2 ~ s3

(The notation suggests, for example, that g1 may mention a1, a2 or c1.)

If we put these coercions in appropriate quantifiers, we get these facts:

  forall_h1 (a1:k1, a2:k2, c1:a1~a2). g1 :: forall a1:k1.s1 ~ forall a2:k2.s2
  forall_h2 (b2:k2, b3:k3, c2:b2~b3). g2 :: forall b2:k2.s2 ~ forall b3:k3.s3

Then, the following transitivity coercion is well-formed, noting that
types are equal up to alpha-equivalence:

  forall (a1:k1, a2:k2, c1:a1~a2). g1 ; forall (b2:k2, b3:k3, c2:b2~b3). g2
    :: forall a1:k1.s1 ~ forall b3:k3.s3

How can we push the transitivity inside the forall? Well, the quantifier
would have to look like

  forall_(h1;h2) (a1:k1, b3:k3, c3:a1~b3). ...

So, we will need to find a way to substitute the a2, c1, b2, and c2 variables.
As usual, the types tell us the answer:

  a2 has to be something with kind k2:
    [a2 |-> b3 |> sym h2]
  c1 has to be a coercion from a1 to the new a2:
    [c1 |-> c3 `mkCoherenceRightCo` sym h2]
  b2 has to be something with kind k2:
    [b2 |-> a1 |> h1]
  c2 has to be a coercion from the new b2 to b3:
    [c2 |-> c3 `mkCoherenceLeftCo` h1]

Note [Sym and InstCo]
~~~~~~~~~~~~~~~~~~~~~
We wish to simplify the following:

sym ((forall_h (a1:k1, a2:k2, c:a1~a2). g1)@g2)

Let g2 : s1 ~ s2. Then, the simplification is this:

sym (g1[a1 |-> s1, a2 |-> s2, c |-> g2])

Note that g2 does *not* have sym applied.

Note [Optimising coercion optimisation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Looking up a coercion's role or kind is linear in the size of the
coercion. Thus, doing this repeatedly during the recursive descent
of coercion optimisation is disastrous. We must be careful to avoid
doing this if at all possible.

Because it is generally easy to know a coercion's components' roles
from the role of the outer coercion, we pass down the known role of
the input in the algorithm below. We also keep functions opt_co2
and opt_co3 separate from opt_co4, so that the former two do Phantom
checks that opt_co4 can avoid. This is a big win because Phantom coercions
rarely appear within non-phantom coercions -- only in some TyConAppCos
and some AxiomInstCos. We handle these cases specially by calling
opt_co2.
-}

optCoercion :: TCvSubst -> Coercion -> NormalCo
-- ^ optCoercion applies a substitution to a coercion, 
--   *and* optimises it to reduce its size
optCoercion env co 
  | opt_NoOptCoercion = substCo env co
  | debugIsOn         = let out_co = opt_co1 env False co
                            Pair in_ty1  in_ty2  = coercionKind co
                            Pair out_ty1 out_ty2 = coercionKind out_co
                        in
                        ASSERT2( substTy env in_ty1 `eqType` out_ty1 &&
                                 substTy env in_ty2 `eqType` out_ty2
                               , text "optCoercion changed types!"
                              $$ hang (text "in_co:") 2 (ppr co)
                              $$ hang (text "in_ty1:") 2 (ppr in_ty1)
                              $$ hang (text "in_ty2:") 2 (ppr in_ty2)
                              $$ hang (text "out_co:") 2 (ppr out_co)
                              $$ hang (text "out_ty1:") 2 (ppr out_ty1)
                              $$ hang (text "out_ty2:") 2 (ppr out_ty2)
                              $$ hang (text "subst:") 2 (ppr env) )
                        out_co
  | otherwise         = opt_co1 env False co

type NormalCo    = Coercion
type NormalCoArg = CoercionArg
  -- Invariants: 
  --  * The substitution has been fully applied
  --  * For trans coercions (co1 `trans` co2)
  --       co1 is not a trans, and neither co1 nor co2 is identity

type NormalNonIdCo = NormalCo  -- Extra invariant: not the identity

-- | Do we apply a @sym@ to the result?
type SymFlag = Bool

-- | Do we force the result to be representational?
type ReprFlag = Bool

-- | Optimize a coercion, making no assumptions.
opt_co1 :: TCvSubst
        -> SymFlag
        -> Coercion -> NormalCo
opt_co1 env sym co = opt_co2 env sym (coercionRole co) co
{-
opt_co env sym co
 = pprTrace "opt_co {" (ppr sym <+> ppr co $$ ppr env) $
   co1 `seq`
   pprTrace "opt_co done }" (ppr co1) $
   (WARN( not same_co_kind, ppr co  <+> dcolon <+> ppr (coercionType co)
                         $$ ppr co1 <+> dcolon <+> ppr (coercionType co1) )
    WARN( not (coreEqCoercion co1 simple_result),
           (text "env=" <+> ppr env) $$
           (text "input=" <+> ppr co) $$
           (text "simple=" <+> ppr simple_result) $$
           (text "opt=" <+> ppr co1) )
   co1)
 where
   co1 = opt_co' env sym co
   same_co_kind = s1 `eqType` s2 && t1 `eqType` t2
   Pair s t = coercionKind (substCo env co)
   (s1,t1) | sym = (t,s)
           | otherwise = (s,t)
   Pair s2 t2 = coercionKind co1

   simple_result | sym = mkSymCo (substCo env co)
                 | otherwise = substCo env co
-}

-- See Note [Optimising coercion optimisation]
-- | Optimize a coercion, knowing the coercion's role. No other assumptions.
opt_co2 :: TCvSubst
        -> SymFlag
        -> Role   -- ^ The role of the input coercion
        -> Coercion -> NormalCo
opt_co2 env sym Phantom co = opt_phantom env sym co
opt_co2 env sym r       co = opt_co3 env sym Nothing r co

-- | Like 'opt_co2' but for 'CoercionArg'
opt_co_arg2 :: TCvSubst
            -> SymFlag
            -> Role   -- ^ The role of the input coercion
            -> CoercionArg -> NormalCoArg
opt_co_arg2 env sym r (TyCoArg co) = TyCoArg $ opt_co2 env sym r co
opt_co_arg2 env sym r (CoCoArg _r h co1 co2)
  = ASSERT( r == _r )
    opt_cocoarg env sym r h co1 co2

-- See Note [Optimising coercion optimisation]
-- | Optimize a coercion, knowing the coercion's non-Phantom role.
opt_co3 :: TCvSubst -> SymFlag -> Maybe Role -> Role -> Coercion -> NormalCo
opt_co3 env sym (Just Phantom)          _ co = opt_phantom env sym co
opt_co3 env sym (Just Representational) r co = opt_co4_wrap env sym True  r co
  -- if mrole is Just Nominal, that can't be a downgrade, so we can ignore
opt_co3 env sym _                       r co = opt_co4_wrap env sym False r co

-- | Like 'opt_co3' but for 'CoercionArg'
opt_co_arg3 :: TCvSubst -> SymFlag -> Maybe Role -> Role
            -> CoercionArg -> NormalCoArg
opt_co_arg3 env sym mrole r (TyCoArg co) = TyCoArg $ opt_co3 env sym mrole r co
opt_co_arg3 env sym mrole r (CoCoArg _r h co1 co2)
  = ASSERT( r == _r )
    opt_cocoarg env sym (mrole `orElse` r) h co1 co2

-- See Note [Optimising coercion optimisation]
-- | Optimize a non-phantom coercion.
opt_co4, opt_co4_wrap :: TCvSubst -> SymFlag -> ReprFlag -> Role -> Coercion -> NormalCo

opt_co4_wrap = opt_co4
{-
opt_co4_wrap env sym rep r co
  = pprTrace "opt_co4_wrap"
    ( vcat [ text "Sym:" <+> ppr sym
           , text "Rep:" <+> ppr rep
           , text "Role:" <+> ppr r
           , text "Co:" <+> ppr co ]) $
    ASSERT( r == coercionRole co )
    opt_co4 env sym rep r co
-}

opt_co4 env _   rep r (Refl _r ty)
  = ASSERT2( r == _r, text "Expected role:" <+> ppr r $$
                      text "Found role:" <+> ppr _r   $$
                      text "Type:" <+> ppr ty )
    Refl (chooseRole rep r) (substTy env ty)

opt_co4 env sym rep r (SymCo co)  = opt_co4_wrap env (not sym) rep r co

opt_co4 env sym rep r g@(TyConAppCo _r tc cos)
  = ASSERT( r == _r )
    case (rep, r) of
      (True, Nominal) ->
        mkTyConAppCo Representational tc
                     (zipWith3 (opt_co_arg3 env sym)
                               (map Just (tyConRolesX Representational tc))
                               (repeat Nominal)
                               cos)
      (False, Nominal) ->
        mkTyConAppCo Nominal tc (map (opt_co_arg4 env sym False Nominal) cos)
      (_, Representational) ->
                      -- must use opt_co2 here, because some roles may be P
                      -- See Note [Optimising coercion optimisation]
        mkTyConAppCo r tc (zipWith (opt_co_arg2 env sym)
                                   (tyConRolesX r tc)  -- the current roles
                                   cos)
      (_, Phantom) -> pprPanic "opt_co4 sees a phantom!" (ppr g)

opt_co4 env sym rep r (AppCo co1 h co2)
  = mkAppCo (opt_co4_wrap env sym rep r co1)
            (opt_co4_wrap env sym rep r h)
            (opt_co_arg4 env sym False Nominal co2)

-- See Note [Sym and ForAllCo] in TyCoRep
opt_co4 env sym rep r (ForAllCo cobndr co)
  = case optForAllCoBndr env sym cobndr of
      (env', cobndr') -> mkForAllCo cobndr' (opt_co4_wrap env' sym rep r co)
     -- Use the "mk" functions to check for nested Refls

opt_co4 env sym rep r (CoVarCo cv)
  | Just co <- lookupCoVar env cv
  = opt_co4_wrap (zapTCvSubst env) sym rep r co

  | Just cv1 <- lookupInScope (getTCvInScope env) cv
  = ASSERT( isCoVar cv1 ) wrapRole rep r $ wrapSym sym (CoVarCo cv1)
                -- cv1 might have a substituted kind!

  | otherwise = WARN( True, ptext (sLit "opt_co: not in scope:") <+> ppr cv $$ ppr env)
                ASSERT( isCoVar cv )
                wrapRole rep r $ wrapSym sym (CoVarCo cv)

opt_co4 env sym rep r (AxiomInstCo con ind cos)
    -- Do *not* push sym inside top-level axioms
    -- e.g. if g is a top-level axiom
    --   g a : f a ~ a
    -- then (sym (g ty)) /= g (sym ty) !!
  = ASSERT( r == coAxiomRole con )
    wrapRole rep (coAxiomRole con) $
    wrapSym sym $
                       -- some sub-cos might be P: use opt_co2
                       -- See Note [Optimising coercion optimisation]
    AxiomInstCo con ind (zipWith (opt_co_arg2 env False)
                                 (coAxBranchRoles (coAxiomNthBranch con ind))
                                 cos)
      -- Note that the_co does *not* have sym pushed into it

-- TODO (RAE): After merging with new OptCoercion, actually make this work
-- better.
opt_co4 env sym _ r (PhantomCo h t1 t2)
  = ASSERT( r == Phantom )
    PhantomCo (opt_co4 env sym False Representational h) a' b'
  where
    (a, b) = if sym then (t2, t1) else (t1, t2)
    a' = substTy env a
    b' = substTy env b

opt_co4 env sym rep r (UnsafeCo s _r oty1 oty2)
  = ASSERT( r == _r )
    opt_unsafe env s (chooseRole rep r) (substTy env a) (substTy env b)
  where
    (a,b) = if sym then (oty2,oty1) else (oty1,oty2)

opt_co4 env sym rep r (TransCo co1 co2)
                      -- sym (g `o` h) = sym h `o` sym g
  | sym       = opt_trans in_scope co2' co1'
  | otherwise = opt_trans in_scope co1' co2'
  where
    co1' = opt_co4_wrap env sym rep r co1
    co2' = opt_co4_wrap env sym rep r co2
    in_scope = getTCvInScope env


opt_co4 env sym rep r co@(NthCo {}) = opt_nth_co env sym rep r co

opt_co4 env sym rep r g@(LRCo lr co)
  | Just pr_co <- splitAppCo_maybe co
  = ASSERT( r == Nominal )
    opt_co4_wrap env sym rep Nominal (pick_lr lr pr_co)
  | Just pr_co <- splitAppCo_maybe co'
  = ASSERT( r == Nominal )
    if rep
    then opt_co4_wrap (zapTCvSubst env) False True Nominal (pick_lr lr pr_co)
    else pick_lr lr pr_co
  | otherwise
  = wrapRole rep Nominal $ LRCo lr co'
  where
    co' = opt_co4_wrap env sym False Nominal co

    pick_lr CLeft  (l, _, _)         = l
    pick_lr CRight (_, _, TyCoArg r) = r
    pick_lr _      _                 = pprPanic "opt_co(LRCo)" (ppr g)

opt_co4 env sym rep r (InstCo co1 arg)
    -- forall over type...
  | TyCoArg co2 <- arg'
  , Just (tv1, tv2, cv, co_body) <- splitForAllCo_Ty_maybe co1
  , Pair ty1 ty2 <- coercionKind co2
  = opt_co4_wrap (extendTCvSubstList env 
              [tv1, tv2, cv]
              [ty1, ty2, mkCoercionTy co2])
              -- See Note [Sym and InstCo]
            sym rep r co_body

    -- forall over coercion...
  | CoCoArg _ _ co2 co3 <- arg'
  , Just (cv1, cv2, co_body) <- splitForAllCo_Co_maybe co1
  = opt_co4_wrap (extendTCvSubstList env [cv1, cv2] (map mkCoercionTy [co2, co3]))
            sym rep r co_body

    -- See if it is a forall after optimization
    -- If so, do an inefficient one-variable substitution, then re-optimize
  
    -- forall over type...
  | TyCoArg co2' <- arg'
  , Just (tv1', tv2', cv', co'_body) <- splitForAllCo_Ty_maybe co1'
  , Pair ty1' ty2' <- coercionKind co2'
  = opt_co4_wrap (extendTCvSubstList (zapTCvSubst env)
                               [tv1', tv2', cv']
                               [ty1', ty2', mkCoercionTy co2'])
            False False r' co'_body

 -- forall over coercion...
  | CoCoArg _ _ co2' co3' <- arg'
  , Just (cv1', cv2', co'_body) <- splitForAllCo_Co_maybe co1'
  = opt_co4_wrap (extendTCvSubstList (zapTCvSubst env)
                                [cv1', cv2']
                                [CoercionTy co2', CoercionTy co3'])
           False False r' co'_body 

  | otherwise = InstCo co1' arg'
  where
    co1' = opt_co4_wrap env sym rep r co1
    r'   = chooseRole rep r
    arg' = opt_co_arg4 env sym False Nominal arg

-- TODO (RAE): Should this interact with PhantomCo?
opt_co4 env sym rep r (CoherenceCo co1 co2)
  | UnsafeCo s _r tyl1 tyr1 <- co1
  = ASSERT( r == _r )
    opt_co4_wrap env sym False output_role (mkUnsafeCo s output_role
                                                (mkCastTy tyl1 co2) tyr1)
  | TransCo col1 cor1 <- co1
  = opt_co4_wrap env sym rep r (mkTransCo (mkCoherenceCo col1 co2) cor1)

  | UnsafeCo s r_out tyl1' tyr1' <- co1'
  = ASSERT( output_role == r_out )
    if sym then mkUnsafeCo s r_out tyl1' (mkCastTy tyr1' co2')
           else mkUnsafeCo s r_out (mkCastTy tyl1' co2') tyr1'
  | TransCo col1' cor1' <- co1'
  = if sym then opt_trans in_scope col1'
                  (optCoercion (zapTCvSubst env) (mkCoherenceRightCo cor1' co2'))
           else opt_trans in_scope (mkCoherenceCo col1' co2') cor1'

  | otherwise
  = wrapSym sym $ CoherenceCo (opt_co4_wrap env False rep r co1) co2'
  where output_role = chooseRole rep r
        co1' = opt_co4_wrap env sym   rep   r                co1
        co2' = opt_co4_wrap env False False Representational co2
        in_scope = getTCvInScope env

opt_co4 env sym _rep r (KindCo co)
  = ASSERT( r == Representational )
    let kco' = promoteCoercion co in
    case kco' of
      KindCo co' -> promoteCoercion (opt_co1 env sym co')
      _          -> opt_co4_wrap env sym False Representational kco'
  -- This might be able to be optimized more to do the promotion
  -- and substitution/optimization at the same time

opt_co4 env sym rep r (KindAppCo co)
-- TODO (RAE): Actually optimize this!
  = mkKindAppCo (opt_co4_wrap env sym rep r co)

opt_co4 env sym _ r (SubCo co)
  = ASSERT( r == Representational )
    opt_co4_wrap env sym True Nominal co

-- XXX: We could add another field to CoAxiomRule that
-- would allow us to do custom simplifications.
opt_co4 env sym rep r (AxiomRuleCo co ts cs)
  = ASSERT( r == coaxrRole co )
    wrapRole rep r $
    wrapSym sym $
    AxiomRuleCo co (map (substTy env) ts)
                   (zipWith (opt_co2 env False) (coaxrAsmpRoles co) cs)
-------------
opt_co_arg4 :: TCvSubst -> SymFlag -> ReprFlag -> Role
            -> CoercionArg -> NormalCoArg
opt_co_arg4 env sym rep r (TyCoArg co) = TyCoArg $ opt_co4_wrap env sym rep r co
opt_co_arg4 env sym rep r (CoCoArg _r h co1 co2)
  = ASSERT( r == _r )
    opt_cocoarg env sym (chooseRole rep r) h co1 co2

-- | Optimize a "coercion" between coercions.
opt_cocoarg :: TCvSubst
            -> SymFlag
            -> Role   -- ^ desired role
            -> Coercion
            -> Coercion
            -> Coercion
            -> NormalCoArg
opt_cocoarg env sym r h co1 co2
  = if sym
    then CoCoArg r h' co2' co1'
    else CoCoArg r h' co1' co2'
  where
    h'   = opt_co4_wrap env sym False Representational h
    co1' = opt_co1 env False co1
    co2' = opt_co1 env False co2

-------------
-- | Optimize a phantom coercion. The input coercion may not necessarily
-- be a phantom, but the output sure will be.
opt_phantom :: TCvSubst -> SymFlag -> Coercion -> NormalCo
  -- TODO (RAE): This is terrible. Write properly.
opt_phantom env sym co
  = if sym
    then mkPhantomCo (mkKindCo (mkSymCo (substCo env co))) ty2' ty1'
    else mkPhantomCo (mkKindCo (substCo env co)) ty1' ty2'
  where
    Pair ty1 ty2 = coercionKind co
    ty1' = substTy env ty1
    ty2' = substTy env ty2

opt_unsafe :: TCvSubst -> FastString -> Role -> Type -> Type -> Coercion
opt_unsafe env prov role oty1 oty2
  | Just (tc1, tys1) <- splitTyConApp_maybe oty1
  , Just (tc2, tys2) <- splitTyConApp_maybe oty2
  , tc1 == tc2
  = mkTyConAppCo role tc1 (zipWith3 (opt_unsafe_arg env prov) (tyConRolesX role tc1) tys1 tys2)

  | Just (l1, r1) <- splitAppTy_maybe oty1
  , Just (l2, r2) <- splitAppTy_maybe oty2
  = let role' = if role == Phantom then Phantom else Nominal in
       -- role' is to comform to mkAppCo's precondition
    mkAppCo (opt_unsafe env prov role l1 l2)
               -- TODO (RAE): Make more efficient
            (opt_unsafe env prov role (typeKind r1) (typeKind r2))
            (opt_unsafe_arg env prov role' r1 r2)

  | Just (bndr1, ty1) <- splitForAllTy_maybe oty1
  , Just tv1          <- binderVar_maybe bndr1
  , Just (bndr2, ty2) <- splitForAllTy_maybe oty2
  , Just tv2          <- binderVar_maybe bndr2
  , isTyVar tv1 == isTyVar tv2   -- rule out weird UnsafeCo
  , let k1 = tyVarKind tv1
        k2 = tyVarKind tv2
  = let eta = opt_unsafe env prov role k1 k2
        cobndr
          | isTyVar tv1 = let c = mkFreshCoVar (getTCvInScope env)
                                               (mkOnlyTyVarTy tv1)
                                               (mkOnlyTyVarTy tv2) in
                          mkForAllCoBndr eta tv1 tv2 (Just c)
          | otherwise   = mkForAllCoBndr eta tv1 tv2 Nothing
    in
    mkForAllCo cobndr (opt_unsafe env prov role ty1 ty2)

  | otherwise
  = mkUnsafeCo prov role oty1 oty2

opt_unsafe_arg :: TCvSubst -> FastString -> Role -> Type -> Type -> CoercionArg
opt_unsafe_arg env prov role oty1 oty2
  | Just co1 <- isCoercionTy_maybe oty1
  , Just co2 <- isCoercionTy_maybe oty2
  = let co1' = opt_co1 env False co1
        co2' = opt_co1 env False co2
        kco = opt_unsafe (zapTCvSubst env) prov Representational
                         (coercionType co1') (coercionType co2')
    in CoCoArg role kco co1' co2'
opt_unsafe_arg env prov role oty1 oty2
  = TyCoArg $ opt_unsafe env prov role oty1 oty2

-------------
-- NthCo must be handled separately, because it's the one case where we can't
-- tell quickly what the component coercion's role is from the containing
-- coercion. To avoid repeated coercionRole calls as opt_co1 calls opt_co2,
-- we just look for nested NthCo's, which can happen in practice.
opt_nth_co :: TCvSubst -> SymFlag -> ReprFlag -> Role -> Coercion -> NormalCo
opt_nth_co env sym rep r = go []
  where
    go ns (NthCo n co) = go (n:ns) co
      -- previous versions checked if the tycon is decomposable. This
      -- is redundant, because a non-decomposable tycon under an NthCo
      -- is entirely bogus. See docs/core-spec/core-spec.pdf.
    go ns co
      = opt_nths ns co

      -- try to resolve 1 Nth
    push_nth n (Refl r1 ty)
      | Just (tc, args) <- splitTyConApp_maybe ty
      = Just (Refl (nthRole r1 tc n) (args `getNth` n))
      | n == 0
      , Just (bndr, _) <- splitForAllTy_maybe ty
      , Just tv        <- binderVar_maybe bndr
      = Just (Refl r1 (tyVarKind tv))
    push_nth n (TyConAppCo _ _ cos)
      = Just (stripTyCoArg $ cos `getNth` n)
    push_nth 0 (ForAllCo (ForAllCoBndr eta _ _ _) _)
      = Just eta
    push_nth _ _ = Nothing

      -- input coercion is *not* yet sym'd or opt'd
    opt_nths [] co = opt_co4_wrap env sym rep r co
    opt_nths (n:ns) co
      | Just co' <- push_nth n co
      = opt_nths ns co'

      -- here, the co isn't a TyConAppCo, so we opt it, hoping to get
      -- a TyConAppCo as output. We don't know the role, so we use
      -- opt_co1. This is slightly annoying, because opt_co1 will call
      -- coercionRole, but as long as we don't have a long chain of
      -- NthCo's interspersed with some other coercion former, we should
      -- be OK.
    opt_nths ns co = opt_nths' ns (opt_co1 env sym co)

      -- input coercion *is* sym'd and opt'd
    opt_nths' [] co
      = if rep && (r == Nominal)
            -- propagate the SubCo:
        then opt_co4_wrap (zapTCvSubst env) False True r co
        else co
    opt_nths' (n:ns) co
      | Just co' <- push_nth n co
      = opt_nths' ns co'
    opt_nths' ns co = wrapRole rep r (mk_nths ns co)

    mk_nths [] co = co
    mk_nths (n:ns) co = mk_nths ns (mkNthCo n co)

-------------
opt_transList :: InScopeSet -> [NormalCoArg] -> [NormalCoArg] -> [NormalCoArg]
opt_transList is = zipWith (opt_trans_arg is)
  where
    opt_trans_arg is (TyCoArg co1) (TyCoArg co2) = TyCoArg (opt_trans is co1 co2)
    opt_trans_arg _  (CoCoArg r hl col1 _col2) (CoCoArg _r hr _cor1 cor2)
      = ASSERT( coercionType _col2 `eqType` coercionType _cor1 )
        ASSERT( r == _r )
        CoCoArg r (opt_trans is hl hr) col1 cor2
    opt_trans_arg _ arg1 arg2 = pprPanic "opt_trans_arg" (ppr arg1 <+> semi <+> ppr arg2)

opt_trans :: InScopeSet -> NormalCo -> NormalCo -> NormalCo
opt_trans is co1 co2
  | isReflCo co1 = co2
  | otherwise    = opt_trans1 is co1 co2

opt_trans_arg :: InScopeSet -> NormalCoArg -> NormalCoArg -> NormalCoArg
opt_trans_arg is arg1 arg2
  | isReflLike arg1 = arg2
  | otherwise       = opt_trans_arg1 is arg1 arg2

opt_trans1 :: InScopeSet -> NormalNonIdCo -> NormalCo -> NormalCo
-- First arg is not the identity
opt_trans1 is co1 co2
  | isReflCo co2 = co1
  | otherwise    = opt_trans2 is co1 co2

opt_trans_arg1 :: InScopeSet -> NormalCoArg -> NormalCoArg -> NormalCoArg
opt_trans_arg1 is arg1 arg2
  | isReflLike arg2 = arg1
  | otherwise       = opt_trans_arg2 is arg1 arg2

opt_trans2 :: InScopeSet -> NormalNonIdCo -> NormalNonIdCo -> NormalCo
-- Neither arg is the identity
opt_trans2 is (TransCo co1a co1b) co2
    -- Don't know whether the sub-coercions are the identity
  = opt_trans is co1a (opt_trans is co1b co2)  

opt_trans2 is co1 co2 
  | Just co <- opt_trans_rule is co1 co2
  = co

opt_trans2 is co1 (TransCo co2a co2b)
  | Just co1_2a <- opt_trans_rule is co1 co2a
  = if isReflCo co1_2a
    then co2b
    else opt_trans1 is co1_2a co2b

opt_trans2 _ co1 co2
  = mkTransCo co1 co2

opt_trans_arg2 :: InScopeSet -> NormalCoArg -> NormalCoArg -> NormalCoArg
opt_trans_arg2 is (TyCoArg co1) (TyCoArg co2) = TyCoArg (opt_trans2 is co1 co2)
opt_trans_arg2 is (CoCoArg r h1 col1 _cor1) (CoCoArg _r h2 _col2 cor2)
  = ASSERT( coercionType _cor1 `eqType` coercionType _col2 )
    ASSERT( r == _r )
    CoCoArg r (opt_trans2 is h1 h2) col1 cor2
opt_trans_arg2 _ arg1 arg2 = pprPanic "opt_trans_arg2" (ppr arg1 <+> semi <+> ppr arg2)

------
-- Optimize coercions with a top-level use of transitivity.
opt_trans_rule :: InScopeSet -> NormalNonIdCo -> NormalNonIdCo -> Maybe NormalCo

-- Push transitivity through matching destructors
opt_trans_rule is in_co1@(NthCo d1 co1) in_co2@(NthCo d2 co2)
  | d1 == d2
  , co1 `compatible_co` co2
  = fireTransRule "PushNth" in_co1 in_co2 $
    mkNthCo d1 (opt_trans is co1 co2)

opt_trans_rule is in_co1@(LRCo d1 co1) in_co2@(LRCo d2 co2)
  | d1 == d2
  , co1 `compatible_co` co2
  = fireTransRule "PushLR" in_co1 in_co2 $
    mkLRCo d1 (opt_trans is co1 co2)

-- Push transitivity inside instantiation
opt_trans_rule is in_co1@(InstCo co1 ty1) in_co2@(InstCo co2 ty2)
  | ty1 `eqCoercionArg` ty2
  , co1 `compatible_co` co2
  = fireTransRule "TrPushInst" in_co1 in_co2 $
    mkInstCo (opt_trans is co1 co2) ty1
 
-- Push transitivity down through matching top-level constructors.
opt_trans_rule is in_co1@(TyConAppCo r1 tc1 cos1) in_co2@(TyConAppCo r2 tc2 cos2)
  | tc1 == tc2 
  = ASSERT( r1 == r2 )
    fireTransRule "PushTyConApp" in_co1 in_co2 $
    mkTyConAppCo r1 tc1 (opt_transList is cos1 cos2)

opt_trans_rule is in_co1@(AppCo co1a h1 co1b) in_co2@(AppCo co2a h2 co2b)
  = fireTransRule "TrPushApp" in_co1 in_co2 $
    mkAppCo (opt_trans     is co1a co2a)
            (opt_trans     is h1   h2)
            (opt_trans_arg is co1b co2b)

-- Eta rules
opt_trans_rule is co1@(TyConAppCo r tc cos1) co2
  | Just cos2 <- etaTyConAppCo_maybe tc co2
  = ASSERT( length cos1 == length cos2 )
    fireTransRule "EtaCompL" co1 co2 $
    mkTyConAppCo r tc (opt_transList is cos1 cos2)

opt_trans_rule is co1 co2@(TyConAppCo r tc cos2)
  | Just cos1 <- etaTyConAppCo_maybe tc co1
  = ASSERT( length cos1 == length cos2 )
    fireTransRule "EtaCompR" co1 co2 $
    mkTyConAppCo r tc (opt_transList is cos1 cos2)

opt_trans_rule is co1@(AppCo co1a h1 co1b) co2
  | Just (co2a,h2,co2b) <- etaAppCo_maybe co2
  = fireTransRule "EtaAppL" co1 co2 $
    mkAppCo (opt_trans     is co1a co2a)
            (opt_trans     is h1   h2)
            (opt_trans_arg is co1b co2b)

opt_trans_rule is co1 co2@(AppCo co2a h2 co2b)
  | Just (co1a,h1,co1b) <- etaAppCo_maybe co1
  = fireTransRule "EtaAppR" co1 co2 $
    mkAppCo (opt_trans     is co1a co2a)
            (opt_trans     is h1   h2)
            (opt_trans_arg is co1b co2b)

-- Push transitivity inside forall
opt_trans_rule is co1 co2
  | Just (cobndr1,r1) <- splitForAllCo_maybe co1
  , Just (cobndr2,r2) <- etaForAllCo_maybe is co2
  = push_trans cobndr1 r1 cobndr2 r2

  | Just (cobndr2,r2) <- splitForAllCo_maybe co2
  , Just (cobndr1,r1) <- etaForAllCo_maybe is co1
  = push_trans cobndr1 r1 cobndr2 r2

  where
  role   = coercionRole co1
  to_rep = downgradeRole Representational role
    
  push_trans (ForAllCoBndr col tvl1 tvl2 m_cvl) r1
             (ForAllCoBndr cor tvr1 tvr2 m_cvr) r2
    | Phantom <- role
       -- abort. We need to use some coercions to cast, and we can't
       -- if we're at a Phantom role.
    = WARN( True, ppr co1 $$ ppr co2 )
      Nothing

      -- See Note [ForAllCo case for opt_trans_rule]
    | (Just cvl, Just cvr) <- (m_cvl, m_cvr)
    = -- kinds of tvl2 and tvr1 must be equal
      let cv       = mkFreshCoVar is (mkOnlyTyVarTy tvl1) (mkOnlyTyVarTy tvr2)
          new_tvl2 = mkCastTy (mkOnlyTyVarTy tvr2) (to_rep $ mkSymCo cor)
          new_cvl  = mkCoherenceRightCo (mkCoVarCo cv) (mkSymCo cor)
          new_tvr1 = mkCastTy (mkOnlyTyVarTy tvl1) (to_rep col)
          new_cvr  = mkCoherenceLeftCo  (mkCoVarCo cv) (col)
          empty    = mkEmptyTCvSubst is'
          subst_r1 = extendTCvSubstList empty [tvl2, cvl] [new_tvl2, mkCoercionTy new_cvl]
          subst_r2 = extendTCvSubstList empty [tvr1, cvr] [new_tvr1, mkCoercionTy new_cvr]
          r1' = optCoercion subst_r1 r1
          r2' = optCoercion subst_r2 r2
          is' = is `extendInScopeSetList` [tvl1, tvl2, cvl, tvr1, tvr2, cvr, cv]
      in
      fireTransRule "EtaAllTy" co1 co2 $
      mkForAllCo (mkForAllCoBndr (opt_trans2 is col cor) tvl1 tvr2 (Just cv))
                 (opt_trans is' r1' r2')

    | otherwise
    = let new_tvl2 = (mkNthCo 2 cor) `mkTransCo`
                     (mkCoVarCo tvr2) `mkTransCo`
                     (mkNthCo 3 $ mkSymCo cor)
          new_tvr1 = (mkNthCo 2 (mkSymCo col)) `mkTransCo`
                     (mkCoVarCo tvl1) `mkTransCo`
                     (mkNthCo 3 col)
          empty    = mkEmptyTCvSubst is'
          subst_r1 = extendTCvSubst empty tvl2 (mkCoercionTy new_tvl2)
          subst_r2 = extendTCvSubst empty tvr1 (mkCoercionTy new_tvr1)
          r1'      = optCoercion subst_r1 r1
          r2'      = optCoercion subst_r2 r2
          is'      = is `extendInScopeSetList` [tvl1, tvl2, tvr1, tvr2]
      in
      fireTransRule "EtaAllCo" co1 co2 $
      mkForAllCo (mkForAllCoBndr (opt_trans2 is col cor) tvl1 tvr2 Nothing)
                 (opt_trans is' r1' r2')

-- Push transitivity inside axioms
opt_trans_rule is co1 co2

  -- See Note [Why call checkAxInstCo during optimisation]
  -- TrPushSymAxR
  | Just (sym, con, ind, cos1) <- co1_is_axiom_maybe
  , True <- sym
  , Just cos2 <- matchAxiom sym con ind co2
  , let newAxInst = AxiomInstCo con ind (opt_transList is (map mkSymCoArg cos2) cos1)
  , Nothing <- checkAxInstCo newAxInst
  = fireTransRule "TrPushSymAxR" co1 co2 $ SymCo newAxInst

  -- TrPushAxR
  | Just (sym, con, ind, cos1) <- co1_is_axiom_maybe
  , False <- sym
  , Just cos2 <- matchAxiom sym con ind co2
  , let newAxInst = AxiomInstCo con ind (opt_transList is cos1 cos2)
  , Nothing <- checkAxInstCo newAxInst
  = fireTransRule "TrPushAxR" co1 co2 newAxInst

  -- TrPushSymAxL
  | Just (sym, con, ind, cos2) <- co2_is_axiom_maybe
  , True <- sym
  , Just cos1 <- matchAxiom (not sym) con ind co1
  , let newAxInst = AxiomInstCo con ind (opt_transList is cos2 (map mkSymCoArg cos1))
  , Nothing <- checkAxInstCo newAxInst
  = fireTransRule "TrPushSymAxL" co1 co2 $ SymCo newAxInst

  -- TrPushAxL  
  | Just (sym, con, ind, cos2) <- co2_is_axiom_maybe
  , False <- sym
  , Just cos1 <- matchAxiom (not sym) con ind co1
  , let newAxInst = AxiomInstCo con ind (opt_transList is cos1 cos2)
  , Nothing <- checkAxInstCo newAxInst
  = fireTransRule "TrPushAxL" co1 co2 newAxInst

  -- TrPushAxSym/TrPushSymAx
  | Just (sym1, con1, ind1, cos1) <- co1_is_axiom_maybe
  , Just (sym2, con2, ind2, cos2) <- co2_is_axiom_maybe
  , con1 == con2
  , ind1 == ind2
  , sym1 == not sym2
  , let branch = coAxiomNthBranch con1 ind1
        qtvs = coAxBranchTyCoVars branch
        lhs  = coAxNthLHS con1 ind1
        rhs  = coAxBranchRHS branch
        pivot_tvs = exactTyCoVarsOfType (if sym2 then rhs else lhs)
  , all (`elemVarSet` pivot_tvs) qtvs
  = fireTransRule "TrPushAxSym" co1 co2 $
    if sym2
       -- TrPushAxSym
    then liftCoSubstWith role qtvs (opt_transList is cos1 (map mkSymCoArg cos2)) lhs
       -- TrPushSymAx
    else liftCoSubstWith role qtvs (opt_transList is (map mkSymCoArg cos1) cos2) rhs
  where
    co1_is_axiom_maybe = isAxiom_maybe co1
    co2_is_axiom_maybe = isAxiom_maybe co2
    role = coercionRole co1 -- should be the same as coercionRole co2!

opt_trans_rule is co1 co2
  | Just (lco, lh) <- isCohRight_maybe co1
  , Just (rco, rh) <- isCohLeft_maybe co2
  , (coercionType lh) `eqType` (coercionType rh)
  = opt_trans_rule is lco rco

opt_trans_rule _ co1 co2        -- Identity rule
  | (Pair ty1 _, r) <- coercionKindRole co1
  , Pair _ ty2 <- coercionKind co2
  , ty1 `eqType` ty2
  = fireTransRule "RedTypeDirRefl" co1 co2 $
    Refl r ty2

opt_trans_rule _ _ _ = Nothing

fireTransRule :: String -> Coercion -> Coercion -> Coercion -> Maybe Coercion
fireTransRule _rule _co1 _co2 res
  = -- pprTrace ("Trans rule fired: " ++ _rule) (vcat [ppr _co1, ppr _co2, ppr res]) $
    Just res

{-
Note [Conflict checking with AxiomInstCo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider the following type family and axiom:

type family Equal (a :: k) (b :: k) :: Bool
type instance where
  Equal a a = True
  Equal a b = False
--
Equal :: forall k::*. k -> k -> Bool
axEqual :: { forall k::*. forall a::k. Equal k a a ~ True
           ; forall k::*. forall a::k. forall b::k. Equal k a b ~ False }

We wish to disallow (axEqual[1] <*> <Int> <Int). (Recall that the index is
0-based, so this is the second branch of the axiom.) The problem is that, on
the surface, it seems that (axEqual[1] <*> <Int> <Int>) :: (Equal * Int Int ~
False) and that all is OK. But, all is not OK: we want to use the first branch
of the axiom in this case, not the second. The problem is that the parameters
of the first branch can unify with the supplied coercions, thus meaning that
the first branch should be taken. See also Note [Branched instance checking]
in types/FamInstEnv.lhs.

Note [Why call checkAxInstCo during optimisation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It is possible that otherwise-good-looking optimisations meet with disaster
in the presence of axioms with multiple equations. Consider

type family Equal (a :: *) (b :: *) :: Bool where
  Equal a a = True
  Equal a b = False
type family Id (a :: *) :: * where
  Id a = a

axEq :: { [a::*].       Equal a a ~ True
        ; [a::*, b::*]. Equal a b ~ False }
axId :: [a::*]. Id a ~ a

co1 = Equal (axId[0] Int) (axId[0] Bool)
  :: Equal (Id Int) (Id Bool) ~  Equal Int Bool
co2 = axEq[1] <Int> <Bool>
  :: Equal Int Bool ~ False

We wish to optimise (co1 ; co2). We end up in rule TrPushAxL, noting that
co2 is an axiom and that matchAxiom succeeds when looking at co1. But, what
happens when we push the coercions inside? We get

co3 = axEq[1] (axId[0] Int) (axId[0] Bool)
  :: Equal (Id Int) (Id Bool) ~ False

which is bogus! This is because the type system isn't smart enough to know
that (Id Int) and (Id Bool) are Surely Apart, as they're headed by type
families. At the time of writing, I (Richard Eisenberg) couldn't think of
a way of detecting this any more efficient than just building the optimised
coercion and checking.
-}

-- | Check to make sure that an AxInstCo is internally consistent.
-- Returns the conflicting branch, if it exists
-- See Note [Conflict checking with AxiomInstCo]
checkAxInstCo :: Coercion -> Maybe CoAxBranch
-- defined here to avoid dependencies in Coercion
-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism] in CoreLint
checkAxInstCo (AxiomInstCo ax ind cos)
  = let branch   = coAxiomNthBranch ax ind
        tvs      = coAxBranchTyCoVars branch
        incomps  = coAxBranchIncomps branch
        tys      = map (pFst . coercionArgKind) cos 
        subst    = zipOpenTCvSubst tvs tys
        target   = Type.substTys subst (coAxBranchLHS branch)
        in_scope = mkInScopeSet $
                   unionVarSets (map (tyCoVarsOfTypes . coAxBranchLHS) incomps)
        flattened_target = flattenTys in_scope target in
    check_no_conflict flattened_target incomps
  where
    check_no_conflict :: [Type] -> [CoAxBranch] -> Maybe CoAxBranch
    check_no_conflict _    [] = Nothing
    check_no_conflict flat (b@CoAxBranch { cab_lhs = lhs_incomp } : rest)
         -- See Note [Apartness] in FamInstEnv
      | SurelyApart <- tcUnifyTysFG instanceBindFun flat lhs_incomp
      = check_no_conflict flat rest
      | otherwise
      = Just b
checkAxInstCo _ = Nothing


-----------
wrapSym :: SymFlag -> Coercion -> Coercion
wrapSym sym co | sym       = SymCo co
               | otherwise = co

-- | Conditionally set a role to be representational
wrapRole :: ReprFlag
         -> Role         -- ^ current role
         -> Coercion -> Coercion
wrapRole False _       = id
wrapRole True  current = downgradeRole Representational current

-- | If we require a representational role, return that. Otherwise,
-- return the "default" role provided.
chooseRole :: ReprFlag
           -> Role    -- ^ "default" role
           -> Role
chooseRole True _ = Representational
chooseRole _    r = r

-----------
isAxiom_maybe :: Coercion -> Maybe (Bool, CoAxiom Branched, Int, [CoercionArg])
isAxiom_maybe (SymCo co) 
  | Just (sym, con, ind, cos) <- isAxiom_maybe co
  = Just (not sym, con, ind, cos)
isAxiom_maybe (AxiomInstCo con ind cos)
  = Just (False, con, ind, cos)
isAxiom_maybe _ = Nothing

matchAxiom :: Bool -- True = match LHS, False = match RHS
           -> CoAxiom br -> Int -> Coercion -> Maybe [CoercionArg]
matchAxiom sym ax@(CoAxiom { co_ax_tc = tc }) ind co
  = let (CoAxBranch { cab_tvs = qtvs
                    , cab_roles = roles
                    , cab_lhs = lhs
                    , cab_rhs = rhs }) = coAxiomNthBranch ax ind in
    case liftCoMatch (mkVarSet qtvs) (if sym then (mkTyConApp tc lhs) else rhs) co of
      Just subst
        | all (`isMappedByLC` subst) qtvs
        -> zipWithM (liftCoSubstTyCoVar subst) roles qtvs
      _ -> Nothing

-------------
-- destruct a CoherenceCo
isCohLeft_maybe :: Coercion -> Maybe (Coercion, Coercion)
isCohLeft_maybe (CoherenceCo co1 co2) = Just (co1, co2)
isCohLeft_maybe _                     = Nothing

-- destruct a (sym (co1 |> co2)).
-- if isCohRight_maybe co = Just (co1, co2), then (sym co1) `mkCohRightCo` co2 = co
isCohRight_maybe :: Coercion -> Maybe (Coercion, Coercion)
isCohRight_maybe (SymCo (CoherenceCo co1 co2)) = Just (mkSymCo co1, co2)
isCohRight_maybe _                             = Nothing

-------------
compatible_co :: Coercion -> Coercion -> Bool
-- Check whether (co1 . co2) will be well-kinded
compatible_co co1 co2
  = x1 `eqType` x2              
  where
    Pair _ x1 = coercionKind co1
    Pair x2 _ = coercionKind co2

-------------
etaForAllCo_maybe :: InScopeSet
                  -> Coercion -> Maybe (ForAllCoBndr, Coercion)
-- Try to make the coercion be of form (forall tv. co)
etaForAllCo_maybe is co
  | Just (cobndr, r) <- splitForAllCo_maybe co
  = Just (cobndr, r)

  | Pair ty1 ty2  <- coercionKind co
  , Just (bndr1, _) <- splitForAllTy_maybe ty1
  , Just (bndr2, _) <- splitForAllTy_maybe ty2
  , Just tv1 <- binderVar_maybe bndr1
  , Just tv2 <- binderVar_maybe bndr2
  , isTyVar tv1 == isTyVar tv2 -- we want them to be the same sort
  = let m_cv | isTyVar tv1
             = Just $
               mkFreshCoVar is (mkOnlyTyVarTy tv1) (mkOnlyTyVarTy tv2)
             | otherwise
             = Nothing
        cobndr = mkForAllCoBndr (mkNthCo 0 co) tv1 tv2 m_cv
    in
    Just (cobndr, mkInstCo co (coBndrWitness cobndr))

  | otherwise
  = Nothing

etaAppCo_maybe :: Coercion -> Maybe (Coercion,Coercion,CoercionArg)
-- If possible, split a coercion
--   g :: t1a t1b ~ t2a t2b
-- into a pair of coercions (left g, right g)
etaAppCo_maybe co
  | Just (co1,h,co2) <- splitAppCo_maybe co
  = Just (co1,h,co2)
  | (Pair ty1 ty2, Nominal) <- coercionKindRole co
  , Just (_,t1) <- splitAppTy_maybe ty1
  , Just (_,t2) <- splitAppTy_maybe ty2
  , let isco1 = isCoercionTy t1
  , let isco2 = isCoercionTy t2
  , isco1 == isco2
  = Just ( LRCo CLeft co, KindAppCo co
         , if not isco1
           then TyCoArg $ LRCo CRight co
           else CoCoArg Nominal (mkSubCo $ KindAppCo co)
                        (stripCoercionTy t1) (stripCoercionTy t2) )
  | otherwise
  = Nothing

etaTyConAppCo_maybe :: TyCon -> Coercion -> Maybe [CoercionArg]
-- If possible, split a coercion 
--       g :: T s1 .. sn ~ T t1 .. tn
-- into [ Nth 0 g :: s1~t1, ..., Nth (n-1) g :: sn~tn ] 
etaTyConAppCo_maybe tc (TyConAppCo _ tc2 cos2)
  = ASSERT( tc == tc2 ) Just cos2

etaTyConAppCo_maybe tc co
  | isDecomposableTyCon tc
  , Pair ty1 ty2     <- coercionKind co
  , Just (tc1, tys1) <- splitTyConApp_maybe ty1
  , Just (tc2, tys2) <- splitTyConApp_maybe ty2
  , tc1 == tc2
  , let n = length tys1
  = ASSERT( tc == tc1 ) 
    ASSERT( n == length tys2 )
    Just (decomposeCo n co)  
    -- NB: n might be <> tyConArity tc
    -- e.g.   data family T a :: * -> *
    --        g :: T a b ~ T c d

  | otherwise
  = Nothing

{-
Note [Eta for AppCo]
~~~~~~~~~~~~~~~~~~~~
Suppose we have 
   g :: s1 t1 ~ s2 t2

Then we can't necessarily make
   left  g :: s1 ~ s2
   right g :: t1 ~ t2
because it's possible that
   s1 :: * -> *         t1 :: *
   s2 :: (*->*) -> *    t2 :: * -> *
and in that case (left g) does not have the same
kind on either side.

It's enough to check that 
  kind t1 = kind t2
because if g is well-kinded then
  kind (s1 t2) = kind (s2 t2)
and these two imply
  kind s1 = kind s2

-}

-- TODO (RAE): I think the "callback" nature of these functions can be changed,
-- now that we've lost optType
optForAllCoBndr :: TCvSubst -> Bool -> ForAllCoBndr -> (TCvSubst, ForAllCoBndr)
optForAllCoBndr env sym
  = substForAllCoBndrCallback sym substTy
                              (\sym' env' -> opt_co1 env' sym') env
                              -- TODO (RAE): Could this be optimized?

