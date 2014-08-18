%
% (c) The University of Glasgow 2006
%

\begin{code}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module OptCoercion ( optCoercion, optType, checkAxInstCo ) where 

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
import StaticFlags	( opt_NoOptCoercion )
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
\end{code}

%************************************************************************
%*                                                                      *
                 Optimising coercions									
%*                                                                      *
%************************************************************************

Note [Hetero case for opt_trans_rule]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
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
~~~~~~~~~~~~~~~~
We wish to simplify the following:

sym ((forall_h (a1:k1, a2:k2, c:a1~a2). g1)@g2)

Let g2 : s1 ~ s2. Then, the simplification is this:

sym (g1[a1 |-> s1, a2 |-> s2, c |-> g2])

Note that g2 does *not* have sym applied.

Note [Optimising Refl]
~~~~~~~~~~~~~~~~~~~~~~
It would seem that we should optimise the type (t |> Refl _) and the coercion
(g |> Refl _) to get rid of the Refls. This would be wrong. Optimising a type
is a dangerous thing, because equality of types is quite sensitive. To be
able to optimise one type to another, we must make sure that the two types
are indistinguishable. This requirement is met by the AppTy/TyConApp invariant
because (AppTy (TyConApp ..) ..) can never happen. This invariant is considered
in mkAppTy and in the unification functions. We could consider having an
invariant that Refl never appears to the right of a CastTy (like there is
for Exprs). But, we run into a problem during unification. Consider unifying
  (a |> c)
with
  (t |> g)
(for suitable type variable a and coercion variable c). There are two possible
unifying substitutions: [a |-> (t |> g), c |-> Refl _] and [a |-> t, c |-> g].
Which to choose? There is no way to know, so backtracking search would be
required. We don't want backtracking search in unification. So, the only viable
option is to say that (t |> Refl _) and t are distinct types, inhabited by
distinct sets of terms. This means that, in turn, the coercion (g |> Refl _)
can't be optimised, because removing the Refl would change the kind of the
coercion, which is not allowed.

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

\begin{code}
optCoercion :: TCvSubst -> Coercion -> NormalCo
-- ^ optCoercion applies a substitution to a coercion, 
--   *and* optimises it to reduce its size
optCoercion env co 
  | opt_NoOptCoercion = substCo env co
  | otherwise         = opt_co1 env False co

optType :: TCvSubst -> Type -> Type
-- ^ optType applies a substitution to a type
-- *and* optimises any coercions therein
optType subst = go
  where
    go (TyVarTy tv)         = substTyVar subst tv
    go (AppTy fun arg)      = mkAppTy (go fun) $! (go arg)
    go (TyConApp tc tys)    = let args = map go tys
                              in  args `seqList` TyConApp tc args
    go (PiTy bndr ty)       = case optBinder subst bndr of
                              (subst', bndr') ->
                                mkPiTy bndr' $! (optType subst' ty)
    go (LitTy n)            = LitTy $! n
    go (CastTy ty co)       = (CastTy $! (go ty)) $! (optCoercion subst co)
    go (CoercionTy co)      = CoercionTy $! (optCoercion subst co)

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
opt_co_arg2 env sym r (CoCoArg _r co1 co2)
  = ASSERT( r == _r )
    opt_cocoarg env sym r co1 co2

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
opt_co_arg3 env sym mrole r (CoCoArg _r co1 co2)
  = ASSERT( r == _r )
    opt_cocoarg env sym (mrole `orElse` r) co1 co2

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
    Refl (chooseRole rep r) (optType env ty)

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

opt_co4 env sym rep r (AppCo co1 co2) = mkAppCo (opt_co4_wrap env sym rep r co1)
                                                (opt_co_arg4 env sym False Nominal co2)

-- See Note [Sym and PiCo] in TyCoRep
opt_co4 env sym rep r (PiCo cobndr co)
  = case optPiCoBndr env sym cobndr of
      (env', cobndr') -> mkPiCo cobndr' (opt_co4_wrap env' sym rep r co)
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
    a' = optType env a
    b' = optType env b

opt_co4 env sym rep r (UnsafeCo _r oty1 oty2)
  = ASSERT( r == _r )
    opt_unsafe env (chooseRole rep r) (optType env a) (optType env b)
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

    pick_lr CLeft  (l, _)         = l
    pick_lr CRight (_, TyCoArg r) = r
    pick_lr _      _              = pprPanic "opt_co(LRCo)" (ppr g)

opt_co4 env sym rep r (InstCo co1 arg)
    -- forall over type...
  | TyCoArg co2 <- arg'
  , Just (tv1, tv2, m_cv, co_body) <- splitPiCo_Ty_maybe co1
  , Pair ty1 ty2 <- coercionKind co2
  = let env1 = extendTCvSubstBinders env  [tv1, tv2] [ty1, ty2]
        env2 = extendTCvSubstMaybe   env1 m_cv (mkCoercionTy co2)
              -- See Note [Sym and InstCo]
    in
    opt_co4_warp evn2 sym rep r co_body

    -- forall over coercion...
  | CoCoArg _ co2 co3 <- arg'
  , Just (cv1, cv2, co_body) <- splitPiCo_Co_maybe co1
  = opt_co4_wrap (extendTCvSubstBinders env [cv1, cv2] (map mkCoercionTy [co2, co3]))
            sym rep r co_body

    -- See if it is a forall after optimization
    -- If so, do an inefficient one-variable substitution, then re-optimize
  
    -- forall over type...
  | TyCoArg co2' <- arg'
  , Just (tv1', tv2', m_cv', co'_body) <- splitPiCo_Ty_maybe co1'
  , Pair ty1' ty2' <- coercionKind co2'
  = let env1 = extendTCvSubstBinders (zapTCvSubst env) [tv1', tv2'] [ty1', ty2']
        env2 = extendTCvSubstMaybe   env1              m_cv' (mkCoercionTy co2')
    in
    opt_co4_wrap env2 False False r' co'_body

 -- forall over coercion...
  | CoCoArg _ co2' co3' <- arg'
  , Just (cv1', cv2', co'_body) <- splitPiCo_Co_maybe co1'
  = opt_co4_wrap (extendTCvSubstBinders (zapTCvSubst env)
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
  | UnsafeCo _r tyl1 tyr1 <- co1
  = ASSERT( r == _r )
    opt_co4_wrap env sym False output_role (mkUnsafeCo output_role
                                                (mkCastTy tyl1 co2) tyr1)
  | TransCo col1 cor1 <- co1
  = opt_co4_wrap env sym rep r (mkTransCo (mkCoherenceCo col1 co2) cor1)
  | CoherenceCo col1 cor1 <- co1
  = opt_co4_wrap env sym rep r (mkCoherenceCo col1 (mkTransCo cor1 co2))

  | UnsafeCo r_out tyl1' tyr1' <- co1'
  = ASSERT( output_role == r_out )
    if sym then mkUnsafeCo r_out tyl1' (mkCastTy tyr1' co2')
           else mkUnsafeCo r_out (mkCastTy tyl1' co2') tyr1'
  | TransCo col1' cor1' <- co1'
  = if sym then opt_trans in_scope col1'
                  (optCoercion (zapTCvSubst env) (mkCoherenceRightCo cor1' co2'))
           else opt_trans in_scope (mkCoherenceCo col1' co2') cor1'
  | CoherenceCo col1' cor1' <- co1'
  = if sym then mkCoherenceCo (mkSymCo col1') (opt_trans in_scope cor1' co2')
           else mkCoherenceCo col1' (opt_trans in_scope cor1' co2')
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
opt_co_arg4 env sym rep r (CoCoArg _r co1 co2)
  | sym       = ASSERT( r == _r ) CoCoArg role co2' co1'
  | otherwise = ASSERT( r == _r ) CoCoArg role co1' co2'
  where co1' = opt_co1 env False co1
        co2' = opt_co1 env False co2
        role = chooseRole rep r

-- | Optimize a "coercion" between coercions.
opt_cocoarg :: TCvSubst
            -> SymFlag
            -> Role   -- ^ desired role
            -> Coercion
            -> Coercion
            -> NormalCoArg
opt_cocoarg env sym r co1 co2
  = if sym
    then CoCoArg r co2' co1'
    else CoCoArg r co1' co2'
  where
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

opt_unsafe :: TCvSubst -> Role -> Type -> Type -> Coercion
opt_unsafe env role oty1 oty2
  | Just (tc1, tys1) <- splitTyConApp_maybe oty1
  , Just (tc2, tys2) <- splitTyConApp_maybe oty2
  , tc1 == tc2
  = mkTyConAppCo role tc1 (zipWith3 (opt_unsafe_arg env) (tyConRolesX role tc1) tys1 tys2)

  | Just (l1, r1) <- splitAppTy_maybe oty1
  , Just (l2, r2) <- splitAppTy_maybe oty2
  , typeKind l1 `eqType` typeKind l2   -- kind(r1) == kind(r2) by consequence
  = let role' = if role == Phantom then Phantom else Nominal in
       -- role' is to comform to mkAppCo's precondition
    mkAppCo (opt_unsafe env role l1 l2) (opt_unsafe_arg env role' r1 r2)

  | Just (bndr1, ty1) <- splitPiTy_maybe oty1
  , Just (bndr2, ty2) <- splitPiTy_maybe oty2
  , let k1 = binderType bndr1
        k2 = binderType bndr2
        bndr1_is_coercion = isCoercionType k1
  , bndr1_is_coercion == isCoercionType k2   -- rule out weird UnsafeCo
  = if k1 `eqType` k2
    then case substBinder2 env bndr1 bndr2 of { (env1, env2, bndr') ->
         let ty1' = optType env1 ty1
             ty2' = optType env2 ty2 in
         mkPiCo (mkHomoCoBndr bdnr')
                (opt_unsafe (zapTCvSubstEnv2 env1 env2) role ty1' ty2') }
    else let eta = opt_unsafe env role k1 k2
             pbndr = mkPairBinder bndr1 bndr2
             cobndr
               | bndr1_is_coercion = mkCoHeteroCoBndr eta pbndr
               | otherwise
               = let m_c = case ( binderVar_maybe bndr1
                                , binderVar_maybe bndr2 ) of
                       (Just tv1, Just tv2 ) ->
                         Just $ mkFreshCoVar (getTCvInScope env)
                                             (mkOnlyTyVarTy tv1)
                                             (mkOnlyTyVarTy tv2)
                       _ -> Nothing
                 in mkTyHeteroCoBndr eta pbndr m_c
         in
         mkPiCo cobndr (opt_unsafe env role ty1 ty2)

  | otherwise
  = mkUnsafeCo role oty1 oty2

opt_unsafe_arg :: TCvSubst -> Role -> Type -> Type -> CoercionArg
opt_unsafe_arg env role oty1 oty2
  | Just co1 <- isCoercionTy_maybe oty1
  , Just co2 <- isCoercionTy_maybe oty2
  = CoCoArg role (opt_co1 env False co1) (opt_co1 env False co2)
  | otherwise
  = TyCoArg $ opt_unsafe env role oty1 oty2

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
    push_nth 0 (PiCo cobndr co)
      | Just v <- getHomoBinder_maybe cobndr
      = Just (Refl (coercionRole co) (binderType v))
      | Just (h, _, _) <- splitHeteroCoBndr_maybe cobndr
      = Just h
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
    opt_trans_arg _  (CoCoArg r col1 _col2) (CoCoArg _r _cor1 cor2)
      = ASSERT( coercionType _col2 `eqType` coercionType _cor1 )
        ASSERT( r == _r )
        CoCoArg r col1 cor2
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
opt_trans_arg2 _ (CoCoArg r col1 _cor1) (CoCoArg _r _col2 cor2)
  = ASSERT( coercionType _cor1 `eqType` coercionType _col2 )
    ASSERT( r == _r )
    CoCoArg r col1 cor2
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
    TyConAppCo r1 tc1 (opt_transList is cos1 cos2)

opt_trans_rule is in_co1@(AppCo co1a co1b) in_co2@(AppCo co2a co2b)
  = fireTransRule "TrPushApp" in_co1 in_co2 $
    mkAppCo (opt_trans is co1a co2a) (opt_trans_arg is co1b co2b)

-- Eta rules
opt_trans_rule is co1@(TyConAppCo r tc cos1) co2
  | Just cos2 <- etaTyConAppCo_maybe tc co2
  = ASSERT( length cos1 == length cos2 )
    fireTransRule "EtaCompL" co1 co2 $
    TyConAppCo r tc (opt_transList is cos1 cos2)

opt_trans_rule is co1 co2@(TyConAppCo r tc cos2)
  | Just cos1 <- etaTyConAppCo_maybe tc co1
  = ASSERT( length cos1 == length cos2 )
    fireTransRule "EtaCompR" co1 co2 $
    TyConAppCo r tc (opt_transList is cos1 cos2)

opt_trans_rule is co1@(AppCo co1a co1b) co2
  | Just (co2a,co2b) <- etaAppCo_maybe co2
  = fireTransRule "EtaAppL" co1 co2 $
    mkAppCo (opt_trans is co1a co2a) (opt_trans_arg is co1b co2b)

opt_trans_rule is co1 co2@(AppCo co2a co2b)
  | Just (co1a,co1b) <- etaAppCo_maybe co1
  = fireTransRule "EtaAppR" co1 co2 $
    mkAppCo (opt_trans is co1a co2a) (opt_trans_arg is co1b co2b)

-- Push transitivity inside forall
opt_trans_rule is co1 co2
  | Just (cobndr1,r1) <- splitPiCo_maybe co1
  , Just (cobndr2,r2) <- etaPiCo_maybe is co2
  = push_trans cobndr1 r1 cobndr2 r2

  | Just (cobndr2,r2) <- splitPiCo_maybe co2
  , Just (cobndr1,r1) <- etaPiCo_maybe is co1
  = push_trans cobndr1 r1 cobndr2 r2

  where
  push_trans cobndr1 r1 cobndr2 r2
    | Phantom <- role
       -- abort. We need to use some coercions to cast, and we can't
       -- if we're at a Phantom role.
    = WARN( True, ppr co1 $$ ppr co2 )
      Nothing

    | otherwise =
    case (cobndr1, cobndr2) of
      (TyHomo tv1, TyHomo tv2) -> -- their kinds must be equal
        let (subst, bndr) = mk_homo_subst is' tv1 tv2
            r1'   = optCoercion subst r1
            r2'   = optCoercion subst r2
            is'   = is `extendInScopeSetMaybes` (map binderVar_maybe [tv1, tv2])
        in
        fireTransRule "EtaAllTyHomoHomo" co1 co2 $
        mkPiCo_TyHomo bndr (opt_trans is' r1' r2')

      -- See Note [Hetero case for opt_trans_rule]
      -- kinds of tvl2 and tvr1 must be equal
      (TyHetero col pbndrl m_cvl, TyHetero cor pbndrr m_cvr) ->
        let Pair bvl1 bvl2 = binderPayload pbndrl
            Pair bvr1 bvr2 = binderPayload pbndr2
            m_cv = case (getBinderVar_maybe bvl1, getBinderVar_maybe bvr2) of
              (Just tvl1, Just tvr2) ->
                Just $ mkFreshCoVar is (mkOnlyTyVarTy tvl1) (mkOnlyTyVarTy tvr2)
              _ -> Nothing
              
            lmap1    = maybe_subst (getBinderVar_maybe bvl2) $
                       mkCastTy (mkOnlyTyVarTy tvr2) (to_rep $ mkSymCo cor)
            lmap2    = maybe_subst m_cvl $
                       mkCoercionTy $
                       mkCoherenceRightCo (mkCoVarCo (fromJust m_cv))
                                          (mkSymCo (to_rep cor))
            rmap1    = maybe_subst (getBinderVar_maybe bvr1) $
                       mkCastTy (mkOnlyTyVarTy tvl1) (to_rep col)
            rmap2    = maybe_subst m_cvr $
                       mkCoercionTy $
                       mkCoherenceLeftCo (mkCoVarCo (fromJust m_cv))
                                         (to_rep col)
            empty    = mkEmptyTCvSubst is'
            subst_r1 = extendTCvSubstMaybes empty [lmap1, lmap2]
            subst_r2 = extendTCvSubstMaybes empty [rmap1, rmap2]
            r1' = optCoercion subst_r1 r1
            r2' = optCoercion subst_r2 r2

            vars = m_cvl : m_cvr : m_cv :
                   map getBinderVar_maybe [bvl1, bvl2, bvr1, bvr2] )
            is' = is `extendInScopeSetMaybes` vars in
        fireTransRule "EtaAllTyHeteroHetero" co1 co2 $
        mkPiCo (mkTyHeteroCoBndr (opt_trans2 is col cor)
                                 (setBinderPayload pbndrl (Pair bvl1 bvr2))
                                 m_cv)
               (opt_trans is' r1' r2')

      (TyHomo tvl, TyHetero eta2 pbndr2 m_cvr2) ->
        let Pair tvr1 tvr2 = binderPayload pbndr2
            vars           = m_cvr2 : binderVar_maybe tvl :
                               map getBinderVar_maybe [tvr1, tvr2])
            is'            = is `extendInScopeSetMaybes` vars
            empty_subst    = mkEmptyTCvSubst is'
            (subst, cobndr)
              = case (binderVar_maybe tvl, getBinderVar_maybe tvr1) of
                  (Just vl, Just vr) ->
                    ( extendTCvSubst empty_subst tvl (mkOnlyTyVarTy tvr1)
                    , cobndr2 )
                  (Just vl, Nothing) ->
                    ( empty_subst
                    , TyHetero eta2
                               (setBinderPayload pbndr2
                                (Pair (mkBinderVar vl) tvr2))
                               Nothing )
                  _ -> (empty_subst, cobndr2)
            r1'   = optCoercion subst r1
        in
        fireTransRule "EtaAllTyHomoHetero" co1 co2 $
        mkPiCo cobndr (opt_trans is' r1' r2)

      (TyHetero eta1 pbndr m_cvl, TyHomo tvr) ->
        let Pair tvl1 tvl2 = binderPayload pbndr
            vars           = m_cvl : binderVar_maybe tvr :
                               map getBinderVar_maybe [tvl1, tvl2])
            is'            = is `extendInScopeSetMaybes` vars
            empty_subst    = mkEmptyTCvSubst is'
            
            (subst, cobndr)
              = case (getBinderVar_maybe tvl2, binderVar_maybe tvr) of
                  (Just vl, Just vr) ->
                    ( extendTCvSubst empty_subst vr (mkOnlyTyVarTy vl)
                    , cobndr1 )
                  (Nothing, Just vr) ->
                    ( empty_subst
                    , TyHetero eta1
                               (setBinderPayload pbndr
                                 (Pair tvl1 (mkBinderVar vr)))
                               Nothing )
                  _ -> (empty_subst, cobndr1)
            r2'   = optCoercion subst r2
        in
        fireTransRule "EtaAllTyHeteroHomo" co1 co2 $
        mkPiCo cobndr (opt_trans is' r1 r2')
   
      (CoHomo cv1, CoHomo cv2) ->
        let (subst, bndr) = mk_homo_subst is' cv1 cv2
            r1'   = optCoercion subst r1
            r2'   = optCoercion subst r2
            is'   = is `extendInScopeSetMaybes` (map binderVar_maybe [cv1, cv2]) in
         fireTransRule "EtaAllCoHomoHomo" co1 co2 $
         mkPiCo_CoHomo bndr (opt_trans is' r1 r2')

      (CoHetero col pbndrl, CoHetero cor pbndrr) ->
        let Pair cvl1 cvl2 = binderPayload pbndr1
            Pair cvr1 cvr2 = binderPayload pbndr2
            lmap     = maybe_subst (getBinderVar_maybe cvl2) $
                       mkCoercionTy $
                       (mkNthCo 2 cor) `mkTransCo`
                       (mkCoVarCo cvr2) `mkTransCo`
                       (mkNthCo 3 $ mkSymCo cor)
            rmap     = maybe_subst (getBinderVar_maybe cvr1) $
                       mkCoercionTy $
                       (mkNthCo 2 (mkSymCo col)) `mkTransCo`
                       (mkCoVarCo cvl1) `mkTransCo`
                       (mkNthCo 3 col)
            empty    = mkEmptyTCvSubst is'
            subst_r1 = extendTCvSubstMaybes empty [lmap]
            subst_r2 = extendTCvSubstMaybes empty [rmap]
            r1'      = optCoercion subst_r1 r1
            r2'      = optCoercion subst_r2 r2
            vars     = map getBinderVar_maybe [cvl1, cvl2, cvr1, cvr2] 
            is'      = is `extendInScopeSetMaybes` vars
            pbndr'   = setBinderPayload pbndrl (Pair cvl1 cvr2)
        in
        fireTransRule "EtaAllCoHeteroHetero" co1 co2 $
        mkPiCo (mkCoHeteroCoBndr (opt_trans2 is col cor) pbndr')
               (opt_trans is' r1' r2')

      (CoHomo cvl, CoHetero h pbndrr) ->
        let Pair cvr1 cvr2 = binderPayload pbndrr
            empty = mkEmptyTCvSubst is'
            (subst, pbndr') = case (binderVar_maybe cvl, getBinderVar_maybe cvr1) of
              (Just vl, Just vr) -> ( extendTCvSubst empty vl (mkTyCoVarTy vr)
                                    , pbndrr )
              (Just vl, Nothing) -> ( empty
                                    , setBinderPayload pbndrr (Pair (mkBinderVar vl) cvr2) )
              _                  -> ( empty, pbndrr )
            r1'   = optCoercion subst r1
            vars  = binderVar_maybe cvl : map getBinderVar_maybe [cvr1, cvr2]
            is'   = is `extendInScopeSetMaybes` vars
        in
        fireTransRule "EtaAllCoHomoHetero" co1 co2 $
        mkPiCo (CoHetero h pbndr') (opt_trans is' r1' r2)

      (CoHetero h pbndrl, CoHomo cvr) ->
        let Pair cvl1 cvl2 = binderPayload pbndrl
            empty = mkEmptyTCvSubst is'
            (subst, pbndr') = case (getBinderVar_maybe cvl2, binderVar_maybe cvr) of
              (Just vl, Just vr) -> ( extendTCvSubst empty vr (mkTyCoVarTy vl)
                                    , pbndrl )
              (Nothing, Just vr) -> ( empty
                                    , setBinderPayload pbndrl (Pair cvl1 (mkBinderVar vr)) )
              _                  -> ( empty, pbndrl )
            r2'   = optCoercion subst r2
            vars  = binderVar_maybe cvr : map getBinderVar_maybe [cvl1, cvl2]
            is'   = is `extendInScopeSetMaybes` vars in
        fireTransRule "EtaAllCoHeteroHomo" co1 co2 $
        mkPiCo (CoHetero h pbndr') (opt_trans is' r1 r2')

      _ -> Nothing
    where
      role   = coercionRole r1  -- must be the same as r2
      to_rep = downgradeRole Representational role

      mk_homo_subst in_scope bndr1 bndr2
        = let empty_subst = mkEmptyTCvSubst in_scope in
          case (binderVar_maybe bndr1, binderVar_maybe bndr2) of
            (Just v1, Just v2) ->
                (extendTCvSubst empty_subst v2 (mkTyCoVarTy v1), bndr1)
            (Nothing, Just _)  -> (empty_subst, bndr2)
            (Just _, Nothing)  -> (empty_subst, bndr1)
            (Nothing, Nothing) -> (empty_subst, bndr1) -- arbitrary choice;
                                                       -- bndr1 == bndr2

      maybe_subst :: Maybe Var -> Type -> Maybe (Var, Type)
      maybe_subst Nothing  _ = Nothing
      maybe_subst (Just v) t = Just (v, t)


-- Push transitivity inside axioms
opt_trans_rule is co1 co2

  -- TrPushSymAxR
  | Just (sym, con, ind, cos1) <- co1_is_axiom_maybe
  , Just cos2 <- matchAxiom sym con ind co2
  , True <- sym
  , let newAxInst = AxiomInstCo con ind (opt_transList is (map mk_sym_co_arg cos2) cos1)
  , Nothing <- checkAxInstCo newAxInst
  = fireTransRule "TrPushSymAxR" co1 co2 $ SymCo newAxInst

  -- TrPushAxR
  | Just (sym, con, ind, cos1) <- co1_is_axiom_maybe
  , Just cos2 <- matchAxiom sym con ind co2
  , False <- sym
  , let newAxInst = AxiomInstCo con ind (opt_transList is cos1 cos2)
  , Nothing <- checkAxInstCo newAxInst
  = fireTransRule "TrPushAxR" co1 co2 newAxInst

  -- TrPushSymAxL
  | Just (sym, con, ind, cos2) <- co2_is_axiom_maybe
  , Just cos1 <- matchAxiom (not sym) con ind co1
  , True <- sym
  , let newAxInst = AxiomInstCo con ind (opt_transList is cos2 (map mk_sym_co_arg cos1))
  , Nothing <- checkAxInstCo newAxInst
  = fireTransRule "TrPushSymAxL" co1 co2 $ SymCo newAxInst

  -- TrPushAxL  
  | Just (sym, con, ind, cos2) <- co2_is_axiom_maybe
  , Just cos1 <- matchAxiom (not sym) con ind co1
  , False <- sym
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
    then liftCoSubstWith role qtvs (opt_transList is cos1 (map mk_sym_co_arg cos2)) lhs
       -- TrPushSymAx
    else liftCoSubstWith role qtvs (opt_transList is (map mk_sym_co_arg cos1) cos2) rhs
  where
    co1_is_axiom_maybe = isAxiom_maybe co1
    co2_is_axiom_maybe = isAxiom_maybe co2
    role = coercionRole co1 -- should be the same as coercionRole co2!

    mk_sym_co_arg (TyCoArg co) = TyCoArg $ mkSymCo co
    mk_sym_co_arg (CoCoArg r co1 co2) = CoCoArg r co2 co1

opt_trans_rule is co1 co2
  | Just (lco, lh) <- isCohRight_maybe co1
  , Just (rco, rh) <- isCohLeft_maybe co2
  , (coercionType lh) `eqType` (coercionType rh)
  = opt_trans_rule is lco rco

opt_trans_rule _ co1 co2	-- Identity rule
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

\end{code}

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

We wish to disallow (axEqual[1] <*> <Int> <Int). (Recall that the index is 0-based,
so this is the second branch of the axiom.) The problem is that, on the surface, it
seems that (axEqual[1] <*> <Int> <Int>) :: (Equal * Int Int ~ False) and that all is
OK. But, all is not OK: we want to use the first branch of the axiom in this case,
not the second. The problem is that the parameters of the first branch can unify with
the supplied coercions, thus meaning that the first branch should be taken. See also
Note [Branched instance checking] in types/FamInstEnv.lhs.

\begin{code}
-- | Check to make sure that an AxInstCo is internally consistent.
-- Returns the conflicting branch, if it exists
-- See Note [Conflict checking with AxiomInstCo]
checkAxInstCo :: Coercion -> Maybe CoAxBranch
-- defined here to avoid dependencies in Coercion
-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism] in CoreLint
checkAxInstCo (AxiomInstCo ax ind cos)
  = let branch = coAxiomNthBranch ax ind
        tvs = coAxBranchTyCoVars branch
        incomps = coAxBranchIncomps branch
        tys = map (pFst . coercionArgKind) cos 
        subst = zipOpenTCvSubst tvs tys
        target = substTys subst (coAxBranchLHS branch)
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
-- takes two tyvars and builds env'ts to map them to the same tyvar
substTyCoVarBndr2 :: TCvSubst -> TyCoVar -> TyCoVar
                  -> (TCvSubst, TCvSubst, TyCoVar)
substTyCoVarBndr2 env tv1 tv2
  = case substTyCoVarBndr env tv1 of
      (env1, tv1') -> (env1, extendTCvSubstAndInScope env tv2 (mkTyCoVarTy tv1'), tv1')
    
zapTCvSubstEnv2 :: TCvSubst -> TCvSubst -> TCvSubst
zapTCvSubstEnv2 env1 env2 = mkTCvSubst (is1 `unionInScope` is2)
                                       emptyTvSubstEnv emptyCvSubstEnv
  where is1 = getTCvInScope env1
        is2 = getTCvInScope env2

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
-- If we succeed in matching, then *all the quantified type variables are bound*
-- E.g.   if tvs = [a,b], lhs/rhs = [b], we'll fail
matchAxiom sym ax@(CoAxiom { co_ax_tc = tc }) ind co
  = let (CoAxBranch { cab_tvs = qtvs
                    , cab_roles = roles
                    , cab_lhs = lhs
                    , cab_rhs = rhs }) = coAxiomNthBranch ax ind in
    case liftCoMatch (mkVarSet qtvs) (if sym then (mkTyConApp tc lhs) else rhs) co of
      Nothing    -> Nothing
      Just subst -> zipWithM (liftCoSubstTyCoVar subst) roles qtvs

-------------
-- destruct a CoherenceCo
isCohLeft_maybe :: Coercion -> Maybe (Coercion, Coercion)
isCohLeft_maybe (CoherenceCo co1 co2) = Just (co1, co2)
isCohLeft_maybe _                     = Nothing

-- destruct a (sym (co1 |> co2)). Note that you probably want to work with
-- sym co1, not co1 directly.
-- if isCohRight_maybe co = Just (co1, co2), then (sym co1) `mkCohRightCo` co2 = co
isCohRight_maybe :: Coercion -> Maybe (Coercion, Coercion)
isCohRight_maybe (SymCo (CoherenceCo co1 co2)) = Just (co1, co2)
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
etaPiCo_maybe :: InScopeSet -> Coercion -> Maybe (PiCoBndr, Coercion)
-- Try to make the coercion be of form (forall tv. co)
etaPiCo_maybe is co
  | Just (cobndr, r) <- splitPiCo_maybe co
  = Just (cobndr, r)

  | Pair ty1 ty2  <- coercionKind co
  , Just (bndr1, _) <- splitPiTy_maybe ty1
  , Just (bndr2, _) <- splitPiTy_maybe ty2
  , let k1 = binderType bndr1
        k2 = binderType bndr2
        bndr1_is_coercion = isCoercionType k1
  , bndr1_is_coercion == isCoercionType k2 -- we want them to be the same sort
  , compatibleBinder bndr1 bndr2
  = if k1 `eqType` k2

    -- homogeneous:
    then -- we need a variable name, but bndr1 and bndr2 might potentially
         -- both be anonymous!
         let (var, _)  = mk_fresh_var is bndr1_is_coercion k1
             bvar      = mkBinderVar var
         in
         Just ( mkHomoCoBndr (setBinderPayload bndr1 bvar)
              , mkInstCo co $ mkCoArgForVar var )

    -- heterogeneous:
    else let (tv1, is1) = mk_fresh_var is  bndr1_is_coercion k1
             (tv2, is2) = mk_fresh_var is1 bndr1_is_coercion k2
             bv1 = mkBinderVar tv1
             bv2 = mkBinderVar tv2
             pbndr = setBinderPayload bndr1 (Pair bv1 bv2)
         in
         if bndr1_is_coercion
         then Just ( mkCoHeteroCoBndr (mkNthCo 0 co) pbndr
                   , mkInstCo co (CoCoArg Nominal (mkCoVarCo tv1)
                                                  (mkCoVarCo tv2)) )
         else let covar = mkFreshCoVar is2 (mkOnlyTyVarTy tv1)
                                           (mkOnlyTyVarTy tv2)
              in
              Just ( mkTyHeteroCoBndr (mkNthCo 0 co) pbndr (Just covar)
                   , mkInstCo co (TyCoArg (mkCoVarCo covar)))

  | otherwise
  = Nothing

  where
    mk_fresh_var in_scope is_coercion ki
      = let (mk_uniq, mk_name, mk_var)
              | is_coercion = (mkCoVarUnique, mkSystemVarName, mkCoVar)
              | otherwise   = (mkAlphaTyVarUnique, mkSysTvName, mkTyVar)
            uniq = mk_uniq 79  -- arbitrary number
            name = mk_name uniq (fsLit "opt_eta")
            var  = uniqAway in_scope $ mk_var name ki
        in (var, in_scope `extendInScopeSet` var)

etaAppCo_maybe :: Coercion -> Maybe (Coercion,CoercionArg)
-- If possible, split a coercion
--   g :: t1a t1b ~ t2a t2b
-- into a pair of coercions (left g, right g)
etaAppCo_maybe co
  | Just (co1,co2) <- splitAppCo_maybe co
  = Just (co1,co2)
  | (Pair ty1 ty2, Nominal) <- coercionKindRole co
  , Just (_,t1) <- splitAppTy_maybe ty1
  , Just (_,t2) <- splitAppTy_maybe ty2
  , let isco1 = isCoercionTy t1
  , let isco2 = isCoercionTy t2
  , isco1 == isco2
  = Just (LRCo CLeft co, if not isco1
                         then TyCoArg $ LRCo CRight co
                         else CoCoArg Nominal
                                      (stripCoercionTy t1)
                                      (stripCoercionTy t2))
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
\end{code}

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

\begin{code}

-- substitution functions that call back to optimization functions
optTyVarBndr :: TCvSubst -> TyVar -> (TCvSubst, TyVar)
optTyVarBndr = substTyVarBndrCallback optType

optPiCoBndr :: TCvSubst -> Bool -> PiCoBndr -> (TCvSubst, PiCoBndr)
optPiCoBndr env sym
  = substPiCoBndrCallback sym optType
                          (\sym' env' -> opt_co1 env' sym') env
                              -- TODO (RAE): Could this be optimized?

\end{code}
