-- (c) The University of Glasgow 2006

{-# LANGUAGE CPP #-}
 -- This module used to take 10GB of memory to compile with the new
 -- (Nov '15) pattern-match checker.

module OptCoercion ( optCoercion, checkAxInstCo ) where

#include "HsVersions.h"

import TyCoRep
import Coercion
import Type hiding( substTyVarBndr, substTy )
import TcType       ( exactTyCoVarsOfType )
import TyCon
import CoAxiom
import VarSet
import VarEnv
import FV
import StaticFlags      ( opt_NoOptCoercion )
import Outputable
import FamInstEnv ( flattenTys )
import Pair
import ListSetOps ( getNth )
import Util
import Unify
import InstEnv

import Control.Monad   ( zipWithM, guard )

{-
%************************************************************************
%*                                                                      *
                 Optimising coercions
%*                                                                      *
%************************************************************************

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

Note [Optimising InstCo]
~~~~~~~~~~~~~~~~~~~~~~~~
When we have (InstCo (ForAllCo tv vis h g) g2), we want to optimise.

Let's look at the typing rules.

h : k1 ~ k2
tv:k1 |- g : t1 ~ t2
-----------------------------
ForAllCo tv vis h g : (all tv:k1.t1) ~ (all tv:k2.t2[tv |-> tv |> sym h])

g1 : (all tv:k1.t1') ~ (all tv:k2.t2')
g2 : s1 ~ s2
--------------------
InstCo g1 g2 : t1'[tv |-> s1] ~ t2'[tv |-> s2]

We thus want some coercion proving this:

  (t1[tv |-> s1]) ~ (t2[tv |-> s2 |> sym h])

If we substitute the *type* tv for the *coercion*
(g2 `mkCoherenceRightCo` sym h) in g, we'll get this result exactly.
This is bizarre,
though, because we're substituting a type variable with a coercion. However,
this operation already exists: it's called *lifting*, and defined in Coercion.
We just need to enhance the lifting operation to be able to deal with
an ambient substitution, which is why a LiftingContext stores a TCvSubst.

-}

optCoercion :: TCvSubst -> Coercion -> NormalCo
-- ^ optCoercion applies a substitution to a coercion,
--   *and* optimises it to reduce its size
optCoercion env co
  | opt_NoOptCoercion = substCo env co
  | debugIsOn
  = let (Pair in_ty1  in_ty2,  in_role)  = coercionKindRole co
        (Pair out_ty1 out_ty2, out_role) = coercionRepKindRole out_rep
    in
    ASSERT2( substTyUnchecked env in_ty1 `eqType` out_ty1 &&
             substTyUnchecked env in_ty2 `eqType` out_ty2 &&
             in_role == out_role
           , text "optCoercion changed types!"
             $$ hang (text "in_co:") 2 (ppr co)
             $$ hang (text "in_ty1:") 2 (ppr in_ty1)
             $$ hang (text "in_ty2:") 2 (ppr in_ty2)
             $$ hang (text "out_co:") 2 (ppr out_co)
             $$ hang (text "out_ty1:") 2 (ppr out_ty1)
             $$ hang (text "out_ty2:") 2 (ppr out_ty2)
             $$ hang (text "subst:") 2 (ppr env) )
    out_co

  | otherwise         = out_co
  where
    lc = mkSubstLiftingContext env
    out_co = CachedCoercion { coercionKind    = substTy env <$> coercionKind co
                            , coercionRole    = coercionRole co
                            , tyCoVarsOfCoAcc = tyCoVarsOfCoRepAcc out_rep
                            , coercionInfo    = NoCachedInfo
                            , coercionRep     = out_rep }
    out_rep = opt_co2 lc False (coercionRole co) (coercionRep co)

type NormalCoRep    = CoercionRep
type NormalCo       = Coercion
  -- Invariants:
  --  * The substitution has been fully applied
  --  * For trans coercions (co1 `trans` co2)
  --       co1 is not a trans, and neither co1 nor co2 is identity

type NormalNonIdCoRep = NormalCoRep  -- Extra invariant: not the identity

-- | Do we apply a @sym@ to the result?
type SymFlag = Bool

-- | Do we force the result to be representational?
type ReprFlag = Bool

-- | Optimize a coercion, making no assumptions. All coercions in
-- the lifting context are already optimized (and sym'd if nec'y)
opt_co1 :: LiftingContext
        -> SymFlag
        -> CoercionRep -> NormalCoRep
opt_co1 env sym co = opt_co2 env sym (coercionRepRole co) co

-- See Note [Optimising coercion optimisation]
-- | Optimize a coercion, knowing the coercion's role. No other assumptions.
opt_co2 :: LiftingContext
        -> SymFlag
        -> Role   -- ^ The role of the input coercion
        -> CoercionRep -> NormalCoRep
opt_co2 env sym Phantom co = opt_phantom env sym co
opt_co2 env sym r       co = opt_co3 env sym Nothing r co

-- See Note [Optimising coercion optimisation]
-- | Optimize a coercion, knowing the coercion's non-Phantom role.
opt_co3 :: LiftingContext -> SymFlag -> Maybe Role -> Role -> CoercionRep -> NormalCoRep
opt_co3 env sym (Just Phantom)          _ co = opt_phantom env sym co
opt_co3 env sym (Just Representational) r co = opt_co4_wrap env sym True  r co
  -- if mrole is Just Nominal, that can't be a downgrade, so we can ignore
opt_co3 env sym _                       r co = opt_co4_wrap env sym False r co

-- See Note [Optimising coercion optimisation]
-- | Optimize a non-phantom coercion.
opt_co4, opt_co4_wrap :: LiftingContext -> SymFlag -> ReprFlag -> Role -> CoercionRep -> NormalCoRep

opt_co4_wrap = opt_co4
{-
opt_co4_wrap env sym rep r co
  = pprTrace "opt_co4_wrap {"
    ( vcat [ text "Sym:" <+> ppr sym
           , text "Rep:" <+> ppr rep
           , text "Role:" <+> ppr r
           , text "Co:" <+> ppr co ]) $
    ASSERT( r == coercionRole co )
    let result = opt_co4 env sym rep r co in
    pprTrace "opt_co4_wrap }" (ppr co $$ text "---" $$ ppr result) $
    result
-}

opt_co4_wrap_co :: LiftingContext
                -> SymFlag
                -> ReprFlag
                -> Role
                -> Coercion
                -> NormalCo
opt_co4_wrap_co env sym repr role (CachedCoercion { coercionKind = kind
                                                  , coercionRole = role1
                                                  , coercionRep  = rep })
  = ASSERT( role == role1 )
    CachedCoercion { coercionKind    = substTy <$> lcSubst env <*> kind
                   , coercionRole    = role
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoRepAcc rep'
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = rep' }
  where
    rep' = opt_co4_wrap env sym repr role rep


opt_co4 env _   rep r (Refl _r ty)
  = ASSERT2( r == _r, text "Expected role:" <+> ppr r $$
                      text "Found role:" <+> ppr _r   $$
                      text "Type:" <+> ppr ty )
    liftCoRepSubst (chooseRole rep r) env ty

opt_co4 env sym rep r (SymCo co)  = opt_co4_wrap env (not sym) rep r co
  -- surprisingly, we don't have to do anything to the env here. This is
  -- because any "lifting" substitutions in the env are tied to ForAllCos,
  -- which treat their left and right sides differently. We don't want to
  -- exchange them.

opt_co4 env sym rep r g@(TyConAppCo _r tc cos)
  = ASSERT( r == _r )
    case (rep, r) of
      (True, Nominal) ->
        mkTyConAppCoRep Representational tc
                        (zipWith3 (opt_co3 env sym)
                                  (map Just (tyConRolesRepresentational tc))
                                  (repeat Nominal)
                                  cos)
      (False, Nominal) ->
        mkTyConAppCoRep Nominal tc (map (opt_co4_wrap env sym False Nominal) cos)
      (_, Representational) ->
                      -- must use opt_co2 here, because some roles may be P
                      -- See Note [Optimising coercion optimisation]
        mkTyConAppCoRep r tc (zipWith (opt_co2 env sym)
                                      (tyConRolesRepresentational tc)  -- the current roles
                                      cos)
      (_, Phantom) -> pprPanic "opt_co4 sees a phantom!" (ppr g)

opt_co4 env sym rep r (AppCo co1 co2)
  = mkAppCoRep (opt_co4_wrap env sym rep r co1)
               (opt_co4_wrap env sym False Nominal co2)

opt_co4 env sym rep r (ForAllCo tv vis k_co co)
  = case optForAllCoBndr env sym tv k_co of
      (env', tv', k_co') -> mkForAllCoRep tv' vis k_co' $
                            opt_co4_wrap env' sym rep r co
     -- Use the "mk" functions to check for nested Refls

opt_co4 env sym rep r (CoVarCo cv)
  | Just co <- lookupCoVar (lcTCvSubst env) cv
  = opt_co4_wrap (zapLiftingContext env) sym rep r (coercionRep co)

  | Just cv1 <- lookupInScope (lcInScopeSet env) cv
  = ASSERT( isCoVar cv1 ) wrapRole rep r $ wrapSym sym (CoVarCo cv1)
                -- cv1 might have a substituted kind!

  | otherwise = WARN( True, text "opt_co: not in scope:" <+> ppr cv $$ ppr env)
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
    AxiomInstCo con ind (zipWith (opt_co2 env False)
                                 (coAxBranchRoles (coAxiomNthBranch con ind))
                                 cos)
      -- Note that the_co does *not* have sym pushed into it

opt_co4 env sym rep r (UnivCo prov _r t1 t2)
  = ASSERT( r == _r )
    opt_univ env sym prov (chooseRole rep r) t1 t2

opt_co4 env sym rep r (TransCo co1 co2)
                      -- sym (g `o` h) = sym h `o` sym g
  | sym       = opt_trans in_scope co2' co1'
  | otherwise = opt_trans in_scope co1' co2'
  where
    co1' = opt_co4_wrap env sym rep r co1
    co2' = opt_co4_wrap env sym rep r co2
    in_scope = lcInScopeSet env


opt_co4 env sym rep r co@(NthCo {}) = opt_nth_co env sym rep r co

opt_co4 env sym rep r (LRCo lr co)
  | Just pr_co <- splitAppCo_maybe co
  = ASSERT( r == Nominal )
    opt_co4_wrap env sym rep Nominal (pick_lr lr pr_co)
  | Just pr_co <- splitAppCo_maybe co'
  = ASSERT( r == Nominal )
    if rep
    then opt_co4_wrap (zapLiftingContext env) False True Nominal (pick_lr lr pr_co)
    else pick_lr lr pr_co
  | otherwise
  = wrapRole rep Nominal $ LRCo lr co'
  where
    co' = opt_co4_wrap env sym False Nominal co

    pick_lr CLeft  (l, _) = l
    pick_lr CRight (_, r) = r

-- See Note [Optimising InstCo]
opt_co4 env sym rep r (InstCo co1 arg)
    -- forall over type...
  | Just (tv, kind_co, co_body) <- splitForAllCo_maybe co1
  = opt_co4_wrap (extendLiftingContextRep env tv
                    (arg' `mkCoherenceRightCoRep` mkSymCo kind_co))
                 sym rep r co_body

    -- See if it is a forall after optimization
    -- If so, do an inefficient one-variable substitution, then re-optimize

    -- forall over type...
  | Just (tv', kind_co', co_body') <- splitForAllCo_maybe co1'
  = opt_co4_wrap (extendLiftingContextRep (zapLiftingContext env) tv'
                    (arg' `mkCoherenceRightCoRep` mkSymCo kind_co'))
            False False r' co_body'

  | otherwise = InstCo co1' arg'
  where
    co1' = opt_co4_wrap env sym rep r co1
    r'   = chooseRole rep r
    arg' = opt_co4_wrap env sym False Nominal arg

opt_co4 env sym rep r (CoherenceCo co1 co2)
  | TransCo col1 cor1 <- co1
  = opt_co4_wrap env sym rep r (mkTransCoRep (mkCoherenceCoRep col1 co2) cor1)

  | TransCo col1' cor1' <- co1'
  = if sym then opt_trans in_scope col1'
                  (opt_co1 (zapLiftingContext env) False
                           (mkCoherenceRightCoRep cor1' co2'))
           else opt_trans in_scope (mkCoherenceCoRep col1' co2') cor1'

  | otherwise
  = wrapSym sym $ CoherenceCo (opt_co4_wrap env False rep r co1) co2'
  where co1' = opt_co4_wrap env sym   rep   r       co1
        co2' = opt_co4_wrap_co env False False Nominal co2
        in_scope = lcInScopeSet env

opt_co4 env sym _rep r (KindCo co)
  = ASSERT( r == Nominal )
    let kco' = promoteCoercion co in
    case kco' of
      KindCo co' -> promoteCoercion (opt_co1 env sym co')
      _          -> opt_co4_wrap env sym False Nominal kco'
  -- This might be able to be optimized more to do the promotion
  -- and substitution/optimization at the same time

opt_co4 env sym repr r (SubCo _r co)
  = opt_co4_wrap env sym (repr || r == Representational) co_role co
  where
    co_role = ASSERT( r == _r )
              coercionRepRole co

-- This could perhaps be optimized more.
opt_co4 env sym rep r (AxiomRuleCo co cs)
  = ASSERT( r == coaxrRole co )
    wrapRole rep r $
    wrapSym sym $
    AxiomRuleCo co (zipWith (opt_co2 env False) (coaxrAsmpRoles co) cs)

-------------
-- | Optimize a phantom coercion. The input coercion may not necessarily
-- be a phantom, but the output sure will be.
opt_phantom :: LiftingContext -> SymFlag -> CoercionRep -> NormalCoRep
opt_phantom env sym co
  = opt_univ env sym (PhantomProv (mkKindCoRep co)) Phantom ty1 ty2
  where
    Pair ty1 ty2 = coercionRepKind co

opt_univ :: LiftingContext -> SymFlag -> UnivCoProvenance -> Role
         -> Type -> Type -> CoercionRep
opt_univ env sym (PhantomProv h) _r ty1 ty2
  | sym       = mkPhantomCoRep h' ty2' ty1'
  | otherwise = mkPhantomCoRep h' ty1' ty2'
  where
    h' = opt_co4 env sym False Nominal h
    ty1' = substTy (lcSubstLeft  env) ty1
    ty2' = substTy (lcSubstRight env) ty2

opt_univ env sym prov role oty1 oty2
  | Just (tc1, tys1) <- splitTyConApp_maybe oty1
  , Just (tc2, tys2) <- splitTyConApp_maybe oty2
  , tc1 == tc2
      -- NB: prov must not be the two interesting ones (ProofIrrel & Phantom);
      -- Phantom is already taken care of, and ProofIrrel doesn't relate tyconapps
  = let roles    = tyConRolesX role tc1
        arg_cos  = zipWith3 (mkUnivCoRep prov) roles tys1 tys2
        arg_cos' = zipWith (opt_co4 env sym False) roles arg_cos
    in
    mkTyConAppCoRep role tc1 arg_cos'

  -- can't optimize the AppTy case because we can't build the kind coercions.

  | Just (Named tv1 vis, ty1) <- splitPiTy_maybe oty1
  , Just (Named tv2 _,   ty2) <- splitPiTy_maybe oty2
      -- NB: prov isn't interesting here either
  = let k1   = tyVarKind tv1
        k2   = tyVarKind tv2
        eta  = mkUnivCo prov Nominal k1 k2
          -- eta gets opt'ed soon, but not yet.
        ty2' = substTyWith [tv2] [TyVarTy tv1 `mkCastTy` eta] ty2

        (env', tv1', eta') = optForAllCoBndr env sym tv1 eta
    in
    mkForAllCoRep tv1' vis eta' (opt_univ env' sym prov role ty1 ty2')

  | otherwise
  = let ty1 = substTyUnchecked (lcSubstLeft  env) oty1
        ty2 = substTyUnchecked (lcSubstRight env) oty2
        (a, b) | sym       = (ty2, ty1)
               | otherwise = (ty1, ty2)
    in
    mkUnivCoRep prov' role a b

  where
    prov' = case prov of
      UnsafeCoerceProv   -> prov
      PhantomProv kco    -> PhantomProv $ opt_co4_wrap env sym False Nominal kco
      ProofIrrelProv kco -> ProofIrrelProv $ opt_co4_wrap env sym False Nominal kco
      PluginProv _       -> prov
      HoleProv h         -> pprPanic "opt_univ fell into a hole" (ppr h)


-------------
-- NthCo must be handled separately, because it's the one case where we can't
-- tell quickly what the component coercion's role is from the containing
-- coercion. To avoid repeated coercionRole calls as opt_co1 calls opt_co2,
-- we just look for nested NthCo's, which can happen in practice.
opt_nth_co :: LiftingContext -> SymFlag -> ReprFlag -> Role -> CoercionRep -> NormalCoRep
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
      , Just (tv, _) <- splitForAllTy_maybe ty
      = Just (Refl Nominal (tyVarKind tv))
    push_nth n (TyConAppCo _ _ cos)
      = Just (cos `getNth` n)
    push_nth 0 (ForAllCo _ _ eta _)
      = Just (coercionRep eta)
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
        then opt_co4_wrap (zapLiftingContext env) False True r co
        else co
    opt_nths' (n:ns) co
      | Just co' <- push_nth n co
      = opt_nths' ns co'
    opt_nths' ns co = wrapRole rep r (mk_nths ns co)

    mk_nths [] co = co
    mk_nths (n:ns) co = mk_nths ns (mkNthCoRep n co)

-------------
opt_transList :: InScopeSet -> [NormalCoRep] -> [NormalCoRep] -> [NormalCoRep]
opt_transList is = zipWith (opt_trans is)

opt_trans_co :: InScopeSet -> NormalCo -> NormalCo -> NormalCo
opt_trans_co is co1 co2
  = CachedCoercion { coercionKind    = Pair ty1 ty3
                   , coercionRole    = coercionRole co1
                   , tyCoVarsOfCoAcc = mapUnionFV tyCoVarsOfCoAcc [co1, co2]
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = opt_trans is (coercionRep co1)
                                                    (coercionRep co2) }
  where
    Pair ty1 _ = coercionKind co1
    Pair _ ty3 = coercionKind co2

opt_trans :: InScopeSet -> NormalCoRep -> NormalCoRep -> NormalCoRep
opt_trans is co1 co2
  | Refl {} <- co1 = co2
  | otherwise      = opt_trans1 is co1 co2

opt_trans1 :: InScopeSet -> NormalNonIdCoRep -> NormalCoRep -> NormalCoRep
-- First arg is not the identity
opt_trans1 is co1 co2
  | Refl {} <- co2 = co1
  | otherwise      = opt_trans2 is co1 co2

opt_trans2 :: InScopeSet -> NormalNonIdCoRep -> NormalNonIdCoRep -> NormalCoRep
-- Neither arg is the identity
opt_trans2 is (TransCo co1a co1b) co2
    -- Don't know whether the sub-coercions are the identity
  = opt_trans is co1a (opt_trans is co1b co2)

opt_trans2 is co1 co2
  | Just co <- opt_trans_rule is co1 co2
  = co

opt_trans2 is co1 (TransCo co2a co2b)
  | Just co1_2a <- opt_trans_rule is co1 co2a
  = case co1_2a of
      Refl {} -> co2b
      _       -> opt_trans1 is co1_2a co2b

opt_trans2 _ co1 co2
  = mkTransCoRep co1 co2

------
-- Optimize coercions with a top-level use of transitivity.
opt_trans_rule :: InScopeSet -> NormalNonIdCoRep -> NormalNonIdCoRep -> Maybe NormalCoRep

-- Push transitivity through matching destructors
opt_trans_rule is in_co1@(NthCo d1 co1) in_co2@(NthCo d2 co2)
  | d1 == d2
  , co1 `compatible_co` co2
  = fireTransRule "PushNth" in_co1 in_co2 $
    mkNthCoRep d1 (opt_trans is co1 co2)

opt_trans_rule is in_co1@(LRCo d1 co1) in_co2@(LRCo d2 co2)
  | d1 == d2
  , co1 `compatible_co` co2
  = fireTransRule "PushLR" in_co1 in_co2 $
    mkLRCoRep d1 (opt_trans is co1 co2)

-- Push transitivity inside instantiation
opt_trans_rule is in_co1@(InstCo co1 ty1) in_co2@(InstCo co2 ty2)
  | ty1 `eqCoercionRep` ty2
  , co1 `compatible_co` co2
  = fireTransRule "TrPushInst" in_co1 in_co2 $
    mkInstCoRep (opt_trans is co1 co2) ty1

opt_trans_rule is in_co1@(UnivCo p1 r1 tyl1 _tyr1)
                  in_co2@(UnivCo p2 r2 _tyl2 tyr2)
  | Just prov' <- opt_trans_prov p1 p2
  = ASSERT( r1 == r2 )
    fireTransRule "UnivCo" in_co1 in_co2 $
    mkUnivCoRep prov' r1 tyl1 tyr2
  where
    -- if the provenances are different, opt'ing will be very confusing
    opt_trans_prov UnsafeCoerceProv      UnsafeCoerceProv      = Just UnsafeCoerceProv
    opt_trans_prov (PhantomProv kco1)    (PhantomProv kco2)
      = Just $ PhantomProv $ opt_trans is kco1 kco2
    opt_trans_prov (ProofIrrelProv kco1) (ProofIrrelProv kco2)
      = Just $ ProofIrrelProv $ opt_trans is kco1 kco2
    opt_trans_prov (PluginProv str1)     (PluginProv str2)     | str1 == str2 = Just p1
    opt_trans_prov _ _ = Nothing

-- Push transitivity down through matching top-level constructors.
opt_trans_rule is in_co1@(TyConAppCo r1 tc1 cos1) in_co2@(TyConAppCo r2 tc2 cos2)
  | tc1 == tc2
  = ASSERT( r1 == r2 )
    fireTransRule "PushTyConApp" in_co1 in_co2 $
    mkTyConAppCoRep r1 tc1 (opt_transList is cos1 cos2)

opt_trans_rule is in_co1@(AppCo co1a co1b) in_co2@(AppCo co2a co2b)
  = fireTransRule "TrPushApp" in_co1 in_co2 $
    mkAppCoRep (opt_trans is co1a co2a)
               (opt_trans is co1b co2b)

-- Eta rules
opt_trans_rule is co1@(TyConAppCo r tc cos1) co2
  | Just cos2 <- etaTyConAppCo_maybe r tc co2
  = ASSERT( length cos1 == length cos2 )
    fireTransRule "EtaCompL" co1 co2 $
    mkTyConAppCoRep r tc (opt_transList is cos1 cos2)

opt_trans_rule is co1 co2@(TyConAppCo r tc cos2)
  | Just cos1 <- etaTyConAppCo_maybe r tc co1
  = ASSERT( length cos1 == length cos2 )
    fireTransRule "EtaCompR" co1 co2 $
    mkTyConAppCoRep r tc (opt_transList is cos1 cos2)

opt_trans_rule is co1@(AppCo co1a co1b) co2
  | Just (co2a,co2b) <- etaAppCo_maybe co2
  = fireTransRule "EtaAppL" co1 co2 $
    mkAppCoRep (opt_trans is co1a co2a)
            (opt_trans is co1b co2b)

opt_trans_rule is co1 co2@(AppCo co2a co2b)
  | Just (co1a,co1b) <- etaAppCo_maybe co1
  = fireTransRule "EtaAppR" co1 co2 $
    mkAppCoRep (opt_trans is co1a co2a)
               (opt_trans is co1b co2b)

-- Push transitivity inside forall
opt_trans_rule is co1 co2
  | ForAllCo tv1 vis eta1 r1 <- co1
  , Just (tv2,eta2,r2) <- etaForAllCo_maybe co2
  = push_trans vis tv1 eta1 r1 tv2 eta2 r2

  | ForAllCo tv2 vis eta2 r2 <- co2
  , Just (tv1,eta1,r1) <- etaForAllCo_maybe co1
  = push_trans vis tv1 eta1 r1 tv2 eta2 r2

  where
  push_trans vis tv1 eta1 r1 tv2 eta2 r2
    = fireTransRule "EtaAllTy" co1 co2 $
      mkForAllCoRep tv1 vis (opt_trans_co is eta1 eta2) (opt_trans is' r1 r2')
    where
      is' = is `extendInScopeSet` tv1
      r2' = substCoRepWithUnchecked [tv2] [TyVarTy tv1] r2

-- Push transitivity inside axioms
opt_trans_rule is co1 co2

  -- See Note [Why call checkAxInstCo during optimisation]
  -- TrPushSymAxR
  | Just (sym, con, ind, cos1) <- co1_is_axiom_maybe
  , True <- sym
  , Just cos2 <- matchAxiom sym con ind co2
  , let newAxInst = AxiomInstCo con ind (opt_transList is (map mkSymCoRep cos2) cos1)
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
  , let newAxInst = AxiomInstCo con ind (opt_transList is cos2 (map mkSymCoRep cos1))
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
        qtvs = coAxBranchTyVars branch ++ coAxBranchCoVars branch
        lhs  = coAxNthLHS con1 ind1
        rhs  = coAxBranchRHS branch
        pivot_tvs = exactTyCoVarsOfType (if sym2 then rhs else lhs)
  , all (`elemVarSet` pivot_tvs) qtvs
  = fireTransRule "TrPushAxSym" co1 co2 $
    if sym2
       -- TrPushAxSym
    then liftCoRepSubstWith role qtvs (opt_transList is cos1 (map mkSymCoRep cos2)) lhs
       -- TrPushSymAx
    else liftCoRepSubstWith role qtvs (opt_transList is (map mkSymCoRep cos1) cos2) rhs
  where
    co1_is_axiom_maybe = isAxiom_maybe co1
    co2_is_axiom_maybe = isAxiom_maybe co2
    role = coercionRepRole co1 -- should be the same as coercionRepRole co2!

opt_trans_rule is co1 co2
  | Just (lco, lh) <- isCohRight_maybe co1
  , Just (rco, rh) <- isCohLeft_maybe co2
  , lh `eqCoercion` rh
  = opt_trans_rule is lco rco

opt_trans_rule _ co1 co2        -- Identity rule
  | (Pair ty1 _, r) <- coercionRepKindRole co1
  , Pair _ ty2 <- coercionRepKind co2
  , ty1 `eqType` ty2
  = fireTransRule "RedTypeDirRefl" co1 co2 $
    Refl r ty2

opt_trans_rule _ _ _ = Nothing

fireTransRule :: String -> CoercionRep -> CoercionRep -> CoercionRep -> Maybe CoercionRep
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
the first branch should be taken. See also Note [Apartness] in
types/FamInstEnv.hs.

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
checkAxInstCo :: CoercionRep -> Maybe CoAxBranch
-- defined here to avoid dependencies in Coercion
-- If you edit this function, you may need to update the GHC formalism
-- See Note [GHC Formalism] in CoreLint
checkAxInstCo (AxiomInstCo ax ind cos)
  = let branch       = coAxiomNthBranch ax ind
        tvs          = coAxBranchTyVars branch
        cvs          = coAxBranchCoVars branch
        incomps      = coAxBranchIncomps branch
        (tys, cotys) = splitAtList tvs (map (pFst . coercionRepKind) cos)
        co_args      = map stripCoercionTy cotys
        subst        = zipTvSubst tvs tys `composeTCvSubst`
                       zipCvSubst cvs co_args
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
wrapSym :: SymFlag -> CoercionRep -> CoercionRep
wrapSym sym co | sym       = SymCo co
               | otherwise = co

-- | Conditionally set a role to be representational
wrapRole :: ReprFlag
         -> Role         -- ^ current role
         -> CoercionRep -> CoercionRep
wrapRole False _       = id
wrapRole True  current = downgradeRoleRep Representational current

-- | If we require a representational role, return that. Otherwise,
-- return the "default" role provided.
chooseRole :: ReprFlag
           -> Role    -- ^ "default" role
           -> Role
chooseRole True _ = Representational
chooseRole _    r = r

-----------
isAxiom_maybe :: CoercionRep -> Maybe (Bool, CoAxiom Branched, Int, [CoercionRep])
isAxiom_maybe (SymCo co)
  | Just (sym, con, ind, cos) <- isAxiom_maybe co
  = Just (not sym, con, ind, cos)
isAxiom_maybe (AxiomInstCo con ind cos)
  = Just (False, con, ind, cos)
isAxiom_maybe _ = Nothing

matchAxiom :: Bool -- True = match LHS, False = match RHS
           -> CoAxiom br -> Int -> CoercionRep -> Maybe [CoercionRep]
matchAxiom sym ax@(CoAxiom { co_ax_tc = tc }) ind co
  | CoAxBranch { cab_tvs = qtvs
               , cab_cvs = []   -- can't infer these, so fail if there are any
               , cab_roles = roles
               , cab_lhs = lhs
               , cab_rhs = rhs } <- coAxiomNthBranch ax ind
  , Just subst <- liftCoMatch (mkVarSet qtvs)
                              (if sym then (mkTyConApp tc lhs) else rhs)
                              co
  , all (`isMappedByLC` subst) qtvs
  = fmap (map coercionRep) $ zipWithM (liftCoSubstTyVar subst) roles qtvs

  | otherwise
  = Nothing

-------------
-- destruct a CoherenceCo
isCohLeft_maybe :: CoercionRep -> Maybe (CoercionRep, Coercion)
isCohLeft_maybe (CoherenceCo co1 co2) = Just (co1, co2)
isCohLeft_maybe _                     = Nothing

-- destruct a (sym (co1 |> co2)).
-- if isCohRight_maybe co = Just (co1, co2), then (sym co1) `mkCohRightCo` co2 = co
isCohRight_maybe :: CoercionRep -> Maybe (CoercionRep, Coercion)
isCohRight_maybe (SymCo (CoherenceCo co1 co2)) = Just (mkSymCoRep co1, co2)
isCohRight_maybe _                             = Nothing

-------------
compatible_co :: CoercionRep -> CoercionRep -> Bool
-- Check whether (co1 . co2) will be well-kinded
compatible_co co1 co2
  = x1 `eqType` x2
  where
    Pair _ x1 = coercionRepKind co1
    Pair x2 _ = coercionRepKind co2

-------------
{-
etaForAllCo_maybe
~~~~~~~~~~~~~~~~~
Suppose we have

  g : all a1:k1.t1  ~  all a2:k2.t2

but g is *not* a ForAllCo. We want to eta-expand it. So, we do this:

  g' = all a1:(ForAllKindCo g).(InstCo g (a1 `mkCoherenceRightCo` ForAllKindCo g))

Call the kind coercion h1 and the body coercion h2. We can see that

  h2 : t1 ~ t2[a2 |-> (a1 |> h2)]

According to the typing rule for ForAllCo, we get that

  g' : all a1:k1.t1  ~  all a1:k2.(t2[a2 |-> (a1 |> h2)][a1 |-> a1 |> sym h2])

or

  g' : all a1:k1.t1  ~  all a1:k2.(t2[a2 |-> a1])

as desired.
-}
etaForAllCo_maybe :: CoercionRep -> Maybe (TyVar, Coercion, CoercionRep)
-- Try to make the coercion be of form (forall tv:kind_co. co)
etaForAllCo_maybe co
  | ForAllCo tv _ kind_co r <- co
  = Just (tv, kind_co, r)

  | Pair ty1 ty2  <- coercionRepKind co
  , Just (tv1, _) <- splitForAllTy_maybe ty1
  , isForAllTy ty2
  , let kind_co    = mkNthCo 0 (mkCachedCoercion co)
  = Just ( tv1, kind_co
         , mkInstCoRep co $
           Refl Nominal (TyVarTy tv1) `mkCoherenceRightCoRep` kind_co )

  | otherwise
  = Nothing

etaAppCo_maybe :: CoercionRep -> Maybe (CoercionRep,CoercionRep)
-- If possible, split a coercion
--   g :: t1a t1b ~ t2a t2b
-- into a pair of coercions (left g, right g)
etaAppCo_maybe co
  | Just (co1,co2) <- splitAppCo_maybe co
  = Just (co1,co2)
  | (Pair ty1 ty2, Nominal) <- coercionRepKindRole co
  , Just (_,t1) <- splitAppTy_maybe ty1
  , Just (_,t2) <- splitAppTy_maybe ty2
  , let isco1 = isCoercionTy t1
  , let isco2 = isCoercionTy t2
  , isco1 == isco2
  = Just (LRCo CLeft co, LRCo CRight co)
  | otherwise
  = Nothing

etaTyConAppCo_maybe :: Role  -- of the CoercionRep
                    -> TyCon -> CoercionRep -> Maybe [CoercionRep]
-- If possible, split a coercion
--       g :: T s1 .. sn ~ T t1 .. tn
-- into [ Nth 0 g :: s1~t1, ..., Nth (n-1) g :: sn~tn ]
etaTyConAppCo_maybe _ tc (TyConAppCo _ tc2 cos2)
  = ASSERT( tc == tc2 ) Just cos2

etaTyConAppCo_maybe r tc co
  | mightBeUnsaturatedTyCon tc
  , isInjectiveTyCon tc r
  , Pair ty1 ty2     <- coercionRepKind co
  , Just (tc1, tys1) <- splitTyConApp_maybe ty1
  , Just (tc2, tys2) <- splitTyConApp_maybe ty2
  , tc1 == tc2
  , let n = length tys1
  = ASSERT( tc == tc1 )
    ASSERT( n == length tys2 )
    Just (decomposeCoRep n co)
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

optForAllCoBndr :: LiftingContext -> Bool
                -> TyVar -> Coercion -> (LiftingContext, TyVar, Coercion)
optForAllCoBndr env sym
  = substForAllCoBndrCallbackLC sym (opt_co4_wrap_co env sym False Nominal) env

{- *********************************************************************
*                                                                      *
         Support functions
*                                                                      *
************************************************************************

These don't deal directly with optimizing coercions, per se, but they are
needed only within this module.

-}

-- | Retrieve the role from a coercion.
coercionRepRole :: CoercionRep -> Role
coercionRepRole = snd . coercionRepKindRole
  -- There's not a better way to do this, because NthCo needs the *kind*
  -- and role of its argument. Luckily, laziness should generally avoid
  -- the need for computing kinds in other cases.

-- | Syntactic equality of coercions
eqCoercionRep :: CoercionRep -> CoercionRep -> Bool
eqCoercionRep co1 co2 = and (eqType <$> coercionRepKind co1 <*> coercionRepKind co2)

-- | Compare two 'CoercionRep's, with respect to an RnEnv2
eqCoercionRepX :: RnEnv2 -> CoercionRep -> CoercionRep -> Bool
eqCoercionRepX env co1 co2
  = and (eqTypeX env <$> coercionRepKind co1 <*> coercionRepKind co2)

mkCoherenceRightCoRep :: CoercionRep -> Coercion -> CoercionRep
mkCoherenceRightCoRep c1 c2 = mkSymCoRep (mkCoherenceCoRep (mkSymCoRep c1) c2)

substCoRepWithUnchecked :: [TyVar] -> [Type] -> CoercionRep -> CoercionRep
substCoRepWithUnchecked tvs tys co = substCoRepUnchecked (zipTvSubst tvs tys) co

-- NB: works only with Nominal coercions
extendLiftingContextRep :: LiftingContext -> TyVar -> CoercionRepN -> LiftingContext
extendLiftingContextRep lc tv rep
  = extendLiftingContext lc tv (mkCachedCoercion rep)

liftCoRepSubstWith :: Role -> [TyCoVar] -> [CoercionRep] -> Type -> CoercionRep
-- NB: This really can be called with CoVars, when optimising axioms.
liftCoRepSubstWith r tvs coreps ty
  = liftCoRepSubst r (mkLiftingContext $ zipEqual "liftCoSubstWith" tvs cos) ty
  where
    cos = map mkCachedCoercion coreps

{-
%************************************************************************
%*                                                                      *
            Matching a (lifted) type against a coercion
%*                                                                      *
%************************************************************************

This section defines essentially an inverse to liftCoSubst.

-}

data MatchEnv = ME { me_tmpls :: TyVarSet
                   , me_env   :: RnEnv2 }

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
liftCoMatch :: TyCoVarSet -> Type -> CoercionRep -> Maybe LiftingContext
liftCoMatch tmpls ty co
  = do { cenv1 <- ty_co_match menv emptyVarEnv ki ki_co ki_ki_co ki_ki_co
       ; cenv2 <- ty_co_match menv cenv1       ty co
                              (mkNomReflCo co_lkind) (mkNomReflCo co_rkind)
       ; return (LC (mkEmptyTCvSubst in_scope) cenv2) }
  where
    menv     = ME { me_tmpls = tmpls, me_env = mkRnEnv2 in_scope }
    in_scope = mkInScopeSet (tmpls `unionVarSet` tyCoVarsOfCoRep co)
    -- Like tcMatchTy, assume all the interesting variables
    -- in ty are in tmpls

    ki       = typeKind ty
    ki_co    = promoteCoercion co
    ki_ki_co = mkNomReflCo liftedTypeKind

    Pair co_lkind co_rkind = coercionRepKind ki_co

-- | 'ty_co_match' does all the actual work for 'liftCoMatch'.
ty_co_match :: MatchEnv      -- ^ ambient helpful info
            -> LiftCoEnv     -- ^ incoming subst
            -> Type          -- ^ ty, type to match
            -> CoercionRep   -- ^ co, coercion to match against
            -> Coercion      -- ^ :: kind of L type of substed ty ~N L kind of co
            -> Coercion      -- ^ :: kind of R type of substed ty ~N R kind of co
            -> Maybe LiftCoEnv
ty_co_match menv subst ty co lkco rkco
  | Just ty' <- coreViewOneStarKind ty = ty_co_match menv subst ty' co lkco rkco

  -- handle Refl case:
  | tyCoVarsOfType ty `isNotInDomainOf` subst
  , Refl _ ty' <- co
  , ty `eqType` ty'
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
  | Just co1' <- lookupVarEnv subst tv1' -- tv1' is already bound to co1
  = if eqCoercionRepX (nukeRnEnvL rn_env) (coercionRep co1') co
    then Just subst
    else Nothing       -- no match since tv1 matches two different coercions

  | tv1' `elemVarSet` me_tmpls menv           -- tv1' is a template var
  = if any (inRnEnvR rn_env) (tyCoVarsOfCoRepList co)
    then Nothing      -- occurs check failed
    else Just $ extendVarEnv subst tv1' $
                castCoercionKind (mkCachedCoercion co) (mkSymCo lkco) (mkSymCo rkco)

  | otherwise
  = Nothing

  where
    rn_env = me_env menv
    tv1' = rnOccL rn_env tv1

  -- just look through SubCo's. We don't really care about roles here.
ty_co_match menv subst ty (SubCo _ co) lkco rkco
  = ty_co_match menv subst ty co lkco rkco

ty_co_match menv subst (AppTy ty1a ty1b) co _lkco _rkco
  | Just (co2, arg2) <- splitAppCo_maybe co     -- c.f. Unify.match on AppTy
  = ty_co_match_app menv subst ty1a ty1b co2 arg2
ty_co_match menv subst ty1 (AppCo co2 arg2) _lkco _rkco
  | Just (ty1a, ty1b) <- repSplitAppTy_maybe ty1
       -- yes, the one from Type, not TcType; this is for coercion optimization
  = ty_co_match_app menv subst ty1a ty1b co2 arg2

ty_co_match menv subst (TyConApp tc1 tys) (TyConAppCo _ tc2 cos) _lkco _rkco
  = ty_co_match_tc menv subst tc1 tys tc2 cos
ty_co_match menv subst (ForAllTy (Anon ty1) ty2) (TyConAppCo _ tc cos) _lkco _rkco
  = ty_co_match_tc menv subst funTyCon [ty1, ty2] tc cos

ty_co_match menv subst (ForAllTy (Named tv1 _) ty1)
                       (ForAllCo tv2 _ kind_co2 co2)
                       lkco rkco
  = do { subst1 <- ty_co_match menv subst (tyVarKind tv1) (coercionRep kind_co2)
                               ki_ki_co ki_ki_co
       ; let rn_env0 = me_env menv
             rn_env1 = rnBndr2 rn_env0 tv1 tv2
             menv'   = menv { me_env = rn_env1 }
       ; ty_co_match menv' subst1 ty1 co2 lkco rkco }
  where
    ki_ki_co = mkNomReflCo liftedTypeKind

ty_co_match _ subst (CoercionTy {}) _ _ _
  = Just subst -- don't inspect coercions

ty_co_match menv subst ty co lkco rkco
  | Just co' <- pushRefl co = ty_co_match menv subst ty co' lkco rkco
  | otherwise               = Nothing

ty_co_match_tc :: MatchEnv -> LiftCoEnv
               -> TyCon -> [Type]
               -> TyCon -> [CoercionRep]
               -> Maybe LiftCoEnv
ty_co_match_tc menv subst tc1 tys1 tc2 cos2
  = do { guard (tc1 == tc2)
       ; ty_co_match_args menv subst tys1 cos2 lkcos rkcos }
  where
    Pair lkcos rkcos
      = traverse (fmap mkNomReflCo . coercionRepKind) cos2

ty_co_match_app :: MatchEnv -> LiftCoEnv
                -> Type -> Type -> CoercionRep -> CoercionRep
                -> Maybe LiftCoEnv
ty_co_match_app menv subst ty1a ty1b co2a co2b
  = do { -- TODO (RAE): Remove this exponential behavior.
         subst1 <- ty_co_match menv subst  ki1a ki2a ki_ki_co ki_ki_co
       ; let Pair lkco rkco = mkNomReflCo <$> coercionRepKind ki2a
       ; subst2 <- ty_co_match menv subst1 ty1a co2a lkco rkco
       ; ty_co_match menv subst2 ty1b co2b (mkNthCo 0 lkco) (mkNthCo 0 rkco) }
  where
    ki1a = typeKind ty1a
    ki2a = promoteCoercion co2a
    ki_ki_co = mkNomReflCo liftedTypeKind

ty_co_match_args :: MatchEnv -> LiftCoEnv -> [Type]
                 -> [CoercionRep] -> [Coercion] -> [Coercion]
                 -> Maybe LiftCoEnv
ty_co_match_args _    subst []       []         _ _ = Just subst
ty_co_match_args menv subst (ty:tys) (arg:args) (lkco:lkcos) (rkco:rkcos)
  = do { subst' <- ty_co_match menv subst ty arg lkco rkco
       ; ty_co_match_args menv subst' tys args lkcos rkcos }
ty_co_match_args _    _     _        _          _ _ = Nothing

pushRefl :: CoercionRep -> Maybe CoercionRep
pushRefl (Refl Nominal (AppTy ty1 ty2))
  = Just (AppCo (Refl Nominal ty1) (Refl Nominal ty2))
pushRefl (Refl r (ForAllTy (Anon ty1) ty2))
  = Just (TyConAppCo r funTyCon [Refl r ty1, Refl r ty2])
pushRefl (Refl r (TyConApp tc tys))
  = Just (TyConAppCo r tc (zipWith Refl (tyConRolesX r tc) tys))
pushRefl (Refl r (ForAllTy (Named tv _) ty))
  = Just (coercionRep $ mkHomoForAllCos_NoRefl [tv] (mkReflCo r ty))
    -- NB: NoRefl variant. Otherwise, we get a loop!
pushRefl (Refl r (CastTy ty co))  = Just (castCoercionKindRep (Refl r ty) co co)
pushRefl _                        = Nothing

-- | like mkKindCoRep, but aggressively & recursively optimizes to avoid using
-- a KindCo constructor. The output role is nominal.
promoteCoercion :: CoercionRep -> CoercionRepN

-- First cases handles anything that should yield refl.
promoteCoercion = go
  where
    go corep = case corep of
      Refl _ ty -> Refl Nominal (typeKind ty)

      TyConAppCo _ tc args
        -> instCoercions (tyConBinders tc) (tyConResKind tc) args

      AppCo {}
        -> mkKindCoRep corep

      ForAllCo _ _ _ g
        -> go g

      CoVarCo {}
        -> mkKindCoRep corep

      AxiomInstCo {}
        -> mkKindCoRep corep

      UnivCo UnsafeCoerceProv _ t1 t2
        -> mkUnivCoRep UnsafeCoerceProv Nominal (typeKind t1) (typeKind t2)

      UnivCo (PhantomProv kco) _ _ _
        -> kco
      UnivCo (ProofIrrelProv kco) _ _ _
        -> kco

      UnivCo (PluginProv _) _ _ _
        -> mkKindCoRep corep

      UnivCo (HoleProv _) _ _ _
        -> mkKindCoRep corep

      SymCo g
        -> mkSymCoRep (go g)

      TransCo co1 co2
        -> mkTransCoRep (go co1) (go co2)

      NthCo n co1
        | Just (_, args) <- splitTyConAppCo_maybe co1
        , n < length args
        -> go (args !! n)

        | Just _ <- splitForAllCo_maybe co1
        , n == 0
        -> mkReflCoRep Nominal liftedTypeKind

        | otherwise
        -> mkKindCoRep corep

      LRCo lr co1
        | Just (lco, rco) <- splitAppCo_maybe co1
        -> case lr of
             CLeft  -> go lco
             CRight -> go rco

        | otherwise
        -> mkKindCoRep corep

      InstCo g _
        -> go g

      CoherenceCo g h
        -> mkSymCoRep (coercionRep h) `mkTransCoRep` go g

      KindCo _
        -> mkReflCoRep Nominal liftedTypeKind

      SubCo _ co
        -> go co

      AxiomRuleCo {}
        -> mkKindCoRep corep

-- | say @g = promoteCoercion h@. Then, @instCoercion g w@ yields @Just g'@,
-- where @g' = promoteCoercion (h w)@.
-- This function assumes that the roles work out.
instCoercion :: Bool         -- ^ does the first coercion relate named foralls?
             -> CoercionRep  -- ^ must be nominal
             -> CoercionRep
             -> CoercionRep
instCoercion True  g w
  = mkInstCoRep g w
instCoercion False g _
  = mkNthCoRep 1 g -- extract result type, which is the 2nd argument to (->)

-- | Suppose tc :: forall k1. k1 -> *, and co1 :: k1 ~ k1'.
-- Now, say
-- h = instCoercions (forall k1. k1 -> *) [co1].
-- Then, h :: (k1 -> *) ~ (k1' -> *).
instCoercions :: [TyBinder] -> Kind -> [CoercionRep] -> CoercionRep
instCoercions bndrs res_kind ws
  = foldl go (Refl Nominal $ mkForAllTys bndrs res_kind) (is_foralls `zip` ws)
  where
    is_foralls = map isNamedBinder bndrs ++ repeat False
       -- the repeat False is just in case the tycon is oversaturated
       -- This can happen only if the return kind of the tycon is a type
       -- variable. Accordingly, predicativity tells us that any oversaturated
       -- applications are non-dependent

    go :: CoercionRep -> (Bool, CoercionRep) -> CoercionRep
    go root (is_forall, arg)
      = instCoercion is_forall root arg

-- | This breaks a 'CoercionRep' with type @T A B C ~ T D E F@ into
-- a list of 'CoercionRep's of kinds @A ~ D@, @B ~ E@ and @E ~ F@. Hence:
--
-- > decomposeCoRep 3 c = [nth 0 c, nth 1 c, nth 2 c]
decomposeCoRep :: Int -> CoercionRep -> [CoercionRep]
decomposeCoRep arity co
  = [mkNthCoRep n co | n <- [0..(arity-1)] ]
           -- Remember, Nth is zero-indexed
