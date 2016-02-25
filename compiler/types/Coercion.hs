{-
(c) The University of Glasgow 2006
-}

{-# LANGUAGE RankNTypes, CPP, DeriveDataTypeable, MultiWayIf #-}

-- | Module for (a) type kinds and (b) type coercions,
-- as used in System FC. See 'CoreSyn.Expr' for
-- more on System FC and how coercions fit into it.
--
module Coercion (
        -- * Main data type
        Coercion, CoercionRep, CoercionN, CoercionR, CoercionP,
        UnivCoProvenance, CoercionHole, LeftOrRight(..),
        Var, CoVar, TyCoVar,
        Role(..), ltRole,

        -- ** Functions over coercions
        coVarTypes, coVarKind, coVarKindsTypesRole, coVarRole,
        coercionType, coercionKind, coercionKinds,
        mkCoercionType,
        coercionRole, coercionKindRole, coercionRepKindRole,
        coercionRepKind,

        -- ** Constructing coercions
        mkCoercion,
        mkReflCo, mkRepReflCo, mkNomReflCo,
        mkCoVarCo, mkCoVarCos,
        mkAxInstCo, mkUnbranchedAxInstCo,
        mkAxInstRHS, mkUnbranchedAxInstRHS,
        mkAxInstLHS, mkUnbranchedAxInstLHS,
        mkPiCo, mkPiCos, mkCoCast,
        mkSymCo, mkTransCo, mkTransAppCo,
        mkNthCo, mkNthCoRole, mkLRCo,
        mkInstCo, mkAppCo, mkAppCos, mkTyConAppCo, mkFunCo, mkFunCos,
        mkForAllCo, mkForAllCos, mkHomoForAllCos, mkHomoForAllCos_NoRefl,
        mkPhantomCo, mkHomoPhantomCo, toPhantomCo,
        mkUnsafeCo, mkHoleCo, mkHoleCoRep, mkUnivCo, mkSubCo, mkSubRoleCo,
        mkAxiomInstCo, mkProofIrrelCo,
        downgradeRole, maybeSubCo, mkAxiomRuleCo,
        mkCoherenceCo, mkCoherenceRightCo, mkCoherenceLeftCo,
        mkKindCo, castCoercionKind,

        mkHeteroCoercionType,

        mkCachedCoercion,

        -- ** Decomposition
        instNewTyCon_maybe,

        NormaliseStepper, NormaliseStepResult(..), composeSteppers,
        modifyStepResultCo, unwrapNewTypeStepper,
        topNormaliseNewType_maybe, topNormaliseTypeX_maybe,

        decomposeCo,
        splitTyConAppCo_maybe,
        splitAppCo_maybe,
        splitForAllCo_maybe,

        nthRole, tyConRolesX, tyConRolesRepresentational, setNominalRole_maybe,

        pickLR,

        isReflCo, isReflCo_maybe, isReflexiveCo, isReflexiveCo_maybe,

        -- ** Coercion variables
        mkCoVar, isCoVar, coVarName, setCoVarName, setCoVarUnique,
        isCoVar_maybe,

        -- ** Free variables
        tyCoVarsOfCo, tyCoVarsOfCos, coVarsOfCo,
        tyCoVarsOfCoAcc, tyCoVarsOfCosAcc, tyCoVarsOfCoDSet,
        coercionSize,

        -- ** Substitution
        CvSubstEnv, emptyCvSubstEnv,
        lookupCoVar,
        substCo, substCos, substCoVar, substCoVars, substCoWith,
        substCoVarBndr,
        extendTvSubstAndInScope, getCvSubstEnv,

        -- ** Lifting
        liftCoSubst, liftCoRepSubst,
        liftCoSubstTyVar, liftCoSubstWith, liftCoSubstWithEx,
        emptyLiftingContext, extendLiftingContext,
        liftCoSubstVarBndrCallback, isMappedByLC,

        mkSubstLiftingContext, zapLiftingContext, mkLiftingContext,
        substForAllCoBndrCallbackLC, lcTCvSubst, lcInScopeSet,

        LiftCoEnv, LiftingContext(..), liftEnvSubstLeft, liftEnvSubstRight,
        swapLiftCoEnv, lcSubstLeft, lcSubstRight, lcSubst, substLeftCo,
        substRightCo,

        -- ** Comparison
        eqCoercion, eqCoercionX,

        -- ** Forcing evaluation of coercions
        seqCo,

        -- * Pretty-printing
        pprCo, pprParendCo, pprCoRep,
        pprCoAxiom, pprCoAxBranch, pprCoAxBranchHdr,

        -- * Tidying
        tidyCo, tidyCos

       ) where

#include "HsVersions.h"

import TyCoRep
import Type
import TyCon
import CoAxiom
import Var
import VarEnv
import VarSet
import FV
import Name hiding ( varName )
import Util
import BasicTypes
import Outputable
import Unique
import Pair
import SrcLoc
import PrelNames
import TysPrim          ( eqPhantPrimTyCon )
import ListSetOps
import Maybes

import Data.Function ( on )
import Control.Applicative ( liftA2 )
import Control.Arrow ( first )

{-
%************************************************************************
%*                                                                      *
     -- The coercion arguments always *precisely* saturate
     -- arity of (that branch of) the CoAxiom.  If there are
     -- any left over, we use AppCo.  See
     -- See [Coercion axioms applied to coercions]

\subsection{Coercion variables}
%*                                                                      *
%************************************************************************
-}

coVarName :: CoVar -> Name
coVarName = varName

setCoVarUnique :: CoVar -> Unique -> CoVar
setCoVarUnique = setVarUnique

setCoVarName :: CoVar -> Name -> CoVar
setCoVarName   = setVarName

coercionSize :: Coercion -> Int
coercionSize = go . coercionRep
  where
    go (Refl _ ty)            = typeSize ty
    go (TyConAppCo _ _ args)  = 1 + sum (map go args)
    go (AppCo co arg)         = go co + go arg
    go (ForAllCo _ _ h co)    = 1 + go co + go (coercionRep h)
    go (CoVarCo _)            = 1
    go (AxiomInstCo _ _ args) = 1 + sum (map go args)
    go (UnivCo p _ t1 t2)     = 1 + provSize p + typeSize t1 + typeSize t2
    go (SymCo co)             = 1 + go co
    go (TransCo co1 co2)      = 1 + go co1 + go co2
    go (NthCo _ co)           = 1 + go co
    go (LRCo  _ co)           = 1 + go co
    go (InstCo co arg)        = 1 + go co + go arg
    go (CoherenceCo c1 c2)    = 1 + go c1 + go (coercionRep c2)
    go (KindCo co)            = 1 + go co
    go (SubCo _ co)           = 1 + go co
    go (AxiomRuleCo _ cs)     = 1 + sum (map go cs)

    provSize :: UnivCoProvenance -> Int
    provSize UnsafeCoerceProv    = 1
    provSize (PhantomProv co)    = 1 + go co
    provSize (ProofIrrelProv co) = 1 + go co
    provSize (PluginProv _)      = 1
    provSize (HoleProv h)        = pprPanic "provSize hits a hole" (ppr h)


{-
%************************************************************************
%*                                                                      *
                   Pretty-printing coercions
%*                                                                      *
%************************************************************************

@pprCo@ is the standard @Coercion@ printer; the overloaded @ppr@
function is defined to use this.  @pprParendCo@ is the same, except it
puts parens around the type, except for the atomic cases.
@pprParendCo@ works just by setting the initial context precedence
very high.
-}

-- Outputable instances are in TyCoRep, to avoid orphans

pprCo, pprParendCo :: Coercion -> SDoc
pprCo       co = ppr_co TopPrec   (coercionRep co)
pprParendCo co = ppr_co TyConPrec (coercionRep co)

pprCoRep :: CoercionRep -> SDoc
pprCoRep co = ppr_co TopPrec co

ppr_co :: TyPrec -> CoercionRep -> SDoc
ppr_co _ (Refl r ty) = angleBrackets (ppr ty) <> ppr_role r

ppr_co p co@(TyConAppCo _ tc [_,_])
  | tc `hasKey` funTyConKey = ppr_fun_co p co

ppr_co _ (TyConAppCo r tc cos) = pprTcAppCo TyConPrec ppr_co tc cos <> ppr_role r
ppr_co p (AppCo co arg)        = maybeParen p TyConPrec $
                                 ppr_co TopPrec co <+> ppr_co TyConPrec arg
ppr_co p co@(ForAllCo {})      = ppr_forall_co p co
ppr_co _ (CoVarCo cv)          = parenSymOcc (getOccName cv) (ppr cv)
ppr_co p (AxiomInstCo con index args)
  = pprPrefixApp p (ppr (getName con) <> brackets (ppr index))
                   (map (ppr_co TyConPrec) args)

ppr_co p co@(TransCo {}) = maybeParen p FunPrec $
                           case trans_co_list co [] of
                             [] -> panic "ppr_co"
                             (co:cos) -> sep ( ppr_co FunPrec co
                                             : [ char ';' <+> ppr_co FunPrec co | co <- cos])
ppr_co p (InstCo co arg) = maybeParen p TyConPrec $
                           ppr_co TyConPrec co <> text "@" <> ppr_co TopPrec arg
ppr_co p (UnivCo UnsafeCoerceProv r ty1 ty2)
  = pprPrefixApp p (text "UnsafeCo" <+> ppr r)
                   [pprParendType ty1, pprParendType ty2]
ppr_co _ (UnivCo p r t1 t2)
  = char 'U'
    <> parens (ppr_prov <> comma <+> ppr t1 <> comma <+> ppr t2)
    <> ppr_role r
  where
    ppr_prov = case p of
      HoleProv h          -> text "hole:"   <> ppr h
      PhantomProv kind_co -> text "phant:"  <> ppr kind_co
      ProofIrrelProv co   -> text "irrel:"  <> ppr co
      PluginProv s        -> text "plugin:" <> text s
      UnsafeCoerceProv    -> text "unsafe"
ppr_co p (SymCo co)          = pprPrefixApp p (text "Sym") [ppr_co TyConPrec co]
ppr_co p (NthCo n co)        = pprPrefixApp p (text "Nth:" <> int n) [ppr_co TyConPrec co]
ppr_co p (LRCo sel co)       = pprPrefixApp p (ppr sel) [ppr_co TyConPrec co]
ppr_co p (CoherenceCo c1 c2) = maybeParen p TyConPrec $
                               (ppr_co FunPrec c1) <+> (text "|>") <+>
                               (pprCo c2)
ppr_co p (KindCo co)         = pprPrefixApp p (text "kind") [ppr_co TyConPrec co]
ppr_co p (SubCo r co)        = pprPrefixApp p (text "Sub" <> ppr_role r) [ppr_co TyConPrec co]
ppr_co p (AxiomRuleCo co cs) = maybeParen p TopPrec $ ppr_axiom_rule_co co cs

ppr_axiom_rule_co :: CoAxiomRule -> [CoercionRep] -> SDoc
ppr_axiom_rule_co co ps = ppr (coaxrName co) <+> parens (interpp'SP ps)

ppr_role :: Role -> SDoc
ppr_role r = underscore <> pp_role
  where pp_role = case r of
                    Nominal          -> char 'N'
                    Representational -> char 'R'
                    Phantom          -> char 'P'
trans_co_list :: CoercionRep -> [CoercionRep] -> [CoercionRep]
trans_co_list (TransCo co1 co2) cos = trans_co_list co1 (trans_co_list co2 cos)
trans_co_list co                cos = co : cos

ppr_fun_co :: TyPrec -> CoercionRep -> SDoc
ppr_fun_co p co = pprArrowChain p (split co)
  where
    split :: CoercionRep -> [SDoc]
    split (TyConAppCo _ f [arg, res])
      | f `hasKey` funTyConKey
      = ppr_co FunPrec arg : split res
    split co = [ppr_co TopPrec co]

ppr_forall_co :: TyPrec -> CoercionRep -> SDoc
ppr_forall_co p (ForAllCo tv vis h co)
  = maybeParen p FunPrec $
    sep [forAllLit <+> pp_bndr, ppr_co TopPrec co]
  where
    name  = tyVarName tv
    pp_tv = ppr name <+> dcolon <+> pprCo h
    pp_bndr = case vis of
      Visible   -> parens pp_tv <+> arrow
      Specified -> parens pp_tv <> dot
      Invisible -> braces pp_tv <> dot
ppr_forall_co _ _ = panic "ppr_forall_co"

pprCoAxiom :: CoAxiom br -> SDoc
pprCoAxiom ax@(CoAxiom { co_ax_branches = branches })
  = hang (text "axiom" <+> ppr ax <+> dcolon)
       2 (vcat (map (ppr_co_ax_branch (const ppr) ax) $ fromBranches branches))

pprCoAxBranch :: CoAxiom br -> CoAxBranch -> SDoc
pprCoAxBranch = ppr_co_ax_branch pprRhs
  where
    pprRhs fam_tc (TyConApp tycon _)
      | isDataFamilyTyCon fam_tc
      = pprDataCons tycon
    pprRhs _ rhs = ppr rhs

pprCoAxBranchHdr :: CoAxiom br -> BranchIndex -> SDoc
pprCoAxBranchHdr ax index = pprCoAxBranch ax (coAxiomNthBranch ax index)

ppr_co_ax_branch :: (TyCon -> Type -> SDoc) -> CoAxiom br -> CoAxBranch -> SDoc
ppr_co_ax_branch ppr_rhs
              (CoAxiom { co_ax_tc = fam_tc, co_ax_name = name })
              (CoAxBranch { cab_tvs = tvs
                          , cab_cvs = cvs
                          , cab_lhs = lhs
                          , cab_rhs = rhs
                          , cab_loc = loc })
  = foldr1 (flip hangNotEmpty 2)
        [ pprUserForAll (map (mkNamedBinder Invisible) (tvs ++ cvs))
        , pprTypeApp fam_tc lhs <+> equals <+> ppr_rhs fam_tc rhs
        , text "-- Defined" <+> pprLoc loc ]
  where
        pprLoc loc
          | isGoodSrcSpan loc
          = text "at" <+> ppr (srcSpanStart loc)

          | otherwise
          = text "in" <+>
              quotes (ppr (nameModule name))

{-
%************************************************************************
%*                                                                      *
        Destructing coercions
%*                                                                      *
%************************************************************************
-}

-- | This breaks a 'Coercion' with type @T A B C ~ T D E F@ into
-- a list of 'Coercion's of kinds @A ~ D@, @B ~ E@ and @E ~ F@. Hence:
--
-- > decomposeCo 3 c = [nth 0 c, nth 1 c, nth 2 c]
decomposeCo :: Arity -> Coercion -> [Coercion]
decomposeCo arity co
  = [mkNthCo n co | n <- [0..(arity-1)] ]
           -- Remember, Nth is zero-indexed

-- | Attempts to tease a coercion apart into a type constructor and the application
-- of a number of coercion arguments to that constructor
splitTyConAppCo_maybe :: CoercionRep -> Maybe (TyCon, [CoercionRep])
splitTyConAppCo_maybe (Refl r ty)
  = do { (tc, tys) <- splitTyConApp_maybe ty
       ; let args = zipWith mkReflCoRep (tyConRolesX r tc) tys
       ; return (tc, args) }
splitTyConAppCo_maybe (TyConAppCo _ tc cos) = Just (tc, cos)
splitTyConAppCo_maybe _                     = Nothing

-- first result has role equal to input; second result is Nominal
splitAppCo_maybe :: CoercionRep -> Maybe (CoercionRep, CoercionRepN)
-- ^ Attempt to take a coercion application apart.
splitAppCo_maybe (AppCo co arg) = Just (co, arg)
splitAppCo_maybe (TyConAppCo r tc args)
  | mightBeUnsaturatedTyCon tc || args `lengthExceeds` tyConArity tc
    -- Never create unsaturated type family apps!
  , Just (args', arg') <- snocView args
  , Just arg'' <- setNominalRole_maybe arg'
  = Just ( mkTyConAppCoRep r tc args', arg'' )

splitAppCo_maybe (Refl r ty)
  | Just (ty1, ty2) <- splitAppTy_maybe ty
  = Just (mkReflCoRep r ty1, mkReflCoRep Nominal ty2)
splitAppCo_maybe _ = Nothing

splitForAllCo_maybe :: CoercionRep
                    -> Maybe (TyVar, Coercion, CoercionRep)
splitForAllCo_maybe co = case co of
  Refl r ty
    |  Just (tv, inner_ty) <- splitForAllTy_maybe ty
    -> Just (tv, mkNomReflCo (tyVarKind tv), Refl r inner_ty)
  ForAllCo tv _ k_co co
    -> Just (tv, k_co, co)
  _ -> Nothing

-------------------------------------------------------
-- and some coercion kind stuff

coVarTypes :: CoVar -> (Type,Type)
coVarTypes cv
  | (_, _, ty1, ty2, _) <- coVarKindsTypesRole cv
  = (ty1, ty2)

coVarKindsTypesRole :: CoVar -> (Kind,Kind,Type,Type,Role)
coVarKindsTypesRole cv
 | Just (tc, [k1,k2,ty1,ty2]) <- splitTyConApp_maybe (varType cv)
 = let role
         | tc `hasKey` eqPrimTyConKey     = Nominal
         | tc `hasKey` eqReprPrimTyConKey = Representational
         | otherwise                      = panic "coVarKindsTypesRole"
   in (k1,k2,ty1,ty2,role)
 | otherwise = pprPanic "coVarKindsTypesRole, non coercion variable"
                        (ppr cv $$ ppr (varType cv))

coVarKind :: CoVar -> Type
coVarKind cv
  = ASSERT( isCoVar cv )
    varType cv

coVarRole :: CoVar -> Role
coVarRole cv
  | tc `hasKey` eqPrimTyConKey
  = Nominal
  | tc `hasKey` eqReprPrimTyConKey
  = Representational
  | otherwise
  = pprPanic "coVarRole: unknown tycon" (ppr cv <+> dcolon <+> ppr (varType cv))

  where
    tc = case tyConAppTyCon_maybe (varType cv) of
           Just tc0 -> tc0
           Nothing  -> pprPanic "coVarRole: not tyconapp" (ppr cv)

-- | Makes a coercion type from two types: the types whose equality
-- is proven by the relevant 'Coercion'
mkCoercionType :: Role -> Type -> Type -> Type
mkCoercionType Nominal          = mkPrimEqPred
mkCoercionType Representational = mkReprPrimEqPred
mkCoercionType Phantom          = \ty1 ty2 ->
  let ki1 = typeKind ty1
      ki2 = typeKind ty2
  in
  TyConApp eqPhantPrimTyCon [ki1, ki2, ty1, ty2]

mkHeteroCoercionType :: Role -> Kind -> Kind -> Type -> Type -> Type
mkHeteroCoercionType Nominal          = mkHeteroPrimEqPred
mkHeteroCoercionType Representational = mkHeteroReprPrimEqPred
mkHeteroCoercionType Phantom          = panic "mkHeteroCoercionType"

-- | Returns the type coerced if this coercion is reflexive. Guaranteed
-- to work very quickly. Sometimes a coercion can be reflexive, but not
-- obviously so. c.f. 'isReflexiveCo_maybe'
isReflCo_maybe :: Coercion -> Maybe (Type, Role)
isReflCo_maybe (CachedCoercion { coercionRep  = Refl role ty }) = Just (ty, role)
isReflCo_maybe _                                                = Nothing

-- | Slowly checks if the coercion is reflexive. Don't call this in a loop,
-- as it walks over the entire coercion.
isReflexiveCo :: Coercion -> Bool
isReflexiveCo = isJust . isReflexiveCo_maybe

-- | Extracts the coerced type from a reflexive coercion. This potentially
-- walks over the entire coercion, so avoid doing this in a loop.
isReflexiveCo_maybe :: Coercion -> Maybe (Type, Role)
isReflexiveCo_maybe co
  | Just pair <- isReflCo_maybe co
  = Just pair

  | ty1 `eqType` ty2
  = Just (ty1, r)
  | otherwise
  = Nothing
  where (Pair ty1 ty2, r) = coercionKindRole co

{-
%************************************************************************
%*                                                                      *
            Building coercions
%*                                                                      *
%************************************************************************

These "smart constructors" maintain the invariants listed in the definition
of Coercion, and they perform very basic optimizations.

Note [Role twiddling functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

There are a plethora of functions for twiddling roles:

mkSubCo: Requires a nominal input coercion and always produces a
representational output. This is used when you (the programmer) are sure you
know exactly that role you have and what you want.

mkSubRoleCo: Low-level function to downgrade a role. Provide only the
new role, and it is up to the caller to ensure that this is a downgrade.
Like downgradeRole, but doesn't check if the role change is indeed a downgrade.

downgradeRole_maybe: This function takes both the input role and the output role
as parameters. (The *output* role comes first!) It can only *downgrade* a
role -- that is, change it from N to R or P, or from R to P. This one-way
behavior is why there is the "_maybe". If an upgrade is requested, this
function produces Nothing. This is used when you need to change the role of a
coercion, but you're not sure (as you're writing the code) of which roles are
involved.

This function could have been written using coercionRole to ascertain the role
of the input. But, that function is recursive, and the caller of downgradeRole_maybe
often knows the input role. So, this is more efficient.

downgradeRole: This is just like downgradeRole_maybe, but it panics if the
conversion isn't a downgrade.

setNominalRole_maybe: This is the only function that can *upgrade* a coercion.
The result (if it exists) is always Nominal. The input can be at any role. It
works on a "best effort" basis, as it should never be strictly necessary to
upgrade a coercion during compilation. It is currently only used within GHC in
splitAppCo_maybe. In order to be a proper inverse of mkAppCo, the second
coercion that splitAppCo_maybe returns must be nominal. But, it's conceivable
that splitAppCo_maybe is operating over a TyConAppCo that uses a
representational coercion. Hence the need for setNominalRole_maybe.
splitAppCo_maybe, in turn, is used only within coercion optimization -- thus,
it is not absolutely critical that setNominalRole_maybe be complete.

Note that setNominalRole_maybe will never upgrade a phantom UnivCo. Phantom
UnivCos are perfectly type-safe, whereas representational and nominal ones are
not. Indeed, `unsafeCoerce` is implemented via a representational UnivCo.
(Nominal ones are no worse than representational ones, so this function *will*
change a UnivCo Representational to a UnivCo Nominal.)

Conal Elliott also came across a need for this function while working with the
GHC API, as he was decomposing Core casts. The Core casts use representational
coercions, as they must, but his use case required nominal coercions (he was
building a GADT). So, that's why this function is exported from this module.

One might ask: shouldn't downgradeRole_maybe just use setNominalRole_maybe as
appropriate? I (Richard E.) have decided not to do this, because upgrading a
role is bizarre and a caller should have to ask for this behavior explicitly.

Note [mkTransAppCo]
~~~~~~~~~~~~~~~~~~~
Suppose we have

  co1 :: a ~R Maybe
  co2 :: b ~R Int

and we want

  co3 :: a b ~R Maybe Int

This seems sensible enough. But, we can't let (co3 = co1 co2), because
that's ill-roled! Note that mkAppCo requires a *nominal* second coercion.

The way around this is to use transitivity:

  co3 = (co1 <b>_N) ; (Maybe co2) :: a b ~R Maybe Int

Or, it's possible everything is the other way around:

  co1' :: Maybe ~R a
  co2' :: Int   ~R b

and we want

  co3' :: Maybe Int ~R a b

then

  co3' = (Maybe co2') ; (co1' <b>_N)

This is exactly what `mkTransAppCo` builds for us. Information for all
the arguments tends to be to hand at call sites, so it's quicker than
using, say, coercionKind.

-}

-- | Build a coercion from its pieces. You probably want this only
-- when filling a CoercionHole.
mkCoercion :: CoercionRep -> Role -> Type -> Type -> Coercion
mkCoercion rep role ty1 ty2
  = CachedCoercion { coercionKind    = Pair ty1 ty2
                   , coercionRole    = role
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoRepAcc rep
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = rep }

mkReflCo :: Role -> Type -> Coercion
mkReflCo r ty
  = CachedCoercion { coercionKind    = Pair ty ty
                   , coercionRole    = r
                   , tyCoVarsOfCoAcc = tyCoVarsOfTypeAcc ty
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkReflCoRep r ty }

-- | Make a representational reflexive coercion
mkRepReflCo :: Type -> Coercion
mkRepReflCo = mkReflCo Representational

-- | Make a nominal reflexive coercion
mkNomReflCo :: Type -> Coercion
mkNomReflCo = mkReflCo Nominal

-- | Apply a type constructor to a list of coercions. It is the
-- caller's responsibility to get the roles correct on argument coercions.
mkTyConAppCo :: Role -> TyCon -> [Coercion] -> Coercion
mkTyConAppCo r tc cos
               -- Expand type synonyms
  | Just (tv_co_prs, rhs_ty, leftover_cos) <- expandSynTyCon_maybe tc cos
  = (mkAppCos (liftCoSubst r (mkLiftingContext tv_co_prs) rhs_ty) leftover_cos)
      { coercionKind = mkTyConApp tc <$> (traverse coercionKind cos) }
        -- don't expand synonyms in the kind, as doing so affects normaliseType

  | otherwise
  = CachedCoercion { coercionKind    = mkTyConApp tc <$>
                                       (sequenceA $ map coercionKind cos)
                   , coercionRole    = r
                   , tyCoVarsOfCoAcc = mapUnionFV tyCoVarsOfCoAcc cos
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkTyConAppCoRep r tc (map coercionRep cos) }

-- | Make a function 'Coercion' between two other 'Coercion's
mkFunCo :: Role -> Coercion -> Coercion -> Coercion
mkFunCo r co1 co2 = mkTyConAppCo r funTyCon [co1, co2]

-- | Make nested function 'Coercion's
mkFunCos :: Role -> [Coercion] -> Coercion -> Coercion
mkFunCos r cos res_co = foldr (mkFunCo r) res_co cos

-- | Apply a 'Coercion' to another 'Coercion'.
-- The second coercion must be Nominal, unless the first is Phantom.
-- If the first is Phantom, then the second can be either Phantom or Nominal.
mkAppCo :: Coercion     -- ^ :: t1 ~r t2
        -> Coercion     -- ^ :: s1 ~N s2
        -> Coercion     -- ^ :: t1 s1 ~r t2 s2
mkAppCo co1 co2
  = CachedCoercion { coercionKind    = mkAppTy <$> coercionKind co1
                                               <*> coercionKind co2
                   , coercionRole    = coercionRole co1
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoAcc co1 `unionFV`
                                       tyCoVarsOfCoAcc co2
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkAppCoRep (coercionRep co1)
                                                  (coercionRep co2) }

-- | Applies multiple 'Coercion's to another 'Coercion', from left to right.
-- See also 'mkAppCo'.
mkAppCos :: Coercion
         -> [Coercion]
         -> Coercion
mkAppCos co1 cos = foldl mkAppCo co1 cos

-- | Like `mkAppCo`, but allows the second coercion to be other than
-- nominal. See Note [mkTransAppCo]. Role r3 cannot be more stringent
-- than either r1 or r2.
mkTransAppCo :: Role         -- ^ r1
             -> Coercion     -- ^ co1 :: ty1a ~r1 ty1b
             -> Type         -- ^ ty1a
             -> Type         -- ^ ty1b
             -> Role         -- ^ r2
             -> Coercion     -- ^ co2 :: ty2a ~r2 ty2b
             -> Type         -- ^ ty2a
             -> Type         -- ^ ty2b
             -> Role         -- ^ r3
             -> Coercion     -- ^ :: ty1a ty2a ~r3 ty1b ty2b
mkTransAppCo r1 co1 ty1a ty1b r2 co2 ty2a ty2b r3
-- How incredibly fiddly! Is there a better way??
  = case (r1, r2, r3) of
      (_,                _,                Phantom)
        -> mkPhantomCo kind_co (mkAppTy ty1a ty2a) (mkAppTy ty1b ty2b)
        where -- ty1a :: k1a -> k2a
              -- ty1b :: k1b -> k2b
              -- ty2a :: k1a
              -- ty2b :: k1b
              -- ty1a ty2a :: k2a
              -- ty1b ty2b :: k2b
              kind_co1 = mkKindCo co1        -- :: k1a -> k2a ~N k1b -> k2b
              kind_co  = mkNthCo 1 kind_co1  -- :: k2a ~N k2b

      (_,                _,                Nominal)
        -> ASSERT( r1 == Nominal && r2 == Nominal )
           mkAppCo co1 co2
      (Nominal,          Nominal,          Representational)
        -> mkSubCo (mkAppCo co1 co2)
      (_,                Nominal,          Representational)
        -> ASSERT( r1 == Representational )
           mkAppCo co1 co2
      (Nominal,          Representational, Representational)
        -> go (mkSubCo co1)
      (_               , _,                Representational)
        -> ASSERT( r1 == Representational && r2 == Representational )
           go co1
  where
    go co1_repr
      | Just (tc1b, tys1b) <- splitTyConApp_maybe ty1b
      , nextRole ty1b == r2
      = (mkAppCo co1_repr (mkNomReflCo ty2a)) `mkTransCo`
        (mkTyConAppCo Representational tc1b
           (zipWith mkReflCo (tyConRolesRepresentational tc1b) tys1b
            ++ [co2]))

      | Just (tc1a, tys1a) <- splitTyConApp_maybe ty1a
      , nextRole ty1a == r2
      = (mkTyConAppCo Representational tc1a
           (zipWith mkReflCo (tyConRolesRepresentational tc1a) tys1a
            ++ [co2]))
        `mkTransCo`
        (mkAppCo co1_repr (mkNomReflCo ty2b))

      | otherwise
      = pprPanic "mkTransAppCo" (vcat [ ppr r1, ppr co1, ppr ty1a, ppr ty1b
                                      , ppr r2, ppr co2, ppr ty2a, ppr ty2b
                                      , ppr r3 ])

-- | Make a Coercion from a tyvar, a kind coercion, and a body coercion.
-- The kind of the tyvar should be the left-hand kind of the kind coercion.
mkForAllCo :: TyVar -> VisibilityFlag -> Coercion -> Coercion -> Coercion
mkForAllCo tv1 vis kind_co co
  = CachedCoercion { coercionKind    = mkNamedForAllTy <$> Pair tv1 tv2
                                                       <*> pure vis
                                                       <*> Pair ty1 ty2'
                   , coercionRole    = coercionRole co
                   , tyCoVarsOfCoAcc = delFV tv1 (tyCoVarsOfCoAcc co)
                                       `unionFV` tyCoVarsOfCoAcc kind_co
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkForAllCoRep tv1 vis kind_co
                                                     (coercionRep co) }
  where
    Pair _ k2    = coercionKind kind_co
    tv2          = setTyVarKind tv1 k2
    Pair ty1 ty2 = coercionKind co
    ty2'         = substTyWithUnchecked
                     [tv1]
                     [TyVarTy tv2 `mk_cast_ty` mkSymCo kind_co]
                     ty2

    -- The real mkCastTy is too slow, and we can easily have nested ForAllCos.
    mk_cast_ty :: Type -> Coercion -> Type
    mk_cast_ty ty co | isReflCo co = ty
                     | otherwise   = CastTy ty co

-- | Make nested ForAllCos
mkForAllCos :: [(TyVar, VisibilityFlag, Coercion)] -> Coercion -> Coercion
mkForAllCos bndrs co
  = CachedCoercion { coercionKind    = mkForAllTys
                                         <$> (liftA2 (zipWith mkNamedBinder)
                                              (pure viss) (Pair tv1s tv2s))
                                         <*> Pair ty1 ty2'
                   , coercionRole    = coercionRole co
                   , tyCoVarsOfCoAcc = fvs
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = foldr (\(tv, vis, kco) -> mkForAllCoRep tv vis kco)
                                             (coercionRep co)
                                             bndrs }
  where
    (tv1s, viss, kind_cos) = unzip3 bndrs
    k2s                    = map (pSnd . coercionKind) kind_cos
    tv2s                   = zipWith setTyVarKind tv1s k2s
    Pair ty1 ty2           = coercionKind co
    ty2'                   = substTyWithUnchecked
                               tv1s
                               [ TyVarTy tv2 `mkCastTy` mkSymCo kind_co
                                 | (tv2, kind_co) <- tv2s `zip` kind_cos ]
                               ty2

    fvs = foldr go_fv (tyCoVarsOfCoAcc co) bndrs
    go_fv (tv, _, kind_co) fv a b c
      = (delFV tv fv `unionFV` tyCoVarsOfCoAcc kind_co) a b c

-- | Make a Coercion quantified over a type variable;
-- the variable has the same type in both sides of the coercion
mkHomoForAllCos :: [TyVar] -> Coercion -> Coercion
mkHomoForAllCos tvs co
  | Just (ty, r) <- isReflCo_maybe co
  = mkReflCo r (mkInvForAllTys tvs ty)
mkHomoForAllCos tvs co = mkHomoForAllCos_NoRefl tvs co

-- | Like 'mkHomoForAllCos', but doesn't check if the inner coercion
-- is reflexive.
mkHomoForAllCos_NoRefl :: [TyVar] -> Coercion -> Coercion
mkHomoForAllCos_NoRefl tvs orig_co
  = CachedCoercion { coercionKind    = mkInvForAllTys tvs <$> coercionKind orig_co
                   , coercionRole    = coercionRole orig_co
                   , tyCoVarsOfCoAcc = delFVs (mkVarSet tvs) $
                                       tyCoVarsOfCoAcc orig_co
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = foldr go (coercionRep orig_co) tvs }
  where
    go tv co = ForAllCo tv Invisible (mkReflCo Nominal (tyVarKind tv)) co

-- mkCoVarCo is in TyCoRep

mkCoVarCos :: [CoVar] -> [Coercion]
mkCoVarCos = map mkCoVarCo

-- | Extract a covar, if possible. This check is dirty. Be ashamed
-- of yourself. (It's dirty because it cares about the structure of
-- a coercion, which is morally reprehensible.)
isCoVar_maybe :: Coercion -> Maybe CoVar
isCoVar_maybe (CachedCoercion { coercionRep = CoVarCo cv }) = Just cv
isCoVar_maybe _                                             = Nothing

mkAxInstCo :: Role -> CoAxiom br -> BranchIndex -> [Type] -> [Coercion]
           -> Coercion
-- mkAxInstCo can legitimately be called over-staturated;
-- i.e. with more type arguments than the coercion requires
mkAxInstCo role ax index tys cos
  | arity == n_tys = downgradeRole role ax_role $
                     mkAxiomInstCo ax_br index (rtys `chkAppend` cos)
  | otherwise      = ASSERT( arity < n_tys )
                     downgradeRole role ax_role $
                     mkAppCos (mkAxiomInstCo ax_br index
                                             (ax_args `chkAppend` cos))
                              leftover_args
  where
    n_tys         = length tys
    ax_br         = toBranchedAxiom ax
    branch        = coAxiomNthBranch ax_br index
    tvs           = coAxBranchTyVars branch
    arity         = length tvs
    arg_roles     = coAxBranchRoles branch
    rtys          = zipWith mkReflCo (arg_roles ++ repeat Nominal) tys
    (ax_args, leftover_args)
                  = splitAt arity rtys
    ax_role       = coAxiomRole ax

mkAxiomInstCo :: CoAxiom Branched -> BranchIndex -> [Coercion] -> Coercion
mkAxiomInstCo ax index args
  = CachedCoercion { coercionKind    = Pair ty1 ty2
                   , coercionRole    = coAxiomRole ax
                   , tyCoVarsOfCoAcc = mapUnionFV tyCoVarsOfCoAcc args
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkAxiomInstCoRep ax index
                                                        (map coercionRep args) }
  where
    CoAxBranch { cab_tvs = tvs, cab_cvs = cvs
               , cab_lhs = lhs, cab_rhs = rhs } = coAxiomNthBranch ax index
    Pair tycos1 tycos2 = sequenceA (map coercionKind args)
    (tys1, cotys1)     = splitAtList tvs tycos1
    (tys2, cotys2)     = splitAtList tvs tycos2
    cos1               = map stripCoercionTy cotys1
    cos2               = map stripCoercionTy cotys2

    in_scope = mkInScopeSet (tyCoVarsOfCos args)

    tv_env1 = zipTyEnv tvs tys1
    cv_env1 = zipCoEnv cvs cos1
    subst1  = mkTCvSubst in_scope (tv_env1, cv_env1)

    tv_env2 = zipTyEnv tvs tys2
    cv_env2 = zipCoEnv cvs cos2
    subst2  = mkTCvSubst in_scope (tv_env2, cv_env2)

    ty1     = mkTyConApp (coAxiomTyCon ax) (substTys subst1 lhs)
    ty2     = substTy subst2 rhs

-- to be used only with unbranched axioms
mkUnbranchedAxInstCo :: Role -> CoAxiom Unbranched
                     -> [Type] -> [Coercion] -> Coercion
mkUnbranchedAxInstCo role ax tys cos
  = mkAxInstCo role ax 0 tys cos

mkAxInstRHS :: CoAxiom br -> BranchIndex -> [Type] -> [Coercion] -> Type
-- Instantiate the axiom with specified types,
-- returning the instantiated RHS
-- A companion to mkAxInstCo:
--    mkAxInstRhs ax index tys = snd (coercionKind (mkAxInstCo ax index tys))
mkAxInstRHS ax index tys cos
  = ASSERT( tvs `equalLength` tys1 )
    mkAppTys rhs' tys2
  where
    branch       = coAxiomNthBranch ax index
    tvs          = coAxBranchTyVars branch
    cvs          = coAxBranchCoVars branch
    (tys1, tys2) = splitAtList tvs tys
    rhs'         = substTyWith tvs tys1 $
                   substTyWithCoVars cvs cos $
                   coAxBranchRHS branch

mkUnbranchedAxInstRHS :: CoAxiom Unbranched -> [Type] -> [Coercion] -> Type
mkUnbranchedAxInstRHS ax = mkAxInstRHS ax 0

-- | Return the left-hand type of the axiom, when the axiom is instantiated
-- at the types given.
mkAxInstLHS :: CoAxiom br -> BranchIndex -> [Type] -> [Coercion] -> Type
mkAxInstLHS ax index tys cos
  = ASSERT( tvs `equalLength` tys1 )
    mkTyConApp fam_tc (lhs_tys `chkAppend` tys2)
  where
    branch       = coAxiomNthBranch ax index
    tvs          = coAxBranchTyVars branch
    cvs          = coAxBranchCoVars branch
    (tys1, tys2) = splitAtList tvs tys
    lhs_tys      = substTysWith tvs tys1 $
                   substTysWithCoVars cvs cos $
                   coAxBranchLHS branch
    fam_tc       = coAxiomTyCon ax

-- | Instantiate the left-hand side of an unbranched axiom
mkUnbranchedAxInstLHS :: CoAxiom Unbranched -> [Type] -> [Coercion] -> Type
mkUnbranchedAxInstLHS ax = mkAxInstLHS ax 0

-- | Manufacture an unsafe coercion from thin air.
--   Currently (May 14) this is used only to implement the
--   @unsafeCoerce#@ primitive.  Optimise by pushing
--   down through type constructors.
mkUnsafeCo :: Role -> Type -> Type -> Coercion
mkUnsafeCo role ty1 ty2
  = CachedCoercion { coercionKind    = Pair ty1 ty2
                   , coercionRole    = role
                   , tyCoVarsOfCoAcc = tyCoVarsOfTypesAcc [ty1, ty2]
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkUnivCoRep UnsafeCoerceProv role ty1 ty2 }

-- | Make a coercion from a coercion hole
mkHoleCo :: CoercionHole -> Role
         -> Type -> Type -> Coercion
mkHoleCo h r t1 t2
  = CachedCoercion { coercionKind    = Pair t1 t2
                   , coercionRole    = r
                   , tyCoVarsOfCoAcc = tyCoVarsOfTypesAcc [t1, t2]
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkUnivCoRep (HoleProv h) r t1 t2 }

-- | Make a universal coercion between two arbitrary types.
mkUnivCo :: UnivCoProvenance
         -> Role       -- ^ role of the built coercion, "r"
         -> Type       -- ^ t1 :: k1
         -> Type       -- ^ t2 :: k2
         -> Coercion   -- ^ :: t1 ~r t2
mkUnivCo prov role ty1 ty2
  = CachedCoercion { coercionKind    = Pair ty1 ty2
                   , coercionRole    = role
                   , tyCoVarsOfCoAcc = tyCoVarsOfProvAcc prov `unionFV`
                                       tyCoVarsOfTypesAcc [ty1, ty2]
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkUnivCoRep prov role ty1 ty2 }

-- | Create a symmetric version of the given 'Coercion' that asserts
--   equality between the same types but in the other "direction", so
--   a kind of @t1 ~ t2@ becomes the kind @t2 ~ t1@.
mkSymCo :: Coercion -> Coercion
mkSymCo co
  = CachedCoercion { coercionKind    = swap (coercionKind co)
                   , coercionRole    = coercionRole co
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoAcc co
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkSymCoRep (coercionRep co) }

-- | Create a new 'Coercion' by composing the two given 'Coercion's transitively.
mkTransCo :: Coercion -> Coercion -> Coercion
mkTransCo co1 co2
  = CachedCoercion { coercionKind    = Pair ty1 ty3
                   , coercionRole    = coercionRole co1
                   , tyCoVarsOfCoAcc = mapUnionFV tyCoVarsOfCoAcc [co1, co2]
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkTransCoRep (coercionRep co1)
                                                    (coercionRep co2) }
  where
    Pair ty1 _ty2 = coercionKind co1
    Pair _t2 ty3  = coercionKind co2

-- the Role is the desired one. It is the caller's responsibility to make
-- sure this request is reasonable
mkNthCoRole :: Role -> Int -> Coercion -> Coercion
mkNthCoRole role n co
  = downgradeRole role nth_role $ nth_co
  where
    nth_co = mkNthCo n co
    nth_role = coercionRole nth_co

mkNthCo :: Int -> Coercion -> Coercion
mkNthCo n co
  = CachedCoercion { coercionKind    = nth_tys
                   , coercionRole    = nth_role
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoAcc co
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkNthCoRep n (coercionRep co) }
  where
    Pair ty1 ty2 = coercionKind co
    role         = coercionRole co

    (nth_tys, nth_role)
      | Just (tv1, _) <- splitForAllTy_maybe ty1
      = ASSERT( n == 0 )
        let (tv2, _) = splitForAllTy ty2 in
        (tyVarKind <$> Pair tv1 tv2, Nominal)

      | otherwise
      = let (tc1,  args1) = splitTyConApp ty1
            (_tc2, args2) = splitTyConApp ty2
        in
        ASSERT( tc1 == _tc2 )
        ((`getNth` n) <$> Pair args1 args2, nthRole role tc1 n)

mkLRCo :: LeftOrRight -> Coercion -> Coercion
mkLRCo lr co
  = CachedCoercion { coercionKind    = (pickLR lr . splitAppTy) <$>
                                       coercionKind co
                   , coercionRole    = Nominal
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoAcc co
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkLRCoRep lr (coercionRep co) }

-- | Instantiates a 'Coercion'.
mkInstCo :: Coercion -> Coercion -> Coercion
mkInstCo co arg
  = CachedCoercion { coercionKind    = kind
                   , coercionRole    = coercionRole co
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoAcc co `unionFV`
                                       tyCoVarsOfCoAcc arg
                   , coercionInfo    = info
                   , coercionRep     = mkInstCoRep (coercionRep co)
                                                   (coercionRep arg) }
  where
    arg_kind = coercionKind arg

     -- It is expected that we'll force only one of kind OR info, but
     -- not both. If the returned coercion is not contained within an
     -- InstCo, it will be kind; if it is within another InstCo, it
     -- will be info. So they're computed separately.
     -- See also Note [Nested InstCos]
    kind = case coercionInfo co of
      NoCachedInfo
        -> piResultTy <$> coercionKind co <*> arg_kind
      CachedInstInfo { cachedUnderlyingPair = root_pair
                     , cachedRevArgs        = args }
        -> piResultTys <$> root_pair <*> fmap reverse ((:) <$> arg_kind <*> args)

    info = case coercionInfo co of
      NoCachedInfo
        -> CachedInstInfo { cachedUnderlyingPair = coercionKind co
                          , cachedRevArgs        = (:[]) <$> arg_kind }
      CachedInstInfo { cachedUnderlyingPair = root_pair
                     , cachedRevArgs        = rev_args }
        -> CachedInstInfo { cachedUnderlyingPair = root_pair
                          , cachedRevArgs        = (:) <$> arg_kind
                                                       <*> rev_args }

-- This could work harder to produce Refl coercions, but that would be
-- quite inefficient. Seems better not to try.
mkCoherenceCo :: Coercion -> Coercion -> Coercion
mkCoherenceCo co1 co2
  = CachedCoercion { coercionKind    = pLiftFst (`mkCastTy` co2) $
                                       coercionKind co1
                   , coercionRole    = coercionRole co1
                   , tyCoVarsOfCoAcc = mapUnionFV tyCoVarsOfCoAcc [co1, co2]
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkCoherenceCoRep (coercionRep co1) co2 }

-- | A CoherenceCo c1 c2 applies the coercion c2 to the left-hand type
-- in the kind of c1. This function uses sym to get the coercion on the
-- right-hand type of c1. Thus, if c1 :: s ~ t, then mkCoherenceRightCo c1 c2
-- has the kind (s ~ (t |> c2)) down through type constructors.
-- The second coercion must be representational.
mkCoherenceRightCo :: Coercion -> Coercion -> Coercion
mkCoherenceRightCo c1 c2 = mkSymCo (mkCoherenceCo (mkSymCo c1) c2)

-- | An explictly directed synonym of mkCoherenceCo. The second
-- coercion must be representational.
mkCoherenceLeftCo :: Coercion -> Coercion -> Coercion
mkCoherenceLeftCo = mkCoherenceCo

infixl 5 `mkCoherenceCo`
infixl 5 `mkCoherenceRightCo`
infixl 5 `mkCoherenceLeftCo`

mkKindCo :: Coercion -> Coercion
mkKindCo co
  = CachedCoercion { coercionKind    = typeKind <$> coercionKind co
                   , coercionRole    = Nominal
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoAcc co
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkKindCoRep (coercionRep co) }

-- input coercion is Nominal; see also Note [Role twiddling functions]
mkSubCo :: CoercionN -> CoercionR
mkSubCo co
  = CachedCoercion { coercionKind    = coercionKind co
                   , coercionRole    = Representational
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoAcc co
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkSubCoRep (coercionRep co) }

mkSubRoleCo :: Role -> Coercion -> Coercion
mkSubRoleCo r co
  = CachedCoercion { coercionKind    = coercionKind co
                   , coercionRole    = r
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoAcc co
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkSubRoleCoRep r (coercionRep co) }

-- | Changes a role, but only a downgrade. See Note [Role twiddling functions]
downgradeRole_maybe :: Role   -- ^ desired role
                    -> Role   -- ^ current role
                    -> Coercion -> Maybe Coercion
-- In (downgradeRole_maybe dr cr co) it's a precondition that
--                                   cr = coercionRole co
downgradeRole_maybe Representational Nominal co = Just (mkSubCo co)
downgradeRole_maybe Nominal Representational _  = Nothing
downgradeRole_maybe Phantom Phantom          co = Just co
downgradeRole_maybe Phantom _                co = Just (toPhantomCo co)
downgradeRole_maybe _ Phantom                _  = Nothing
downgradeRole_maybe _ _                      co = Just co

-- | Like 'downgradeRole_maybe', but panics if the change isn't a downgrade.
-- See Note [Role twiddling functions]
downgradeRole :: Role  -- desired role
              -> Role  -- current role
              -> Coercion -> Coercion
downgradeRole r1 r2 co
  = case downgradeRole_maybe r1 r2 co of
      Just co' -> co'
      Nothing  -> pprPanic "downgradeRole" (ppr co)

-- | If the EqRel is ReprEq, makes a SubCo; otherwise, does nothing.
-- Note that the input coercion should always be nominal.
maybeSubCo :: EqRel -> Coercion -> Coercion
maybeSubCo NomEq  = id
maybeSubCo ReprEq = mkSubCo

mkAxiomRuleCo :: CoAxiomRule -> [Coercion] -> Coercion
mkAxiomRuleCo rule cos
  = CachedCoercion { coercionKind    = expectJust "mkAxiomRuleCo" $
                                       coaxrProves rule (map coercionKind cos)
                   , coercionRole    = coaxrRole rule
                   , tyCoVarsOfCoAcc = mapUnionFV tyCoVarsOfCoAcc cos
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = AxiomRuleCo rule (map coercionRep cos) }

-- | Make a "coercion between coercions".
mkProofIrrelCo :: Role       -- ^ role of the created coercion, "r"
               -> Coercion   -- ^ :: phi1 ~N phi2
               -> Coercion   -- ^ g1 :: phi1
               -> Coercion   -- ^ g2 :: phi2
               -> Coercion   -- ^ :: g1 ~r g2
mkProofIrrelCo r kco g1 g2
    -- if the two coercion prove the same fact, I just don't care what
    -- the individual coercions are.
  | isReflCo kco = mkReflCo r (CoercionTy g1)

  | otherwise
  = CachedCoercion { coercionKind    = Pair ty1 ty2
                   , coercionRole    = r
                   , tyCoVarsOfCoAcc = mapUnionFV tyCoVarsOfCoAcc [kco, g1, g2]
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkUnivCoRep (ProofIrrelProv (coercionRep kco))
                                                   r ty1 ty2 }
  where
    ty1 = mkCoercionTy g1
    ty2 = mkCoercionTy g2

-- | This puts a 'CoercionRep' into a 'Coercion'. You generally shouldn't need
-- this function, as this is needed only when the structure of a coercion is
-- being inspected, and that shouldn't happen, outside of OptCoercion.
mkCachedCoercion :: CoercionRep -> Coercion
mkCachedCoercion rep
  = CachedCoercion { coercionKind    = kind
                   , coercionRole    = role
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoRepAcc rep
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = rep }
  where
    (kind, role) = coercionRepKindRole rep

{-
%************************************************************************
%*                                                                      *
   Roles
%*                                                                      *
%************************************************************************
-}

-- | Converts a coercion to be nominal, if possible.
-- See Note [Role twiddling functions]
setNominalRole_maybe :: CoercionRep -> Maybe CoercionRepN
setNominalRole_maybe = go
  where
    go (SubCo _ co) = go co
    go (Refl _ ty) = Just $ Refl Nominal ty
    go (TyConAppCo Representational tc cos)
      = do { cos' <- mapM go cos
           ; return $ TyConAppCo Nominal tc cos' }
    go (SymCo co)
      = SymCo <$> go co
    go (TransCo co1 co2)
      = TransCo <$> go co1 <*> go co2
    go (AppCo co1 co2)
      = AppCo <$> go co1 <*> pure co2
    go (ForAllCo tv vis kind_co co)
      = ForAllCo tv vis kind_co <$> go co
    go (NthCo n co)
      = NthCo n <$> go co
    go (InstCo co arg)
      = InstCo <$> go co <*> pure arg
    go (CoherenceCo co1 co2)
      = CoherenceCo <$> go co1 <*> pure co2
    go (UnivCo prov _ co1 co2)
      | case prov of UnsafeCoerceProv -> True   -- it's always unsafe
                     PhantomProv _    -> False  -- should always be phantom
                     ProofIrrelProv _ -> True   -- it's always safe
                     PluginProv _     -> False  -- who knows? This choice is conservative.
                     HoleProv _       -> False  -- no no no.
      = Just $ UnivCo prov Nominal co1 co2
    go _ = Nothing

-- | Make a phantom coercion between two types. The coercion passed
-- in must be a nominal coercion between the kinds of the
-- types.
mkPhantomCo :: Coercion -> Type -> Type -> Coercion
mkPhantomCo h t1 t2
  = CachedCoercion { coercionKind    = Pair t1 t2
                   , coercionRole    = Phantom
                   , tyCoVarsOfCoAcc = mapUnionFV tyCoVarsOfTypeAcc [t1, t2]
                                       `unionFV` tyCoVarsOfCoAcc h
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = mkUnivCoRep (PhantomProv (coercionRep h))
                                                   Phantom t1 t2 }

-- | Make a phantom coercion between two types of the same kind.
mkHomoPhantomCo :: Type -> Type -> Coercion
mkHomoPhantomCo t1 t2
  = ASSERT( k1 `eqType` typeKind t2 )
    mkPhantomCo (mkNomReflCo k1) t1 t2
  where
    k1 = typeKind t1

-- takes any coercion and turns it into a Phantom coercion
toPhantomCo :: Coercion -> Coercion
toPhantomCo co
  = mkPhantomCo (mkKindCo co) ty1 ty2
  where Pair ty1 ty2 = coercionKind co

-- the Role parameter is the Role of the TyConAppCo
-- defined here because this is intimiately concerned with the implementation
-- of TyConAppCo
tyConRolesX :: Role -> TyCon -> [Role]
tyConRolesX Representational tc = tyConRolesRepresentational tc
tyConRolesX role             _  = repeat role

tyConRolesRepresentational :: TyCon -> [Role]
tyConRolesRepresentational tc = tyConRoles tc ++ repeat Nominal

nthRole :: Role -> TyCon -> Int -> Role
nthRole Nominal _ _ = Nominal
nthRole Phantom _ _ = Phantom
nthRole Representational tc n
  = (tyConRolesRepresentational tc) `getNth` n

ltRole :: Role -> Role -> Bool
-- Is one role "less" than another?
--     Nominal < Representational < Phantom
ltRole Phantom          _       = False
ltRole Representational Phantom = True
ltRole Representational _       = False
ltRole Nominal          Nominal = False
ltRole Nominal          _       = True

-------------------------------
-- | Creates a new coercion with both of its types casted by different casts
-- castCoercionKind g h1 h2, where g :: t1 ~ t2, has type (t1 |> h1) ~ (t2 |> h2)
-- The second and third coercions must be nominal.
castCoercionKind :: Coercion -> Coercion -> Coercion -> Coercion
castCoercionKind g h1 h2
  = CachedCoercion { coercionKind    = mkCastTy <$> coercionKind g <*> Pair h1 h2
                   , coercionRole    = coercionRole g
                   , tyCoVarsOfCoAcc = mapUnionFV tyCoVarsOfCoAcc [g, h1, h2]
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = castCoercionKindRep (coercionRep g)
                                                           h1 h2 }

-- See note [Newtype coercions] in TyCon

mkPiCos :: Role -> [Var] -> Coercion -> Coercion
mkPiCos r vs co = foldr (mkPiCo r) co vs

mkPiCo  :: Role -> Var -> Coercion -> Coercion
mkPiCo r v co | isTyVar v = mkHomoForAllCos [v] co
              | otherwise = mkFunCo r (mkReflCo r (varType v)) co

-- The second coercion is sometimes lifted (~) and sometimes unlifted (~#).
-- So, we have to make sure to supply the right parameter to decomposeCo.
-- mkCoCast (c :: s1 ~# t1) (g :: (s1 ~# s2) ~# (t1 ~# t2)) :: s2 ~# t2
-- Both coercions *must* have the same role.
mkCoCast :: Coercion -> Coercion -> Coercion
mkCoCast c g
  = mkSymCo g1 `mkTransCo` c `mkTransCo` g2
  where
       -- g  :: (s1 ~# s2) ~# (t1 ~#  t2)
       -- g1 :: s1 ~# t1
       -- g2 :: s2 ~# t2
    (_, args) = splitTyConApp (pFst $ coercionKind g)
    n_args = length args
    co_list = decomposeCo n_args g
    g1 = co_list `getNth` (n_args - 2)
    g2 = co_list `getNth` (n_args - 1)

{-
%************************************************************************
%*                                                                      *
            Newtypes
%*                                                                      *
%************************************************************************
-}

-- | If @co :: T ts ~ rep_ty@ then:
--
-- > instNewTyCon_maybe T ts = Just (rep_ty, co)
--
-- Checks for a newtype, and for being saturated
instNewTyCon_maybe :: TyCon -> [Type] -> Maybe (Type, Coercion)
instNewTyCon_maybe tc tys
  | Just (tvs, ty, co_tc) <- unwrapNewTyConEtad_maybe tc  -- Check for newtype
  , tvs `leLength` tys                                    -- Check saturated enough
  = Just (applyTysX tvs ty tys, mkUnbranchedAxInstCo Representational co_tc tys [])
  | otherwise
  = Nothing

{-
************************************************************************
*                                                                      *
         Type normalisation
*                                                                      *
************************************************************************
-}

-- | A function to check if we can reduce a type by one step. Used
-- with 'topNormaliseTypeX_maybe'.
type NormaliseStepper = RecTcChecker
                     -> TyCon     -- tc
                     -> [Type]    -- tys
                     -> NormaliseStepResult

-- | The result of stepping in a normalisation function.
-- See 'topNormaliseTypeX_maybe'.
data NormaliseStepResult
  = NS_Done   -- ^ Nothing more to do
  | NS_Abort  -- ^ Utter failure. The outer function should fail too.
  | NS_Step RecTcChecker Type Coercion  -- ^ We stepped, yielding new bits;
                                        -- ^ co :: old type ~ new type

modifyStepResultCo :: (Coercion -> Coercion)
                   -> NormaliseStepResult -> NormaliseStepResult
modifyStepResultCo f (NS_Step rec_nts ty co) = NS_Step rec_nts ty (f co)
modifyStepResultCo _ result                  = result

-- | Try one stepper and then try the next, if the first doesn't make
-- progress.
-- So if it returns NS_Done, it means that both steppers are satisfied
composeSteppers :: NormaliseStepper -> NormaliseStepper
                -> NormaliseStepper
composeSteppers step1 step2 rec_nts tc tys
  = case step1 rec_nts tc tys of
      success@(NS_Step {}) -> success
      NS_Done              -> step2 rec_nts tc tys
      NS_Abort             -> NS_Abort

-- | A 'NormaliseStepper' that unwraps newtypes, careful not to fall into
-- a loop. If it would fall into a loop, it produces 'NS_Abort'.
unwrapNewTypeStepper :: NormaliseStepper
unwrapNewTypeStepper rec_nts tc tys
  | Just (ty', co) <- instNewTyCon_maybe tc tys
  = case checkRecTc rec_nts tc of
      Just rec_nts' -> NS_Step rec_nts' ty' co
      Nothing       -> NS_Abort

  | otherwise
  = NS_Done

-- | A general function for normalising the top-level of a type. It continues
-- to use the provided 'NormaliseStepper' until that function fails, and then
-- this function returns. The roles of the coercions produced by the
-- 'NormaliseStepper' must all be the same, which is the role returned from
-- the call to 'topNormaliseTypeX_maybe'.
topNormaliseTypeX_maybe :: NormaliseStepper -> Type -> Maybe (Coercion, Type)
topNormaliseTypeX_maybe stepper
  = go initRecTc Nothing
  where
    go rec_nts mb_co1 ty
      | Just (tc, tys) <- splitTyConApp_maybe ty
      = case stepper rec_nts tc tys of
          NS_Step rec_nts' ty' co2
            -> go rec_nts' (mb_co1 `trans` co2) ty'

          NS_Done  -> all_done
          NS_Abort -> Nothing

      | otherwise
      = all_done
      where
        all_done | Just co <- mb_co1 = Just (co, ty)
                 | otherwise         = Nothing

    Nothing    `trans` co2 = Just co2
    (Just co1) `trans` co2 = Just (co1 `mkTransCo` co2)

topNormaliseNewType_maybe :: Type -> Maybe (Coercion, Type)
-- ^ Sometimes we want to look through a @newtype@ and get its associated coercion.
-- This function strips off @newtype@ layers enough to reveal something that isn't
-- a @newtype@.  Specifically, here's the invariant:
--
-- > topNormaliseNewType_maybe rec_nts ty = Just (co, ty')
--
-- then (a)  @co : ty0 ~ ty'@.
--      (b)  ty' is not a newtype.
--
-- The function returns @Nothing@ for non-@newtypes@,
-- or unsaturated applications
--
-- This function does *not* look through type families, because it has no access to
-- the type family environment. If you do have that at hand, consider to use
-- topNormaliseType_maybe, which should be a drop-in replacement for
-- topNormaliseNewType_maybe
topNormaliseNewType_maybe ty
  = topNormaliseTypeX_maybe unwrapNewTypeStepper ty

{-
%************************************************************************
%*                                                                      *
                   Comparison of coercions
%*                                                                      *
%************************************************************************
-}

-- | Syntactic equality of coercions
eqCoercion :: Coercion -> Coercion -> Bool
eqCoercion = eqType `on` coercionType

-- | Compare two 'Coercion's, with respect to an RnEnv2
eqCoercionX :: RnEnv2 -> Coercion -> Coercion -> Bool
eqCoercionX env = eqTypeX env `on` coercionType

{-
%************************************************************************
%*                                                                      *
           A CoercionRep's kind
%*                                                                      *
%************************************************************************

Note [Computing a coercion kind and role]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
To compute a coercion's kind is straightforward: see coercionRepKind.
But to compute a coercion's role, in the case for NthCo we need
its kind as well.  So if we have two separate functions (one for kinds
and one for roles) we can get exponentially bad behaviour, since each
NthCo node makes a separate call to coercionRepKind, which traverses the
sub-tree again.  This was part of the problem in Trac #9233.

Solution: compute both together; hence coercionRepKindRole.  We keep a
separate coercionRepKind function because it's a bit more efficient if
the kind is all you want.

-}

-- | Get a coercion's kind and role.
-- Why both at once?  See Note [Computing a coercion kind and role]
-- Please don't use this. You should generally be working with
-- 'Coercion's, not 'CoercionRep's, and getting the details of
-- a 'Coercion' is speedy, because the details are cached. If
-- you use this function, you're probably both violating the design
-- of coercions (which should stay opaque, not revealing their 'CoercionRep's)
-- and making your algorithm exponential (because this traverses the
-- whole 'CoercionRep').
coercionRepKindRole :: CoercionRep -> (Pair Type, Role)
coercionRepKindRole = go
  where
    go (Refl r ty) = (Pair ty ty, r)
    go (TyConAppCo r tc cos)
      = (mkTyConApp tc <$> (sequenceA $ map coercionRepKind cos), r)
    go (AppCo co1 co2)
      = let (tys1, r1) = go co1 in
        (mkAppTy <$> tys1 <*> coercionRepKind co2, r1)
    go (ForAllCo tv1 vis k_co co)
      = let Pair _ k2          = coercionKind k_co
            tv2                = setTyVarKind tv1 k2
            (Pair ty1 ty2, r)  = go co
            ty2' = substTyWithUnchecked [tv1] [TyVarTy tv2 `mkCastTy` mkSymCo k_co] ty2 in
        (mkNamedForAllTy <$> Pair tv1 tv2 <*> pure vis <*> Pair ty1 ty2', r)
    go (CoVarCo cv) = (toPair $ coVarTypes cv, coVarRole cv)
    go co@(AxiomInstCo ax _ _) = (coercionRepKind co, coAxiomRole ax)
    go (UnivCo _ r ty1 ty2)  = (Pair ty1 ty2, r)
    go (SymCo co) = first swap $ go co
    go (TransCo co1 co2)
      = let (tys1, r) = go co1 in
        (Pair (pFst tys1) (pSnd $ coercionRepKind co2), r)
    go (NthCo d co)
      | Just (tv1, _) <- splitForAllTy_maybe ty1
      = ASSERT( d == 0 )
        let (tv2, _) = splitForAllTy ty2 in
        (tyVarKind <$> Pair tv1 tv2, Nominal)

      | otherwise
      = let (tc1,  args1) = splitTyConApp ty1
            (_tc2, args2) = splitTyConApp ty2
        in
        ASSERT( tc1 == _tc2 )
        ((`getNth` d) <$> Pair args1 args2, nthRole r tc1 d)

      where
        (Pair ty1 ty2, r) = go co
    go co@(LRCo {}) = (coercionRepKind co, Nominal)
    go (InstCo co arg) = go_app co [arg]
    go (CoherenceCo co1 co2)
      = let (Pair t1 t2, r) = go co1 in
        (Pair (t1 `mkCastTy` co2) t2, r)
    go co@(KindCo {}) = (coercionRepKind co, Nominal)
    go (SubCo r co) = (coercionRepKind co, r)
    go co@(AxiomRuleCo ax _) = (coercionRepKind co, coaxrRole ax)

    go_app :: CoercionRep -> [CoercionRep] -> (Pair Type, Role)
    -- Collect up all the arguments and apply all at once
    -- See Note [Nested InstCos]
    go_app (InstCo co arg) args = go_app co (arg:args)
    go_app co              args
      = let (pair, r) = go co in
        (piResultTys <$> pair <*> (sequenceA $ map coercionRepKind args), r)

-- | Retrieve the two types a coercion coerces between. But do see the
-- warnings on 'coercionRepKindRole', which this function calls.
coercionRepKind :: CoercionRep -> Pair Type
coercionRepKind co = go co
  where
    go (Refl _ ty)          = Pair ty ty
    go (TyConAppCo _ tc cos)= mkTyConApp tc <$> (sequenceA $ map go cos)
    go (AppCo co1 co2)      = mkAppTy <$> go co1 <*> go co2
    go (ForAllCo tv1 vis k_co co)
      = let Pair _ k2          = coercionKind k_co
            tv2                = setTyVarKind tv1 k2
            Pair ty1 ty2       = go co
            ty2' = substTyWithUnchecked [tv1] [TyVarTy tv2 `mk_cast_ty` mkSymCo k_co] ty2 in
        mkNamedForAllTy <$> Pair tv1 tv2 <*> pure vis <*> Pair ty1 ty2'
    go (CoVarCo cv)         = toPair $ coVarTypes cv
    go (AxiomInstCo ax ind cos)
      | CoAxBranch { cab_tvs = tvs, cab_cvs = cvs
                   , cab_lhs = lhs, cab_rhs = rhs } <- coAxiomNthBranch ax ind
      , let Pair tycos1 tycos2 = sequenceA (map go cos)
            (tys1, cotys1) = splitAtList tvs tycos1
            (tys2, cotys2) = splitAtList tvs tycos2
            cos1           = map stripCoercionTy cotys1
            cos2           = map stripCoercionTy cotys2
      = ASSERT( cos `equalLength` (tvs ++ cvs) )
                  -- Invariant of AxiomInstCo: cos should
                  -- exactly saturate the axiom branch
        Pair (substTyWith tvs tys1 $
              substTyWithCoVars cvs cos1 $
              mkTyConApp (coAxiomTyCon ax) lhs)
             (substTyWith tvs tys2 $
              substTyWithCoVars cvs cos2 rhs)
    go (UnivCo _ _ ty1 ty2)   = Pair ty1 ty2
    go (SymCo co)             = swap $ go co
    go (TransCo co1 co2)      = Pair (pFst $ go co1) (pSnd $ go co2)
    go g@(NthCo d co)
      | Just argss <- traverse tyConAppArgs_maybe tys
      = ASSERT( and $ ((d <) . length) <$> argss )
        (`getNth` d) <$> argss

      | d == 0
      , Just splits <- traverse splitForAllTy_maybe tys
      = (tyVarKind . fst) <$> splits

      | otherwise
      = pprPanic "coercionKind" (ppr g)
      where
        tys = go co
    go (LRCo lr co)         = (pickLR lr . splitAppTy) <$> go co
    go (InstCo aco arg)     = go_app aco [arg]
    go (CoherenceCo g h)
      = let Pair ty1 ty2 = go g in
        Pair (mkCastTy ty1 h) ty2
    go (KindCo co)          = typeKind <$> go co
    go (SubCo _ co)         = go co
    go (AxiomRuleCo ax cos) = expectJust "coercionKind" $
                              coaxrProves ax (map go cos)

    go_app :: CoercionRep -> [CoercionRep] -> Pair Type
    -- Collect up all the arguments and apply all at once
    -- See Note [Nested InstCos]
    go_app (InstCo co arg) args = go_app co (arg:args)
    go_app co              args = piResultTys <$> go co <*> (sequenceA $ map go args)

    -- The real mkCastTy is too slow, and we can easily have nested ForAllCos.
    mk_cast_ty :: Type -> Coercion -> Type
    mk_cast_ty ty co | isReflCo co = ty
                     | otherwise   = CastTy ty co

{-
%************************************************************************
%*                                                                      *
                   "Lifting" substitution
           [(TyCoVar,Coercion)] -> Type -> Coercion
%*                                                                      *
%************************************************************************

Note [Lifting coercions over types: liftCoSubst]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The KPUSH rule deals with this situation
   data T a = MkK (a -> Maybe a)
   g :: T t1 ~ K t2
   x :: t1 -> Maybe t1

   case (K @t1 x) |> g of
     K (y:t2 -> Maybe t2) -> rhs

We want to push the coercion inside the constructor application.
So we do this

   g' :: t1~t2  =  Nth 0 g

   case K @t2 (x |> g' -> Maybe g') of
     K (y:t2 -> Maybe t2) -> rhs

The crucial operation is that we
  * take the type of K's argument: a -> Maybe a
  * and substitute g' for a
thus giving *coercion*.  This is what liftCoSubst does.

In the presence of kind coercions, this is a bit
of a hairy operation. So, we refer you to the paper introducing kind coercions,
available at www.cis.upenn.edu/~sweirich/papers/fckinds-extended.pdf
-}

-- ----------------------------------------------------
-- See Note [Lifting coercions over types: liftCoSubst]
-- ----------------------------------------------------

data LiftingContext = LC TCvSubst LiftCoEnv
  -- in optCoercion, we need to lift when optimizing InstCo.
  -- See Note [Optimising InstCo] in OptCoercion
  -- We thus propagate the substitution from OptCoercion here.

instance Outputable LiftingContext where
  ppr (LC _ env) = hang (text "LiftingContext:") 2 (ppr env)

type LiftCoEnv = VarEnv Coercion
     -- Maps *type variables* to *coercions*.
     -- That's the whole point of this function!

-- like liftCoSubstWith, but allows for existentially-bound types as well
liftCoSubstWithEx :: Role          -- desired role for output coercion
                  -> [TyVar]       -- universally quantified tyvars
                  -> [Coercion]    -- coercions to substitute for those
                  -> [TyVar]       -- existentially quantified tyvars
                  -> [Type]        -- types to be bound to ex vars
                  -> (Type -> Coercion, [Type]) -- (lifting function, converted ex args)
liftCoSubstWithEx role univs omegas exs rhos
  = let theta = mkLiftingContext (zipEqual "liftCoSubstWithExU" univs omegas)
        psi   = extendLiftingContextEx theta (zipEqual "liftCoSubstWithExX" exs rhos)
    in (ty_co_subst psi role, substTyVars (lcSubstRight psi) exs)

liftCoSubstWith :: Role -> [TyCoVar] -> [Coercion] -> Type -> Coercion
-- NB: This really can be called with CoVars, when optimising axioms.
liftCoSubstWith r tvs cos ty
  = liftCoSubst r (mkLiftingContext $ zipEqual "liftCoSubstWith" tvs cos) ty

-- | @liftCoSubst role lc ty@ produces a coercion (at role @role@)
-- that coerces between @lc_left(ty)@ and @lc_right(ty)@, where
-- @lc_left@ is a substitution mapping type variables to the left-hand
-- types of the mapped coercions in @lc@, and similar for @lc_right@.
liftCoSubst :: Role -> LiftingContext -> Type -> Coercion
liftCoSubst r lc@(LC subst env) ty
  | isEmptyVarEnv env = mkReflCo r (substTy subst ty)
  | otherwise         = ty_co_subst lc r ty

-- | Like 'liftCoSubst', but for 'CoercionRep's
liftCoRepSubst :: Role -> LiftingContext -> Type -> CoercionRep
liftCoRepSubst r lc@(LC subst env) ty
  | isEmptyVarEnv env = mkReflCoRep r (substTy subst ty)
  | otherwise         = ty_co_rep_subst lc r ty

emptyLiftingContext :: InScopeSet -> LiftingContext
emptyLiftingContext in_scope = LC (mkEmptyTCvSubst in_scope) emptyVarEnv

mkLiftingContext :: [(TyCoVar,Coercion)] -> LiftingContext
mkLiftingContext pairs
  = LC (mkEmptyTCvSubst $ mkInScopeSet $ tyCoVarsOfCos (map snd pairs))
       (mkVarEnv pairs)

mkSubstLiftingContext :: TCvSubst -> LiftingContext
mkSubstLiftingContext subst = LC subst emptyVarEnv

-- | Extend a lifting context with a new mapping.
extendLiftingContext :: LiftingContext  -- ^ original LC
                     -> TyVar           -- ^ new variable to map...
                     -> Coercion        -- ^ ...to this lifted version
                     -> LiftingContext
extendLiftingContext (LC subst env) tv arg
  | Just (ty, _) <- isReflCo_maybe arg
  = LC (extendTvSubst subst tv ty) env
  | otherwise
  = LC subst (extendVarEnv env tv arg)

-- | Extend a lifting context with existential-variable bindings.
-- This follows the lifting context extension definition in the
-- "FC with Explicit Kind Equality" paper.
extendLiftingContextEx :: LiftingContext    -- ^ original lifting context
                       -> [(TyVar,Type)]    -- ^ ex. var / value pairs
                       -> LiftingContext
-- Note that this is more involved than extendLiftingContext. That function
-- takes a coercion to extend with, so it's assumed that the caller has taken
-- into account any of the kind-changing stuff worried about here.
extendLiftingContextEx lc [] = lc
extendLiftingContextEx lc@(LC subst env) ((v,ty):rest)
-- This function adds bindings for *Nominal* coercions. Why? Because it
-- works with existentially bound variables, which are considered to have
-- nominal roles.
  = let lc' = LC (subst `extendTCvInScopeSet` tyCoVarsOfType ty)
                 (extendVarEnv env v (mkSymCo $ mkCoherenceCo
                                         (mkNomReflCo ty)
                                         (ty_co_subst lc Nominal (tyVarKind v))))
    in extendLiftingContextEx lc' rest

-- | Erase the environments in a lifting context
zapLiftingContext :: LiftingContext -> LiftingContext
zapLiftingContext (LC subst _) = LC (zapTCvSubst subst) emptyVarEnv

-- | Like 'substForAllCoBndr', but works on a lifting context
substForAllCoBndrCallbackLC :: Bool
                            -> (Coercion -> Coercion)
                            -> LiftingContext -> TyVar -> Coercion
                            -> (LiftingContext, TyVar, Coercion)
substForAllCoBndrCallbackLC sym sco (LC subst lc_env) tv co
  = (LC subst' lc_env, tv', co')
  where
    (subst', tv', co') = substForAllCoBndrCallback sym sco subst tv co

-- | The \"lifting\" operation which substitutes coercions for type
--   variables in a type to produce a coercion.
--
--   For the inverse operation, see 'liftCoMatch'
ty_co_subst :: LiftingContext -> Role -> Type -> Coercion
ty_co_subst lc r ty
  = CachedCoercion { coercionKind    = substTy <$> lcSubst lc <*> pure ty
                   , coercionRole    = r
                   , tyCoVarsOfCoAcc = tyCoVarsOfCoRepAcc rep
                   , coercionInfo    = NoCachedInfo
                   , coercionRep     = rep }
  where
    rep = ty_co_rep_subst lc r ty

ty_co_rep_subst :: LiftingContext -> Role -> Type -> CoercionRep
ty_co_rep_subst lc = go
  where
    go Phantom ty          = lift_phantom ty

    go r ty | Just ty' <- coreView ty = go r ty'
      -- necessary so that we don't call mkTyConAppCoRep with a synonym

    go r (TyVarTy tv)      = coercionRep $
                             expectJust "ty_co_subst bad roles" $
                             liftCoSubstTyVar lc r tv
    go r (AppTy ty1 ty2)   = mkAppCoRep (go r ty1) (go Nominal ty2)
    go r (TyConApp tc tys) = mkTyConAppCoRep r tc (zipWith go (tyConRolesX r tc) tys)
    go r (ForAllTy (Anon ty1) ty2)
                           = mkTyConAppCoRep r funTyCon (map (go r) [ty1, ty2])
    go r (ForAllTy (Named v vis) ty)
                           = let (lc', v', h) = liftCoSubstVarBndr lc v in
                             mkForAllCoRep v' vis h $! ty_co_rep_subst lc' r ty
    go r ty@(LitTy {})     = ASSERT( r == Nominal )
                             mkReflCoRep r ty
    go r (CastTy ty co)    = castCoercionKindRep (go r ty) (substLeftCo lc co)
                                                           (substRightCo lc co)
    go r (CoercionTy co)   = mkProofIrrelCoRep r (go Nominal (coercionType co))
                                                 (substLeftCo lc co)
                                                 (substRightCo lc co)

    lift_phantom ty = mkPhantomCoRep (go Nominal (typeKind ty))
                                     (substTy (lcSubstLeft  lc) ty)
                                     (substTy (lcSubstRight lc) ty)

{-
Note [liftCoSubstTyVar]
~~~~~~~~~~~~~~~~~~~~~~~~~
This function can fail if a coercion in the environment is of too low a role.

liftCoSubstTyVar is called from two places: in liftCoSubst (naturally), and
also in matchAxiom in OptCoercion. From liftCoSubst, the so-called lifting
lemma guarantees that the roles work out. If we fail in this
case, we really should panic -- something is deeply wrong. But, in matchAxiom,
failing is fine. matchAxiom is trying to find a set of coercions
that match, but it may fail, and this is healthy behavior.

-}

-- See Note [liftCoSubstTyVar]
liftCoSubstTyVar :: LiftingContext -> Role -> TyVar -> Maybe Coercion
liftCoSubstTyVar (LC subst env) r v
  | Just co_arg <- lookupVarEnv env v
  = downgradeRole_maybe r (coercionRole co_arg) co_arg

  | otherwise
  = Just $ mkReflCo r (substTyVar subst v)

liftCoSubstVarBndr :: LiftingContext -> TyVar
                   -> (LiftingContext, TyVar, Coercion)
liftCoSubstVarBndr lc tv
  = let (lc', tv', co', _) = liftCoSubstVarBndrCallback callback lc tv in
    (lc', tv', co')
  where
    callback lc' ty' = (co, ty1', ty2')
      where
        co = ty_co_subst lc' Nominal ty'
        Pair ty1' ty2' = coercionKind co

liftCoSubstVarBndrCallback :: (LiftingContext -> Type -> (Coercion, Kind, Kind))
                                 -- the kinds are the two types of the
                                 -- coercion (but possibly with different synonyms
                                 -- expanded)
                           -> LiftingContext -> TyVar
                           -> (LiftingContext, TyVar, Coercion, Kind)
                                 -- also returns the right-hand kind of the coercion
liftCoSubstVarBndrCallback fun lc@(LC subst cenv) old_var
  = ( LC (subst `extendTCvInScope` new_var) new_cenv
    , new_var, eta, rhs_kind )
  where
    old_kind                  = tyVarKind old_var
    (eta, lhs_kind, rhs_kind) = fun lc old_kind
    new_var                   = uniqAway (getTCvInScope subst)
                                         (setVarType old_var lhs_kind)

    lifted   = mkReflCo Nominal (TyVarTy new_var)
    new_cenv = extendVarEnv cenv old_var lifted

-- | Is a var in the domain of a lifting context?
isMappedByLC :: TyCoVar -> LiftingContext -> Bool
isMappedByLC tv (LC _ env) = tv `elemVarEnv` env

-- If [a |-> g] is in the substitution and g :: t1 ~ t2, substitute a for t1
-- If [a |-> (g1, g2)] is in the substitution, substitute a for g1
substLeftCo :: LiftingContext -> Coercion -> Coercion
substLeftCo lc co
  = substCo (lcSubstLeft lc) co

-- Ditto, but for t2 and g2
substRightCo :: LiftingContext -> Coercion -> Coercion
substRightCo lc co
  = substCo (lcSubstRight lc) co

-- | Apply "sym" to all coercions in a 'LiftCoEnv'
swapLiftCoEnv :: LiftCoEnv -> LiftCoEnv
swapLiftCoEnv = mapVarEnv mkSymCo

lcSubstLeft :: LiftingContext -> TCvSubst
lcSubstLeft (LC subst lc_env) = liftEnvSubstLeft subst lc_env

lcSubstRight :: LiftingContext -> TCvSubst
lcSubstRight (LC subst lc_env) = liftEnvSubstRight subst lc_env

lcSubst :: LiftingContext -> Pair TCvSubst
lcSubst (LC subst lc_env) = liftEnvSubst <$> Pair pFst pSnd <*> pure subst
                                                            <*> pure lc_env

liftEnvSubstLeft :: TCvSubst -> LiftCoEnv -> TCvSubst
liftEnvSubstLeft = liftEnvSubst pFst

liftEnvSubstRight :: TCvSubst -> LiftCoEnv -> TCvSubst
liftEnvSubstRight = liftEnvSubst pSnd

liftEnvSubst :: (Pair Type -> Type) -> TCvSubst -> LiftCoEnv -> TCvSubst
liftEnvSubst selector subst lc_env
  = composeTCvSubst (TCvSubst emptyInScopeSet tenv cenv) subst
  where
    pairs            = varEnvToList lc_env
    (tpairs, cpairs) = partitionWith ty_or_co pairs
    tenv             = mkVarEnv_Directly tpairs
    cenv             = mkVarEnv_Directly cpairs

    ty_or_co :: (Unique, Coercion) -> Either (Unique, Type) (Unique, Coercion)
    ty_or_co (u, co)
      | Just equality_co <- isCoercionTy_maybe equality_ty
      = Right (u, equality_co)
      | otherwise
      = Left (u, equality_ty)
      where
        equality_ty = selector (coercionKind co)

-- | Extract the underlying substitution from the LiftingContext
lcTCvSubst :: LiftingContext -> TCvSubst
lcTCvSubst (LC subst _) = subst

-- | Get the 'InScopeSet' from a 'LiftingContext'
lcInScopeSet :: LiftingContext -> InScopeSet
lcInScopeSet (LC subst _) = getTCvInScope subst

{-
%************************************************************************
%*                                                                      *
            Sequencing on coercions
%*                                                                      *
%************************************************************************
-}

seqCoRep :: CoercionRep -> ()
seqCoRep (Refl r ty)               = r `seq` seqType ty
seqCoRep (TyConAppCo r tc cos)     = r `seq` tc `seq` seqCoReps cos
seqCoRep (AppCo co1 co2)           = seqCoRep co1 `seq` seqCoRep co2
seqCoRep (ForAllCo tv vis k co)    = seqType (tyVarKind tv) `seq` vis
                                                            `seq` seqCo k
                                                            `seq` seqCoRep co
seqCoRep (CoVarCo cv)              = cv `seq` ()
seqCoRep (AxiomInstCo con ind cos) = con `seq` ind `seq` seqCoReps cos
seqCoRep (UnivCo p r t1 t2)        = seqProv p `seq` r `seq` seqType t1 `seq` seqType t2
seqCoRep (SymCo co)                = seqCoRep co
seqCoRep (TransCo co1 co2)         = seqCoRep co1 `seq` seqCoRep co2
seqCoRep (NthCo n co)              = n `seq` seqCoRep co
seqCoRep (LRCo lr co)              = lr `seq` seqCoRep co
seqCoRep (InstCo co arg)           = seqCoRep co `seq` seqCoRep arg
seqCoRep (CoherenceCo co1 co2)     = seqCoRep co1 `seq` seqCo co2
seqCoRep (KindCo co)               = seqCoRep co
seqCoRep (SubCo r co)              = r `seq` seqCoRep co
seqCoRep (AxiomRuleCo _ cs)        = seqCoReps cs

seqProv :: UnivCoProvenance -> ()
seqProv UnsafeCoerceProv    = ()
seqProv (PhantomProv co)    = seqCoRep co
seqProv (ProofIrrelProv co) = seqCoRep co
seqProv (PluginProv _)      = ()
seqProv (HoleProv _)        = ()

seqCoReps :: [CoercionRep] -> ()
seqCoReps []       = ()
seqCoReps (co:cos) = seqCoRep co `seq` seqCoReps cos

seqCo :: Coercion -> ()
  -- NB: Don't evaluate the coercionInfo, as that duplicates work
  -- with coercionKind. See Note [Nested InstCos].
seqCo (CachedCoercion { coercionKind    = Pair ty1 ty2
                      , coercionRole    = role
                      , tyCoVarsOfCoAcc = fvs
                      , coercionRep     = rep })
  = seqType ty1 `seq`
    seqType ty2 `seq`
    role `seq`
    fvs `seq`
    seqCoRep rep

{-
%************************************************************************
%*                                                                      *
             The kind of a type, and of a coercion
%*                                                                      *
%************************************************************************

-}

coercionType :: Coercion -> Type
coercionType co = case coercionKindRole co of
  (Pair ty1 ty2, r) -> mkCoercionType r ty1 ty2

-- | Apply 'coercionKind' to multiple 'Coercion's
coercionKinds :: [Coercion] -> Pair [Type]
coercionKinds tys = sequenceA $ map coercionKind tys

-- | Get a coercion's kind and role.
coercionKindRole :: Coercion -> (Pair Type, Role)
coercionKindRole co = (coercionKind co, coercionRole co)

{-
Note [Nested InstCos]
~~~~~~~~~~~~~~~~~~~~~
In Trac #5631 we found that 70% of the entire compilation time was
being spent in coercionKind!  The reason was that we had
   (g @ ty1 @ ty2 .. @ ty100)    -- The "@s" are InstCos
where
   g :: forall a1 a2 .. a100. phi
If we deal with the InstCos one at a time, we'll do this:
   1.  Find the kind of (g @ ty1 .. @ ty99) : forall a100. phi'
   2.  Substitute phi'[ ty100/a100 ], a single tyvar->type subst
But this is a *quadratic* algorithm, and the blew up Trac #5631.
So it's very important to do the substitution simultaneously;
cf Type.piResultTys (which in fact we call here).

Now that we're caching coercionKind, it's necessary to keep enough
of the pieces around to do this optimization. This is the motivation
behind CachedInstInfo.

Example: Suppose we have (forall a b c. <(a,b,c)>)@Int@Bool@Double.
Then the top-level CachedInstInfo is like
  CachedInstInfo { cachedUnderlyingPair = Pair (a,b,c) (a,b,c)
                 , cachedRevArgs        = Pair [Double, Bool, Int]
                                               [Double, Bool, Int] }
The arguments are reversed for easy consing.

Another way to think of this is to pretend that coercions store their
kind as a Pair DeferredKind, where a DeferredKind is a (Kind, Subst).
That is, a DeferredKind is some kind with a substitution to apply. When
we want a Kind out of a DeferredKind, we simply apply the substitution.
Yet we don't want to store it this way, because we want coercionKind to
be snappy and not to look for a deferred version. So we store both
the non-deferred kind and a deferred kind, but we're careful to force
only one of these two fields. The real kind is coercionKind, the
deferred one is coercionInfo.

-}
