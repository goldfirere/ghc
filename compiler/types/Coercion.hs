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
        Coercion, CoercionArg, ForAllCoBndr, LeftOrRight(..),
        Var, CoVar, TyCoVar, mkFreshCoVar, mkFreshReprCoVar, mkFreshCoVarOfType,
        Role(..), ltRole,

        -- ** Functions over coercions
        coVarTypes, coVarKind, coVarKindsTypesRole, coVarRole,
        coercionType, coercionKind, coercionKinds,
        mkCoercionType, coercionArgKind,
        coercionRole, coercionKindRole, coercionArgRole,

        -- ** Constructing coercions
        mkReflCo, mkRepReflCo, mkNomReflCo,
        mkReflCoArg, mkRepReflCoArg, mkNomReflCoArg,
        mkCoVarCo, 
        mkAxInstCo, mkUnbranchedAxInstCo,
        mkAxInstRHS, mkUnbranchedAxInstRHS,
        mkAxInstLHS, mkUnbranchedAxInstLHS,
        mkPiCo, mkPiCos, mkCoCast,
        mkSymCo, mkSymCoArg, mkTransCo, mkTransAppCo,
        mkNthCo, mkNthCoArg, mkNthCoRole, mkLRCo,
        mkInstCo, mkAppCo, mkAppCos, mkTyConAppCo, mkFunCo, mkFunCos,
        mkForAllCo, mkHomoForAllCo,
        mkPhantomCo, mkHomoPhantomCo, toPhantomCo,
        mkUnsafeCo, mkUnsafeCoArg, mkSubCo,
        mkNewTypeCo, mkAxiomInstCo,
        downgradeRole, downgradeRoleArg, maybeSubCo, mkAxiomRuleCo,
        mkCoherenceCo, mkCoherenceRightCo, mkCoherenceLeftCo,
        mkKindCo, mkKindAppCo, castCoercionKind,
        buildKindCos, buildKindCosX,

        mkForAllCoBndr, mkHomoCoBndr, coBndrVars, coBndrKind,
        mkHeteroCoercionType,

        mkTyCoArg, mkCoCoArg, mkCoArgForVar,

        -- ** Decomposition
        instNewTyCon_maybe,

        NormaliseStepper, NormaliseStepResult(..), composeSteppers,
        modifyStepResultCo, unwrapNewTypeStepper,
        topNormaliseNewType_maybe, topNormaliseTypeX_maybe,

        decomposeCo, getCoVar_maybe,
        splitTyConAppCo_maybe,
        splitAppCo_maybe,
        splitForAllCo_maybe,
        splitForAllCo_Ty_maybe, splitForAllCo_Co_maybe,

        nthRole, tyConRolesX, setNominalRole_maybe,

        pickLR,

        coBndrKindCo, coBndrWitness, setCoBndrKindCo,

        stripTyCoArg, splitCoCoArg_maybe,

        isReflCo, isReflCo_maybe, isReflLike, isReflLike_maybe,

        -- ** Coercion variables
        mkCoVar, isCoVar, coVarName, setCoVarName, setCoVarUnique,

        -- ** Free variables
        tyCoVarsOfCo, tyCoVarsOfCos, coVarsOfCo, coVarsOfCoArg,
        coercionSize,
        tyCoVarsOfCoArg, tyCoVarsOfCoArgs,
        
        -- ** Substitution
        CvSubstEnv, emptyCvSubstEnv,
        lookupCoVar,
        substCo, substCoArg, substCos, substCoVar, substCoVars,
        substCoVarBndr, substCoWithIS, substForAllCoBndr,
        extendTCvSubstAndInScope, getCvSubstEnv,

        -- ** Lifting
        liftCoSubst, liftCoSubstTyVar, liftCoSubstWith, liftCoSubstWithEx,
        emptyLiftingContext, extendLiftingContext, extendLiftingContextIS,
        liftCoSubstTyCoVar,
        liftCoSubstVarBndrCallback, isMappedByLC,

        LiftCoEnv, LiftingContext(..), liftEnvSubstLeft, liftEnvSubstRight,
        substRightCo, substLeftCo, swapLiftCoEnv,

        -- ** Comparison
        eqCoercion, eqCoercionX, eqCoercionArg,

        -- ** Forcing evaluation of coercions
        seqCo,
        
        -- * Pretty-printing
        pprCo, pprParendCo, pprCoArg, pprCoBndr,
        pprCoAxiom, pprCoAxBranch, pprCoAxBranchHdr, 

        -- * Tidying
        tidyCo, tidyCos,

        -- * Other
        applyCo, promoteCoercion, mkGADTVars,
        buildCoherenceCo, buildCoherenceCoX, buildCoherenceCoArg,
        buildCoherenceCoArgX
       ) where 

#include "HsVersions.h"

import TyCoRep
import Type 
import TyCon
import CoAxiom
import Var
import VarEnv
import VarSet
import Name hiding ( varName )
import Util
import BasicTypes
import Outputable
import Unique
import UniqSupply
import Pair
import SrcLoc
import PrelNames
import TysPrim          ( eqPhantPrimTyCon )
import ListSetOps
import Maybes
  
import Control.Applicative hiding ( empty )
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable (traverse, sequenceA)
#endif
import Control.Monad (foldM, zipWithM)
import FastString
import Control.Arrow ( first )
import Data.List ( mapAccumR )
import Data.Function ( on )

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
coercionSize (Refl _ ty)         = typeSize ty
coercionSize (TyConAppCo _ _ args) = 1 + sum (map coercionArgSize args)
coercionSize (AppCo co h arg)    = coercionSize co + coercionSize h + coercionArgSize arg
coercionSize (ForAllCo _ co)     = 1 + coercionSize co
coercionSize (CoVarCo _)         = 1
coercionSize (AxiomInstCo _ _ args) = 1 + sum (map coercionArgSize args)
coercionSize (PhantomCo h t1 t2) = 1 + coercionSize h + typeSize t1 + typeSize t2
coercionSize (UnsafeCo _ _ t1 t2)= 1 + typeSize t1 + typeSize t2
coercionSize (SymCo co)          = 1 + coercionSize co
coercionSize (TransCo co1 co2)   = 1 + coercionSize co1 + coercionSize co2
coercionSize (NthCo _ co)        = 1 + coercionSize co
coercionSize (LRCo  _ co)        = 1 + coercionSize co
coercionSize (InstCo co arg)     = 1 + coercionSize co + coercionArgSize arg
coercionSize (CoherenceCo c1 c2) = 1 + coercionSize c1 + coercionSize c2
coercionSize (KindCo co)         = 1 + coercionSize co
coercionSize (KindAppCo co)      = 1 + coercionSize co
coercionSize (SubCo co)          = 1 + coercionSize co
coercionSize (AxiomRuleCo _ ts cs) = 1 + sum (map typeSize ts)
                                       + sum (map coercionSize cs)

coercionArgSize :: CoercionArg -> Int
coercionArgSize (TyCoArg co)        = coercionSize co
coercionArgSize (CoCoArg _ h c1 c2) = sum $ map coercionSize [h, c1, c2]

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
pprCo       co = ppr_co TopPrec   co
pprParendCo co = ppr_co TyConPrec co

pprCoArg :: CoercionArg -> SDoc
pprCoArg = ppr_arg TopPrec

ppr_co :: TyPrec -> Coercion -> SDoc
ppr_co _ (Refl r ty) = angleBrackets (ppr ty) <> ppr_role r

ppr_co p co@(TyConAppCo _ tc [_,_])
  | tc `hasKey` funTyConKey = ppr_fun_co p co

ppr_co _ (TyConAppCo r tc cos)  = pprTcApp TyConPrec ppr_arg tc cos <> ppr_role r
ppr_co p (AppCo co h arg)      = maybeParen p TyConPrec $
                                 pprCo co <+> ppr_arg TyConPrec arg <>
                                 ifPprDebug (braces $ braces $ ppr h)
ppr_co p co@(ForAllCo {})      = ppr_forall_co p co
ppr_co _ (CoVarCo cv)          = parenSymOcc (getOccName cv) (ppr cv)
ppr_co p (AxiomInstCo con index args)
  = pprPrefixApp p (ppr (getName con) <> brackets (ppr index))
                   (map (ppr_arg TyConPrec) args)

ppr_co p co@(TransCo {}) = maybeParen p FunPrec $
                           case trans_co_list co [] of
                             [] -> panic "ppr_co"
                             (co:cos) -> sep ( ppr_co FunPrec co
                                             : [ char ';' <+> ppr_co FunPrec co | co <- cos])
ppr_co p (InstCo co arg) = maybeParen p TyConPrec $
                           pprParendCo co <> ptext (sLit "@") <> ppr_arg TopPrec arg

ppr_co _ (PhantomCo h t1 t2) = angleBrackets ( ppr t1 <> comma <+> ppr t2 ) <> char '_' <> pprParendCo h
ppr_co p (UnsafeCo s r ty1 ty2)
  = pprPrefixApp p (ptext (sLit "UnsafeCo") <+> ftext s <+> ppr r)
                   [pprParendType ty1, pprParendType ty2]
ppr_co p (SymCo co)          = pprPrefixApp p (ptext (sLit "Sym")) [pprParendCo co]
ppr_co p (NthCo n co)        = pprPrefixApp p (ptext (sLit "Nth:") <> int n) [pprParendCo co]
ppr_co p (LRCo sel co)       = pprPrefixApp p (ppr sel) [pprParendCo co]
ppr_co p (CoherenceCo c1 c2) = maybeParen p TyConPrec $
                               (ppr_co FunPrec c1) <+> (ptext (sLit "|>")) <+>
                               (ppr_co FunPrec c2)
ppr_co p (KindCo co)         = pprPrefixApp p (ptext (sLit "kind")) [pprParendCo co]
ppr_co p (KindAppCo co)     = pprPrefixApp p (text "kapp") [pprParendCo co]
ppr_co p (SubCo co)         = pprPrefixApp p (ptext (sLit "Sub")) [pprParendCo co]
ppr_co p (AxiomRuleCo co ts cs) = maybeParen p TopPrec $
                                  ppr_axiom_rule_co co ts cs

ppr_axiom_rule_co :: CoAxiomRule -> [Type] -> [Coercion] -> SDoc
ppr_axiom_rule_co co ts ps = ppr (coaxrName co) <> ppTs ts $$ nest 2 (ppPs ps)
  where
  ppTs []   = Outputable.empty
  ppTs [t]  = ptext (sLit "@") <> ppr_type TopPrec t
  ppTs ts   = ptext (sLit "@") <>
                parens (hsep $ punctuate comma $ map pprType ts)

  ppPs []   = Outputable.empty
  ppPs [p]  = pprParendCo p
  ppPs (p : ps) = ptext (sLit "(") <+> pprCo p $$
                  vcat [ ptext (sLit ",") <+> pprCo q | q <- ps ] $$
                  ptext (sLit ")")

ppr_role :: Role -> SDoc
ppr_role r = underscore <> pp_role
  where pp_role = case r of
                    Nominal          -> char 'N'
                    Representational -> char 'R'
                    Phantom          -> char 'P'

ppr_arg :: TyPrec -> CoercionArg -> SDoc
ppr_arg p (TyCoArg co) = ppr_co p co
ppr_arg _ (CoCoArg r h co1 co2)
  = parens (pprCo co1 <> comma <+> pprCo co2) <> ppr_role r <>
    ifPprDebug (braces $ braces $ pprCo h)

trans_co_list :: Coercion -> [Coercion] -> [Coercion]
trans_co_list (TransCo co1 co2) cos = trans_co_list co1 (trans_co_list co2 cos)
trans_co_list co                cos = co : cos

ppr_fun_co :: TyPrec -> Coercion -> SDoc
ppr_fun_co p co = pprArrowChain p (split co)
  where
    split :: Coercion -> [SDoc]
    split (TyConAppCo _ f [TyCoArg arg, TyCoArg res])
      | f `hasKey` funTyConKey
      = ppr_co FunPrec arg : split res
    split co = [ppr_co TopPrec co]

ppr_forall_co :: TyPrec -> Coercion -> SDoc
ppr_forall_co p (ForAllCo cobndr co)
  = maybeParen p FunPrec $
    sep [pprCoBndr cobndr, ppr_co TopPrec co]
ppr_forall_co _ _ = panic "ppr_forall_co"

pprCoBndr :: ForAllCoBndr -> SDoc
pprCoBndr cobndr = pprForAllImplicit (coBndrVars cobndr)

pprCoAxiom :: CoAxiom br -> SDoc
pprCoAxiom ax@(CoAxiom { co_ax_tc = tc, co_ax_branches = branches })
  = hang (ptext (sLit "axiom") <+> ppr ax <+> dcolon)
       2 (vcat (map (pprCoAxBranch tc) $ fromBranchList branches))

pprCoAxBranch :: TyCon -> CoAxBranch -> SDoc
pprCoAxBranch fam_tc (CoAxBranch { cab_tvs = tvs
                                 , cab_lhs = lhs
                                 , cab_rhs = rhs })
  = hang (pprUserForAllImplicit tvs)
       2 (hang (pprTypeApp fam_tc lhs) 2 (equals <+> (ppr rhs)))

pprCoAxBranchHdr :: CoAxiom br -> BranchIndex -> SDoc
pprCoAxBranchHdr ax@(CoAxiom { co_ax_tc = fam_tc, co_ax_name = name }) index
  | CoAxBranch { cab_lhs = tys, cab_loc = loc } <- coAxiomNthBranch ax index
  = hang (pprTypeApp fam_tc tys)
       2 (ptext (sLit "-- Defined") <+> ppr_loc loc)
  where
        ppr_loc loc
          | isGoodSrcSpan loc
          = ptext (sLit "at") <+> ppr (srcSpanStart loc)
    
          | otherwise
          = ptext (sLit "in") <+>
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
decomposeCo :: Arity -> Coercion -> [CoercionArg]
decomposeCo arity co 
  = [mkNthCoArg n co | n <- [0..(arity-1)] ]
           -- Remember, Nth is zero-indexed

-- | Attempts to obtain the type variable underlying a 'Coercion'
getCoVar_maybe :: Coercion -> Maybe CoVar
getCoVar_maybe (CoVarCo cv) = Just cv  
getCoVar_maybe _            = Nothing

-- | Attempts to tease a coercion apart into a type constructor and the application
-- of a number of coercion arguments to that constructor
splitTyConAppCo_maybe :: Coercion -> Maybe (TyCon, [CoercionArg])
splitTyConAppCo_maybe (Refl r ty)
  = do { (tc, tys) <- splitTyConApp_maybe ty
       ; let args = zipWith mkReflCoArg (tyConRolesX r tc) tys
       ; return (tc, args) }
splitTyConAppCo_maybe (TyConAppCo _ tc cos) = Just (tc, cos)
splitTyConAppCo_maybe _                     = Nothing

-- first & second result has role equal to input; third result is Nominal
-- second result is a kind equality for the types in the third result
splitAppCo_maybe :: Coercion -> Maybe (Coercion, Coercion, CoercionArg)
-- ^ Attempt to take a coercion application apart.
splitAppCo_maybe (AppCo co h arg) = Just (co, h, arg)
splitAppCo_maybe (TyConAppCo r tc args)
  | isDecomposableTyCon tc || args `lengthExceeds` tyConArity tc
    -- Never create unsaturated type family apps!
  , Just (args', arg') <- snocView args
  , Just arg'' <- setNominalRoleArg_maybe arg'
  = Just ( mkTyConAppCo r tc args'
         , only $ buildKindCos r (tyConKind tc) args' [arg'']
         , arg'' ) 
       -- Use mkTyConAppCo to preserve the invariant
       --  that identity coercions are always represented by Refl

splitAppCo_maybe (Refl r ty) 
  | Just (ty1, ty2) <- splitAppTy_maybe ty 
  = Just (mkReflCo r ty1, mkReflCo r (typeKind ty2), mkNomReflCoArg ty2)
splitAppCo_maybe _ = Nothing

splitForAllCo_maybe :: Coercion -> Maybe (ForAllCoBndr, Coercion)
splitForAllCo_maybe (ForAllCo cobndr co) = Just (cobndr, co)
splitForAllCo_maybe _                    = Nothing

-- returns the two type variables abstracted over
splitForAllCo_Ty_maybe :: Coercion -> Maybe (TyVar, TyVar, CoVar, Coercion)
splitForAllCo_Ty_maybe (ForAllCo (ForAllCoBndr _ tv1 tv2 (Just cv)) co)
  = Just (tv1, tv2, cv, co)
splitForAllCo_Ty_maybe _
  = Nothing

-- returns the two coercion variables abstracted over
splitForAllCo_Co_maybe :: Coercion -> Maybe (CoVar, CoVar, Coercion)
splitForAllCo_Co_maybe (ForAllCo (ForAllCoBndr _ cv1 cv2 Nothing) co)
  = Just (cv1, cv2, co)
splitForAllCo_Co_maybe _
  = Nothing

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
 | Just (tc, [k,ty1,ty2]) <- splitTyConApp_maybe (varType cv)
 = let role  -- this case should only happen during typechecking.
             -- TODO (RAE): Remove this when there are no more lifted
             -- equalities in the typechecker.
         | tc `hasKey` eqTyConKey         = Nominal
         | tc `hasKey` coercibleTyConKey  = Representational
         | otherwise                      = panic "coVarKindsTypeRole 2"
   in (k,k,ty1,ty2,role)
 | otherwise = pprPanic "coVarKindsTypesRole, non coercion variable"
                        (ppr cv $$ ppr (varType cv))

coVarKind :: CoVar -> Type
coVarKind cv
  = ASSERT( isCoVar cv )
    varType cv

coVarRole :: CoVar -> Role
coVarRole cv
-- TODO (RAE): Remove lifted tycons after lifted equality is removed
  | tc `hasKey` eqPrimTyConKey || tc `hasKey` eqTyConKey
  = Nominal
  | tc `hasKey` eqReprPrimTyConKey || tc `hasKey` coercibleTyConKey
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

isReflCo :: Coercion -> Bool
isReflCo (Refl {}) = True
isReflCo _         = False

isReflCo_maybe :: Coercion -> Maybe (Type, Role)
isReflCo_maybe (Refl r ty) = Just (ty, r)
isReflCo_maybe _           = Nothing

-- | Returns the Refl'd type if the CoercionArg is "Refl-like".
-- A TyCoArg (Refl ...) is Refl-like.
-- A CoCoArg co1 co2 is Refl-like if co1 and co2 have the same type.
-- The Type returned in the second case is the first coercion in the CoCoArg.
isReflLike_maybe :: CoercionArg -> Maybe Type
isReflLike_maybe (TyCoArg (Refl _ ty)) = Just ty
isReflLike_maybe (CoCoArg _ (Refl {}) co1 _)
  = Just $ CoercionTy co1

isReflLike_maybe _ = Nothing

isReflLike :: CoercionArg -> Bool
isReflLike = isJust . isReflLike_maybe

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
that's ill-roled! Note that mkAppCo requires a *nominal* third coercion.

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

mkReflCo :: Role -> Type -> Coercion
mkReflCo r ty
  = ASSERT( not $ isCoercionTy ty )
    Refl r ty

-- | Make a representational reflexive coercion
mkRepReflCo :: Type -> Coercion
mkRepReflCo = mkReflCo Representational

-- | Make a nominal reflexive coercion
mkNomReflCo :: Type -> Coercion
mkNomReflCo = mkReflCo Nominal

-- | Make a reflexive CoercionArg
mkReflCoArg :: Role -> Type -> CoercionArg
mkReflCoArg r (CoercionTy co)
  = CoCoArg r (mkRepReflCo (coercionType co)) co co
mkReflCoArg r ty = TyCoArg $ mkReflCo r ty

-- | Make a representational reflexive CoercionArg
mkRepReflCoArg :: Type -> CoercionArg
mkRepReflCoArg = mkReflCoArg Representational

-- | Make a nominal reflexive CoercionArg
mkNomReflCoArg :: Type -> CoercionArg
mkNomReflCoArg = mkReflCoArg Nominal

-- | Apply a type constructor to a list of coercions. It is the
-- caller's responsibility to get the roles correct on argument coercions.
mkTyConAppCo :: Role -> TyCon -> [CoercionArg] -> Coercion
mkTyConAppCo r tc cos
               -- Expand type synonyms
  | Just (tv_co_prs, rhs_ty, leftover_cos) <- tcExpandTyCon_maybe tc cos
  = let leftover_kcos = drop (tyConArity tc) $
                        buildKindCos r (tyConKind tc) [] cos
        leftover_co_pairs = zip leftover_kcos leftover_cos
    in
    mkAppCos (liftCoSubst r (mkLiftingContext tv_co_prs) rhs_ty) leftover_co_pairs

  | Just tys <- traverse isReflLike_maybe cos 
  = Refl r (mkTyConApp tc tys)    -- See Note [Refl invariant]

  | otherwise = TyConAppCo r tc cos

-- | Make a function 'Coercion' between two other 'Coercion's
mkFunCo :: Role -> Coercion -> Coercion -> Coercion
mkFunCo r co1 co2 = mkTyConAppCo r funTyCon [TyCoArg co1, TyCoArg co2]

-- | Make nested function 'Coercion's
mkFunCos :: Role -> [Coercion] -> Coercion -> Coercion
mkFunCos r cos res_co = foldr (mkFunCo r) res_co cos

-- | Apply a 'Coercion' to another 'CoercionArg'.
-- The third coercion must be Nominal, unless the first is Phantom.
-- If the first is Phantom, then the second can be either Phantom or Nominal.
mkAppCo :: Coercion     -- ^ :: t1 ~r t2
        -> Coercion     -- ^ :: k1 ~r k2
        -> CoercionArg  -- ^ :: s1 ~N s2, where s1 :: k1, s2 :: k2
        -> Coercion     -- ^ :: t1 s1 ~r t2 s2
mkAppCo (Refl r ty1) _ arg
  | Just ty2 <- isReflLike_maybe arg
  = Refl r (mkAppTy ty1 ty2)

  | Just (tc, tys) <- splitTyConApp_maybe ty1
    -- Expand type synonyms; a TyConAppCo can't have a type synonym (Trac #9102)
  = TyConAppCo r tc (zip_roles (tyConRolesX r tc) tys)
  where
    zip_roles (r1:_)  []            = [downgradeRoleArg r1 Nominal arg]
    zip_roles (r1:rs) (ty1:tys)     = mkReflCoArg r1 ty1 : zip_roles rs tys
    zip_roles _       _             = panic "zip_roles" -- but the roles are infinite...
    
mkAppCo (TyConAppCo r tc args) _ arg
  = case r of
      Nominal          -> TyConAppCo Nominal tc (args ++ [arg])
      Representational -> TyConAppCo Representational tc (args ++ [arg'])
        where new_role = (tyConRolesX Representational tc) !! (length args)
              arg'     = downgradeRoleArg new_role Nominal arg
      Phantom          -> TyConAppCo Phantom tc (args ++ [toPhantomCoArg arg])
mkAppCo co kco arg
  = AppCo co kco arg
-- Note, mkAppCo is careful to maintain invariants regarding
-- where Refl constructors appear; see the comments in the definition
-- of Coercion and the Note [Refl invariant] in types/TyCoRep.lhs.

-- | Applies multiple 'Coercion's to another 'CoercionArg', from left to right.
-- See also 'mkAppCo'.
mkAppCos :: Coercion -> [(Coercion, CoercionArg)] -> Coercion
mkAppCos co1 cos = foldl (uncurry2 mkAppCo) co1 cos

-- | Like `mkAppCo`, but allows the second coercion to be other than
-- nominal. See Note [mkTransAppCo]. Role r3 cannot be more stringent
-- than either r1 or r2.
mkTransAppCo :: Role         -- ^ r1
             -> Coercion     -- ^ co1 :: ty1a ~r1 ty1b
             -> Type         -- ^ ty1a
             -> Type         -- ^ ty1b
             -> Coercion     -- ^ kco :: kind ty2a ~r1 kind ty2b
                             --   (Only used when r1 is N)
             -> Role         -- ^ r2
             -> CoercionArg  -- ^ co2 :: ty2a ~r2 ty2b
             -> Type         -- ^ ty2a
             -> Type         -- ^ ty2b
             -> Role         -- ^ r3
             -> Coercion     -- ^ :: ty1a ty2a ~r3 ty1b ty2b
mkTransAppCo r1 co1 ty1a ty1b kco r2 co2 ty2a ty2b r3
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
              kind_co1 = mkKindCo co1        -- :: k1a -> k2a ~R k1b -> k2b
              kind_co  = mkNthCo 1 kind_co1  -- :: k2a ~R k2b
          
      (_,                _,                Nominal)
        -> ASSERT( r1 == Nominal && r2 == Nominal )
           mkAppCo co1 kco co2
      (Nominal,          Nominal,          Representational)
        -> mkSubCo (mkAppCo co1 kco co2)
      (_,                Nominal,          Representational)
        -> ASSERT( r1 == Representational )
           mkAppCo co1 (mkKindCoArg co2) co2
      (Nominal,          Representational, Representational)
        -> go (mkSubCo co1)
      (_               , _,                Representational)
        -> ASSERT( r1 == Representational && r2 == Representational )
           go co1
  where
    go co1_repr
      | Just (tc1b, tys1b) <- splitTyConApp_maybe ty1b
      , nextRole ty1b == r2
      = (mkAppCo co1_repr (mkRepReflCo (typeKind ty2a))
                          (mkNomReflCoArg ty2a)) `mkTransCo`
        (mkTyConAppCo Representational tc1b
           (zipWith mkReflCoArg (tyConRolesX Representational tc1b) tys1b
            ++ [co2]))

      | Just (tc1a, tys1a) <- splitTyConApp_maybe ty1a
      , nextRole ty1a == r2
      = (mkTyConAppCo Representational tc1a
           (zipWith mkReflCoArg (tyConRolesX Representational tc1a) tys1a
            ++ [co2]))
        `mkTransCo`
        (mkAppCo co1_repr (mkRepReflCo (typeKind ty2b))
                          (mkNomReflCoArg ty2b))

      | otherwise
      = pprPanic "mkTransAppCo" (vcat [ ppr r1, ppr co1, ppr ty1a, ppr ty1b
                                      , ppr r2, ppr co2, ppr ty2a, ppr ty2b
                                      , ppr r3 ])

-- | Make a Coercion from a ForAllCoBndr and Coercion
mkForAllCo :: ForAllCoBndr -> Coercion -> Coercion
mkForAllCo cobndr@(ForAllCoBndr _ tv _ _) co
  | Refl r ty <- co
  = Refl r (mkNamedForAllTy tv Invisible ty)
  | otherwise
  = ForAllCo cobndr co

-- | Make a Coercion quantified over a type or coercion variable;
-- the variable has the same type in both types of the coercion
mkHomoForAllCo :: Role -> TyCoVar -> Coercion -> Coercion
mkHomoForAllCo _r tv (Refl r ty)
  = ASSERT( _r == r )
    Refl r (mkNamedForAllTy tv Invisible ty)
mkHomoForAllCo r tv co
  = ForAllCo (mkHomoCoBndr in_scope r tv) co
  where
    in_scope = mkInScopeSet $ tyCoVarsOfCo co

mkCoVarCo :: CoVar -> Coercion
-- cv :: s ~# t
mkCoVarCo cv
  | ty1 `eqType` ty2 = Refl (coVarRole cv) ty1
  | otherwise        = CoVarCo cv
  where
    (ty1, ty2) = coVarTypes cv

-- | Creates a new, fresh (w.r.t. the InScopeSet) Nominal covar between the
-- given types.
mkFreshCoVar :: InScopeSet -> Type -> Type -> CoVar
mkFreshCoVar in_scope ty1 ty2 = mkFreshCoVarOfType in_scope $
                                mkCoercionType Nominal ty1 ty2

-- | Like 'mkFreshCoVar', but for a Representational covar.
mkFreshReprCoVar :: InScopeSet -> Type -> Type -> CoVar
mkFreshReprCoVar in_scope ty1 ty2 = mkFreshCoVarOfType in_scope $
                                    mkCoercionType Representational ty1 ty2

-- | Makes a fresh covar of the given type. The type must be a coercion type!
mkFreshCoVarOfType :: InScopeSet -> Type -> CoVar
mkFreshCoVarOfType in_scope ty
  = ASSERT( isCoercionType ty )
    let cv_uniq = mkCoVarUnique 31 -- arbitrary number
        cv_name = mkSystemVarName cv_uniq (fsLit "c") in
    uniqAway in_scope $ mkCoVar cv_name ty

mkAxInstCo :: Role -> CoAxiom br -> BranchIndex -> [Type] -> Coercion
-- mkAxInstCo can legitimately be called over-staturated; 
-- i.e. with more type arguments than the coercion requires
mkAxInstCo role ax index tys
  | arity == n_tys = downgradeRole role ax_role $ AxiomInstCo ax_br index rtys
  | otherwise      = ASSERT( arity < n_tys )
                     downgradeRole role ax_role $
                     mkAppCos (mkAxiomInstCo ax_br index ax_args)
                              (zip leftover_kcos leftover_args)
  where
    n_tys         = length tys
    ax_br         = toBranchedAxiom ax
    branch        = coAxiomNthBranch ax_br index
    tvs           = coAxBranchTyCoVars branch
    arity         = length tvs
    arg_roles     = coAxBranchRoles branch
    rtys          = zipWith mkReflCoArg (arg_roles ++ repeat Nominal) tys
    (ax_args, leftover_args)
                  = splitAt arity rtys
    ax_role       = coAxiomRole ax
    rhs           = coAxBranchRHS branch
    ax_kind       = mkInvForAllTys tvs (typeKind rhs)
    leftover_kcos = buildKindCos ax_role ax_kind ax_args leftover_args

-- worker function; just checks to see if it should produce Refl
mkAxiomInstCo :: CoAxiom Branched -> BranchIndex -> [CoercionArg] -> Coercion
mkAxiomInstCo ax index args
  = ASSERT( coAxiomArity ax index == length args )
    let co           = AxiomInstCo ax index args
        Pair ty1 ty2 = coercionKind co in
    if ty1 `eqType` ty2
    then Refl (coAxiomRole ax) ty1
    else co

-- to be used only with unbranched axioms
mkUnbranchedAxInstCo :: Role -> CoAxiom Unbranched -> [Type] -> Coercion
mkUnbranchedAxInstCo role ax tys
  = mkAxInstCo role ax 0 tys

mkAxInstRHS :: CoAxiom br -> BranchIndex -> [Type] -> Type
-- Instantiate the axiom with specified types,
-- returning the instantiated RHS
-- A companion to mkAxInstCo: 
--    mkAxInstRhs ax index tys = snd (coercionKind (mkAxInstCo ax index tys))
mkAxInstRHS ax index tys
  = ASSERT( tvs `equalLength` tys1 ) 
    mkAppTys rhs' tys2
  where
    branch       = coAxiomNthBranch ax index
    tvs          = coAxBranchTyCoVars branch
    (tys1, tys2) = splitAtList tvs tys
    rhs'         = substTyWith tvs tys1 (coAxBranchRHS branch)

mkUnbranchedAxInstRHS :: CoAxiom Unbranched -> [Type] -> Type
mkUnbranchedAxInstRHS ax = mkAxInstRHS ax 0

-- | Return the left-hand type of the axiom, when the axiom is instantiated
-- at the types given.
mkAxInstLHS :: CoAxiom br -> BranchIndex -> [Type] -> Type
mkAxInstLHS ax index tys
  = ASSERT( tvs `equalLength` tys1 )
    mkTyConApp fam_tc (lhs_tys `chkAppend` tys2)
  where
    branch       = coAxiomNthBranch ax index
    tvs          = coAxBranchTyCoVars branch
    (tys1, tys2) = splitAtList tvs tys
    lhs_tys      = substTysWith tvs tys1 (coAxBranchLHS branch)
    fam_tc       = coAxiomTyCon ax

-- | Instantiate the left-hand side of an unbranched axiom
mkUnbranchedAxInstLHS :: CoAxiom Unbranched -> [Type] -> Type
mkUnbranchedAxInstLHS ax = mkAxInstLHS ax 0

-- | Manufacture an unsafe coercion from thin air.
--   Currently (May 14) this is used only to implement the
--   @unsafeCoerce#@ primitive.  Optimise by pushing
--   down through type constructors.
mkUnsafeCo :: FastString -> Role -> Type -> Type -> Coercion
mkUnsafeCo provenance role ty1 ty2
  | ty1 `eqType` ty2 = Refl role ty1
  | otherwise        = UnsafeCo provenance role ty1 ty2

-- TODO (RAE): Remove this if unused.
mkUnsafeCoArg :: FastString -> Role -> Type -> Type -> CoercionArg
mkUnsafeCoArg prov r (CoercionTy co1) (CoercionTy co2)
  = CoCoArg r (mkUnsafeCo prov Representational (coercionType co1)
                                                (coercionType co2))
            co1 co2
mkUnsafeCoArg provenance role ty1 ty2
  = ASSERT( not (isCoercionTy ty1) && not (isCoercionTy ty2) )
    TyCoArg $ mkUnsafeCo provenance role ty1 ty2

-- | Create a symmetric version of the given 'Coercion' that asserts
--   equality between the same types but in the other "direction", so
--   a kind of @t1 ~ t2@ becomes the kind @t2 ~ t1@.
mkSymCo :: Coercion -> Coercion

-- Do a few simple optimizations, but don't bother pushing occurrences
-- of symmetry to the leaves; the optimizer will take care of that.
mkSymCo co@(Refl {})              = co
mkSymCo    (UnsafeCo s r ty1 ty2) = UnsafeCo s r ty2 ty1
mkSymCo    (SymCo co)             = co
mkSymCo    (SubCo (SymCo co))     = SubCo co
mkSymCo co                        = SymCo co

-- | Create a new 'Coercion' by composing the two given 'Coercion's transitively.
mkTransCo :: Coercion -> Coercion -> Coercion
mkTransCo co1 (Refl {}) = co1
mkTransCo (Refl {}) co2 = co2
mkTransCo co1 co2
  | Pair s1 _s2 <- coercionKind co1
  , Pair _t1 t2 <- coercionKind co2
  , s1 `eqType` t2
    -- NB: Don't check for invalid coercions here, as there may be
    -- unzonked variables about
  = Refl (coercionRole co1) s1
mkTransCo co1 co2     = TransCo co1 co2

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
  | TyCoArg co' <- mkNthCoArg n co
  = co'
  | otherwise
  = pprPanic "mkNthCo" (ppr co)

mkNthCoArg :: Int -> Coercion -> CoercionArg
mkNthCoArg n (Refl r ty) = ASSERT( ok_tc_app ty n )
                           mkReflCoArg r' (tyConAppArgN n ty)
  where tc = tyConAppTyCon ty
        r' = nthRole r tc n
        
mkNthCoArg n co
  | Just (bndr1, _) <- splitForAllTy_maybe ty1
  , Just (bndr2, _) <- splitForAllTy_maybe ty2
  , binderType bndr1 `eqType` binderType bndr2
  , n == 0
  = mkReflCoArg (coercionRole co) (binderType bndr1)

  | Just (tc1, tys1) <- splitTyConApp_maybe ty1
  , Just (_tc2, tys2) <- splitTyConApp_maybe ty2
  , let arg1 = tys1 `getNth` n
        arg2 = tys2 `getNth` n
  , arg1 `eqType` arg2
  = ASSERT( tc1 == _tc2 )
    mkReflCoArg (nthRole (coercionRole co) tc1 n) arg1

  | otherwise
  = TyCoArg $ NthCo n co
  where
    Pair ty1 ty2 = coercionKind co

ok_tc_app :: Type -> Int -> Bool
ok_tc_app ty n
  | Just (_, tys) <- splitTyConApp_maybe ty
  = tys `lengthExceeds` n
  | isForAllTy ty  -- nth:0 pulls out a kind coercion from a hetero forall
  = n == 0
  | otherwise
  = False

mkLRCo :: LeftOrRight -> Coercion -> Coercion
mkLRCo lr (Refl eq ty) = Refl eq (pickLR lr (splitAppTy ty))
mkLRCo lr co    
  | ty1 `eqType` ty2
  = Refl Nominal ty1
  | otherwise
  = LRCo lr co
  where Pair ty1 ty2 = (pickLR lr . splitAppTy) <$> coercionKind co

-- | Instantiates a 'Coercion'.
mkInstCo :: Coercion -> CoercionArg -> Coercion
mkInstCo co arg = let result = InstCo co arg
                      Pair ty1 ty2 = coercionKind result in
                  if ty1 `eqType` ty2
                  then Refl (coercionRole co) ty1
                  else result

-- See Note [Don't optimize mkCoherenceCo]
-- TODO (RAE): This seems inefficient, if repeated. 
mkCoherenceCo :: Coercion -> Coercion -> Coercion
mkCoherenceCo co1 (Refl {}) = co1
mkCoherenceCo (CoherenceCo co1 co2) co3
  = CoherenceCo co1 (co2 `mkTransCo` co3)
mkCoherenceCo co1 co2     = let result = CoherenceCo co1 co2
                                Pair ty1 ty2 = coercionKind result in
                            if ty1 `eqType` ty2
                            then Refl (coercionRole co1) ty1
                            else result

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
mkKindCo (Refl _ ty) = Refl Representational (typeKind ty)
mkKindCo co
  | Pair ty1 ty2 <- coercionKind co  -- TODO (RAE): This looks inefficient.
  , typeKind ty1 `eqType` typeKind ty2
  = Refl Representational (typeKind ty1)
  | otherwise
  = KindCo co

-- | Extract a kind equality from a CoercionArg. Always returns representational
mkKindCoArg :: CoercionArg -> Coercion
mkKindCoArg (TyCoArg co)        = mkKindCo co
mkKindCoArg (CoCoArg _ kco _ _) = kco

-- | Make a KindAppCo, retrieving a coercion between the kinds of the argument
-- of an AppTy
mkKindAppCo :: Coercion -> Coercion
mkKindAppCo (Refl r ty)
  | Just (_, s) <- splitAppTy_maybe ty
  = Refl r (typeKind s)
mkKindAppCo co
  | let (Pair ty1 ty2, r) = coercionKindRole co
  , Just (_, s1) <- splitAppTy_maybe ty1
  , Just (_, s2) <- splitAppTy_maybe ty2
  , let k = typeKind s1
  , k `eqType` typeKind s2
  = Refl r k

  | otherwise
  = KindAppCo co

-- input coercion is Nominal; see also Note [Role twiddling functions]
mkSubCo :: Coercion -> Coercion
mkSubCo (Refl Nominal ty) = Refl Representational ty
mkSubCo (TyConAppCo Nominal tc cos)
  = TyConAppCo Representational tc (applyRoles tc cos)
mkSubCo (UnsafeCo s Nominal ty1 ty2) = UnsafeCo s Representational ty1 ty2
mkSubCo co = ASSERT2( coercionRole co == Nominal, ppr co <+> ppr (coercionRole co) )
             SubCo co

-- | Changes a role, but only a downgrade. See Note [Role twiddling functions]
downgradeRole_maybe :: Role   -- ^ desired role
                    -> Role   -- ^ current role
                    -> Coercion -> Maybe Coercion
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

-- | Like 'downgradeRole_maybe', but for 'CoercionArg's
setRoleArg_maybe :: Role -> Role -> CoercionArg -> Maybe CoercionArg
setRoleArg_maybe r1 r2 (TyCoArg co)
  = fmap TyCoArg (downgradeRole_maybe r1 r2 co)
setRoleArg_maybe r  _  (CoCoArg _ h co1 co2) = Just $ CoCoArg r h co1 co2

-- | Like 'downgradeRole', but for 'CoercionArg's
downgradeRoleArg :: Role -> Role -> CoercionArg -> CoercionArg
downgradeRoleArg r1 r2 arg
  | Just arg' <- setRoleArg_maybe r1 r2 arg
  = arg'
  | otherwise
  = pprPanic "downgradeRoleArg" (ppr arg)

-- | If the EqRel is ReprEq, makes a SubCo; otherwise, does nothing.
-- Note that the input coercion should always be nominal.
maybeSubCo :: EqRel -> Coercion -> Coercion
maybeSubCo NomEq  = id
maybeSubCo ReprEq = mkSubCo


mkAxiomRuleCo :: CoAxiomRule -> [Type] -> [Coercion] -> Coercion
mkAxiomRuleCo = AxiomRuleCo

{-
%************************************************************************
%*                                                                      *
   Roles
%*                                                                      *
%************************************************************************
-}

-- | Converts a coercion to be nominal, if possible.
-- See Note [Role twiddling functions]
setNominalRole_maybe :: Coercion -> Maybe Coercion
setNominalRole_maybe co
  | Nominal <- coercionRole co = Just co
setNominalRole_maybe (SubCo co)  = Just co
setNominalRole_maybe (Refl _ ty) = Just $ Refl Nominal ty
setNominalRole_maybe (TyConAppCo Representational tc cos)
  = do { cos' <- mapM setNominalRoleArg_maybe cos
       ; return $ TyConAppCo Nominal tc cos' }
setNominalRole_maybe (UnsafeCo s _ ty1 ty2) = Just $ UnsafeCo s Nominal ty1 ty2
setNominalRole_maybe (SymCo co)
  = SymCo <$> setNominalRole_maybe co
setNominalRole_maybe (TransCo co1 co2)
  = TransCo <$> setNominalRole_maybe co1 <*> setNominalRole_maybe co2
setNominalRole_maybe (AppCo co1 h co2)
  = AppCo <$> setNominalRole_maybe co1 <*> setNominalRole_maybe h <*> pure co2
setNominalRole_maybe (ForAllCo cobndr co)
  = ForAllCo <$> setNominalRoleCoBndr_maybe cobndr <*> setNominalRole_maybe co
setNominalRole_maybe (NthCo n co)
  = NthCo n <$> setNominalRole_maybe co
setNominalRole_maybe (InstCo co arg)
  = InstCo <$> setNominalRole_maybe co <*> pure arg
setNominalRole_maybe (CoherenceCo co1 co2)
  = CoherenceCo <$> setNominalRole_maybe co1 <*> pure co2
setNominalRole_maybe _ = Nothing

-- | Makes a 'CoercionArg' become nominal, if possible
setNominalRoleArg_maybe :: CoercionArg -> Maybe CoercionArg
setNominalRoleArg_maybe (TyCoArg co)
  = fmap TyCoArg (setNominalRole_maybe co)
setNominalRoleArg_maybe (CoCoArg _ h c1 c2) = Just $ CoCoArg Nominal h c1 c2

-- | Makes a 'ForAllCoBndr' become nominal, if possible
setNominalRoleCoBndr_maybe :: ForAllCoBndr -> Maybe ForAllCoBndr
setNominalRoleCoBndr_maybe (ForAllCoBndr h tv1 tv2 m_cv) =
  ForAllCoBndr <$> setNominalRole_maybe h <*> pure tv1 <*> pure tv2 <*> pure m_cv

-- | Make a phantom coercion between two types. The coercion passed
-- in must be a representational coercion between the kinds of the
-- types.
mkPhantomCo :: Coercion -> Type -> Type -> Coercion
mkPhantomCo h t1 t2
  | t1 `eqType` t2
  = Refl Phantom t1
  | otherwise
  = PhantomCo h t1 t2

-- | Make a phantom coercion between two types of the same kind.
mkHomoPhantomCo :: Type -> Type -> Coercion
mkHomoPhantomCo t1 t2
  = ASSERT( k1 `eqType` typeKind t2 )
    mkPhantomCo (mkRepReflCo k1) t1 t2
  where
    k1 = typeKind t1

-- takes any coercion and turns it into a Phantom coercion
toPhantomCo :: Coercion -> Coercion
toPhantomCo co
  | Just (ty, _) <- isReflCo_maybe co = Refl Phantom ty
  | Pair ty1 ty2 <- coercionKind co   = PhantomCo (mkKindCo co) ty1 ty2
  -- don't optimise here... wait for OptCoercion

toPhantomCoArg :: CoercionArg -> CoercionArg
toPhantomCoArg (TyCoArg co)          = TyCoArg (toPhantomCo co)
toPhantomCoArg (CoCoArg _ h co1 co2) = CoCoArg Phantom h co1 co2

-- All input coercions are assumed to be Nominal,
-- or, if Role is Phantom, the Coercion can be Phantom, too.
applyRole :: Role -> CoercionArg -> CoercionArg
applyRole r (CoCoArg _ h c1 c2) = CoCoArg r h c1 c2
applyRole Nominal          a  = a
applyRole Representational (TyCoArg c)  = TyCoArg $ mkSubCo c
applyRole Phantom          (TyCoArg c)  = TyCoArg $ toPhantomCo c

-- Convert args to a TyConAppCo Nominal to the same TyConAppCo Representational
applyRoles :: TyCon -> [CoercionArg] -> [CoercionArg]
applyRoles tc cos
  = zipWith applyRole (tyConRolesX Representational tc) cos

-- the Role parameter is the Role of the TyConAppCo
-- defined here because this is intimiately concerned with the implementation
-- of TyConAppCo
tyConRolesX :: Role -> TyCon -> [Role]
tyConRolesX Representational tc = tyConRoles tc ++ repeat Nominal
tyConRolesX role             _  = repeat role

nthRole :: Role -> TyCon -> Int -> Role
nthRole Nominal _ _ = Nominal
nthRole Phantom _ _ = Phantom
nthRole Representational tc n
  = (tyConRolesX Representational tc) `getNth` n

ltRole :: Role -> Role -> Bool
-- Is one role "less" than another?
--     Nominal < Representational < Phantom
ltRole Phantom          _       = False
ltRole Representational Phantom = True
ltRole Representational _       = False
ltRole Nominal          Nominal = False
ltRole Nominal          _       = True

-- | Produces a list of coercions, each at the (one) desired role, that relate
-- the kinds of coercion arguments about to be applied. For example,
-- @buildKindCos N (tyConKind tc) args1 args2@ will give a list of N coercions
-- @kcos@, each of which relate the two types related by @args2@ (respectively).
-- This is appropriate right before calling @mkAppCos (tc args1) args2@.
-- The second and third
-- parameters (the initial type and some arguments) are helpful in building
-- the coercions.
buildKindCos :: Role
             -> Type           -- ^ type of tycon at the head of the coercion
             -> [CoercionArg]  -- ^ args already applied
             -> [CoercionArg]  -- ^ new args
             -> [Coercion]     -- ^ kind coercions
buildKindCos r ty args1 args2 = dropList args1 $ fst $
                                buildKindCosX r (mkReflCo r ty) (args1 ++ args2)

-- | Like 'buildKindCos', but suitable for use in the "middle" of a coercion
buildKindCosX :: Role          -- ^ r
              -> Coercion      -- ^ an "r"-coercion relating the kinds of arguments to come
              -> [CoercionArg] -- ^ those arguments
              -> ([Coercion], Maybe Coercion)
                     -- ^ "r"-coercions relating the kinds of the arguments,
                     -- and a kind coercion useful for a future call to
                     -- this function. That kind coercion is only produced
                     -- when "r" = N. Otherwise, this function doesn't quite
                     -- have enough info to pull it off, but the caller should.
buildKindCosX Nominal co_so_far args
  = go [] (pFst $ coercionKind co_so_far) co_so_far args
  where
    go :: [Coercion]    -- accumulator of results, reversed
       -> Type          -- :: L kinds to expect
       -> Coercion      -- :: L kinds to expect ~ R kinds to expect
       -> [CoercionArg] -- actual args of those kinds
       -> ([Coercion], Maybe Coercion)
                        -- results (in normal order), with a coercion relating
                        -- the kinds of arguments to come
    go acc _         co_so_far []     = (reverse acc, Just co_so_far)
    go acc left_type co_so_far (a:as)
      | isNamedForAllTy left_type
      = ASSERT( coercionArgRole a == Nominal )
        go (next_co : acc) next_left_type (mkInstCo co_so_far a) as

      | otherwise
      = go (next_co : acc) next_left_type (mkNthCo 1 co_so_far) as
      where
        next_left_type = piResultTy left_type (pFst $ coercionArgKind a)
        next_co        = mkNthCo 0 co_so_far
        
buildKindCosX Representational _ args = (map mkKindCoArg args, Nothing)
buildKindCosX Phantom          _ args = (map mk_phantom args,  Nothing)
  where
    mk_phantom arg = mkPhantomCo kco k1 k2
      where
        Pair t1 t2 = coercionArgKind arg
        k1         = typeKind t1
        k2         = typeKind t2
        kco        = mkRepReflCo liftedTypeKind

{-
%************************************************************************
%*                                                                      *
   ForAllCoBndr
%*                                                                      *
%************************************************************************
-}

-- | Makes homogeneous ForAllCoBndr
mkHomoCoBndr :: InScopeSet -> Role -> TyCoVar -> ForAllCoBndr
mkHomoCoBndr in_scope r v = ForAllCoBndr eta v v m_cv
  where
    eta = mkReflCo r (varType v)
    
    m_cv | isTyVar v = Just $ mkFreshCoVar in_scope ty ty
         | otherwise = Nothing

    ty = mkOnlyTyVarTy v

mkForAllCoBndr :: Coercion -> TyVar -> TyVar -> Maybe CoVar -> ForAllCoBndr
mkForAllCoBndr co tv1 tv2 m_cv
  | debugIsOn
  = let Pair k1 k2 = coercionKind co in
    ASSERT2( k1 `eqType` tyVarKind tv1
           , ppr tv1 $$ ppr k1 $$ ppr (tyVarKind tv1) )
    ASSERT2( k2 `eqType` tyVarKind tv2
           , ppr tv2 $$ ppr k2 $$ ppr (tyVarKind tv2) )
    let result = ForAllCoBndr co tv1 tv2 m_cv in
    case m_cv of
      Nothing -> ASSERT2( isCoVar tv1 && isCoVar tv2, ppr tv1 $$ ppr tv2 )
                 result
      Just cv -> ASSERT2( isTyVar tv1 && isTyVar tv2, ppr tv1 $$ ppr tv2 )
                 ASSERT2( r == Nominal, cv_doc )
                 ASSERT2( cvk1 `eqType` mkOnlyTyVarTy tv1, cv_doc $$ ppr tv1 )
                 ASSERT2( cvk2 `eqType` mkOnlyTyVarTy tv2, cv_doc $$ ppr tv2 )
                 result
        where
          (_, _, cvk1, cvk2, r) = coVarKindsTypesRole cv
          cv_doc = ppr cv $$ ppr (varType cv)

  | otherwise
  = ForAllCoBndr co tv1 tv2 m_cv

-- | Gets a 'CoercionArg' that proves that the two variables bound
-- in this ForAllCoBndr are nominally equal
coBndrWitness :: ForAllCoBndr -> CoercionArg
coBndrWitness (ForAllCoBndr _   _   _   (Just cv)) = TyCoArg (mkCoVarCo cv)
coBndrWitness (ForAllCoBndr eta cv1 cv2 Nothing)
  = CoCoArg Nominal (downgradeRole Representational (coercionRole eta) eta)
            (mkCoVarCo cv1) (mkCoVarCo cv2)

-- | Extracts a coercion that witnesses the equality between a 'ForAllCoBndr''s
-- type variables' kinds.
coBndrKindCo :: ForAllCoBndr -> Coercion
coBndrKindCo (ForAllCoBndr h _ _ _) = h

-- | changes the "eta" coercion in a hetero CoBndr
setCoBndrKindCo :: ForAllCoBndr -> Coercion -> ForAllCoBndr
setCoBndrKindCo (ForAllCoBndr _ tv1 tv2 cv) h = ForAllCoBndr h tv1 tv2 cv


-------------------------------

-- | like mkKindCo, but aggressively & recursively optimizes to avoid using
-- a KindCo constructor. The output role is representational.
promoteCoercion :: Coercion -> Coercion

-- First cases handles anything that should yield refl. 
promoteCoercion co = case co of
  
    _ | ki1 `eqType` ki2
      -> mkRepReflCo (typeKind ty1)
     -- no later branch should return refl
     --    The ASSERT( False )s throughout
     -- are these cases explicitly, but they should never fire.

    Refl _ ty -> ASSERT( False )
                 mkRepReflCo (typeKind ty)

    TyConAppCo _ tc args
      | Just co' <- instCoercions (mkRepReflCo (tyConKind tc)) args
      -> co'
      | otherwise
      -> mkKindCo co
    
    AppCo co1 _ arg
      | Just co' <- instCoercion (promoteCoercion co1) arg
      -> co'
      | otherwise
      -> mkKindCo co
         
    ForAllCo _ g
      -> promoteCoercion g
         
    CoVarCo {}
      -> mkKindCo co
         
    AxiomInstCo {}
      -> mkKindCo co
         
    PhantomCo co _ _
      -> co

    UnsafeCo s _ _ _
      -> mkUnsafeCo s Representational ki1 ki2

    SymCo g
      -> mkSymCo (promoteCoercion g)

    TransCo co1 co2
      -> mkTransCo (promoteCoercion co1) (promoteCoercion co2)
         
    NthCo n co1
      | Just (_, args) <- splitTyConAppCo_maybe co1
      , n < length args
      -> case args !! n of
           TyCoArg co1     -> promoteCoercion co1
           CoCoArg _ _ _ _ -> pprPanic "promoteCoercion" (ppr co)

      | Just _ <- splitForAllCo_maybe co
      , n == 0
      -> ASSERT( False ) mkRepReflCo liftedTypeKind

      | otherwise
      -> mkKindCo co

    LRCo lr co1
      | Just (lco, h, _) <- splitAppCo_maybe co1
      -> case lr of
           CLeft  -> promoteCoercion lco
           CRight -> mkSubCo h 

      | otherwise
      -> mkKindCo co

    InstCo g _
      -> promoteCoercion g

    CoherenceCo g h
      -> mkSymCo h `mkTransCo` promoteCoercion g

    KindCo _
      -> ASSERT( False )
         mkRepReflCo liftedTypeKind

    KindAppCo _
      -> ASSERT( False )
         mkRepReflCo liftedTypeKind

    SubCo g
      -> promoteCoercion g

    AxiomRuleCo {}
      -> mkKindCo co

  where
    Pair ty1 ty2 = coercionKind co
    ki1 = typeKind ty1
    ki2 = typeKind ty2

-- | say @g = promoteCoercion h@. Then, @instCoercion g w@ yields @Just g'@,
-- where @g' = promoteCoercion (h w)@.
-- fails if this is not possible, if @g@ coerces between a forall and an ->
-- or if second parameter has a representational role and can't be used
-- with an InstCo. The result role matches is representational.
instCoercion :: Coercion  -- ^ must be representational
             -> CoercionArg
             -> Maybe Coercion
instCoercion g w
  | isNamedForAllTy ty1 && isNamedForAllTy ty2
  , Just w' <- setNominalRoleArg_maybe w
  = Just $ mkInstCo g w'
  | isFunTy ty1 && isFunTy ty2
  = Just $ mkNthCo 1 g -- extract result type, which is the 2nd argument to (->)
  | otherwise -- one forall, one funty...
  = Nothing
  where
    -- TODO (RAE): This is inefficient.
    Pair ty1 ty2 = coercionKind g

instCoercions :: Coercion -> [CoercionArg] -> Maybe Coercion
instCoercions = foldM instCoercion

-- | Creates a new coercion with both of its types casted by different casts
-- castCoercionKind g h1 h2, where g :: t1 ~ t2, has type (t1 |> h1) ~ (t2 |> h2)
-- The second and third coercions must be representational.
castCoercionKind :: Coercion -> Coercion -> Coercion -> Coercion
castCoercionKind g h1 h2
  = g `mkCoherenceLeftCo` h1 `mkCoherenceRightCo` h2

-- See note [Newtype coercions] in TyCon

-- | Create a coercion constructor (axiom) suitable for the given
--   newtype 'TyCon'. The 'Name' should be that of a new coercion
--   'CoAxiom', the 'TyVar's the arguments expected by the @newtype@ and
--   the type the appropriate right hand side of the @newtype@, with
--   the free variables a subset of those 'TyVar's.
mkNewTypeCo :: Name -> TyCon -> [TyVar] -> [Role] -> Type -> CoAxiom Unbranched
mkNewTypeCo name tycon tvs roles rhs_ty
  = CoAxiom { co_ax_unique   = nameUnique name
            , co_ax_name     = name
            , co_ax_implicit = True  -- See Note [Implicit axioms] in TyCon
            , co_ax_role     = Representational
            , co_ax_tc       = tycon
            , co_ax_branches = FirstBranch branch }
  where branch = CoAxBranch { cab_loc = getSrcSpan name
                            , cab_tvs = tvs
                            , cab_lhs = mkTyCoVarTys tvs
                            , cab_roles   = roles
                            , cab_rhs     = rhs_ty
                            , cab_incomps = [] }

mkPiCos :: Role -> [Var] -> Coercion -> Coercion
mkPiCos r vs co = foldr (mkPiCo r) co vs

mkPiCo  :: Role -> Var -> Coercion -> Coercion
mkPiCo r v co | isTyVar v || isCoVar v = mkHomoForAllCo r v co
              | otherwise              = mkFunCo r (mkReflCo r (varType v)) co

-- The second coercion is sometimes lifted (~) and sometimes unlifted (~#).
-- So, we have to make sure to supply the right parameter to decomposeCo.
-- mkCoCast (c :: s1 ~# t1) (g :: (s1 ~# s2) ~# (t1 ~# t2)) :: s2 ~# t2
-- The first coercion *must* be Nominal.
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
    TyCoArg g1 = co_list `getNth` (n_args - 2)
    TyCoArg g2 = co_list `getNth` (n_args - 1)

{-
%************************************************************************
%*                                                                      *
   CoercionArgs
%*                                                                      *
%************************************************************************
-}

mkTyCoArg :: Coercion -> CoercionArg
mkTyCoArg = TyCoArg

mkCoCoArg :: Role -> Coercion -> Coercion -> Coercion -> CoercionArg
mkCoCoArg = CoCoArg

isTyCoArg :: CoercionArg -> Bool
isTyCoArg (TyCoArg _) = True
isTyCoArg _           = False

stripTyCoArg :: CoercionArg -> Coercion
stripTyCoArg (TyCoArg co) = co
stripTyCoArg arg          = pprPanic "stripTyCoArg" (ppr arg)

stripCoCoArg :: CoercionArg -> Pair Coercion
stripCoCoArg (CoCoArg _ _ co1 co2) = Pair co1 co2
stripCoCoArg arg                   = pprPanic "stripCoCoArg" (ppr arg)

splitCoCoArg_maybe :: CoercionArg -> Maybe (Coercion, Coercion)
splitCoCoArg_maybe (TyCoArg _)         = Nothing
splitCoCoArg_maybe (CoCoArg _ _ c1 c2) = Just (c1, c2)

-- | Makes a suitable CoercionArg representing the passed-in variable
-- during a lifting-like substitution. Output is Nominal.
mkCoArgForVar :: TyCoVar -> CoercionArg
mkCoArgForVar v
  | isTyVar v = TyCoArg $ mkNomReflCo $ mkOnlyTyVarTy v
  | otherwise = CoCoArg Nominal (mkRepReflCo (varType v))
                                (mkCoVarCo v) (mkCoVarCo v)

mkSymCoArg :: CoercionArg -> CoercionArg
mkSymCoArg (TyCoArg co)          = TyCoArg (mkSymCo co)
mkSymCoArg (CoCoArg r h co1 co2) = CoCoArg r (mkSymCo h) co2 co1

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
  = Just (applyTysX tvs ty tys, mkUnbranchedAxInstCo Representational co_tc tys)
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
  = NS_Done   -- ^ nothing more to do
  | NS_Abort  -- ^ utter failure. The outer function should fail too.
  | NS_Step RecTcChecker Type Coercion  -- ^ we stepped, yielding new bits;
                                        -- ^ co :: old type ~ new type

modifyStepResultCo :: (Coercion -> Coercion)
                   -> NormaliseStepResult -> NormaliseStepResult
modifyStepResultCo f (NS_Step rec_nts ty co) = NS_Step rec_nts ty (f co)
modifyStepResultCo _ result                  = result

-- | Try one stepper and then try the next, if the first doesn't make
-- progress.
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

eqCoercionArg :: CoercionArg -> CoercionArg -> Bool
eqCoercionArg (TyCoArg co1) (TyCoArg co2) = eqCoercion co1 co2
eqCoercionArg (CoCoArg r1 h1 _ _) (CoCoArg r2 h2 _ _)
  = r1 == r2 && h1 `eqCoercion` h2
eqCoercionArg _ _ = False

{-
%************************************************************************
%*                                                                      *
                   "Lifting" substitution
           [(TyCoVar,CoercionArg)] -> Type -> Coercion
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

data LiftingContext = LC InScopeSet LiftCoEnv

instance Outputable LiftingContext where
  ppr (LC _ env) = hang (text "LiftingContext:") 2 (ppr env)

type LiftCoEnv = VarEnv CoercionArg
     -- Maps *type variables* to *coercions* (TyCoArg) and coercion variables
     -- to pairs of coercions (CoCoArg). That's the whole point of this function!

-- like liftCoSubstWith, but allows for existentially-bound types as well
liftCoSubstWithEx :: Role          -- desired role for output coercion
                  -> [TyCoVar]     -- universally quantified tycovars
                  -> [CoercionArg] -- coercions to substitute for those
                  -> [TyCoVar]     -- existentially quantified tycovars
                  -> [Type]        -- types and coercions to be bound to ex vars
                  -> (Type -> Coercion, [Type]) -- (lifting function, converted ex args)
liftCoSubstWithEx role univs omegas exs rhos
  = let theta = mkLiftingContext (zipEqual "liftCoSubstWithExU" univs omegas)
        psi   = extendLiftingContextEx theta (zipEqual "liftCoSubstWithExX" exs rhos)
    in (ty_co_subst psi role, substTys (lcSubstRight psi) (mkTyCoVarTys exs))

liftCoSubstWith :: Role -> [TyCoVar] -> [CoercionArg] -> Type -> Coercion
liftCoSubstWith r tvs cos ty
  = liftCoSubst r (mkLiftingContext $ zipEqual "liftCoSubstWith" tvs cos) ty

liftCoSubst :: Role -> LiftingContext -> Type -> Coercion
liftCoSubst r lc@(LC _ env) ty
  | isEmptyVarEnv env = Refl r ty
  | otherwise         = ty_co_subst lc r ty

emptyLiftingContext :: InScopeSet -> LiftingContext
emptyLiftingContext in_scope = LC in_scope emptyVarEnv

mkLiftingContext :: [(TyCoVar,CoercionArg)] -> LiftingContext
mkLiftingContext prs = LC (mkInScopeSet (tyCoVarsOfCoArgs (map snd prs)))
                          (mkVarEnv prs)

-- | Add a variable to the in-scope set of a lifting context
extendLiftingContextIS :: LiftingContext -> Var -> LiftingContext
extendLiftingContextIS (LC in_scope env) var
  = LC (extendInScopeSet in_scope var) env

-- | Extend a lifting context with a new /type/ mapping.
extendLiftingContext :: LiftingContext  -- ^ original LC
                     -> TyVar           -- ^ new variable to map...
                     -> Coercion        -- ^ ...to this lifted version
                     -> LiftingContext
extendLiftingContext (LC in_scope env) tv co
  = ASSERT( isTyVar tv )
    LC in_scope (extendVarEnv env tv (TyCoArg co))

-- | Extend a lifting context with existential-variable bindings.
-- This follows the lifting context extension definition in the
-- "FC with Explicit Kind Equality" paper.
extendLiftingContextEx :: LiftingContext    -- ^ original lifting context
                       -> [(TyCoVar,Type)]  -- ^ ex. var / value pairs
                       -> LiftingContext
extendLiftingContextEx lc [] = lc
extendLiftingContextEx lc@(LC in_scope env) ((v,ty):rest)
-- This function adds bindings for *Nominal* coercions. Why? Because it
-- works with existentially bound variables, which are considered to have
-- nominal roles.
  | isTyVar v
  = let lc' = LC (in_scope `extendInScopeSetSet` tyCoVarsOfType ty)
                 (extendVarEnv env v (TyCoArg $ mkSymCo $ mkCoherenceCo
                                         (mkNomReflCo ty)
                                         (ty_co_subst lc Representational (tyVarKind v))))
    in extendLiftingContextEx lc' rest
       
  | CoercionTy co <- ty
  = -- co :: s1 ~r s2
    -- lift_r(s1) :: s1 ~r s1'
    -- lift_r(s2) :: s2 ~r s2'
    -- kco :: (s1 ~r s2) ~R (s1' ~r s2')
    let (_, _, s1, s2, r) = coVarKindsTypesRole v
        lift_s1 = ty_co_subst lc r s1
        lift_s2 = ty_co_subst lc r s2
        kco = mkTyConAppCo Representational (equalityTyCon r) $
                map TyCoArg [ mkKindCo lift_s1
                            , mkKindCo lift_s2
                            , lift_s1
                            , lift_s2 ]
        lc' = LC (in_scope `extendInScopeSetSet` tyCoVarsOfCo co)
                 (extendVarEnv env v (CoCoArg Nominal kco co $
                                         (mkSymCo lift_s1) `mkTransCo`
                                         co `mkTransCo`
                                         lift_s2))
    in extendLiftingContextEx lc' rest
  | otherwise
  = pprPanic "extendLiftingContextEx" (ppr v <+> ptext (sLit "|->") <+> ppr ty)

-- | The \"lifting\" operation which substitutes coercions for type
--   variables in a type to produce a coercion.
--
--   For the inverse operation, see 'liftCoMatch' 
ty_co_subst :: LiftingContext -> Role -> Type -> Coercion
ty_co_subst lc@(LC _ env) role ty
  = go role ty
  where
    go :: Role -> Type -> Coercion
    go Phantom ty        = lift_phantom ty
    go r ty | tyCoVarsOfType ty `isNotInDomainOf` env = mkReflCo r ty
    go r (TyVarTy tv)      = case liftCoSubstTyVar lc r tv of
                               Just co -> co
                               Nothing -> pprPanic "ty_co_subst" (vcat [ppr tv, ppr env])
                               -- TODO (RAE): make the typeKind more efficient
    go r (AppTy ty1 ty2)   = mkAppCo (go r ty1) (go r (typeKind ty2))
                                                (go_arg Nominal ty2)
    go r (TyConApp tc tys) = mkTyConAppCo r tc (zipWith go_arg (tyConRolesX r tc) tys)
    go r (ForAllTy (Anon ty1) ty2)
                           = mkFunCo r (go r ty1) (go r ty2)
    go r (ForAllTy (Named v _) ty)
                           = let (lc', cobndr) = liftCoSubstVarBndr r lc v in
                             mkForAllCo cobndr $! ty_co_subst lc' r ty
    go r ty@(LitTy {})     = ASSERT( r == Nominal )
                             mkReflCo r ty
    go r (CastTy ty co)    = castCoercionKind (go r ty) (substLeftCo lc co)
                                                        (substRightCo lc co)
    go _ (CoercionTy co)   = pprPanic "ty_co_subst" (ppr co)

    go_arg :: Role -> Type -> CoercionArg
    go_arg r (CoercionTy co) = CoCoArg r kco (substLeftCo lc co)
                                             (substRightCo lc co)
      where kco = go Representational (coercionType co)
    go_arg r ty              = TyCoArg (go r ty)

    isNotInDomainOf :: VarSet -> VarEnv a -> Bool
    isNotInDomainOf set env
      = noneSet (\v -> elemVarEnv v env) set

    noneSet :: (Var -> Bool) -> VarSet -> Bool
    noneSet f = foldVarSet (\v rest -> rest && (not $ f v)) True

    lift_phantom ty = mkPhantomCo (go Representational (typeKind ty))
                                  (substTy (lcSubstLeft  lc) ty)
                                  (substTy (lcSubstRight lc) ty)

{-
Note [liftCoSubstTyVar]
~~~~~~~~~~~~~~~~~~~~~~~
This function can fail if a coercion in the environment is of too low a role.

liftCoSubstTyVar is called from two places: in liftCoSubst (naturally), and
also in matchAxiom in OptCoercion. From liftCoSubst, the so-called lifting
lemma guarantees that the roles work out. If we fail in this
case, we really should panic -- something is deeply wrong. But, in matchAxiom,
failing is fine. matchAxiom is trying to find a set of coercions
that match, but it may fail, and this is healthy behavior.
-}

liftCoSubstTyVar :: LiftingContext -> Role -> TyVar -> Maybe Coercion
liftCoSubstTyVar (LC _ cenv) r tv
  | Just (TyCoArg co) <- lookupVarEnv cenv tv
  = downgradeRole_maybe r (coercionRole co) co -- see Note [liftCoSubstTyVar]
      -- could theoretically take (coercionRole co) as a parameter,
      -- but it would be painful

  | otherwise
  = Just $ mkReflCo r (mkOnlyTyVarTy tv)

liftCoSubstTyCoVar :: LiftingContext -> Role -> TyCoVar -> Maybe CoercionArg
liftCoSubstTyCoVar (LC _ env) r v
  | Just co_arg <- lookupVarEnv env v
  = setRoleArg_maybe r (coercionArgRole co_arg) co_arg

  | otherwise
  = Just $ mkReflCoArg r (mkTyCoVarTy v)

liftCoSubstVarBndr :: Role -> LiftingContext -> TyCoVar
                     -> (LiftingContext, ForAllCoBndr)
liftCoSubstVarBndr = liftCoSubstVarBndrCallback ty_co_subst False

liftCoSubstVarBndrCallback :: (LiftingContext -> Role -> Type -> Coercion)
                           -> Bool -- ^ True <=> homogenize hetero substs
                                   -- see Note [Normalising types] in FamInstEnv
                           -> Role -- ^ output rule; not Phantom
                           -> LiftingContext -> TyCoVar
                           -> (LiftingContext, ForAllCoBndr)
liftCoSubstVarBndrCallback fun homo r lc@(LC in_scope cenv) old_var
  = (LC (in_scope `extendInScopeSetList` coBndrVars cobndr) new_cenv, cobndr)
  where
    old_kind   = tyVarKind old_var
    eta        = fun lc r old_kind
    Pair k1 k2 = coercionKind eta
    new_var    = uniqAway in_scope (setVarType old_var k1)

    (new_cenv, cobndr)
      | new_var == old_var
      , isEmptyVarSet (tyCoVarsOfType old_kind)
      , k1 `eqType` k2
      = (delVarEnv cenv old_var, mkHomoCoBndr in_scope r old_var)

      | isTyVar old_var
      = let a1 = new_var
            in_scope1 = in_scope `extendInScopeSet` a1
            a2 = uniqAway in_scope1 $ setVarType new_var k2
            in_scope2 = in_scope1 `extendInScopeSet` a2
            c  = mkFreshCoVar in_scope2 (mkOnlyTyVarTy a1) (mkOnlyTyVarTy a2) 
            lifted = if homo
                     then mkCoVarCo c `mkCoherenceRightCo` mkSymCo eta
                     else mkCoVarCo c
        in
        ( extendVarEnv cenv old_var (TyCoArg lifted)
        , mkForAllCoBndr eta a1 a2 (Just c) )

      | otherwise
      = let cv1 = new_var
            in_scope1 = in_scope `extendInScopeSet` cv1
            cv2 = uniqAway in_scope1 $ setVarType new_var k2
              -- cv_eta is like eta, but its role matches cv1/2
            cv_role = coVarRole cv1
            cv_eta = downgradeRole_maybe cv_role r eta `orElse`
                     fun lc cv_role old_kind

            (kco, lifted_r)
              = if homo
                then ( mkRepReflCo (varType cv1)
                     , mkNthCo 2 cv_eta
                       `mkTransCo` (mkCoVarCo cv2)
                       `mkTransCo` mkNthCo 3 (mkSymCo cv_eta) )
                else ( downgradeRole_maybe Representational r eta `orElse`
                       fun lc Representational old_kind
                     , mkCoVarCo cv2 )
        in
        ( extendVarEnv cenv old_var (CoCoArg Nominal kco (mkCoVarCo cv1) lifted_r)
        , mkForAllCoBndr cv_eta cv1 cv2 Nothing )

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
swapLiftCoEnv = mapVarEnv mkSymCoArg

lcSubstLeft :: LiftingContext -> TCvSubst
lcSubstLeft (LC in_scope lc_env) = liftEnvSubstLeft in_scope lc_env

lcSubstRight :: LiftingContext -> TCvSubst
lcSubstRight (LC in_scope lc_env) = liftEnvSubstRight in_scope lc_env

liftEnvSubstLeft :: InScopeSet -> LiftCoEnv -> TCvSubst
liftEnvSubstLeft = liftEnvSubst pFst

liftEnvSubstRight :: InScopeSet -> LiftCoEnv -> TCvSubst
liftEnvSubstRight = liftEnvSubst pSnd

liftEnvSubst :: (forall a. Pair a -> a) -> InScopeSet -> LiftCoEnv -> TCvSubst
liftEnvSubst fn in_scope lc_env
  = mkTCvSubst in_scope (tenv, cenv)
  where
    (tenv0, cenv0) = partitionVarEnv isTyCoArg lc_env
    tenv           = mapVarEnv (fn . coercionKind . stripTyCoArg) tenv0
    cenv           = mapVarEnv (fn . stripCoCoArg) cenv0

{-
%************************************************************************
%*                                                                      *
            Sequencing on coercions
%*                                                                      *
%************************************************************************
-}

seqCo :: Coercion -> ()
seqCo (Refl r ty)           = r `seq` seqType ty
seqCo (TyConAppCo r tc cos) = r `seq` tc `seq` seqCoArgs cos
seqCo (AppCo co1 h co2)     = seqCo co1 `seq` seqCo h `seq` seqCoArg co2
seqCo (ForAllCo cobndr co)  = seqCoBndr cobndr `seq` seqCo co
seqCo (CoVarCo cv)          = cv `seq` ()
seqCo (AxiomInstCo con ind cos) = con `seq` ind `seq` seqCoArgs cos
seqCo (PhantomCo h t1 t2)   = seqCo h `seq` seqType t1 `seq` seqType t2
seqCo (UnsafeCo s r ty1 ty2)= s `seq` r `seq` seqType ty1 `seq` seqType ty2
seqCo (SymCo co)            = seqCo co
seqCo (TransCo co1 co2)     = seqCo co1 `seq` seqCo co2
seqCo (NthCo _ co)          = seqCo co
seqCo (LRCo _ co)           = seqCo co
seqCo (InstCo co arg)       = seqCo co `seq` seqCoArg arg
seqCo (CoherenceCo co1 co2) = seqCo co1 `seq` seqCo co2
seqCo (KindCo co)           = seqCo co
seqCo (KindAppCo co)        = seqCo co
seqCo (SubCo co)            = seqCo co
seqCo (AxiomRuleCo _ ts cs) = seqTypes ts `seq` seqCos cs

seqCos :: [Coercion] -> ()
seqCos []       = ()
seqCos (co:cos) = seqCo co `seq` seqCos cos

seqCoArg :: CoercionArg -> ()
seqCoArg (TyCoArg co)          = seqCo co
seqCoArg (CoCoArg r h co1 co2) = r `seq` seqCo h `seq` seqCo co1 `seq` seqCo co2

seqCoArgs :: [CoercionArg] -> ()
seqCoArgs []         = ()
seqCoArgs (arg:args) = seqCoArg arg `seq` seqCoArgs args

seqCoBndr :: ForAllCoBndr -> ()
seqCoBndr (ForAllCoBndr h tv1 tv2 m_cv)
  = seqCo h `seq` tv1 `seq` tv2 `seq` m_cv `m_seq` ()
  where
    Nothing `m_seq` x = x
    Just cv `m_seq` x = cv `seq` x
    infixr 0 `m_seq`
    
{-
%************************************************************************
%*                                                                      *
             The kind of a type, and of a coercion
%*                                                                      *
%************************************************************************

Note [Computing a coercion kind and role]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
To compute a coercion's kind is straightforward: see coercionKind.
But to compute a coercion's role, in the case for NthCo we need
its kind as well.  So if we have two separate functions (one for kinds
and one for roles) we can get exponentially bad behaviour, since each
NthCo node makes a separate call to coercionKind, which traverses the
sub-tree again.  This was part of the problem in Trac #9233.

Solution: compute both together; hence coercionKindRole.  We keep a
separate coercionKind function because it's a bit more efficient if
the kind is all you want.
-}

coercionType :: Coercion -> Type
coercionType co = case coercionKindRole co of
  (Pair ty1 ty2, r) -> mkCoercionType r ty1 ty2

------------------
-- | If it is the case that
--
-- > c :: (t1 ~ t2)
--
-- i.e. the kind of @c@ relates @t1@ and @t2@, then @coercionKind c = Pair t1 t2@.

coercionKind :: Coercion -> Pair Type 
coercionKind co = go co
  where 
    go (Refl _ ty)          = Pair ty ty
    go (TyConAppCo _ tc cos)= mkTyConApp tc <$> (sequenceA $ map coercionArgKind cos)
    go (AppCo co1 _ co2)    = mkAppTy <$> go co1 <*> coercionArgKind co2
    go (ForAllCo cobndr co) = mkNamedForAllTy <$> coBndrKind cobndr <*> pure Invisible <*> go co
    go (CoVarCo cv)         = toPair $ coVarTypes cv
    go (AxiomInstCo ax ind cos)
      | CoAxBranch { cab_tvs = tvs, cab_lhs = lhs, cab_rhs = rhs } <- coAxiomNthBranch ax ind
      , Pair tys1 tys2 <- sequenceA (map coercionArgKind cos)
      = ASSERT( cos `equalLength` tvs )  -- Invariant of AxiomInstCo: cos should 
                                         -- exactly saturate the axiom branch
        Pair (substTyWith tvs tys1 (mkTyConApp (coAxiomTyCon ax) lhs))
             (substTyWith tvs tys2 rhs)
    go (PhantomCo _ t1 t2)    = Pair t1 t2
    go (UnsafeCo _ _ ty1 ty2) = Pair ty1 ty2
    go (SymCo co)             = swap $ go co
    go (TransCo co1 co2)      = Pair (pFst $ go co1) (pSnd $ go co2)
    go g@(NthCo d co)
      | Just args1 <- tyConAppArgs_maybe ty1
      , Just args2 <- tyConAppArgs_maybe ty2
      = ASSERT( d < length args1 && d < length args2 )
        (`getNth` d) <$> Pair args1 args2
     
      | d == 0
      , Just (bndr1, _) <- splitForAllTy_maybe ty1
      , Just (bndr2, _) <- splitForAllTy_maybe ty2
      = binderType <$> Pair bndr1 bndr2

      | otherwise
      = pprPanic "coercionKind" (ppr g)
      where
        Pair ty1 ty2 = coercionKind co
    go (LRCo lr co)         = (pickLR lr . splitAppTy) <$> go co
    go (InstCo aco arg)     = go_app aco [arg]
    go (CoherenceCo g h)
      = let Pair ty1 ty2 = go g in
        Pair (mkCastTy ty1 h) ty2
    go (KindCo co)          = typeKind <$> go co
    go (KindAppCo co)       = typeKind <$> (snd <$> (splitAppTy <$> go co))
    go (SubCo co)           = go co
    go (AxiomRuleCo ax tys cos) =
      case coaxrProves ax tys (map go cos) of
        Just res -> res
        Nothing  -> panic "coercionKind: Malformed coercion"

    go_app :: Coercion -> [CoercionArg] -> Pair Type
    -- Collect up all the arguments and apply all at once
    -- See Note [Nested InstCos]
    go_app (InstCo co arg) args = go_app co (arg:args)
    go_app co              args = applyTys <$> go co <*> (sequenceA $ map coercionArgKind args)

coercionArgKind :: CoercionArg -> Pair Type
coercionArgKind (TyCoArg co)          = coercionKind co
coercionArgKind (CoCoArg _ _ co1 co2) = Pair (CoercionTy co1) (CoercionTy co2)

-- | Apply 'coercionKind' to multiple 'Coercion's
coercionKinds :: [Coercion] -> Pair [Type]
coercionKinds tys = sequenceA $ map coercionKind tys

-- | Get a coercion's kind and role.
-- Why both at once?  See Note [Computing a coercion kind and role]
coercionKindRole :: Coercion -> (Pair Type, Role)
coercionKindRole = go
  where
    go (Refl r ty) = (Pair ty ty, r)
    go (TyConAppCo r tc cos)
      = (mkTyConApp tc <$> (sequenceA $ map coercionArgKind cos), r)
    go (AppCo co1 _ co2)
      = let (tys1, r1) = go co1 in
        (mkAppTy <$> tys1 <*> coercionArgKind co2, r1)
    go (ForAllCo cobndr co)
      = let (tys, r) = go co in
        (mkNamedForAllTy <$> coBndrKind cobndr <*> pure Invisible <*> tys, r)
    go (CoVarCo cv) = (toPair $ coVarTypes cv, coVarRole cv)
    go co@(AxiomInstCo ax _ _) = (coercionKind co, coAxiomRole ax)
    go (PhantomCo _ ty1 ty2)   = (Pair ty1 ty2, Phantom)
    go (UnsafeCo _ r ty1 ty2)  = (Pair ty1 ty2, r)
    go (SymCo co) = first swap $ go co
    go (TransCo co1 co2)
      = let (tys1, r) = go co1 in
        (Pair (pFst tys1) (pSnd $ coercionKind co2), r)
    go (NthCo d co)
      | Just (bndr1, _) <- splitForAllTy_maybe ty1
      , isNamedBinder bndr1   -- don't split (->)!
      = ASSERT( d == 0 )
        let (bndr2, _) = splitForAllTy ty2 in
        (binderType <$> Pair bndr1 bndr2, r)

      | otherwise
      = let (tc1,  args1) = splitTyConApp ty1
            (_tc2, args2) = splitTyConApp ty2
        in
        ASSERT( tc1 == _tc2 )
        ((`getNth` d) <$> Pair args1 args2, nthRole r tc1 d)

      where
        (Pair ty1 ty2, r) = go co
    go co@(LRCo {}) = (coercionKind co, Nominal)
    go (InstCo co arg) = go_app co [arg]
    go (CoherenceCo co1 co2)
      = let (Pair t1 t2, r) = go co1 in
        (Pair (t1 `mkCastTy` co2) t2, r)
    go co@(KindCo {}) = (coercionKind co, Representational)
    go (KindAppCo co)
      = let (tys, r) = go co in
        (typeKind <$> (snd <$> (splitAppTy <$> tys)), r)
    go (SubCo co) = (coercionKind co, Representational)
    go co@(AxiomRuleCo ax _ _) = (coercionKind co, coaxrRole ax)

    go_app :: Coercion -> [CoercionArg] -> (Pair Type, Role)
    -- Collect up all the arguments and apply all at once
    -- See Note [Nested InstCos]
    go_app (InstCo co arg) args = go_app co (arg:args)
    go_app co              args
      = let (pair, r) = go co in
        (applyTys <$> pair <*> (sequenceA $ map coercionArgKind args), r)

-- | Retrieve the role from a coercion.
coercionRole :: Coercion -> Role
coercionRole = snd . coercionKindRole
  -- There's not a better way to do this, because NthCo needs the *kind*
  -- and role of its argument. Luckily, laziness should generally avoid
  -- the need for computing kinds in other cases.

-- | Get a 'CoercionArg's kind and role.
-- Why both at once?  See Note [Computing a coercion kind and role]
coercionArgKindRole :: CoercionArg -> (Pair Type, Role)
coercionArgKindRole (TyCoArg co)          = coercionKindRole co
coercionArgKindRole (CoCoArg r _ co1 co2) = (CoercionTy <$> Pair co1 co2, r)

-- | Get a 'CoercionArg's role.
coercionArgRole :: CoercionArg -> Role
coercionArgRole = snd . coercionArgKindRole

-- | Get the pair of vars bound by a 'ForAllCo'
coBndrKind :: ForAllCoBndr -> Pair Var
coBndrKind (ForAllCoBndr _ tv1 tv2 _) = Pair tv1 tv2

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
So it's very important to do the substitution simultaneously.

cf Type.applyTys (which in fact we call here)
-}

applyCo :: Type -> Coercion -> Type
-- Gives the type of (e co) where e :: (a~b) => ty
applyCo ty co | Just ty' <- coreView ty = applyCo ty' co
applyCo (ForAllTy (Named cv _) ty) co = substTyWith [cv] [CoercionTy co] ty
applyCo (ForAllTy (Anon _)     ty) _  = ty
applyCo _                          _  = panic "applyCo"

{-
%************************************************************************
%*                                                                      *
             GADT return types
%*                                                                      *
%************************************************************************

Note [mkGADTVars]
~~~~~~~~~~~~~~~~~

Running example:

data T (k1 :: *) (k2 :: *) (a :: k2) (b :: k2) where
  MkT :: T x1 * (Proxy (y :: x1), z) z

We need the rejigged type to be

  MkT :: forall (x1 :: *) (k2 :: *) (a :: k2) (z :: k2).
         forall (y :: x1) (c1 :: k2 ~# *)
                (c2 :: a ~# ((Proxy x1 y, z |> c1) |> sym c1)).
         T x1 k2 a z

The HsTypes have already been desugared to proper Types:

  T x1 * (Proxy (y :: x1), z) z
becomes
  [x1 :: *, y :: x1, z :: *]. T x1 * (Proxy x1 y, z) z

We start off by matching (T k1 k2 a b) with (T x1 * (Proxy x1 y, z) z). We
know this match will succeed because of the validity check (actually done
later, but laziness saves us -- see Note [Checking GADT return types]). Thus,
we get

  subst := { k1 |-> x1, k2 |-> *, a |-> (Proxy x1 y, z), b |-> z }

Now, we need to figure out what the GADT equalities should be. In this case,
we *don't* want (k1 ~ x1) to be a GADT equality: it should just be a
renaming. The others should be GADT equalities, but they need to be
homogeneous so that the solver can make sense of them. We also need to make
sure that the universally-quantified variables of the datacon match up
with the tyvars of the tycon, as required for Core context well-formedness.
(This last bit is why we have to rejig at all!)

`choose` walks down the tycon tyvars, figuring out what to do with each one.
It carries three substitutions:
  - t_sub's domain is *template* or *tycon* tyvars, mapping them to variables
    mentioned in the datacon signature.
  - r_sub's domain is *result* tyvars, names written by the programmer in
    the datacon signature. The final rejigged type will use these names, but
    the subst is still needed because sometimes the kind of these variables
    is different than what the user wrote.
  - lc is a lifting context -- that is, a mapping from type variables to
    coercions -- that maps from *tycon* tyvars to coercion variables witnessing
    the relevant GADT equality.

Before explaining the details of `choose`, let's just look at its operation
on our example:

  choose [] [] {} {} {} [k1, k2, a, b]
  -->          -- first branch of `case` statement
  choose
    univ_tvs: [x1 :: *]
    covars:   []
    t_sub:    {k1 |-> x1}
    r_sub:    {x1 |-> x1 |> <*>}
    lc:       {}
    t_tvs:    [k2, a, b]
  -->          -- second branch of `case` statement
  choose
    univ_tvs: [k2 :: *, x1 :: *]
    covars:   [c1 :: k2 ~# (* |> sym <*>)]
    t_sub:    {k1 |-> x1, k2 |-> k2}
    r_sub:    {x1 |-> x1 |> <*>}
    lc:       {k2 |-> c1}
    t_tvs:    [a, b]
  -->          -- second branch of `case` statement
  choose
    univ_tvs: [a :: k2, k2 :: *, x1 :: *]
    covars:   [ c2 :: a ~# ((Proxy x1 y, z) |> sym c1)
              , c1 :: k2 ~# (* |> sym <*>) ]
    t_sub:    {k1 |-> x1, k2 |-> k2, a |-> a}
    r_sub:    {x1 |-> x1 |> <*>}
    lc:       {k2 |-> c1, a |-> c2}
    t_tvs:    [b]
  -->          -- first branch of `case` statement
  choose
    univ_tvs: [z :: k2, a :: k2, k2 :: *, x1 :: *]
    covars:   [ c2 :: a ~# ((Proxy x1 y, z |> c1) |> sym c1)
              , c1 :: k2 ~# (* |> sym <*>) ]
    t_sub:    {k1 |-> x1, k2 |-> k2, a |-> a, b |-> z}
    r_sub:    {x1 |-> x1 |> <*>, z |-> z |> c1}
    lc:       {k2 |-> c1, a |-> c2}
    t_tvs:    []
  -->          -- end of recursion
  ([x1, k2, a, z], [c1, c2], {x1 |-> x1 |> <*>, z |-> z |> c1})

`choose` looks up each tycon tyvar in the matching (it *must* be matched!). If
it finds a bare result tyvar (the first branch of the `case` statement), it
checks to make sure that the result tyvar isn't yet in the list of univ_tvs.
If it is in that list, then we have a repeated variable in the return type,
and we in fact need a GADT equality. Assuming no repeated variables, we wish
to use the variable name given in the datacon signature (that is, `x1` not
`k1` and `z` not `b`), not the tycon signature (which may have been made up by
GHC!). So, we add a mapping from the tycon tyvar to the result tyvar to t_sub.
But, it's essential that the kind of the result tyvar (which is now becoming a
proper universally- quantified variable) match the tycon tyvar. Thus, the
setTyVarKind in the definition of r_tv'. This last step is necessary in
fixing the kind of the universally-quantified `z`.

However, because later uses of the result tyvar will expect it to have
the user-supplied kind (that is, (z :: *) instead of (z :: k2)), we also
must extend r_sub appropriately. This work with r_sub must take into account
that some of the covars may mention the variables in question. Thus,
the `mapAccumR substCoVarBndr`.

If we discover that a mapping in `subst` gives us a non-tyvar (the second
branch of the `case` statement), then we have a GADT equality to create.
We create a fresh coercion variable and extend the substitutions accordingly,
being careful to apply the correct substitutions built up from previous
variables.

This whole algorithm is quite delicate, indeed. I (Richard E.) see two ways
of simplifying it:

1) The first branch of the `case` statement is really an optimization, used
in order to get fewer GADT equalities. It might be possible to make a GADT
equality for *every* univ. tyvar, even if the equality is trivial, and then
either deal with the bigger type or somehow reduce it later.

2) This algorithm strives to use the names for type variables as specified
by the user in the datacon signature. If we always used the tycon tyvar
names, for example, this would be simplified. This change would almost
certainly degrade error messages a bit, though.
-}

-- ^ From information about a source datacon definition, extract out
-- what the universal variables and the GADT equalities should be.
-- Called from TcTyClsDecls.rejigConRes, but it gets so involved with
-- lifting and coercions that it seemed to belong here.
-- See Note [mkGADTVars].   TODO (RAE): Update note to remove LCs
mkGADTVars :: [TyVar]    -- ^ The tycon vars
           -> [TyCoVar]  -- ^ The datacon vars
           -> TCvSubst   -- ^ The matching between the template result type
                         -- and the actual result type
           -> UniqSM ( [TyVar]
                     , [CoVar]
                     , TCvSubst ) -- ^ The univ. variables, the GADT equalities,
                                  -- and a subst to apply to any existentials.
mkGADTVars tmpl_tvs dc_tvs subst
  = choose [] [] empty_subst empty_subst tmpl_tvs
  where
    in_scope = mkInScopeSet (mkVarSet tmpl_tvs `unionVarSet` mkVarSet dc_tvs)
    empty_subst = mkEmptyTCvSubst in_scope
                                          
    choose :: [TyVar]           -- accumulator of univ tvs, reversed
           -> [CoVar]           -- accumulator of GADT equality covars, reversed
           -> TCvSubst          -- template substutition
           -> TCvSubst          -- res. substitution
           -> [TyVar]           -- template tvs (the univ tvs passed in)
           -> UniqSM ( [TyVar]  -- the univ_tvs
                     , [CoVar]  -- the covars witnessing GADT equalities
                     , TCvSubst )  -- a substitution to fix kinds in ex_tvs
           
    choose univs eqs _     r_sub []
      = return (reverse univs, reverse eqs, r_sub)
    choose univs eqs t_sub r_sub (t_tv:t_tvs)
      | Just r_ty <- lookupVar subst t_tv
      = case getTyVar_maybe r_ty of
          Just r_tv
            |  not (r_tv `elem` univs)
            -> -- simple variable substitution. we should continue to subst.
               choose (r_tv':univs) eqs'
                      (extendTCvSubst t_sub t_tv r_ty')
                      (composeTCvSubst r_sub2 r_sub)
                      t_tvs
            where
              r_tv1 = setTyVarName r_tv (choose_tv_name r_tv t_tv)
              r_tv' = setTyVarKind r_tv1 (substTy t_sub (tyVarKind t_tv))
              r_ty' = mkOnlyTyVarTy r_tv'
                -- fixed r_ty' has the same kind as r_tv
              r_tv_subst = extendTCvSubst empty_subst r_tv r_ty'

                -- use mapAccumR not mapAccumL: eqs is *reversed*
              (r_sub2, eqs') = mapAccumR substCoVarBndr r_tv_subst eqs


               -- not a simple substitution. make an equality predicate
               -- and extend the lifting context
          _ -> do { cv <- fresh_co_var (mkOnlyTyVarTy t_tv') r_ty
                  ; let t_sub' = extendTCvInScope t_sub cv
                        r_sub' = extendTCvInScope r_sub cv
                  ; choose (t_tv':univs) (cv:eqs)
                           (extendTCvSubst t_sub' t_tv (mkOnlyTyVarTy t_tv'))
                           r_sub' t_tvs }
            where t_tv' = updateTyVarKind (substTy t_sub) t_tv

      | otherwise
      = pprPanic "mkGADTVars" (ppr tmpl_tvs $$ ppr subst)

      -- creates a fresh gadt covar, with a Nominal role
    fresh_co_var :: Type -> Type -> UniqSM CoVar
    fresh_co_var t1 t2
      = do { u <- getUniqueM
           ; let name = mkSystemVarName u (fsLit "gadt")
           ; return $ mkCoVar name (mkCoercionType Nominal t1 t2) }

      -- choose an appropriate name for a univ tyvar.
      -- This *must* preserve the Unique of the result tv, so that we
      -- can detect repeated variables. It prefers user-specified names
      -- over system names, but never outputs a System name, because
      -- those print terribly.
    choose_tv_name :: TyVar -> TyVar -> Name
    choose_tv_name r_tv t_tv
      | isSystemName r_tv_name
      = setNameUnique t_tv_name (getUnique r_tv_name)

      | otherwise
      = r_tv_name

      where
        r_tv_name = getName r_tv
        t_tv_name = getName t_tv

{-
%************************************************************************
%*                                                                      *
             Building a coherence coercion
%*                                                                      *
%************************************************************************
-}

-- | Finds a nominal coercion between two types, if the
-- erased version of those types are equal. Returns Nothing otherwise.
buildCoherenceCo :: Type -> Type -> Maybe Coercion
buildCoherenceCo orig_ty1 orig_ty2
  = buildCoherenceCoX
      (mkRnEnv2 (mkInScopeSet (tyCoVarsOfTypes [orig_ty1, orig_ty2])))
      orig_ty1 orig_ty2

buildCoherenceCoX :: RnEnv2 -> Type -> Type -> Maybe Coercion
buildCoherenceCoX = go
  where
    go env ty1 ty2 | Just ty1' <- coreViewOneStarKind ty1 = go env ty1' ty2
    go env ty1 ty2 | Just ty2' <- coreViewOneStarKind ty2 = go env ty1  ty2'
    
    go env (TyVarTy tv1) (TyVarTy tv2)
      | rnOccL env tv1 == rnOccR env tv2
      = Just $ mkNomReflCo (mkOnlyTyVarTy $ rnOccL env tv1)
    go env (AppTy tyl1 tyr1) (AppTy tyl2 tyr2)
      = mkAppCo <$> go env tyl1 tyl2
                      -- TODO (RAE): This next line is inefficient
                <*> go env (typeKind tyr1) (typeKind tyr2)
                <*> buildCoherenceCoArgX env tyr1 tyr2
    go env (TyConApp tc1 tys1) (TyConApp tc2 tys2)
      | tc1 == tc2
      = mkTyConAppCo Nominal tc1 <$> zipWithM (buildCoherenceCoArgX env) tys1 tys2
    go env (ForAllTy (Anon arg1) res1) (ForAllTy (Anon arg2) res2)
      = mkFunCo Nominal <$> go env arg1 arg2 <*> go env res1 res2
    go env (ForAllTy (Named tv1 _) ty1) (ForAllTy (Named tv2 _) ty2)
      = do { (env', bndr) <- go_bndr env tv1 tv2
           ; mkForAllCo bndr <$> go env' ty1 ty2 }
    go _   (LitTy lit1) (LitTy lit2)
      | lit1 == lit2
      = Just $ mkNomReflCo (LitTy lit1)
    go env (CastTy ty1 co1) ty2
      = mkCoherenceLeftCo <$> go env ty1 ty2 <*> pure (rename_co rnEnvL env co1)
    go env ty1 (CastTy ty2 co2)
      = mkCoherenceRightCo <$> go env ty1 ty2 <*> pure (rename_co rnEnvR env co2)

    go _ _ _ = Nothing

    go_bndr env tv1 tv2
      = do { eta <- go env k1 k2
           ; if | isCoVar tv1
                  -> let (env1, tv1') = rnBndrL env  tv1
                         (env2, tv2') = rnBndrR env1 tv2 in
                     Just (env2, mkForAllCoBndr eta tv1' tv2' Nothing)

                | otherwise
                  -> let (env1, tv1') = rnBndrL env  tv1
                         (env2, tv2') = rnBndrR env1 tv2
                         in_scope     = rnInScopeSet env2
                         cv           = mkFreshCoVar in_scope
                                                     (mkOnlyTyVarTy tv1')
                                                     (mkOnlyTyVarTy tv2')
                         env3         = addRnInScopeSet env2 (unitVarSet cv)
                     in
                     Just (env3, mkForAllCoBndr eta tv1' tv2' (Just cv)) }
      where
        k1  = tyVarKind tv1
        k2  = tyVarKind tv2

buildCoherenceCoArg :: Type -> Type -> Maybe CoercionArg
buildCoherenceCoArg orig_ty1 orig_ty2
  = buildCoherenceCoArgX
      (mkRnEnv2 (mkInScopeSet (tyCoVarsOfTypes [orig_ty1, orig_ty2])))
      orig_ty1 orig_ty2

buildCoherenceCoArgX :: RnEnv2 -> Type -> Type -> Maybe CoercionArg
buildCoherenceCoArgX = go_arg
  where
    go_arg env (CoercionTy co1) (CoercionTy co2)
      = mkCoCoArg Nominal
          <$> (mkSubCo <$>
               buildCoherenceCoX env (coercionType co1) (coercionType co2))
          <*> pure (rename_co rnEnvL env co1)
          <*> pure (rename_co rnEnvR env co2)
                 
    go_arg env ty1 ty2
      = mkTyCoArg <$> buildCoherenceCoX env ty1 ty2

rename_co :: (RnEnv2 -> VarEnv Var) -> RnEnv2 -> Coercion -> Coercion
rename_co getvars env = substCo subst
  where varenv = getvars env
        (ty_env, co_env) = partitionVarEnv isTyVar varenv
        tv_subst_env = mapVarEnv mkOnlyTyVarTy ty_env
        cv_subst_env = mapVarEnv mkCoVarCo     co_env

        subst = mkTCvSubst (rnInScopeSet env) (tv_subst_env, cv_subst_env)
