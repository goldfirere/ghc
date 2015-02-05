{-
(c) The University of Glasgow 2006
-}

{-# LANGUAGE RankNTypes, CPP, DeriveDataTypeable #-}

-- | Module for (a) type kinds and (b) type coercions, 
-- as used in System FC. See 'CoreSyn.Expr' for
-- more on System FC and how coercions fit into it.
--
module Coercion (
        -- * Main data type
        Coercion, CoercionArg, ForAllCoBndr, LeftOrRight(..),
        Var, CoVar, TyCoVar, mkFreshCoVar, mkFreshReprCoVar,
        Role(..), ltRole,

        -- ** Functions over coercions
        coVarTypes, coVarKind, coVarKindsTypesRole, coVarRole,
        coercionType, coercionKind, coercionKinds,
        mkCoercionType, coercionArgKind,
        coercionRole, coercionKindRole,

        -- ** Constructing coercions
        mkReflCo, mkCoVarCo, 
        mkAxInstCo, mkUnbranchedAxInstCo,
        mkAxInstRHS, mkUnbranchedAxInstRHS,
        mkAxInstLHS, mkUnbranchedAxInstLHS,
        mkPiCo, mkPiCos, mkCoCast,
        mkSymCo, mkTransCo, mkNthCo, mkNthCoRole, mkLRCo,
        mkInstCo, mkAppCo, mkAppCoFlexible, mkTyConAppCo, mkFunCo,
        mkForAllCo, mkForAllCo_TyHomo, mkForAllCo_CoHomo,
        mkPhantomCo, mkHomoPhantomCo,
        mkUnsafeCo, mkUnsafeCoArg, mkSubCo,
        mkNewTypeCo, mkAppCos, mkAxiomInstCo,
        downgradeRole, downgradeRoleArg, mkAxiomRuleCo,
        mkCoherenceCo, mkCoherenceRightCo, mkCoherenceLeftCo,
        mkKindCo, castCoercionKind,
        bulletCo,

        mkTyHeteroCoBndr, mkCoHeteroCoBndr, mkHomoCoBndr,
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

        getHomoVar_maybe, splitHeteroCoBndr_maybe, coBndrBoundVars,

        stripTyCoArg, splitCoCoArg_maybe,

        isReflCo, isReflCo_maybe, isReflLike, isReflLike_maybe,

        -- ** Coercion variables
        mkCoVar, isCoVar, coVarName, setCoVarName, setCoVarUnique,

        -- ** Free variables
        tyCoVarsOfCo, tyCoVarsOfCos, coVarsOfCo, coercionSize,
        tyCoVarsOfCoArg, tyCoVarsOfCoArgs,
        
        -- ** Substitution
        CvSubstEnv, emptyCvSubstEnv,
        lookupCoVar,
        substCo, substCos, substCoVar, substCoVars,
        substCoVarBndr, substCoWithIS, substForAllCoBndr,
        extendTCvSubstAndInScope, rnCoBndr2,

        -- ** Lifting
        liftCoSubst, liftCoSubstTyVar, liftCoSubstWith, liftCoSubstWithEx,
        emptyLiftingContext, extendLiftingContext, extendLiftingContextIS,
        liftCoSubstTyCoVar, liftSimply,
        liftCoSubstVarBndrCallback, isMappedByLC,

        LiftCoEnv, LiftingContext(..), liftEnvSubstLeft, liftEnvSubstRight,
        substRightCo, substLeftCo,

        -- ** Comparison
        eqCoercion, eqCoercionX, cmpCoercionX, eqCoercionArg,

        -- ** Forcing evaluation of coercions
        seqCo,
        
        -- * Pretty-printing
        pprCo, pprParendCo, pprCoArg, pprCoBndr,
        pprCoAxiom, pprCoAxBranch, pprCoAxBranchHdr, 

        -- * Tidying
        tidyCo, tidyCos,

        -- * Other
        applyCo, promoteCoercion, mkGADTVars,
        buildCoherenceCo, buildCoherenceCoArg
       ) where 

#include "HsVersions.h"

import {-# SOURCE #-} TysWiredIn ( unitTy )

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
import PrelNames        ( funTyConKey, eqPrimTyConKey, eqReprPrimTyConKey
                        , wildCardName )
import ListSetOps
  
import Control.Applicative hiding ( empty )
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable (traverse, sequenceA)
#endif
import Control.Monad (foldM)
import Data.Maybe (isJust)
import FastString
import Control.Arrow ( first )
import Data.List ( mapAccumR )

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
coercionSize (AppCo co arg)      = coercionSize co + coercionArgSize arg
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
coercionSize (CoherenceCo a b c d)= 1 + sum $ map coercionSize [a, b, c, d]
coercionSize (KindCo co)         = 1 + coercionSize co
coercionSize (SubCo co)          = 1 + coercionSize co
coercionSize (AxiomRuleCo _ ts cs) = 1 + sum (map typeSize ts)
                                       + sum (map coercionSize cs)

coercionArgSize :: CoercionArg -> Int
coercionArgSize (TyCoArg co)       = coercionSize co
coercionArgSize (CoCoArg _ c1 c2)  = coercionSize c1 + coercionSize c2

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
ppr_co p (AppCo co arg)        = maybeParen p TyConPrec $
                                 pprCo co <+> ppr_arg TyConPrec arg
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
ppr_co p (CoherenceCo { coh_base = co, coh_kind = k_co, coh_left = l, coh_right = r })
                             = maybeParen p TyConPrec $
                               (ppr_co FunPrec c1) <+> (ptext (sLit "|>_"))
                               <> pprParendCo k_co
                               <+> parens (pprCo l <> comma <+> prpCo r)
ppr_co p (KindCo co)         = pprPrefixApp p (ptext (sLit "kind")) [pprParendCo co]
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
ppr_arg _ (CoCoArg r co1 co2) = parens (pprCo co1 <> comma <+> pprCo co2) <> ppr_role r

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
       ; let args = zipWith liftSimply (tyConRolesX r tc) tys
       ; return (tc, args) }
splitTyConAppCo_maybe (TyConAppCo _ tc cos) = Just (tc, cos)
splitTyConAppCo_maybe _                     = Nothing

-- first result has role equal to input; second result is Nominal
splitAppCo_maybe :: Coercion -> Maybe (Coercion, CoercionArg)
-- ^ Attempt to take a coercion application apart.
splitAppCo_maybe (AppCo co arg) = Just (co, arg)
splitAppCo_maybe (TyConAppCo r tc args)
  | isDecomposableTyCon tc || args `lengthExceeds` tyConArity tc 
  , Just (args', arg') <- snocView args
  , Just arg'' <- setNominalRoleArg_maybe arg'
  = Just (mkTyConAppCo r tc args', arg'') -- Never create unsaturated type family apps!
       -- Use mkTyConAppCo to preserve the invariant
       --  that identity coercions are always represented by Refl
splitAppCo_maybe (Refl r ty) 
  | Just (ty1, ty2) <- splitAppTy_maybe ty 
  = Just (mkReflCo r ty1, liftSimply Nominal ty2)
splitAppCo_maybe _ = Nothing

splitForAllCo_maybe :: Coercion -> Maybe (ForAllCoBndr, Coercion)
splitForAllCo_maybe (ForAllCo cobndr co) = Just (cobndr, co)
splitForAllCo_maybe _                    = Nothing

-- returns the two type variables abstracted over
splitForAllCo_Ty_maybe :: Coercion -> Maybe (TyVar, TyVar, CoVar, Coercion)
splitForAllCo_Ty_maybe (ForAllCo (TyHomo tv) co)
  = let k  = tyVarKind tv
        cv = mkCoVar wildCardName (mkCoercionType Nominal k k) in
    Just (tv, tv, cv, co) -- cv won't occur in co anyway
splitForAllCo_Ty_maybe (ForAllCo (TyHetero _ tv1 tv2 cv) co)
  = Just (tv1, tv2, cv, co)
splitForAllCo_Ty_maybe _
  = Nothing

-- returns the two coercion variables abstracted over
splitForAllCo_Co_maybe :: Coercion -> Maybe (CoVar, CoVar, Coercion)
splitForAllCo_Co_maybe (ForAllCo (CoHomo cv) co)          = Just (cv, cv, co)
splitForAllCo_Co_maybe (ForAllCo (CoHetero _ cv1 cv2) co) = Just (cv1, cv2, co)
splitForAllCo_Co_maybe _                                  = Nothing

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
 | otherwise = pprPanic "coVarTypes, non coercion variable"
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
mkCoercionType Phantom          = panic "mkCoercionType"

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
isReflLike_maybe (CoCoArg _ co1 co2)
  | coercionType co1 `eqType` coercionType co2
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
of Coercion, and they perform very basic optimizations. Note that if you
add a new optimization here, you will have to update the code in Unify
to account for it. These smart constructors are used in substitution, so
to preserve the semantics of matching and unification, those algorithms must
be aware of any optimizations done here.

See also Note [Coercion optimizations and match_co] in Unify.

Note [Don't optimize mkTransCo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
One would expect to implement the following two optimizations in mkTransCo:
  mkTransCo co1 (Refl ...) --> co1
  mkTransCo (Refl ...) co1 --> co1

However, doing this would make unification require backtracking search. Say
we had these optimizations and we are trying to match (co1 ; co2 ; co3) with
(co1' ; co2') (where ; means `TransCo`) One of the coercions disappeared, but
which one? Yuck. So, instead of putting this optimization here, we just have
it in OptCoercion.

Note [Don't optimize mkCoherenceCo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
TODO (RAE): Note still valid?
One would expect to use an easy optimization in mkCoherenceCo: we would want
  (CoherenceCo (CoherenceCo co1 co2) co3)
to become
  (CoherenceCo co1 (mkTransCo co2 co3))

This would be completely sound, and in fact it is done in OptCoercion. But
we *can't* do it here. This is because these smart constructors must be
invertible, in some sense. In the matching algorithm, we must consider all
optimizations that can happen during substitution. Because mkCoherenceCo
is used in substitution, if we did this optimization, the match function
would need to look for substitutions that yield this optimization. The
problem is that these substitutions are hard to find, because the mkTransCo
itself might be optimized. The basic problem is that it is hard to figure
out what co2 could possibly be from the optimized version. So, we don't
do the optimization.

Note [Optimizing mkSymCo is OK]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given the previous two notes, the implementation of mkSymCo seems fishy.
Why is it OK to optimize this one? Because the optimizations don't require
backtracking search to invert, essentially. Say we are matching (SymCo co1)
with co2. If co2 is (SymCo co2'), then we just match co1 with co2'. If
co2 is (UnsafeCo ty1 ty2), then we match co1 with (UnsafeCo ty2 ty1). Otherwise,
we match co1 with (SymCo co2) -- the only way to get a coercion headed by
something other than SymCo or UnsafeCo is the SymCo (SymCo ..) optimization.
Also, critically, it is impossible to get a coercion headed by SymCo or
UnsafeCo by this optimization. (Contrast to the missing optimization in
mkTransCo, which could produce a TransCo.) So, we can keep these here. Phew.

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
-}

mkReflCo :: Role -> Type -> Coercion
mkReflCo r ty
  = ASSERT( not $ isCoercionTy ty )
    Refl r ty

-- | Apply a type constructor to a list of coercions. It is the
-- caller's responsibility to get the roles correct on argument coercions.
mkTyConAppCo :: Role -> TyCon -> [CoercionArg] -> Coercion
mkTyConAppCo r tc cos
               -- Expand type synonyms
  | Just (tv_co_prs, rhs_ty, leftover_cos) <- tcExpandTyCon_maybe tc cos
  = mkAppCos (liftCoSubst r (mkLiftingContext tv_co_prs) rhs_ty) leftover_cos

  | Just tys <- traverse isReflLike_maybe cos 
  = Refl r (mkTyConApp tc tys)    -- See Note [Refl invariant]

  | otherwise = TyConAppCo r tc cos

-- | Make a function 'Coercion' between two other 'Coercion's
mkFunCo :: Role -> Coercion -> Coercion -> Coercion
mkFunCo r co1 co2 = mkTyConAppCo r funTyCon [TyCoArg co1, TyCoArg co2]

-- | Apply a 'Coercion' to another 'CoercionArg'.
-- The second coercion must be Nominal, unless the first is Phantom.
-- If the first is Phantom, then the second can be either Phantom or Nominal.
mkAppCo :: Coercion -> CoercionArg -> Coercion
mkAppCo co1 co2 = mkAppCoFlexible co1 Nominal co2

mkAppCoFlexible :: Coercion -> Role -> CoercionArg -> Coercion
mkAppCoFlexible (Refl r ty1) _ arg
  | Just ty2 <- isReflLike_maybe arg
  = Refl r (mkAppTy ty1 ty2)
mkAppCoFlexible (Refl r ty1) r2 co2
  | Just (tc, tys) <- splitTyConApp_maybe ty1
    -- Expand type synonyms; a TyConAppCo can't have a type synonym (Trac #9102)
  = TyConAppCo r tc (zip_roles (tyConRolesX r tc) tys)
  where
    zip_roles (r1:_)  []            = [downgradeRoleArg r1 r2 co2]
    zip_roles (r1:rs) (ty1:tys)     = liftSimply r1 ty1 : zip_roles rs tys
    zip_roles _       _             = panic "zip_roles" -- but the roles are infinite...
mkAppCoFlexible (TyConAppCo r tc cos) r2 co
  = case r of
      Nominal          -> ASSERT( r2 == Nominal )
                          TyConAppCo Nominal tc (cos ++ [co])
      Representational -> TyConAppCo Representational tc (cos ++ [co'])
        where new_role = (tyConRolesX Representational tc) !! (length cos)
              co'      = downgradeRoleArg new_role r2 co
      Phantom          -> TyConAppCo Phantom tc (cos ++ [toPhantomCoArg co])
mkAppCoFlexible co1 _r2 co2
  = ASSERT( _r2 == Nominal )
    AppCo co1 co2
-- Note, mkAppCo is careful to maintain invariants regarding
-- where Refl constructors appear; see the comments in the definition
-- of Coercion and the Note [Refl invariant] in types/TyCoRep.lhs.

-- | Applies multiple 'Coercion's to another 'CoercionArg', from left to right.
-- See also 'mkAppCo'.
mkAppCos :: Coercion -> [CoercionArg] -> Coercion
mkAppCos co1 cos = foldl mkAppCo co1 cos

-- | Make a Coercion from a ForAllCoBndr and Coercion
mkForAllCo :: ForAllCoBndr -> Coercion -> Coercion
mkForAllCo cobndr co
  | Refl r ty <- co
  = Refl r (mkNamedForAllTy (getHomoVar cobndr) Invisible ty)
                            -- vis. doesn't matter
  | otherwise
  = ASSERT( isHomoCoBndr cobndr || (not $ isReflCo $ getHeteroKindCo cobndr) )
    ForAllCo cobndr co

-- | Make a Coercion quantified over a type variable; the variable has
-- the same type in both types of the coercion
mkForAllCo_TyHomo :: TyVar -> Coercion -> Coercion
mkForAllCo_TyHomo tv (Refl r ty)
  = ASSERT( isTyVar tv ) Refl r (mkNamedForAllTy tv Invisible ty)
mkForAllCo_TyHomo tv co          = ASSERT( isTyVar tv ) ForAllCo (TyHomo tv) co

-- | Make a Coercion quantified over a coercion variable; the variable has
-- the same type in both types of the coercion
mkForAllCo_CoHomo :: CoVar -> Coercion -> Coercion
mkForAllCo_CoHomo cv (Refl r ty)
  = ASSERT( isCoVar cv ) Refl r (mkNamedForAllTy cv Invisible ty)
mkForAllCo_CoHomo cv co          = ASSERT( isCoVar cv ) ForAllCo (CoHomo cv) co

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
mkFreshCoVar = mk_fresh_co_var Nominal

-- | Like 'mkFreshCoVar', but for a Representational covar.
mkFreshReprCoVar :: InScopeSet -> Type -> Type -> CoVar
mkFreshReprCoVar = mk_fresh_co_var Representational

-- | Worker for 'mkFreshCoVar' and 'mkFreshReprCoVar'
mk_fresh_co_var :: Role -> InScopeSet -> Type -> Type -> CoVar
mk_fresh_co_var r in_scope ty1 ty2
  = let cv_uniq = mkCoVarUnique 31 -- arbitrary number
        cv_name = mkSystemVarName cv_uniq (fsLit "c") in
    uniqAway in_scope $ mkCoVar cv_name (mkCoercionType r ty1 ty2)

mkAxInstCo :: Role -> CoAxiom br -> BranchIndex -> [Type] -> Coercion
-- mkAxInstCo can legitimately be called over-staturated; 
-- i.e. with more type arguments than the coercion requires
mkAxInstCo role ax index tys
  | arity == n_tys = downgradeRole role ax_role $ AxiomInstCo ax_br index rtys
  | otherwise      = ASSERT( arity < n_tys )
                     downgradeRole role ax_role $
                     foldl mkAppCo (mkAxiomInstCo ax_br index (take arity rtys))
                                   (drop arity rtys)
  where
    n_tys = length tys
    ax_br     = toBranchedAxiom ax
    branch    = coAxiomNthBranch ax_br index
    arity     = length $ coAxBranchTyCoVars branch
    arg_roles = coAxBranchRoles branch
    rtys      = zipWith liftSimply (arg_roles ++ repeat Nominal) tys
    ax_role   = coAxiomRole ax

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
mkUnsafeCoArg _ r (CoercionTy co1) (CoercionTy co2) = CoCoArg r co1 co2
mkUnsafeCoArg provenance role ty1 ty2
  = ASSERT( not (isCoercionTy ty1) && not (isCoercionTy ty2) )
    TyCoArg $ mkUnsafeCo provenance role ty1 ty2

-- | Create a symmetric version of the given 'Coercion' that asserts
--   equality between the same types but in the other "direction", so
--   a kind of @t1 ~ t2@ becomes the kind @t2 ~ t1@.
mkSymCo :: Coercion -> Coercion

-- Do a few simple optimizations, but don't bother pushing occurrences
-- of symmetry to the leaves; the optimizer will take care of that.
-- See Note [Optimizing mkSymCo is OK]
mkSymCo co@(Refl {})              = co
mkSymCo    (UnsafeCo s r ty1 ty2) = UnsafeCo s r ty2 ty1
mkSymCo    (SymCo co)             = co
mkSymCo co                        = SymCo co

-- | Create a new 'Coercion' by composing the two given 'Coercion's transitively.
mkTransCo :: Coercion -> Coercion -> Coercion
-- See Note [Don't optimize mkTransCo]
mkTransCo co1 co2
  | Pair s1 _s2 <- coercionKind co1
  , Pair _t1 t2 <- coercionKind co2
  , ASSERT2( _s2 `eqType` _t1, ppr co1 $$ ppr s1 $$ ppr _s2 $$ ppr co2 $$ ppr _t1 $$ ppr t2 )
    s1 `eqType` t2
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
                           liftSimply r' (tyConAppArgN n ty)
  where tc = tyConAppTyCon ty
        r' = nthRole r tc n
        
mkNthCoArg n co
  | Just (bndr1, _) <- splitForAllTy_maybe ty1
  , Just (bndr2, _) <- splitForAllTy_maybe ty2
  , binderType bndr1 `eqType` binderType bndr2
  , n == 0
       -- TODO (RAE): Is this the correct role in the named case??
  = liftSimply (coercionRole co) (binderType bndr1)

  | Just (tc1, tys1) <- splitTyConApp_maybe ty1
  , Just (_tc2, tys2) <- splitTyConApp_maybe ty2
  , let arg1 = tys1 `getNth` n
        arg2 = tys2 `getNth` n
  , arg1 `eqType` arg2
  = ASSERT( tc1 == _tc2 )
    liftSimply (nthRole (coercionRole co) tc1 n) arg1

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

mkCoherenceCo :: Coercion     -- ^ :: t1 ~r t2; t1 :: k1; t2 :: k2
              -> Coercion     -- ^ :: k1' ~r k2'
              -> Coercion     -- ^ h1 :: k1 ~R k1'
              -> Coercion     -- ^ h2 :: k2 ~R k2'
              -> Coercion     -- ^ :: (t1 |> h1) ~r (t2 |> h2)
mkCoherenceCo base _ (Refl _) (Refl _) = base
mkCoherenceCo base kind l r = CoherenceCo { coh_base = base, coh_kind  = kind
                                          , coh_left = l,    coh_right = r }

-- | See arguments.
mkCoherenceRightCo :: Coercion  -- ^ :: t1 ~r t2, where t1 :: k1 & t2 :: k2
                   -> Coercion  -- ^ :: k1 ~r k2'
                   -> Coercion  -- ^ co :: k2 ~R k2'
                   -> Coercion  -- ^ :: t1 ~r (t2 |> co)
mkCoherenceRightCo base _ (Refl {}) = base
mkCoherenceRightCo base kind co
  = CoherenceCo { coh_base = base, coh_kind = kind, coh_right = right
                , coh_left = mkReflCo Representational k1 }
  where
    Pair t1 _ = coercionKind base
    k1        = typeKind t1

-- | See arguments.
mkCoherenceLeftCo :: Coercion   -- ^ :: t1 ~r t2, where t1 :: k1 & t2 :: k2
                  -> Coercion   -- ^ :: k1' ~r k2
                  -> Coercion   -- ^ co :: k1 ~R k1'
                  -> Coercion   -- ^ :: (t1 |> co) ~r t2
mkCoherenceLeftCo base _ (Refl {}) = base
mkCoherenceLeftCo base kind co
  = CoherenceCo { coh_base = base, coh_kind = kind, coh_left = left
                , coh_right = mkReflCo Representational k2 }
  where
    Pair _ t2 = coercionKind base
    k2        = typeKind t2

mkKindCo :: Coercion -> Coercion
mkKindCo (Refl _ ty) = Refl Representational (typeKind ty)
mkKindCo co
  | Pair ty1 ty2 <- coercionKind co  -- TODO (RAE): This looks inefficient.
  , typeKind ty1 `eqType` typeKind ty2
  = Refl Representational (typeKind ty1)
  | otherwise
  = KindCo co

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
setRoleArg_maybe r1 r2 (TyCoArg co) = fmap TyCoArg (downgradeRole_maybe r1 r2 co)
setRoleArg_maybe r  _  (CoCoArg _ co1 co2) = Just $ CoCoArg r co1 co2

-- | Like 'downgradeRole', but for 'CoercionArg's
downgradeRoleArg :: Role -> Role -> CoercionArg -> CoercionArg
downgradeRoleArg r1 r2 arg
  | Just arg' <- setRoleArg_maybe r1 r2 arg
  = arg'
  | otherwise
  = pprPanic "downgradeRoleArg" (ppr arg)

mkAxiomRuleCo :: CoAxiomRule -> [Type] -> [Coercion] -> Coercion
mkAxiomRuleCo = AxiomRuleCo

-- | Coercion used as a placeholder in erased types
bulletCo :: Coercion
bulletCo = Refl Nominal unitTy

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
setNominalRole_maybe (AppCo co1 co2)
  = AppCo <$> setNominalRole_maybe co1 <*> pure co2
setNominalRole_maybe (ForAllCo cobndr co)
  = ForAllCo <$> setNominalRoleCoBndr_maybe cobndr <*> setNominalRole_maybe co
setNominalRole_maybe (NthCo n co)
  = NthCo n <$> setNominalRole_maybe co
setNominalRole_maybe (InstCo co arg)
  = InstCo <$> setNominalRole_maybe co <*> pure arg
setNominalRole_maybe co@(CoherenceCo { coh_base = base, coh_kind = kind })
  = do { base' <- setNominalRole_maybe base
       ; kind' <- setNominalRole_maybe kind
       ; return (co { coh_base = base', coh_kind = kind' }) }
setNominalRole_maybe _ = Nothing

-- | Makes a 'CoercionArg' become nominal, if possible
setNominalRoleArg_maybe :: CoercionArg -> Maybe CoercionArg
setNominalRoleArg_maybe (TyCoArg co)      = fmap TyCoArg (setNominalRole_maybe co)
setNominalRoleArg_maybe (CoCoArg _ c1 c2) = Just $ CoCoArg Nominal c1 c2

-- | Makes a 'ForAllCoBndr' become nominal, if possible
setNominalRoleCoBndr_maybe :: ForAllCoBndr -> Maybe ForAllCoBndr
setNominalRoleCoBndr_maybe cobndr@(TyHomo {}) = Just cobndr
setNominalRoleCoBndr_maybe (TyHetero h tv1 tv2 cv) =
  TyHetero <$> setNominalRole_maybe h <*> pure tv1 <*> pure tv2 <*> pure cv
setNominalRoleCoBndr_maybe cobndr@(CoHomo {}) = Just cobndr
setNominalRoleCoBndr_maybe (CoHetero h cv1 cv2) =
  CoHetero <$> setNominalRole_maybe h <*> pure cv1 <*> pure cv2

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
    mkPhantomCo (mkReflCo Representational k1) t1 t2
  where
    k1 = typeKind t1

-- takes any coercion and turns it into a Phantom coercion
toPhantomCo :: Coercion -> Coercion
toPhantomCo co
  | Just (ty, _) <- isReflCo_maybe co = Refl Phantom ty
  | Pair ty1 ty2 <- coercionKind co   = PhantomCo (KindCo co) ty1 ty2
  -- don't optimise here... wait for OptCoercion

toPhantomCoArg :: CoercionArg -> CoercionArg
toPhantomCoArg (TyCoArg co)        = TyCoArg (toPhantomCo co)
toPhantomCoArg (CoCoArg _ co1 co2) = CoCoArg Phantom co1 co2

-- All input coercions are assumed to be Nominal,
-- or, if Role is Phantom, the Coercion can be Phantom, too.
applyRole :: Role -> CoercionArg -> CoercionArg
applyRole r (CoCoArg _ c1 c2) = CoCoArg r c1 c2
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

{-
%************************************************************************
%*                                                                      *
   ForAllCoBndr
%*                                                                      *
%************************************************************************
-}

-- | Makes homogeneous ForAllCoBndr, choosing between TyHomo and CoHomo
-- based on the nature of the TyCoVar
mkHomoCoBndr :: TyCoVar -> ForAllCoBndr
mkHomoCoBndr v
  | isTyVar v = TyHomo v
  | otherwise = CoHomo v

getHomoVar :: ForAllCoBndr -> TyCoVar
getHomoVar cobndr
  | Just v <- getHomoVar_maybe cobndr = v
  | otherwise                          = pprPanic "getHomoVar" (ppr cobndr)

getHomoVar_maybe :: ForAllCoBndr -> Maybe TyCoVar
getHomoVar_maybe (TyHomo tv) = Just tv
getHomoVar_maybe (CoHomo cv) = Just cv
getHomoVar_maybe _           = Nothing

-- | Split up a hetero cobndr. The role of the coercion depends on the
-- nature of the cobndr -- don't rely on it!
splitHeteroCoBndr_maybe :: ForAllCoBndr -> Maybe (Coercion, TyCoVar, TyCoVar)
splitHeteroCoBndr_maybe (TyHetero eta tv1 tv2 _) = Just (eta, tv1, tv2)
splitHeteroCoBndr_maybe (CoHetero eta cv1 cv2)   = Just (eta, cv1, cv2)
splitHeteroCoBndr_maybe _                        = Nothing

coBndrBoundVars :: ForAllCoBndr -> (TyCoVar, TyCoVar)
coBndrBoundVars (TyHomo tv)            = (tv,  tv)
coBndrBoundVars (TyHetero _ tv1 tv2 _) = (tv1, tv2)
coBndrBoundVars (CoHomo cv)            = (cv,  cv)
coBndrBoundVars (CoHetero _ cv1 cv2)   = (cv1, cv2)

isHomoCoBndr :: ForAllCoBndr -> Bool
isHomoCoBndr (TyHomo {}) = True
isHomoCoBndr (CoHomo {}) = True
isHomoCoBndr _           = False

-- | Retrive the "eta" coercion from a cobndr.
getHeteroKindCo :: ForAllCoBndr -> Coercion
getHeteroKindCo (TyHetero eta _ _ _) = eta
getHeteroKindCo (CoHetero eta _ _) = eta
getHeteroKindCo cobndr = pprPanic "getHeteroKindCo" (ppr cobndr)

mkTyHeteroCoBndr :: Coercion -> TyVar -> TyVar -> CoVar -> ForAllCoBndr
mkTyHeteroCoBndr h tv1 tv2 cv
  = ASSERT( _hty1 `eqType` (tyVarKind tv1) )
    ASSERT( _hty2 `eqType` (tyVarKind tv2) )
    ASSERT( coVarKind cv `eqType` (mkCoercionType Nominal (mkOnlyTyVarTy tv1) (mkOnlyTyVarTy tv2)) )
    TyHetero h tv1 tv2 cv
    where Pair _hty1 _hty2 = coercionKind h

mkCoHeteroCoBndr :: Coercion -> CoVar -> CoVar -> ForAllCoBndr
mkCoHeteroCoBndr h cv1 cv2
  = ASSERT( _hty1 `eqType` (coVarKind cv1) )
    ASSERT( _hty2 `eqType` (coVarKind cv2) )
    CoHetero h cv1 cv2
    where Pair _hty1 _hty2 = coercionKind h

-------------------------------

-- | like mkKindCo, but aggressively & recursively optimizes to avoid using
-- a KindCo constructor. The output role is representational.
promoteCoercion :: Coercion -> Coercion

-- First cases handles anything that should yield refl. The ASSERT( False )s throughout
-- are these cases explicitly, but they should never fire.
promoteCoercion co
  | Pair ty1 ty2 <- coercionKind co
  , (typeKind ty1) `eqType` (typeKind ty2)
  = mkReflCo Representational (typeKind ty1)

-- These should never return refl.
promoteCoercion (Refl _ ty) = ASSERT( False )
                              mkReflCo Representational (typeKind ty)
promoteCoercion g@(TyConAppCo _ tc args)
  | Just co' <- instCoercions (mkReflCo Representational (tyConKind tc)) args
  = co'
  | otherwise
  = mkKindCo g
promoteCoercion g@(AppCo co arg)
  | Just co' <- instCoercion (promoteCoercion co) arg
  = co'
  | otherwise
  = mkKindCo g
promoteCoercion (ForAllCo _ g)
  = ASSERT( False ) mkReflCo (coercionRole g) liftedTypeKind
promoteCoercion g@(CoVarCo {})     = mkKindCo g
promoteCoercion g@(AxiomInstCo {}) = mkKindCo g
promoteCoercion (PhantomCo co _ _) = co
promoteCoercion (UnsafeCo s _ t1 t2)
  = mkUnsafeCo s Representational (typeKind t1) (typeKind t2)
promoteCoercion (SymCo co)         = mkSymCo (promoteCoercion co)
promoteCoercion (TransCo co1 co2)  = mkTransCo (promoteCoercion co1)
                                               (promoteCoercion co2)
promoteCoercion g@(NthCo n co)
  | Just (_, args) <- splitTyConAppCo_maybe co
  , n < length args
  = case args !! n of
      TyCoArg co1   -> promoteCoercion co1
      CoCoArg _ _ _ -> pprPanic "promoteCoercion" (ppr g)
  | Just _ <- splitForAllCo_maybe co
  , n == 0
  = ASSERT( False ) mkReflCo Representational liftedTypeKind
  | otherwise
  = mkKindCo g
promoteCoercion g@(LRCo lr co)
  | Just (lco, rarg) <- splitAppCo_maybe co
  = case lr of
      CLeft  -> promoteCoercion lco
      CRight -> case rarg of
        TyCoArg co1 -> promoteCoercion co1
        CoCoArg _ _ _ -> pprPanic "promoteCoercion" (ppr g)
  | otherwise
  = mkKindCo g
promoteCoercion (InstCo g _) = promoteCoercion g
promoteCoercion (CoherenceCo { coh_kind = kind }) = kind
promoteCoercion (KindCo _)
  = ASSERT( False ) mkReflCo Representational liftedTypeKind
promoteCoercion (SubCo g)         = promoteCoercion g
promoteCoercion g@(AxiomRuleCo {})= mkKindCo g

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
mkPiCo r v co | isTyVar v = mkForAllCo_TyHomo v co
              | isCoVar v = mkForAllCo_CoHomo v co
              | otherwise = mkFunCo r (mkReflCo r (varType v)) co

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

mkCoCoArg :: Role -> Coercion -> Coercion -> CoercionArg
mkCoCoArg = CoCoArg

isTyCoArg :: CoercionArg -> Bool
isTyCoArg (TyCoArg _) = True
isTyCoArg _           = False

stripTyCoArg :: CoercionArg -> Coercion
stripTyCoArg (TyCoArg co) = co
stripTyCoArg arg          = pprPanic "stripTyCoArg" (ppr arg)

stripCoCoArg :: CoercionArg -> Pair Coercion
stripCoCoArg (CoCoArg _ co1 co2) = Pair co1 co2
stripCoCoArg arg                 = pprPanic "stripCoCoArg" (ppr arg)

splitCoCoArg_maybe :: CoercionArg -> Maybe (Coercion, Coercion)
splitCoCoArg_maybe (TyCoArg _)       = Nothing
splitCoCoArg_maybe (CoCoArg _ c1 c2) = Just (c1, c2)

-- | Makes a suitable CoercionArg representing the passed-in variable
-- during a lifting-like substitution. Output is Nominal.
mkCoArgForVar :: TyCoVar -> CoercionArg
mkCoArgForVar v
  | isTyVar v = TyCoArg $ mkReflCo Nominal $ mkOnlyTyVarTy v
  | otherwise = CoCoArg Nominal (mkCoVarCo v) (mkCoVarCo v)

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
eqCoercion c1 c2 = isEqual $ cmpCoercion c1 c2
  
-- | Compare two 'Coercion's, with respect to an RnEnv2
eqCoercionX :: RnEnv2 -> Coercion -> Coercion -> Bool
eqCoercionX env c1 c2 = isEqual $ cmpCoercionX env c1 c2

-- | Substitute within several 'Coercion's
cmpCoercion :: Coercion -> Coercion -> Ordering
cmpCoercion c1 c2 = cmpCoercionX rn_env c1 c2
  where rn_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfCo c1 `unionVarSet` tyCoVarsOfCo c2))

cmpCoercionX :: RnEnv2 -> Coercion -> Coercion -> Ordering
cmpCoercionX env (Refl r1 ty1)                (Refl r2 ty2)
  = cmpTypeX env ty1 ty2 `thenCmp` compare r1 r2
cmpCoercionX env (TyConAppCo r1 tc1 args1)    (TyConAppCo r2 tc2 args2)
  = (tc1 `cmpTc` tc2) `thenCmp` cmpCoercionArgsX env args1 args2 `thenCmp` compare r1 r2
cmpCoercionX env (AppCo co1 arg1)             (AppCo co2 arg2)
  = cmpCoercionX env co1 co2 `thenCmp` cmpCoercionArgX env arg1 arg2
cmpCoercionX env (ForAllCo cobndr1 co1)       (ForAllCo cobndr2 co2)
  = cmpCoBndrX env cobndr1 cobndr2 `thenCmp`
    cmpCoercionX (rnCoBndr2 env cobndr1 cobndr2) co1 co2
cmpCoercionX env (CoVarCo cv1)                (CoVarCo cv2)
  = rnOccL env cv1 `compare` rnOccR env cv2
cmpCoercionX env (AxiomInstCo ax1 ind1 args1) (AxiomInstCo ax2 ind2 args2)
  = (ax1 `cmpByUnique` ax2) `thenCmp`
    (ind1 `compare` ind2) `thenCmp`
    cmpCoercionArgsX env args1 args2
cmpCoercionX env (PhantomCo h1 t1 s1)         (PhantomCo h2 t2 s2)
  = cmpCoercionX env h1 h2 `thenCmp` cmpTypeX env t1 t2 `thenCmp` cmpTypeX env s1 s2
-- the provenance string is just a note, so don't use in comparisons
cmpCoercionX env (UnsafeCo _ r1 tyl1 tyr1)    (UnsafeCo _ r2 tyl2 tyr2)
  = cmpTypeX env tyl1 tyl2 `thenCmp` cmpTypeX env tyr1 tyr2 `thenCmp` compare r1 r2
cmpCoercionX env (SymCo co1)                  (SymCo co2)
  = cmpCoercionX env co1 co2
cmpCoercionX env (TransCo col1 cor1)          (TransCo col2 cor2)
  = cmpCoercionX env col1 col2 `thenCmp` cmpCoercionX env cor1 cor2
cmpCoercionX env (NthCo n1 co1)               (NthCo n2 co2)
  = (n1 `compare` n2) `thenCmp` cmpCoercionX env co1 co2
cmpCoercionX env (InstCo co1 arg1)            (InstCo co2 arg2)
  = cmpCoercionX env co1 co2 `thenCmp` cmpCoercionArgX env arg1 arg2
cmpCoercionX env (CoherenceCo col1 cor1)      (CoherenceCo col2 cor2)
  = cmpCoercionX env col1 col2 `thenCmp` cmpCoercionX env cor1 cor2
cmpCoercionX env (KindCo co1)                 (KindCo co2)
  = cmpCoercionX env co1 co2
cmpCoercionX env (SubCo co1)                  (SubCo co2)
  = cmpCoercionX env co1 co2
cmpCoercionX env (AxiomRuleCo a1 ts1 cs1)     (AxiomRuleCo a2 ts2 cs2)
  = cmpByUnique a1 a2
    `thenCmp` cmpTypesX env ts1 ts2
    `thenCmp` cmpCoercionsX env cs1 cs2

-- Deal with the rest, in constructor order
-- Refl < TyConAppCo < AppCo < ForAllCo < CoVarCo < AxiomInstCo <
--  PhantomCo < UnsafeCo < SymCo < TransCo < NthCo < LRCo <
--  InstCo < CoherenceCo < KindCo < SubCo < AxiomRuleCo
cmpCoercionX _ co1 co2
  = (get_rank co1) `compare` (get_rank co2)
  where get_rank :: Coercion -> Int
        get_rank (Refl {})        = 0
        get_rank (TyConAppCo {})  = 1
        get_rank (AppCo {})       = 2
        get_rank (ForAllCo {})    = 3
        get_rank (CoVarCo {})     = 4
        get_rank (AxiomInstCo {}) = 5
        get_rank (PhantomCo {})   = 6
        get_rank (UnsafeCo {})    = 7
        get_rank (SymCo {})       = 8
        get_rank (TransCo {})     = 9
        get_rank (NthCo {})       = 10
        get_rank (LRCo {})        = 11
        get_rank (InstCo {})      = 12
        get_rank (CoherenceCo {}) = 13
        get_rank (KindCo {})      = 14
        get_rank (SubCo {})       = 15
        get_rank (AxiomRuleCo {}) = 16

cmpCoercionsX :: RnEnv2 -> [Coercion] -> [Coercion] -> Ordering
cmpCoercionsX _   []        []        = EQ
cmpCoercionsX env (c1:cos1) (c2:cos2)
  = cmpCoercionX env c1 c2 `thenCmp` cmpCoercionsX env cos1 cos2
cmpCoercionsX _   []        _         = LT
cmpCoercionsX _   _         []        = GT


eqCoercionArg :: CoercionArg -> CoercionArg -> Bool
eqCoercionArg arg1 arg2 = isEqual $ cmpCoercionArgX rn_env arg1 arg2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfCoArg arg1 `unionVarSet`
                                     tyCoVarsOfCoArg arg2))

cmpCoercionArgX :: RnEnv2 -> CoercionArg -> CoercionArg -> Ordering
cmpCoercionArgX env (TyCoArg co1)          (TyCoArg co2)
  = cmpCoercionX env co1 co2
cmpCoercionArgX env (CoCoArg r1 col1 cor1) (CoCoArg r2 col2 cor2)
  = cmpCoercionX env col1 col2
    `thenCmp` cmpCoercionX env cor1 cor2
    `thenCmp` compare r1 r2
cmpCoercionArgX _ (TyCoArg {}) (CoCoArg {}) = LT
cmpCoercionArgX _ (CoCoArg {}) (TyCoArg {}) = GT

cmpCoercionArgsX :: RnEnv2 -> [CoercionArg] -> [CoercionArg] -> Ordering
cmpCoercionArgsX _ [] [] = EQ
cmpCoercionArgsX env (arg1:args1) (arg2:args2)
  = cmpCoercionArgX env arg1 arg2 `thenCmp` cmpCoercionArgsX env args1 args2
cmpCoercionArgsX _ [] _  = LT
cmpCoercionArgsX _ _  [] = GT

cmpCoBndrX :: RnEnv2 -> ForAllCoBndr -> ForAllCoBndr -> Ordering
cmpCoBndrX env (TyHomo tv1) (TyHomo tv2)
  = cmpTypeX env (tyVarKind tv1) (tyVarKind tv2)
cmpCoBndrX env (TyHetero co1 tvl1 tvr1 cv1) (TyHetero co2 tvl2 tvr2 cv2)
  = cmpCoercionX env co1 co2 `thenCmp`
    cmpTypeX env (tyVarKind tvl1) (tyVarKind tvl2) `thenCmp`
    cmpTypeX env (tyVarKind tvr1) (tyVarKind tvr2) `thenCmp`
    cmpTypeX env (coVarKind cv1)  (coVarKind cv2)
cmpCoBndrX env (CoHomo cv1) (CoHomo cv2)
  = cmpTypeX env (coVarKind cv1) (coVarKind cv2)
cmpCoBndrX env (CoHetero co1 cvl1 cvr1) (CoHetero co2 cvl2 cvr2)
  = cmpCoercionX env co1 co2 `thenCmp`
    cmpTypeX env (coVarKind cvl1) (coVarKind cvl2) `thenCmp`
    cmpTypeX env (coVarKind cvr1) (coVarKind cvr2)
cmpCoBndrX _ cobndr1 cobndr2
  = (get_rank cobndr1) `compare` (get_rank cobndr2)
  where get_rank :: ForAllCoBndr -> Int
        get_rank (TyHomo {})   = 0
        get_rank (TyHetero {}) = 1
        get_rank (CoHomo {})   = 2
        get_rank (CoHetero {}) = 3

rnCoBndr2 :: RnEnv2 -> ForAllCoBndr -> ForAllCoBndr -> RnEnv2
rnCoBndr2 env cobndr1 cobndr2
  = foldl2 rnBndr2 env (coBndrVars cobndr1) (coBndrVars cobndr2)

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
  = let k    = tyVarKind v
        k_co = liftCoSubst Nominal lc k
        co   = mkCoherenceCo (mkReflCo Nominal ty) k_co
                             (mkReflCo Representational k) (mkSubCo k_co)
                            
        lc' = LC (in_scope `extendInScopeSetSet` tyCoVarsOfType ty)
                 (extendVarEnv env v (TyCoArg co))
    in extendLiftingContextEx lc' rest
  | CoercionTy co <- ty
  = let (_, _, s1, s2, r) = coVarKindsTypesRole v
        lc' = LC (in_scope `extendInScopeSetSet` tyCoVarsOfCo co)
                 (extendVarEnv env v (CoCoArg Nominal co $
                                         (mkSymCo (ty_co_subst lc r s1)) `mkTransCo`
                                         co `mkTransCo`
                                         (ty_co_subst lc r s2)))
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
    go r (AppTy ty1 ty2)   = mkAppCo (go r ty1) (go_arg Nominal ty2)
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
    go_arg r (CoercionTy co) = CoCoArg r (substLeftCo lc co) (substRightCo lc co)
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
  = Just $ liftSimply r (mkTyCoVarTy v)

liftCoSubstVarBndr :: Role -> LiftingContext -> TyCoVar
                     -> (LiftingContext, ForAllCoBndr)
liftCoSubstVarBndr = liftCoSubstVarBndrCallback ty_co_subst False

liftCoSubstVarBndrCallback :: (LiftingContext -> Role -> Type -> Coercion)
                           -> Bool -- ^ True <=> homogenize TyHetero substs
                                   -- see Note [Normalising types] in FamInstEnv
                           -> Role -- ^ output rule; not Phantom
                           -> LiftingContext -> TyCoVar
                           -> (LiftingContext, ForAllCoBndr)
liftCoSubstVarBndrCallback fun homo r lc@(LC in_scope cenv) old_var
  = (LC (in_scope `extendInScopeSetList` coBndrVars cobndr) new_cenv, cobndr)
  where
    eta        = fun lc r (tyVarKind old_var)
    Pair k1 k2 = coercionKind eta
    new_var    = uniqAway in_scope (setVarType old_var k1)

    (new_cenv, cobndr)
      | new_var == old_var
      , isEmptyVarSet (tyCoVarsOfType (tyVarKind old_var))
      , k1 `eqType` k2
      = (delVarEnv cenv old_var, mkHomoCoBndr old_var)

      | k1 `eqType` k2
        -- mkCoArgForVar returns a Nominal coercion. This is good here
        -- because Nominal is the most expressive one. Remember: when
        -- the coercion actually gets subst'ed in during lifting, we
        -- re-check the roles and apply a SubCo if necessary
      = (extendVarEnv cenv old_var (mkCoArgForVar new_var), mkHomoCoBndr new_var)

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
        , mkTyHeteroCoBndr eta a1 a2 c )

      | otherwise
      = let cv1 = new_var
            in_scope1 = in_scope `extendInScopeSet` cv1
            cv2 = uniqAway in_scope1 $ setVarType new_var k2
              -- cv_eta is like eta, but its role matches cv1/2
            cv_eta = case (coVarRole cv1, r) of
                       (r1, r2) | r1 == r2       -> eta
                                | r2 `ltRole` r1 -> downgradeRole r1 r2 eta
                                | otherwise      -> fun lc r1 (tyVarKind old_var)
            lifted_r = if homo
                       then mkNthCo 2 cv_eta
                            `mkTransCo` (mkCoVarCo cv2)
                            `mkTransCo` mkNthCo 3 (mkSymCo cv_eta)
                       else mkCoVarCo cv2
        in
        ( extendVarEnv cenv old_var (CoCoArg Nominal (mkCoVarCo cv1) lifted_r)
        , mkCoHeteroCoBndr cv_eta cv1 cv2 )

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

-- | all types that are not coercions get lifted into TyCoArg (Refl ty)
-- a coercion (g :: t1 ~ t2) becomes (CoCoArg (Refl t1) (Refl t2)).
-- If you need to convert a Type to a CoercionArg and you are tempted to
-- just call Refl, then you want this.
liftSimply :: Role -> Type -> CoercionArg
liftSimply r (CoercionTy co)
  = let Pair t1 t2 = coercionKind co in
  -- TODO (RAE): Should these be Nominal? How does the choice matter??
    CoCoArg r (mkReflCo Nominal t1) (mkReflCo Nominal t2)
liftSimply r ty = TyCoArg $ mkReflCo r ty

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
seqCo (AppCo co1 co2)       = seqCo co1 `seq` seqCoArg co2
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
seqCo (CoherenceCo a b c d) = seqCos [a,b,c,d]
seqCo (KindCo co)           = seqCo co
seqCo (SubCo co)            = seqCo co
seqCo (AxiomRuleCo _ ts cs) = seqTypes ts `seq` seqCos cs

seqCos :: [Coercion] -> ()
seqCos []       = ()
seqCos (co:cos) = seqCo co `seq` seqCos cos

seqCoArg :: CoercionArg -> ()
seqCoArg (TyCoArg co)        = seqCo co
seqCoArg (CoCoArg r co1 co2) = r `seq` seqCo co1 `seq` seqCo co2

seqCoArgs :: [CoercionArg] -> ()
seqCoArgs []         = ()
seqCoArgs (arg:args) = seqCoArg arg `seq` seqCoArgs args

seqCoBndr :: ForAllCoBndr -> ()
seqCoBndr (TyHomo tv) = tv `seq` ()
seqCoBndr (TyHetero h tv1 tv2 cv) = seqCo h `seq` tv1 `seq` tv2 `seq` cv `seq` ()
seqCoBndr (CoHomo cv) = cv `seq` ()
seqCoBndr (CoHetero h cv1 cv2) = seqCo h `seq` cv1 `seq` cv2 `seq` ()

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
    go (AppCo co1 co2)      = mkAppTy <$> go co1 <*> coercionArgKind co2
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
    go (CoherenceCo { coh_base = co, coh_left = l, coh_right = r })
      = mkCastTy <$> go co <*> Pair l r
    go (KindCo co)          = typeKind <$> go co
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
coercionArgKind (TyCoArg co)        = coercionKind co
coercionArgKind (CoCoArg _ co1 co2) = Pair (CoercionTy co1) (CoercionTy co2)

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
    go (AppCo co1 co2)
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
    go (CoherenceCo { coh_base = co, coh_left = left, coh_right = right})
      = let (tys, role) = go co in
        (mkCastTy <$> tys <*> Pair left right, role) 
    go co@(KindCo {}) = (coercionKind co, Representational)
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
coercionArgKindRole (TyCoArg co)        = coercionKindRole co
coercionArgKindRole (CoCoArg r co1 co2) = (CoercionTy <$> Pair co1 co2, r)

-- | Get a 'CoercionArg's role.
coercionArgRole :: CoercionArg -> Role
coercionArgRole = snd . coercionArgKindRole

-- | Get the pair of vars bound by a 'ForAllCo'
coBndrKind :: ForAllCoBndr -> Pair Var
coBndrKind (TyHomo tv)            = pure tv
coBndrKind (TyHetero _ tv1 tv2 _) = Pair tv1 tv2
coBndrKind (CoHomo cv)            = pure cv
coBndrKind (CoHetero _ cv1 cv2)   = Pair cv1 cv2

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
              r_tv' = setTyVarKind r_tv (substTy t_sub (tyVarKind t_tv))
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

