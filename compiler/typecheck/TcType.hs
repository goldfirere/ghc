{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

\section[TcType]{Types used in the typechecker}

This module provides the Type interface for front-end parts of the
compiler.  These parts

        * treat "source types" as opaque:
                newtypes, and predicates are meaningful.
        * look through usage types

The "tc" prefix is for "TypeChecker", because the type checker
is the principal client.
-}

{-# LANGUAGE CPP #-}

module TcType (
  --------------------------------
  -- Types
  TcType, TcSigmaType, TcRhoType, TcTauType, TcPredType, TcThetaType,
  TcTyVar, TcTyVarSet, TcTyCoVarSet, TcKind, TcCoVar, TcTyCoVar,

  -- TcLevel
  TcLevel(..), topTcLevel, pushTcLevel, isTopTcLevel,
  strictlyDeeperThan, sameDepthAs, fskTcLevel,

  --------------------------------
  -- MetaDetails
  UserTypeCtxt(..), pprUserTypeCtxt, pprSigCtxt,
  TcTyVarDetails(..), pprTcTyVarDetails, vanillaSkolemTv, superSkolemTv,
  MetaDetails(Flexi, Indirect), MetaInfo(..),
  isImmutableTyVar, isSkolemTyVar, isSkolemTyCoVar,
  isMetaTyVar,  isMetaTyVarTy, isTyVarTy, isReturnTyVar,
  isSigTyVar, isOverlappableTyVar,  isTyConableTyVar, 
  isFskTyVar, isFmvTyVar, isFlattenTyVar, 
  isAmbiguousTyVar, metaTvRef, metaTyVarInfo,
  isFlexi, isIndirect, isRuntimeUnkSkol,
  metaTyVarTcLevel, setMetaTyVarTcLevel, metaTyVarTcLevel_maybe,
  isTouchableMetaTyVar, isTouchableOrFmv,
  isFloatedTouchableMetaTyVar,
  canUnifyWithPolyType,

  --------------------------------
  -- Builders
  mkPhiTy, mkInvSigmaTy, mkSigmaTy,
  mkTcEqPred, mkTcReprEqPred, mkTcEqPredBR,
  mkNakedTyConApp, mkNakedAppTys, mkNakedAppTy, mkNakedFunTy,
  mkNakedInvSigmaTy, mkNakedCastTy,

  --------------------------------
  -- Splitters
  -- These are important because they do not look through newtypes
  tcView, getTyVar,
  tcSplitForAllTys, tcSplitNamedForAllTys, tcSplitNamedForAllTysB,
  tcIsNamedForAllTy,
  tcSplitPhiTy, tcSplitPredFunTy_maybe,
  tcSplitFunTy_maybe, tcSplitFunTys, tcFunArgTy, tcFunResultTy, tcSplitFunTysN,
  tcSplitTyConApp, tcSplitTyConApp_maybe, tcTyConAppTyCon, tcTyConAppArgs,
  tcSplitAppTy_maybe, tcSplitAppTy, tcSplitAppTys, repSplitAppTy_maybe,
  tcInstHeadTyNotSynonym, tcInstHeadTyAppAllTyVars,
  tcGetTyVar_maybe, tcGetTyCoVar_maybe, tcGetTyVar, nextRole,
  tcSplitSigmaTy, tcDeepSplitSigmaTy_maybe,
  tcSplitCastTy_maybe,

  ---------------------------------
  -- Predicates.
  -- Again, newtypes are opaque
  eqType, eqTypes, cmpType, cmpTypes, eqTypeX,
  pickyEqType, tcEqType, tcEqKind, tcEqTypeNoKindCheck, tcEqTypeVis,
  isSigmaTy, isRhoTy, isOverloadedTy,
  isDoubleTy, isFloatTy, isIntTy, isWordTy, isStringTy,
  isIntegerTy, isBoolTy, isUnitTy, isCharTy,
  isTauTy, isTauTyCon, tcIsTyVarTy, tcIsForAllTy,
  isPredTy, isTyVarClassPred, isTyVarExposed,

  ---------------------------------
  -- Misc type manipulators
  deNoteType, occurCheckExpand, OccCheckResult(..),
  orphNamesOfType, orphNamesOfDFunHead, orphNamesOfCo,
  orphNamesOfTypes, orphNamesOfCoCon,
  getDFunTyKey,
  evVarPred_maybe, evVarPred,
  mkEqBoxTy,

  ---------------------------------
  -- Predicate types
  mkMinimalBySCs, transSuperClasses, immSuperClasses,
  quantifyPred,

  -- * Finding type instances
  tcTyFamInsts,

  -- * Finding "exact" (non-dead) type variables
  exactTyCoVarsOfType, exactTyCoVarsOfTypes,

  ---------------------------------
  -- Foreign import and export
  isFFIArgumentTy,     -- :: DynFlags -> Safety -> Type -> Bool
  isFFIImportResultTy, -- :: DynFlags -> Type -> Bool
  isFFIExportResultTy, -- :: Type -> Bool
  isFFIExternalTy,     -- :: Type -> Bool
  isFFIDynTy,          -- :: Type -> Type -> Bool
  isFFIPrimArgumentTy, -- :: DynFlags -> Type -> Bool
  isFFIPrimResultTy,   -- :: DynFlags -> Type -> Bool
  isFFILabelTy,        -- :: Type -> Bool
  isFFITy,             -- :: Type -> Bool
  isFunPtrTy,          -- :: Type -> Bool
  tcSplitIOType_maybe, -- :: Type -> Maybe Type

  --------------------------------
  -- Rexported from Kind
  Kind, typeKind,
  unliftedTypeKind, liftedTypeKind,
  constraintKind, mkArrowKind, mkArrowKinds,
  isLiftedTypeKind, isUnliftedTypeKind, classifiesTypeWithValues,

  --------------------------------
  -- Rexported from Type
  Type, PredType, ThetaType, Binder, VisibilityFlag(..),

  mkForAllTy, mkForAllTys, mkInvForAllTys, mkNamedForAllTy,
  mkFunTy, mkFunTys,
  mkTyConApp, mkAppTy, mkAppTys, applyTys,
  mkTyCoVarTy, mkTyCoVarTys, mkTyConTy, mkOnlyTyVarTy,
  mkOnlyTyVarTys,

  isClassPred, isEqPred, isNomEqPred, isIPPred,
  mkClassPred,
  isDictLikeTy,
  tcSplitDFunTy, tcSplitDFunHead,
  mkEqPred, isLevityVar, isSortPolymorphic, isSortPolymorphic_maybe,

  -- Type substitutions
  TCvSubst(..),         -- Representation visible to a few friends
  TvSubstEnv, emptyTCvSubst,
  mkOpenTCvSubst, zipOpenTCvSubst, zipTopTCvSubst,
  mkTopTCvSubst, notElemTCvSubst, unionTCvSubst,
  getTvSubstEnv, setTvSubstEnv, getTCvInScope, extendTCvInScope,
  Type.lookupTyVar, Type.lookupVar, Type.extendTCvSubst, Type.substTyVarBndr,
  extendTCvSubstList, isInScope, mkTCvSubst, zipTyCoEnv,
  Type.substTy, substTys, substTyWith, substTheta, substTyCoVar, substTyCoVars,

  isUnLiftedType,       -- Source types are always lifted
  isUnboxedTupleType,   -- Ditto
  isPrimitiveType,

  tyCoVarsOfType, tyCoVarsOfTypes,
  closeOverKinds,
  
  pprKind, pprParendKind, pprSigmaType,
  pprType, pprParendType, pprTypeApp, pprTyThingCategory,
  pprTheta, pprThetaArrowTy, pprClassPred

  ) where

#include "HsVersions.h"

-- friends:
import Kind
import TyCoRep
import Class
import Var
import ForeignCall
import VarSet
import Coercion
import Type
import TyCon
import CoAxiom

-- others:
import DynFlags
import Name -- hiding (varName)
            -- We use this to make dictionaries for type literals.
            -- Perhaps there's a better way to do this?
import NameSet
import VarEnv
import PrelNames
import TysWiredIn
import DataCon     ( promoteDataCon )
import BasicTypes
import Util
import Maybes
import ListSetOps
import Outputable
import FastString
import Pair
import ErrUtils( Validity(..), isValid )

import Data.IORef
import Control.Monad (liftM, ap)
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative (Applicative(..))
#endif

{-
************************************************************************
*                                                                      *
\subsection{Types}
*                                                                      *
************************************************************************

The type checker divides the generic Type world into the
following more structured beasts:

sigma ::= forall tyvars. phi
        -- A sigma type is a qualified type
        --
        -- Note that even if 'tyvars' is empty, theta
        -- may not be: e.g.   (?x::Int) => Int

        -- Note that 'sigma' is in prenex form:
        -- all the foralls are at the front.
        -- A 'phi' type has no foralls to the right of
        -- an arrow

phi :: theta => rho

rho ::= sigma -> rho
     |  tau

-- A 'tau' type has no quantification anywhere
-- Note that the args of a type constructor must be taus
tau ::= tyvar
     |  tycon tau_1 .. tau_n
     |  tau_1 tau_2
     |  tau_1 -> tau_2

-- In all cases, a (saturated) type synonym application is legal,
-- provided it expands to the required form.
-}

type TcTyVar = TyVar    -- Used only during type inference
type TcCoVar = CoVar    -- Used only during type inference
type TcType = Type      -- A TcType can have mutable type variables
type TcTyCoVar = Var    -- Either a TcTyVar or a CoVar
        -- Invariant on ForAllTy in TcTypes:
        --      forall a. T
        -- a cannot occur inside a MutTyVar in T; that is,
        -- T is "flattened" before quantifying over a

-- These types do not have boxy type variables in them
type TcPredType     = PredType
type TcThetaType    = ThetaType
type TcSigmaType    = TcType
type TcRhoType      = TcType  -- Note [TcRhoType]
type TcTauType      = TcType
type TcKind         = Kind
type TcTyVarSet     = TyVarSet
type TcTyCoVarSet   = TyCoVarSet

{-
Note [TcRhoType]
~~~~~~~~~~~~~~~~
A TcRhoType has no foralls or contexts at the top, or to the right of an arrow
  YES    (forall a. a->a) -> Int
  NO     forall a. a ->  Int
  NO     Eq a => a -> a
  NO     Int -> forall a. a -> Int


************************************************************************
*                                                                      *
\subsection{TyVarDetails}
*                                                                      *
************************************************************************

TyVarDetails gives extra info about type variables, used during type
checking.  It's attached to mutable type variables only.
It's knot-tied back to Var.lhs.  There is no reason in principle
why Var.lhs shouldn't actually have the definition, but it "belongs" here.

Note [Signature skolems]
~~~~~~~~~~~~~~~~~~~~~~~~
Consider this

  f :: forall a. [a] -> Int
  f (x::b : xs) = 3

Here 'b' is a lexically scoped type variable, but it turns out to be
the same as the skolem 'a'.  So we have a special kind of skolem
constant, SigTv, which can unify with other SigTvs. They are used
*only* for pattern type signatures.

Similarly consider
  data T (a:k1) = MkT (S a)
  data S (b:k2) = MkS (T b)
When doing kind inference on {S,T} we don't want *skolems* for k1,k2,
because they end up unifying; we want those SigTvs again.

Note [ReturnTv]
~~~~~~~~~~~~~~~
We sometimes want to convert a checking algorithm into an inference
algorithm. An easy way to do this is to "check" that a term has a
metavariable as a type. But, we must be careful to allow that metavariable
to unify with *anything*. (Well, anything that doesn't fail an occurs-check.)
This is what ReturnTv means.

For example, if we have

  (undefined :: (forall a. TF1 a ~ TF2 a => a)) x

we'll call (tcInfer . tcExpr) on the function expression. tcInfer will
create a ReturnTv to represent the expression's type. We really need this
ReturnTv to become set to (forall a. TF1 a ~ TF2 a => a) despite the fact
that this type mentions type families and is a polytype.

However, we must also be careful to make sure that the ReturnTvs really
always do get unified with something -- we don't want these floating
around in the solver. So, we check after running the checker to make
sure the ReturnTv is filled. If it's not, we set it to a TauTv.

We can't ASSERT that no ReturnTvs hit the solver, because they
can if there's, say, a kind error that stops checkTauTvUpdate from
working. This happens in test case typecheck/should_fail/T5570, for
example.

See also the commentary on #9404.
-}

-- A TyVarDetails is inside a TyVar
data TcTyVarDetails
  = SkolemTv      -- A skolem
       Bool       -- True <=> this skolem type variable can be overlapped
                  --          when looking up instances
                  -- See Note [Binding when looking up instances] in InstEnv

  | FlatSkol      -- A flatten-skolem.  It stands for the TcType, and zonking
       TcType     -- will replace it by that type.
                  -- See Note [The flattening story] in TcFlatten

  | RuntimeUnk    -- Stands for an as-yet-unknown type in the GHCi
                  -- interactive context

  | MetaTv { mtv_info  :: MetaInfo
           , mtv_ref   :: IORef MetaDetails
           , mtv_tclvl :: TcLevel }  -- See Note [TcLevel and untouchable type variables]

vanillaSkolemTv, superSkolemTv :: TcTyVarDetails
-- See Note [Binding when looking up instances] in InstEnv
vanillaSkolemTv = SkolemTv False  -- Might be instantiated
superSkolemTv   = SkolemTv True   -- Treat this as a completely distinct type

-----------------------------
data MetaDetails
  = Flexi  -- Flexi type variables unify to become Indirects
  | Indirect TcType

instance Outputable MetaDetails where
  ppr Flexi         = ptext (sLit "Flexi")
  ppr (Indirect ty) = ptext (sLit "Indirect") <+> ppr ty

data MetaInfo
   = TauTv Bool    -- This MetaTv is an ordinary unification variable
                   -- A TauTv is always filled in with a tau-type, which
                   -- never contains any ForAlls.
                   -- The boolean is true when the meta var originates
                   -- from a wildcard.

   | ReturnTv      -- Can unify with *anything*. Used to convert a
                   -- type "checking" algorithm into a type inference algorithm.
                   -- See Note [ReturnTv]

   | SigTv         -- A variant of TauTv, except that it should not be
                   -- unified with a type, only with a type variable
                   -- SigTvs are only distinguished to improve error messages
                   --      see Note [Signature skolems]
                   --      The MetaDetails, if filled in, will
                   --      always be another SigTv or a SkolemTv

   | FlatMetaTv    -- A flatten meta-tyvar
                   -- It is a meta-tyvar, but it is always untouchable, with level 0
                   -- See Note [The flattening story] in TcFlatten

-------------------------------------
-- UserTypeCtxt describes the origin of the polymorphic type
-- in the places where we need to an expression has that type

data UserTypeCtxt
  = FunSigCtxt Name     -- Function type signature
                        -- Also used for types in SPECIALISE pragmas
  | InfSigCtxt Name     -- Inferred type for function
  | ExprSigCtxt         -- Expression type signature
  | ConArgCtxt Name     -- Data constructor argument
  | TySynCtxt Name      -- RHS of a type synonym decl
  | PatSigCtxt          -- Type sig in pattern
                        --   eg  f (x::t) = ...
                        --   or  (x::t, y) = e
  | RuleSigCtxt Name    -- LHS of a RULE forall
                        --    RULE "foo" forall (x :: a -> a). f (Just x) = ...
  | ResSigCtxt          -- Result type sig
                        --      f x :: t = ....
  | ForSigCtxt Name     -- Foreign import or export signature
  | DefaultDeclCtxt     -- Types in a default declaration
  | InstDeclCtxt        -- An instance declaration
  | SpecInstCtxt        -- SPECIALISE instance pragma
  | ThBrackCtxt         -- Template Haskell type brackets [t| ... |]
  | GenSigCtxt          -- Higher-rank or impredicative situations
                        -- e.g. (f e) where f has a higher-rank type
                        -- We might want to elaborate this
  | GhciCtxt            -- GHCi command :kind <type>

  | ClassSCCtxt Name    -- Superclasses of a class
  | SigmaCtxt           -- Theta part of a normal for-all type
                        --      f :: <S> => a -> a
  | DataTyCtxt Name     -- Theta part of a data decl
                        --      data <S> => T a = MkT a

{-
-- Notes re TySynCtxt
-- We allow type synonyms that aren't types; e.g.  type List = []
--
-- If the RHS mentions tyvars that aren't in scope, we'll
-- quantify over them:
--      e.g.    type T = a->a
-- will become  type T = forall a. a->a
--
-- With gla-exts that's right, but for H98 we should complain.


************************************************************************
*                                                                      *
                Untoucable type variables
*                                                                      *
************************************************************************
-}

newtype TcLevel = TcLevel Int deriving( Eq )
  -- See Note [TcLevel and untouchable type variables] for what this Int is

{-
Note [TcLevel and untouchable type variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* Each unification variable (MetaTv)
  and each Implication
  has a level number (of type TcLevel)

* INVARIANTS.  In a tree of Implications,

    (ImplicInv) The level number of an Implication is
                STRICTLY GREATER THAN that of its parent

    (MetaTvInv) The level number of a unification variable is
                LESS THAN OR EQUAL TO that of its parent
                implication

* A unification variable is *touchable* if its level number
  is EQUAL TO that of its immediate parent implication.

* INVARIANT
    (GivenInv)  The free variables of the ic_given of an
                implication are all untouchable; ie their level
                numbers are LESS THAN the ic_tclvl of the implication


Note [Skolem escape prevention]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We only unify touchable unification variables.  Because of
(MetaTvInv), there can be no occurrences of he variable further out,
so the unification can't cause the kolems to escape. Example:
     data T = forall a. MkT a (a->Int)
     f x (MkT v f) = length [v,x]
We decide (x::alpha), and generate an implication like
      [1]forall a. (a ~ alpha[0])
But we must not unify alpha:=a, because the skolem would escape.

For the cases where we DO want to unify, we rely on floating the
equality.   Example (with same T)
     g x (MkT v f) = x && True
We decide (x::alpha), and generate an implication like
      [1]forall a. (Bool ~ alpha[0])
We do NOT unify directly, bur rather float out (if the constraint
does not mention 'a') to get
      (Bool ~ alpha[0]) /\ [1]forall a.()
and NOW we can unify alpha.

The same idea of only unifying touchables solves another problem.
Suppose we had
   (F Int ~ uf[0])  /\  [1](forall a. C a => F Int ~ beta[1])
In this example, beta is touchable inside the implication. The
first solveSimpleWanteds step leaves 'uf' un-unified. Then we move inside
the implication where a new constraint
       uf  ~  beta
emerges. If we (wrongly) spontaneously solved it to get uf := beta,
the whole implication disappears but when we pop out again we are left with
(F Int ~ uf) which will be unified by our final zonking stage and
uf will get unified *once more* to (F Int).
-}

fskTcLevel :: TcLevel
fskTcLevel = TcLevel 0  -- 0 = Outside the outermost level:
                                  --     flatten skolems

topTcLevel :: TcLevel
topTcLevel = TcLevel 1   -- 1 = outermost level

isTopTcLevel :: TcLevel -> Bool
isTopTcLevel (TcLevel 1) = True
isTopTcLevel _           = False

pushTcLevel :: TcLevel -> TcLevel
pushTcLevel (TcLevel us) = TcLevel (us+1)

strictlyDeeperThan :: TcLevel -> TcLevel -> Bool
strictlyDeeperThan (TcLevel tv_tclvl) (TcLevel ctxt_tclvl)
  = tv_tclvl > ctxt_tclvl

sameDepthAs :: TcLevel -> TcLevel -> Bool
sameDepthAs (TcLevel ctxt_tclvl) (TcLevel tv_tclvl)
  = ctxt_tclvl == tv_tclvl   -- NB: invariant ctxt_tclvl >= tv_tclvl
                             --     So <= would be equivalent

checkTcLevelInvariant :: TcLevel -> TcLevel -> Bool
-- Checks (MetaTvInv) from Note [TcLevel and untouchable type variables]
checkTcLevelInvariant (TcLevel ctxt_tclvl) (TcLevel tv_tclvl)
  = ctxt_tclvl >= tv_tclvl

instance Outputable TcLevel where
  ppr (TcLevel us) = ppr us

{-
************************************************************************
*                                                                      *
                Pretty-printing
*                                                                      *
************************************************************************
-}

pprTcTyVarDetails :: TcTyVarDetails -> SDoc
-- For debugging
pprTcTyVarDetails (SkolemTv True)  = ptext (sLit "ssk")
pprTcTyVarDetails (SkolemTv False) = ptext (sLit "sk")
pprTcTyVarDetails (RuntimeUnk {})  = ptext (sLit "rt")
pprTcTyVarDetails (FlatSkol {})    = ptext (sLit "fsk")
pprTcTyVarDetails (MetaTv { mtv_info = info, mtv_tclvl = tclvl })
  = pp_info <> colon <> ppr tclvl
  where
    pp_info = case info of
                ReturnTv    -> ptext (sLit "ret")
                TauTv True  -> ptext (sLit "twc")
                TauTv False -> ptext (sLit "tau")
                SigTv       -> ptext (sLit "sig")
                FlatMetaTv  -> ptext (sLit "fuv")

pprUserTypeCtxt :: UserTypeCtxt -> SDoc
pprUserTypeCtxt (InfSigCtxt n)    = ptext (sLit "the inferred type for") <+> quotes (ppr n)
pprUserTypeCtxt (FunSigCtxt n)    = ptext (sLit "the type signature for") <+> quotes (ppr n)
pprUserTypeCtxt (RuleSigCtxt n)   = ptext (sLit "a RULE for") <+> quotes (ppr n)
pprUserTypeCtxt ExprSigCtxt       = ptext (sLit "an expression type signature")
pprUserTypeCtxt (ConArgCtxt c)    = ptext (sLit "the type of the constructor") <+> quotes (ppr c)
pprUserTypeCtxt (TySynCtxt c)     = ptext (sLit "the RHS of the type synonym") <+> quotes (ppr c)
pprUserTypeCtxt ThBrackCtxt       = ptext (sLit "a Template Haskell quotation [t|...|]")
pprUserTypeCtxt PatSigCtxt        = ptext (sLit "a pattern type signature")
pprUserTypeCtxt ResSigCtxt        = ptext (sLit "a result type signature")
pprUserTypeCtxt (ForSigCtxt n)    = ptext (sLit "the foreign declaration for") <+> quotes (ppr n)
pprUserTypeCtxt DefaultDeclCtxt   = ptext (sLit "a type in a `default' declaration")
pprUserTypeCtxt InstDeclCtxt      = ptext (sLit "an instance declaration")
pprUserTypeCtxt SpecInstCtxt      = ptext (sLit "a SPECIALISE instance pragma")
pprUserTypeCtxt GenSigCtxt        = ptext (sLit "a type expected by the context")
pprUserTypeCtxt GhciCtxt          = ptext (sLit "a type in a GHCi command")
pprUserTypeCtxt (ClassSCCtxt c)   = ptext (sLit "the super-classes of class") <+> quotes (ppr c)
pprUserTypeCtxt SigmaCtxt         = ptext (sLit "the context of a polymorphic type")
pprUserTypeCtxt (DataTyCtxt tc)   = ptext (sLit "the context of the data type declaration for") <+> quotes (ppr tc)

pprSigCtxt :: UserTypeCtxt -> SDoc -> SDoc -> SDoc
-- (pprSigCtxt ctxt <extra> <type>)
-- prints    In <extra> the type signature for 'f':
--              f :: <type>
-- The <extra> is either empty or "the ambiguity check for"
pprSigCtxt ctxt extra pp_ty
  = sep [ ptext (sLit "In") <+> extra <+> pprUserTypeCtxt ctxt <> colon
        , nest 2 (pp_sig ctxt) ]
  where
    pp_sig (FunSigCtxt n)  = pp_n_colon n
    pp_sig (ConArgCtxt n)  = pp_n_colon n
    pp_sig (ForSigCtxt n)  = pp_n_colon n
    pp_sig _               = pp_ty

    pp_n_colon n = pprPrefixOcc n <+> dcolon <+> pp_ty

{-
************************************************************************
*                  *
    Finding type family instances
*                  *
************************************************************************
-}

-- | Finds outermost type-family applications occuring in a type,
-- after expanding synonyms.
tcTyFamInsts :: Type -> [(TyCon, [Type])]
tcTyFamInsts ty
  | Just exp_ty <- tcView ty    = tcTyFamInsts exp_ty
tcTyFamInsts (TyVarTy _)        = []
tcTyFamInsts (TyConApp tc tys)
  | isTypeFamilyTyCon tc        = [(tc, tys)]
  | otherwise                   = concat (map tcTyFamInsts tys)
tcTyFamInsts (LitTy {})         = []
tcTyFamInsts (ForAllTy bndr ty) = tcTyFamInsts (binderType bndr)
                                  ++ tcTyFamInsts ty
tcTyFamInsts (AppTy ty1 ty2)    = tcTyFamInsts ty1 ++ tcTyFamInsts ty2
tcTyFamInsts (CastTy ty _)      = tcTyFamInsts ty
tcTyFamInsts (CoercionTy _)     = []  -- don't count tyfams in coercions,
                                      -- as they never get normalized, anyway
{-
************************************************************************
*                  *
          The "exact" free variables of a type
*                  *
************************************************************************

Note [Silly type synonym]
~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
  type T a = Int
What are the free tyvars of (T x)?  Empty, of course!
Here's the example that Ralf Laemmel showed me:
  foo :: (forall a. C u a -> C u a) -> u
  mappend :: Monoid u => u -> u -> u

  bar :: Monoid u => u
  bar = foo (\t -> t `mappend` t)
We have to generalise at the arg to f, and we don't
want to capture the constraint (Monad (C u a)) because
it appears to mention a.  Pretty silly, but it was useful to him.

exactTyCoVarsOfType is used by the type checker to figure out exactly
which type variables are mentioned in a type.  It's also used in the
smart-app checking code --- see TcExpr.tcIdApp

On the other hand, consider a *top-level* definition
  f = (\x -> x) :: T a -> T a
If we don't abstract over 'a' it'll get fixed to GHC.Prim.Any, and then
if we have an application like (f "x") we get a confusing error message
involving Any.  So the conclusion is this: when generalising
  - at top level use tyCoVarsOfType
  - in nested bindings use exactTyCoVarsOfType
See Trac #1813 for example.
-}

exactTyCoVarsOfType :: Type -> TyCoVarSet
-- Find the free type variables (of any kind)
-- but *expand* type synonyms.  See Note [Silly type synonym] above.
exactTyCoVarsOfType ty
  = go ty
  where
    go ty | Just ty' <- tcView ty = go ty'  -- This is the key line
    go (TyVarTy tv)         = unitVarSet tv
    go (TyConApp _ tys)     = exactTyCoVarsOfTypes tys
    go (LitTy {})           = emptyVarSet
    go (AppTy fun arg)      = go fun `unionVarSet` go arg
    go (ForAllTy bndr ty)   = delBinderVar (go ty) bndr `unionVarSet` go (binderType bndr)
    go (CastTy ty co)       = go ty `unionVarSet` goCo co
    go (CoercionTy co)      = goCo co

    goCo (Refl _ ty)        = go ty
    goCo (TyConAppCo _ _ args)= goCoArgs args
    goCo (AppCo co h arg)   = goCo co `unionVarSet` goCo h `unionVarSet` goCoArg arg
    goCo (ForAllCo bndr co)
      = let (vars, kinds) = coBndrVarsKinds bndr in
        goCo co `delVarSetList` vars `unionVarSet` exactTyCoVarsOfTypes kinds
    goCo (CoVarCo v)         = unitVarSet v
    goCo (AxiomInstCo _ _ args) = goCoArgs args
    goCo (PhantomCo h t1 t2) = goCo h `unionVarSet` go t1 `unionVarSet` go t2
    goCo (UnsafeCo _ _ t1 t2)= go t1 `unionVarSet` go t2
    goCo (SymCo co)          = goCo co
    goCo (TransCo co1 co2)   = goCo co1 `unionVarSet` goCo co2
    goCo (NthCo _ co)        = goCo co
    goCo (LRCo _ co)         = goCo co
    goCo (InstCo co arg)     = goCo co `unionVarSet` goCoArg arg
    goCo (CoherenceCo c1 c2) = goCo c1 `unionVarSet` goCo c2
    goCo (KindCo co)         = goCo co
    goCo (KindAppCo co)      = goCo co
    goCo (SubCo co)          = goCo co
    goCo (AxiomRuleCo _ t c) = exactTyCoVarsOfTypes t `unionVarSet` goCos c

    goCos cos = foldr (unionVarSet . goCo) emptyVarSet cos

    goCoArg (TyCoArg co)          = goCo co
    goCoArg (CoCoArg _ h co1 co2) = mapUnionVarSet goCo [h, co1, co2]

    goCoArgs args            = mapUnionVarSet goCoArg args

exactTyCoVarsOfTypes :: [Type] -> TyVarSet
exactTyCoVarsOfTypes tys = mapUnionVarSet exactTyCoVarsOfType tys

{-
************************************************************************
*                                                                      *
                Predicates
*                                                                      *
************************************************************************
-}

isTouchableOrFmv :: TcLevel -> TcTyVar -> Bool
isTouchableOrFmv ctxt_tclvl tv
  = case tcTyVarDetails tv of
      MetaTv { mtv_tclvl = tv_tclvl, mtv_info = info }
        -> ASSERT2( checkTcLevelInvariant ctxt_tclvl tv_tclvl,
                    ppr tv $$ ppr tv_tclvl $$ ppr ctxt_tclvl )
           case info of
             FlatMetaTv -> True
             _          -> tv_tclvl `sameDepthAs` ctxt_tclvl
      _          -> False

isTouchableMetaTyVar :: TcLevel -> TcTyVar -> Bool
isTouchableMetaTyVar ctxt_tclvl tv
  | isTyVar tv
  = case tcTyVarDetails tv of
      MetaTv { mtv_tclvl = tv_tclvl }
        -> ASSERT2( checkTcLevelInvariant ctxt_tclvl tv_tclvl,
                    ppr tv $$ ppr tv_tclvl $$ ppr ctxt_tclvl )
           tv_tclvl `sameDepthAs` ctxt_tclvl
      _ -> False
  | otherwise = False

isFloatedTouchableMetaTyVar :: TcLevel -> TcTyVar -> Bool
isFloatedTouchableMetaTyVar ctxt_tclvl tv
  | isTyVar tv
  = case tcTyVarDetails tv of
      MetaTv { mtv_tclvl = tv_tclvl } -> tv_tclvl `strictlyDeeperThan` ctxt_tclvl
      _ -> False
  | otherwise = False

isImmutableTyVar :: TyCoVar -> Bool
isImmutableTyVar tv
  | isTcTyVar tv = isSkolemTyVar tv
  | otherwise    = True

isTyConableTyVar, isSkolemTyVar, isSkolemTyCoVar, isOverlappableTyVar,
  isMetaTyVar, isReturnTyVar, isAmbiguousTyVar, 
  isFmvTyVar, isFskTyVar, isFlattenTyVar :: TcTyVar -> Bool

isTyConableTyVar tv
        -- True of a meta-type variable that can be filled in
        -- with a type constructor application; in particular,
        -- not a SigTv
  | isTyVar tv
  = case tcTyVarDetails tv of
        MetaTv { mtv_info = SigTv } -> False
        _                           -> True
  | otherwise = True

isFmvTyVar tv
  = case tcTyVarDetails tv of
        MetaTv { mtv_info = FlatMetaTv } -> True
        _                                -> False

-- | True of both given and wanted flatten-skolems (fak and usk)
isFlattenTyVar tv
  = case tcTyVarDetails tv of
        FlatSkol {}                      -> True
        MetaTv { mtv_info = FlatMetaTv } -> True
        _                                -> False

-- | True of FlatSkol skolems only
isFskTyVar tv
  = case tcTyVarDetails tv of
        FlatSkol {} -> True
        _           -> False

isSkolemTyVar tv
  = case tcTyVarDetails tv of
        MetaTv {} -> False
        _other    -> True

isSkolemTyCoVar tv
  = isCoVar tv || isSkolemTyVar tv

isOverlappableTyVar tv
  | isTyVar tv
  = case tcTyVarDetails tv of
        SkolemTv overlappable -> overlappable
        _                     -> False
  | otherwise = False

isMetaTyVar tv
  | isTyVar tv
  = case tcTyVarDetails tv of
        MetaTv {} -> True
        _         -> False
  | otherwise = False

isReturnTyVar tv
  = case tcTyVarDetails tv of
      MetaTv { mtv_info = ReturnTv } -> True
      _                              -> False

-- isAmbiguousTyVar is used only when reporting type errors
-- It picks out variables that are unbound, namely meta
-- type variables and the RuntimUnk variables created by
-- RtClosureInspect.zonkRTTIType.  These are "ambiguous" in
-- the sense that they stand for an as-yet-unknown type
isAmbiguousTyVar tv
  | isTyVar tv
  = case tcTyVarDetails tv of
        MetaTv {}     -> True
        RuntimeUnk {} -> True
        _             -> False
  | otherwise = False

isMetaTyVarTy :: TcType -> Bool
isMetaTyVarTy (TyVarTy tv) = isMetaTyVar tv
isMetaTyVarTy _            = False

metaTyVarInfo :: TcTyVar -> MetaInfo
metaTyVarInfo tv
  = case tcTyVarDetails tv of
      MetaTv { mtv_info = info } -> info
      _ -> pprPanic "metaTyVarInfo" (ppr tv)

metaTyVarTcLevel :: TcTyVar -> TcLevel
metaTyVarTcLevel tv
  = case tcTyVarDetails tv of
      MetaTv { mtv_tclvl = tclvl } -> tclvl
      _ -> pprPanic "metaTyVarTcLevel" (ppr tv)

metaTyVarTcLevel_maybe :: TcTyVar -> Maybe TcLevel
metaTyVarTcLevel_maybe tv
  = case tcTyVarDetails tv of
      MetaTv { mtv_tclvl = tclvl } -> Just tclvl
      _                            -> Nothing

setMetaTyVarTcLevel :: TcTyVar -> TcLevel -> TcTyVar
setMetaTyVarTcLevel tv tclvl
  = case tcTyVarDetails tv of
      details@(MetaTv {}) -> setTcTyVarDetails tv (details { mtv_tclvl = tclvl })
      _ -> pprPanic "metaTyVarTcLevel" (ppr tv)

isSigTyVar :: Var -> Bool
isSigTyVar tv
  = case tcTyVarDetails tv of
        MetaTv { mtv_info = SigTv } -> True
        _                           -> False

metaTvRef :: TyVar -> IORef MetaDetails
metaTvRef tv
  = case tcTyVarDetails tv of
        MetaTv { mtv_ref = ref } -> ref
        _ -> pprPanic "metaTvRef" (ppr tv)

isFlexi, isIndirect :: MetaDetails -> Bool
isFlexi Flexi = True
isFlexi _     = False

isIndirect (Indirect _) = True
isIndirect _            = False

isRuntimeUnkSkol :: TyVar -> Bool
-- Called only in TcErrors; see Note [Runtime skolems] there
isRuntimeUnkSkol x
  | isTcTyVar x, RuntimeUnk <- tcTyVarDetails x = True
  | otherwise                                   = False

{-
************************************************************************
*                                                                      *
\subsection{Tau, sigma and rho}
*                                                                      *
************************************************************************
-}

mkSigmaTy :: [Binder] -> [PredType] -> Type -> Type
mkSigmaTy bndrs theta tau = mkForAllTys bndrs (mkPhiTy theta tau)

mkInvSigmaTy :: [TyCoVar] -> [PredType] -> Type -> Type
mkInvSigmaTy tyvars
  = mkSigmaTy (zipWith mkNamedBinder tyvars (repeat Invisible))

mkPhiTy :: [PredType] -> Type -> Type
mkPhiTy = mkFunTys

mkNakedSigmaTy :: [Binder] -> [PredType] -> Type -> Type
-- See Note [Zonking inside the knot] in TcHsType
mkNakedSigmaTy bndrs theta tau = mkForAllTys bndrs (mkNakedPhiTy theta tau)

mkNakedInvSigmaTy :: [TyCoVar] -> [PredType] -> Type -> Type
-- See Note [Zonking inside the knot] in TcHsType
mkNakedInvSigmaTy tyvars
  = mkNakedSigmaTy (zipWith mkNamedBinder tyvars (repeat Invisible))

mkNakedPhiTy :: [PredType] -> Type -> Type
-- See Note [Zonking inside the knot] in TcHsType
mkNakedPhiTy = flip $ foldr mkNakedFunTy
    
mkTcEqPred :: TcType -> TcType -> Type
-- During type checking we build equalities between
-- types of differing kinds. This all gets sorted out when
-- we desugar to Core (which allows heterogeneous equality
-- anyway), but we must be careful *not* to check that the
-- two types have the same kind here!
mkTcEqPred ty1 ty2
  = mkTyConApp eqTyCon [k, ty1, ty2]
  where
    k = typeKind ty1

-- | Make a representational equality predicate
mkTcReprEqPred :: TcType -> TcType -> Type
mkTcReprEqPred ty1 ty2
  = mkTyConApp coercibleTyCon [k, ty1, ty2]
  where
    k = typeKind ty1

-- | Make an equality predicate at a given boxity & role.
-- The role must not be Phantom.
mkTcEqPredBR :: Boxity -> Role -> TcType -> TcType -> Type
mkTcEqPredBR Boxed   Nominal          = mkTcEqPred
mkTcEqPredBR Boxed   Representational = mkTcReprEqPred
mkTcEqPredBR Unboxed Nominal          = mkPrimEqPred
mkTcEqPredBR Unboxed Representational = mkReprPrimEqPred
mkTcEqPredBR _       Phantom          = panic "mkTcEqPredBR Phantom"

-- @isTauTy@ tests if a type is "simple". It should not be called on a boxy type.
isTauTy :: Type -> Bool
isTauTy ty | Just ty' <- tcView ty = isTauTy ty'
isTauTy (TyVarTy _)           = True
isTauTy (LitTy {})            = True
isTauTy (TyConApp tc tys)     = all isTauTy tys && isTauTyCon tc
isTauTy (AppTy a b)           = isTauTy a && isTauTy b
isTauTy (ForAllTy (Anon a) b) = isTauTy a && isTauTy b
isTauTy (ForAllTy {})         = False
isTauTy (CastTy _ _)          = False
isTauTy (CoercionTy _)        = False

isTauTyCon :: TyCon -> Bool
-- Returns False for type synonyms whose expansion is a polytype
isTauTyCon tc
  | Just (_, rhs) <- synTyConDefn_maybe tc = isTauTy rhs
  | otherwise                              = True

---------------
getDFunTyKey :: Type -> OccName -- Get some string from a type, to be used to
                                -- construct a dictionary function name
getDFunTyKey ty | Just ty' <- tcView ty = getDFunTyKey ty'
getDFunTyKey (TyVarTy tv)            = getOccName tv
getDFunTyKey (TyConApp tc _)         = getOccName tc
getDFunTyKey (LitTy x)               = getDFunTyLitKey x
getDFunTyKey (AppTy fun _)           = getDFunTyKey fun
getDFunTyKey (ForAllTy (Anon _) _)   = getOccName funTyCon
getDFunTyKey (ForAllTy (Named {}) t) = getDFunTyKey t
getDFunTyKey (CastTy ty _)           = getDFunTyKey ty
getDFunTyKey t@(CoercionTy _)        = pprPanic "getDFunTyKey" (ppr t)

getDFunTyLitKey :: TyLit -> OccName
getDFunTyLitKey (NumTyLit n) = mkOccName Name.varName (show n)
getDFunTyLitKey (StrTyLit n) = mkOccName Name.varName (show n)  -- hm

---------------
mkNakedTyConApp :: TyCon -> [Type] -> Type
-- Builds a TyConApp 
--   * without being strict in TyCon,
--   * without satisfying the invariants of TyConApp
-- A subsequent zonking will establish the invariants
-- See Note [Zonking inside the knot] in TcHsType
mkNakedTyConApp tc tys = TyConApp tc tys

mkNakedAppTys :: Type -> [Type] -> Type
-- See Note [Zonking inside the knot] in TcHsType
mkNakedAppTys ty1                []   = ty1
mkNakedAppTys (TyConApp tc tys1) tys2 = mkNakedTyConApp tc (tys1 ++ tys2)
mkNakedAppTys ty1                tys2 = foldl AppTy ty1 tys2

mkNakedAppTy :: Type -> Type -> Type
-- See Note [Zonking inside the knot] in TcHsType
mkNakedAppTy ty1 ty2 = mkNakedAppTys ty1 [ty2]

mkNakedFunTy :: Type -> Type -> Type
-- See Note [Zonking inside the knot] in TcHsType
mkNakedFunTy arg res = ForAllTy (Anon arg) res

mkNakedCastTy :: Type -> Coercion -> Type
mkNakedCastTy = CastTy

{-
************************************************************************
*                                                                      *
\subsection{Expanding and splitting}
*                                                                      *
************************************************************************

These tcSplit functions are like their non-Tc analogues, but
        *) they do not look through newtypes

However, they are non-monadic and do not follow through mutable type
variables.  It's up to you to make sure this doesn't matter.
-}

-- | Splits a forall type into a list of 'Binder's and the inner type.
-- Always succeeds, even if it returns an empty list.
tcSplitForAllTys :: Type -> ([Binder], Type)
tcSplitForAllTys = splitForAllTys

-- | Like 'tcSplitForAllTys', but splits off only named binders, returning
-- just the tycovars.
tcSplitNamedForAllTys :: Type -> ([TyCoVar], Type)
tcSplitNamedForAllTys = splitNamedForAllTys

-- | Like 'tcSplitForAllTys', but splits off only named binders.
tcSplitNamedForAllTysB :: Type -> ([Binder], Type)
tcSplitNamedForAllTysB = splitNamedForAllTysB

tcIsForAllTy :: Type -> Bool
tcIsForAllTy ty | Just ty' <- tcView ty = tcIsForAllTy ty'
tcIsForAllTy (ForAllTy {}) = True
tcIsForAllTy _             = False

-- | Is this a ForAllTy with a named binder?
tcIsNamedForAllTy :: Type -> Bool
tcIsNamedForAllTy ty | Just ty' <- tcView ty = tcIsNamedForAllTy ty'
tcIsNamedForAllTy (ForAllTy (Named {}) _) = True
tcIsNamedForAllTy _                       = False

tcSplitPredFunTy_maybe :: Type -> Maybe (PredType, Type)
-- Split off the first predicate argument from a type
tcSplitPredFunTy_maybe ty
  | Just ty' <- tcView ty = tcSplitPredFunTy_maybe ty'
tcSplitPredFunTy_maybe (ForAllTy (Anon arg) res)
  | isPredTy arg = Just (arg, res)
tcSplitPredFunTy_maybe _
  = Nothing

tcSplitPhiTy :: Type -> (ThetaType, Type)
tcSplitPhiTy ty
  = split ty []
  where
    split ty ts
      = case tcSplitPredFunTy_maybe ty of
          Just (pred, ty) -> split ty (pred:ts)
          Nothing         -> (reverse ts, ty)

-- | Split a sigma type into its parts.
tcSplitSigmaTy :: Type -> ([TyCoVar], ThetaType, Type)
tcSplitSigmaTy ty = case tcSplitNamedForAllTys ty of
                        (tvs, rho) -> case tcSplitPhiTy rho of
                                        (theta, tau) -> (tvs, theta, tau)

-----------------------
tcDeepSplitSigmaTy_maybe
  :: TcSigmaType -> Maybe ([TcType], [TyCoVar], ThetaType, TcSigmaType)
-- Looks for a *non-trivial* quantified type, under zero or more function arrows
-- By "non-trivial" we mean either tyvars or constraints are non-empty

tcDeepSplitSigmaTy_maybe ty
  | Just (arg_ty, res_ty)           <- tcSplitFunTy_maybe ty
  , Just (arg_tys, tvs, theta, rho) <- tcDeepSplitSigmaTy_maybe res_ty
  = Just (arg_ty:arg_tys, tvs, theta, rho)

  | (tvs, theta, rho) <- tcSplitSigmaTy ty
  , not (null tvs && null theta)
  = Just ([], tvs, theta, rho)

  | otherwise = Nothing

-----------------------
tcTyConAppTyCon :: Type -> TyCon
tcTyConAppTyCon ty = case tcSplitTyConApp_maybe ty of
                        Just (tc, _) -> tc
                        Nothing      -> pprPanic "tcTyConAppTyCon" (pprType ty)

tcTyConAppArgs :: Type -> [Type]
tcTyConAppArgs ty = case tcSplitTyConApp_maybe ty of
                        Just (_, args) -> args
                        Nothing        -> pprPanic "tcTyConAppArgs" (pprType ty)

tcSplitTyConApp :: Type -> (TyCon, [Type])
tcSplitTyConApp ty = case tcSplitTyConApp_maybe ty of
                        Just stuff -> stuff
                        Nothing    -> pprPanic "tcSplitTyConApp" (pprType ty)

tcSplitTyConApp_maybe :: Type -> Maybe (TyCon, [Type])
tcSplitTyConApp_maybe ty | Just ty' <- tcView ty = tcSplitTyConApp_maybe ty'
tcSplitTyConApp_maybe (TyConApp tc tys)          = Just (tc, tys)
tcSplitTyConApp_maybe (ForAllTy (Anon arg) res)  = Just (funTyCon, [arg,res])
        -- Newtypes are opaque, so they may be split
        -- However, predicates are not treated
        -- as tycon applications by the type checker
tcSplitTyConApp_maybe _                 = Nothing

-----------------------
tcSplitFunTys :: Type -> ([Type], Type)
tcSplitFunTys ty = case tcSplitFunTy_maybe ty of
                        Nothing        -> ([], ty)
                        Just (arg,res) -> (arg:args, res')
                                       where
                                          (args,res') = tcSplitFunTys res

tcSplitFunTy_maybe :: Type -> Maybe (Type, Type)
tcSplitFunTy_maybe ty | Just ty' <- tcView ty           = tcSplitFunTy_maybe ty'
tcSplitFunTy_maybe (ForAllTy (Anon arg) res)
                                   | not (isPredTy arg) = Just (arg, res)
tcSplitFunTy_maybe _                                    = Nothing
        -- Note the typeKind guard
        -- Consider     (?x::Int) => Bool
        -- We don't want to treat this as a function type!
        -- A concrete example is test tc230:
        --      f :: () -> (?p :: ()) => () -> ()
        --
        --      g = f () ()

tcSplitFunTysN
        :: TcRhoType
        -> Arity                -- N: Number of desired args
        -> ([TcSigmaType],      -- Arg types (N or fewer)
            TcSigmaType)        -- The rest of the type

tcSplitFunTysN ty n_args
  | n_args == 0
  = ([], ty)
  | Just (arg,res) <- tcSplitFunTy_maybe ty
  = case tcSplitFunTysN res (n_args - 1) of
        (args, res) -> (arg:args, res)
  | otherwise
  = ([], ty)

tcSplitFunTy :: Type -> (Type, Type)
tcSplitFunTy  ty = expectJust "tcSplitFunTy" (tcSplitFunTy_maybe ty)

tcFunArgTy :: Type -> Type
tcFunArgTy    ty = fst (tcSplitFunTy ty)

tcFunResultTy :: Type -> Type
tcFunResultTy ty = snd (tcSplitFunTy ty)

-----------------------
tcSplitAppTy_maybe :: Type -> Maybe (Type, Type)
tcSplitAppTy_maybe ty | Just ty' <- tcView ty = tcSplitAppTy_maybe ty'
tcSplitAppTy_maybe ty = repSplitAppTy_maybe ty

tcSplitAppTy :: Type -> (Type, Type)
tcSplitAppTy ty = case tcSplitAppTy_maybe ty of
                    Just stuff -> stuff
                    Nothing    -> pprPanic "tcSplitAppTy" (pprType ty)

tcSplitAppTys :: Type -> (Type, [Type])
tcSplitAppTys ty
  = go ty []
  where
    go ty args = case tcSplitAppTy_maybe ty of
                   Just (ty', arg) -> go ty' (arg:args)
                   Nothing         -> (ty,args)

-----------------------
tcGetTyVar_maybe :: Type -> Maybe TyVar
tcGetTyVar_maybe ty | Just ty' <- tcView ty = tcGetTyVar_maybe ty'
tcGetTyVar_maybe (TyVarTy tv)   = Just tv
tcGetTyVar_maybe _              = Nothing

tcGetTyCoVar_maybe :: Type -> Maybe TyCoVar
tcGetTyCoVar_maybe ty | Just ty' <- tcView ty = tcGetTyCoVar_maybe ty'
tcGetTyCoVar_maybe (TyVarTy tv)               = Just tv
tcGetTyCoVar_maybe (CoercionTy (CoVarCo cv))  = Just cv
tcGetTyCoVar_maybe _                          = Nothing

tcGetTyVar :: String -> Type -> TyVar
tcGetTyVar msg ty = expectJust msg (tcGetTyVar_maybe ty)

tcIsTyVarTy :: Type -> Bool
tcIsTyVarTy ty | Just ty' <- tcView ty = tcIsTyVarTy ty'
tcIsTyVarTy (CastTy ty _) = tcIsTyVarTy ty  -- look through casts, as
                                            -- this is only used for
                                            -- e.g., FlexibleContexts
tcIsTyVarTy (TyVarTy _)   = True
tcIsTyVarTy _             = False

-----------------------
tcSplitCastTy_maybe :: TcType -> Maybe (TcType, Coercion)
tcSplitCastTy_maybe ty | Just ty' <- tcView ty = tcSplitCastTy_maybe ty'
tcSplitCastTy_maybe (CastTy ty co)             = Just (ty, co)
tcSplitCastTy_maybe _                          = Nothing

-----------------------
tcSplitDFunTy :: Type -> ([TyCoVar], [Type], Class, [Type])
-- Split the type of a dictionary function
-- We don't use tcSplitSigmaTy,  because a DFun may (with NDP)
-- have non-Pred arguments, such as
--     df :: forall m. (forall b. Eq b => Eq (m b)) -> C m
--
-- Also NB splitFunTys, not tcSplitFunTys;
-- the latter  specifically stops at PredTy arguments,
-- and we don't want to do that here
tcSplitDFunTy ty
  = case tcSplitNamedForAllTys ty   of { (tvs, rho)    ->
    case splitFunTys rho            of { (theta, tau)  ->
    case tcSplitDFunHead tau        of { (clas, tys)   ->
    (tvs, theta, clas, tys) }}}

tcSplitDFunHead :: Type -> (Class, [Type])
tcSplitDFunHead = getClassPredTys

tcInstHeadTyNotSynonym :: Type -> Bool
-- Used in Haskell-98 mode, for the argument types of an instance head
-- These must not be type synonyms, but everywhere else type synonyms
-- are transparent, so we need a special function here
tcInstHeadTyNotSynonym ty
  = case ty of
        TyConApp tc _ -> not (isTypeSynonymTyCon tc)
        _ -> True

tcInstHeadTyAppAllTyVars :: Type -> Bool
-- Used in Haskell-98 mode, for the argument types of an instance head
-- These must be a constructor applied to type variable arguments.
-- But we allow kind instantiations.
tcInstHeadTyAppAllTyVars ty
  | Just ty' <- tcView ty       -- Look through synonyms
  = tcInstHeadTyAppAllTyVars ty'
  | otherwise
  = case ty of
        TyConApp tc tys         -> ok (filterInvisibles tc tys)  -- avoid kinds
        ForAllTy (Anon arg) res -> ok [arg, res]
        _                       -> False
  where
        -- Check that all the types are type variables,
        -- and that each is distinct
    ok tys = equalLength tvs tys && hasNoDups tvs
           where
             tvs = mapMaybe get_tv tys

    get_tv (TyVarTy tv)  = Just tv      -- through synonyms
    get_tv _             = Nothing

tcEqKind :: TcKind -> TcKind -> Bool
tcEqKind = tcEqType

tcEqType :: TcType -> TcType -> Bool
-- tcEqType is a proper implements the same Note [Non-trivial definitional
-- equality] (in TyCoRep) as `eqType`, but Type.eqType believes (* ==
-- Constraint), and that is NOT what we want in the type checker!
tcEqType ty1 ty2
  = isNothing (tc_eq_type ki1 ki2) && isNothing (tc_eq_type ty1 ty2)
  where
    ki1 = typeKind ty1
    ki2 = typeKind ty2

-- | Just like 'tcEqType', but will return True for types of different kinds
-- as long as their non-coercion structure is identical.
tcEqTypeNoKindCheck :: TcType -> TcType -> Bool
tcEqTypeNoKindCheck ty1 ty2 = isNothing $ tc_eq_type ty1 ty2

-- | Like 'tcEqType', but returns information about whether the difference
-- is visible in the case of a mismatch. A return of Nothing means the types
-- are 'tcEqType'.
tcEqTypeVis :: TcType -> TcType -> Maybe VisibilityFlag
tcEqTypeVis ty1 ty2
  = tc_eq_type ty1 ty2 `and_then` tc_eq_type ki1 ki2
  where
    ki1 = typeKind ty1
    ki2 = typeKind ty2

    Nothing `and_then` x = x
    just    `and_then` _ = just

-- | Worker for 'tcEqType'. No kind check!
tc_eq_type :: TcType -> TcType -> Maybe VisibilityFlag
tc_eq_type t1 t2 = tc_eq_type_erased init_env (erase t1) (erase t2)
  where
    init_env = mkRnEnv2 $
               mkInScopeSet $
               tyCoVarsOfType t1 `unionVarSet` tyCoVarsOfType t2
    erase = eraseType tcView

-- | Real worker for 'tcEqType'. Works on erased types.
tc_eq_type_erased :: RnEnv2 -> EType -> EType -> Maybe VisibilityFlag
tc_eq_type_erased = go Visible
  where
    go vis env (ETyVarTy tv1)       (ETyVarTy tv2)
      = check vis $ rnOccL env tv1 == rnOccR env tv2
        
    go vis _   (ELitTy lit1)        (ELitTy lit2)
      = check vis $ lit1 == lit2
        
    go vis env (EForAllTy (ENamed tv1 k1 vis1) ty1)
               (EForAllTy (ENamed tv2 k2 vis2) ty2)
      = go vis1 env k1 k2 `and_then` go vis (rnBndr2 env tv1 tv2) ty1 ty2
                          `and_then` check vis (vis1 == vis2)
    go vis env (EForAllTy (EAnon arg1) res1) (EForAllTy (EAnon arg2) res2)
      = go vis env arg1 arg2 `and_then` go vis env res1 res2
    go vis env (EAppTy s1 k1 t1)    (EAppTy s2 k2 t2)
      = go vis env s1 s2 `and_then` go Invisible env k1 k2
                         `and_then` go vis env t1 t2
    go vis env (ETyConApp tc1 ts1)  (ETyConApp tc2 ts2)
      = check vis (tc1 == tc2) `and_then` gos (tc_vis tc1) env ts1 ts2
    go _   _   ECoercionTy          ECoercionTy = Nothing
    go vis _   _                    _           = Just vis

    gos _      _   []       []       = Nothing
    gos (v:vs) env (t1:ts1) (t2:ts2) = go v env t1 t2 `and_then` gos vs env ts1 ts2
    gos (v:_)  _   _        _        = Just v
    gos _      _   _        _        = panic "tc_eq_type_erased"

    tc_vis :: TyCon -> [VisibilityFlag]
    tc_vis tc = viss ++ repeat Visible
       -- the repeat Visible is necessary because tycons can legitimately
       -- be oversaturated
      where
        k          = tyConKind tc
        (bndrs, _) = splitForAllTys k
        viss       = map binderVisibility bndrs

    check :: VisibilityFlag -> Bool -> Maybe VisibilityFlag
    check _   True  = Nothing
    check vis False = Just vis

    Nothing `and_then` x = x
    just    `and_then` _ = just
    infixr 3 `and_then`

-- | Like 'pickyEqTypeVis', but returns a Bool for convenience
pickyEqType :: TcType -> TcType -> Bool
-- Check when two types _look_ the same, _including_ synonyms.
-- So (pickyEqType String [Char]) returns False
-- This still ignores coercions, because this is used only for printing,
-- and we omit coercions there.
pickyEqType ty1 ty2
  = tc_eq_type_erased init_env (erase ki1) (erase ki2)
    `and_then`
    tc_eq_type_erased init_env (erase ty1) (erase ty2)
  where
    ki1 = typeKind ty1
    ki2 = typeKind ty2
    
    init_env = mkRnEnv2 $
               mkInScopeSet $
               tyCoVarsOfType ty1 `unionVarSet` tyCoVarsOfType ty2

    erase = eraseType (const Nothing)

    Nothing  `and_then` x = isNothing x      -- first test succeeded; use second
    (Just _) `and_then` _ = False

{-
Note [Occurs check expansion]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
(occurCheckExpand tv xi) expands synonyms in xi just enough to get rid
of occurrences of tv outside type function arguments, if that is
possible; otherwise, it returns Nothing.

For example, suppose we have
  type F a b = [a]
Then
  occurCheckExpand b (F Int b) = Just [Int]
but
  occurCheckExpand a (F a Int) = Nothing

We don't promise to do the absolute minimum amount of expanding
necessary, but we try not to do expansions we don't need to.  We
prefer doing inner expansions first.  For example,
  type F a b = (a, Int, a, [a])
  type G b   = Char
We have
  occurCheckExpand b (F (G b)) = F Char
even though we could also expand F to get rid of b.

See also Note [occurCheckExpand] in TcCanonical
-}

data OccCheckResult a
  = OC_OK a
  | OC_Forall
  | OC_NonTyVar
  | OC_Occurs

instance Functor OccCheckResult where
      fmap = liftM

instance Applicative OccCheckResult where
      pure = return
      (<*>) = ap

instance Monad OccCheckResult where
  return x = OC_OK x
  OC_OK x     >>= k = k x
  OC_Forall   >>= _ = OC_Forall
  OC_NonTyVar >>= _ = OC_NonTyVar
  OC_Occurs   >>= _ = OC_Occurs

occurCheckExpand :: DynFlags -> TcTyVar -> Type -> OccCheckResult Type
-- See Note [Occurs check expansion]
-- Check whether
--   a) the given variable occurs in the given type.
--   b) there is a forall in the type (unless we have -XImpredicativeTypes
--                                     or it's a ReturnTv
--   c) if it's a SigTv, ty should be a tyvar
--
-- We may have needed to do some type synonym unfolding in order to
-- get rid of the variable (or forall), so we also return the unfolded
-- version of the type, which is guaranteed to be syntactically free
-- of the given type variable.  If the type is already syntactically
-- free of the variable, then the same type is returned.

occurCheckExpand dflags tv ty
  | MetaTv { mtv_info = SigTv } <- details
                  = go_sig_tv ty
  | fast_check ty = return ty
  | otherwise     = go ty
  where
    details = tcTyVarDetails tv

    impredicative = canUnifyWithPolyType dflags details

    -- Check 'ty' is a tyvar, or can be expanded into one
    go_sig_tv ty@(TyVarTy {})            = OC_OK ty
    go_sig_tv ty | Just ty' <- tcView ty = go_sig_tv ty'
    go_sig_tv _                          = OC_NonTyVar

    -- True => fine
    fast_check (LitTy {})          = True
    fast_check (TyVarTy tv')       = tv /= tv'
    fast_check (TyConApp _ tys)    = all fast_check tys
    fast_check (ForAllTy (Anon a) r) = fast_check a && fast_check r
    fast_check (AppTy fun arg)     = fast_check fun && fast_check arg
    fast_check (ForAllTy (Named tv' _) ty)
                                   = impredicative
                                   && fast_check (tyVarKind tv')
                                   && (tv == tv' || fast_check ty)
    fast_check (CastTy ty co)      = fast_check ty && fast_check_co co
    fast_check (CoercionTy co)     = fast_check_co co

    fast_check_co (Refl _ ty)            = fast_check ty
    fast_check_co (TyConAppCo _ _ args)  = all fast_check_co_arg args
    fast_check_co (AppCo co h arg)       = fast_check_co co &&
                                           fast_check_co h &&
                                           fast_check_co_arg arg
    fast_check_co (ForAllCo (ForAllCoBndr h v1 v2 _) co)
      = impredicative && fast_check_co h && fast_check (varType v1)
                      && fast_check (varType v2) && (tv == v1 || tv == v2 || fast_check_co co)
    fast_check_co (CoVarCo _)            = True
    fast_check_co (AxiomInstCo _ _ args) = all fast_check_co_arg args
    fast_check_co (PhantomCo h t1 t2)    = fast_check_co h && fast_check t1
                                                           && fast_check t2
    fast_check_co (UnsafeCo _ _ ty1 ty2) = fast_check ty1 && fast_check ty2
    fast_check_co (SymCo co)             = fast_check_co co
    fast_check_co (TransCo co1 co2)      = fast_check_co co1 && fast_check_co co2
    fast_check_co (InstCo co arg)        = fast_check_co co && fast_check_co_arg arg
    fast_check_co (NthCo _ co)           = fast_check_co co
    fast_check_co (LRCo _ co)            = fast_check_co co
    fast_check_co (CoherenceCo co1 co2)  = fast_check_co co1 && fast_check_co co2
    fast_check_co (KindCo co)            = fast_check_co co
    fast_check_co (KindAppCo co)         = fast_check_co co
    fast_check_co (SubCo co)             = fast_check_co co
    fast_check_co (AxiomRuleCo _ ts cs)
      = all fast_check ts && all fast_check_co cs

    fast_check_co_arg (TyCoArg co)          = fast_check_co co
    fast_check_co_arg (CoCoArg _ h co1 co2) = all fast_check_co [h, co1, co2]

    go t@(TyVarTy tv') | tv == tv' = OC_Occurs
                       | otherwise = return t
    go ty@(LitTy {}) = return ty
    go (AppTy ty1 ty2) = do { ty1' <- go ty1
                            ; ty2' <- go ty2
                            ; return (mkAppTy ty1' ty2') }
    go (ForAllTy (Anon ty1) ty2)
                       = do { ty1' <- go ty1
                            ; ty2' <- go ty2
                            ; return (mkFunTy ty1' ty2') }
    go ty@(ForAllTy (Named tv' vis) body_ty)
       | not impredicative                = OC_Forall
       | not (fast_check (tyVarKind tv')) = OC_Occurs
           -- Can't expand away the kinds unless we create
           -- fresh variables which we don't want to do at this point.
           -- In principle fast_check might fail because of a for-all
           -- but we don't yet have poly-kinded tyvars so I'm not
           -- going to worry about that now
       | tv == tv' = return ty
       | otherwise = do { body' <- go body_ty
                        ; return (ForAllTy (Named tv' vis) body') }

    -- For a type constructor application, first try expanding away the
    -- offending variable from the arguments.  If that doesn't work, next
    -- see if the type constructor is a type synonym, and if so, expand
    -- it and try again.
    go ty@(TyConApp tc tys)
      = case do { tys <- mapM go tys; return (mkTyConApp tc tys) } of
          OC_OK ty -> return ty  -- First try to eliminate the tyvar from the args
          bad | Just ty' <- tcView ty -> go ty'
              | otherwise             -> bad
                      -- Failing that, try to expand a synonym

    go (CastTy ty co) =  do { ty' <- go ty
                            ; co' <- go_co co
                            ; return (mkCastTy ty' co') }
    go (CoercionTy co) = do { co' <- go_co co
                            ; return (mkCoercionTy co') }

    go_co (Refl r ty)               = do { ty' <- go ty
                                         ; return (mkReflCo r ty') }
      -- Note: Coercions do not contain type synonyms
    go_co (TyConAppCo r tc args)    = do { args' <- mapM go_arg args
                                         ; return (mkTyConAppCo r tc args') }
    go_co (AppCo co h arg)          = do { co' <- go_co co
                                         ; h' <- go_co h
                                         ; arg' <- go_arg arg
                                         ; return (mkAppCo co' h' arg') }
    go_co (ForAllCo cobndr co)
      | not impredicative           = OC_Forall
      | not (all fast_check (map varType (coBndrVars cobndr)))
                                    = OC_Occurs
      | tv `elem` coBndrVars cobndr = return co
      | otherwise = do { h' <- go_co (coBndrKindCo cobndr)
                       ; let cobndr' = setCoBndrKindCo cobndr h'
                       ; co' <- go_co co
                       ; return (mkForAllCo cobndr' co') }
    go_co co@(CoVarCo {})           = return co
    go_co (AxiomInstCo ax ind args) = do { args' <- mapM go_arg args
                                         ; return (mkAxiomInstCo ax ind args') }
    go_co (PhantomCo h ty1 ty2)     = do { h' <- go_co h
                                         ; ty1' <- go ty1
                                         ; ty2' <- go ty2
                                         ; return (mkPhantomCo h' ty1' ty2') }
    go_co (UnsafeCo s r ty1 ty2)    = do { ty1' <- go ty1
                                         ; ty2' <- go ty2
                                         ; return (mkUnsafeCo s r ty1' ty2') }
    go_co (SymCo co)                = do { co' <- go_co co
                                         ; return (mkSymCo co') }
    go_co (TransCo co1 co2)         = do { co1' <- go_co co1
                                         ; co2' <- go_co co2
                                         ; return (mkTransCo co1' co2') }
    go_co (NthCo n co)              = do { co' <- go_co co
                                         ; return (mkNthCo n co') }
    go_co (LRCo lr co)              = do { co' <- go_co co
                                         ; return (mkLRCo lr co') }
    go_co (InstCo co arg)           = do { co' <- go_co co
                                         ; arg' <- go_arg arg
                                         ; return (mkInstCo co' arg') }
    go_co (CoherenceCo co1 co2)     = do { co1' <- go_co co1
                                         ; co2' <- go_co co2
                                         ; return (mkCoherenceCo co1' co2') }
    go_co (KindCo co)               = do { co' <- go_co co
                                         ; return (mkKindCo co') }
    go_co (KindAppCo co)            = do { co' <- go_co co
                                         ; return (mkKindAppCo co') }
    go_co (SubCo co)                = do { co' <- go_co co
                                         ; return (mkSubCo co') }
    go_co (AxiomRuleCo ax ts cs)    = do { ts' <- mapM go ts
                                         ; cs' <- mapM go_co cs
                                         ; return (AxiomRuleCo ax ts' cs') }

    go_arg (TyCoArg co)             = do { co' <- go_co co
                                         ; return (TyCoArg co') }
    go_arg (CoCoArg r h co1 co2)    = do { h'   <- go_co h
                                         ; co1' <- go_co co1
                                         ; co2' <- go_co co2
                                         ; return (CoCoArg r h' co1' co2') }

canUnifyWithPolyType :: DynFlags -> TcTyVarDetails -> Bool
canUnifyWithPolyType dflags details
  = case details of
      MetaTv { mtv_info = ReturnTv } -> True      -- See Note [ReturnTv]
      MetaTv { mtv_info = SigTv }    -> False
      MetaTv { mtv_info = TauTv _ }  -> xopt Opt_ImpredicativeTypes dflags
      _other                         -> True
          -- We can have non-meta tyvars in given constraints

{-
Note [OpenTypeKind accepts foralls]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here is a common paradigm:
   foo :: (forall a. a -> a) -> Int
   foo = error "urk"
To make this work we need to instantiate 'error' with a polytype.
A similar case is
   bar :: Bool -> (forall a. a->a) -> Int
   bar True = \x. (x 3)
   bar False = error "urk"
Here we need to instantiate 'error' with a polytype.

But 'error' has an OpenTypeKind type variable, precisely so that
we can instantiate it with Int#.  So we also allow such type variables
to be instantiated with foralls.  It's a bit of a hack, but seems
straightforward.

************************************************************************
*                                                                      *
\subsection{Predicate types}
*                                                                      *
************************************************************************

Deconstructors and tests on predicate types
-}

isTyVarClassPred :: PredType -> Bool
isTyVarClassPred ty = case getClassPredTys_maybe ty of
    Just (_, tys) -> all isTyVarTy tys
    _             -> False

evVarPred_maybe :: EvVar -> Maybe PredType
evVarPred_maybe v = if isPredTy ty then Just ty else Nothing
  where ty = varType v

evVarPred :: EvVar -> PredType
evVarPred var
 | debugIsOn
  = case evVarPred_maybe var of
      Just pred -> pred
      Nothing   -> pprPanic "tcEvVarPred" (ppr var <+> ppr (varType var))
 | otherwise
  = varType var

-------------------------------
-- | This takes @a ~# b@ (or @a ~# R b@) and returns @a ~ b@ (or @Coercible a b@).
-- c.f. MkCore.mkEqBox
mkEqBoxTy :: Coercion -> Type
-- NB: Defined here to avoid module loops with DataCon
mkEqBoxTy co
  = ASSERT2( typeKind ty2 `eqType` k
           , ppr co $$
             ppr ty1 $$
             ppr ty2 $$
             ppr (typeKind ty1) $$
             ppr (typeKind ty2) )
    mkTyConApp (promoteDataCon datacon) [k, ty1, ty2, mkCoercionTy co]
  where (Pair ty1 ty2, role) = coercionKindRole co
        k = typeKind ty1
        datacon = case role of
            Nominal ->          eqBoxDataCon
            Representational -> coercibleDataCon
            Phantom ->
              pprPanic "mkEqBoxTy does not support boxing phantom coercions" (ppr co)

------------------
-- | When inferring types, should we quantify over a given predicate?
-- Generally true of classes; generally false of equality constraints.
-- Equality constraints that mention quantified type variables and
-- implicit variables complicate the story. See Notes
-- [Inheriting implicit parameters] and [Quantifying over equality constraints]
quantifyPred :: TyCoVarSet         -- Quantifying over these
             -> PredType -> Bool   -- True <=> quantify over this wanted
-- This function decides whether a particular constraint shoudl be
-- quantified over, given the type variables that are being quantified
quantifyPred qtvs pred
  = case classifyPredType pred of
      ClassPred cls tys
         | isIPClass cls    -> True -- See note [Inheriting implicit parameters]
         | otherwise        -> tyCoVarsOfTypes tys `intersectsVarSet` qtvs
                               
      EqPred NomEq ty1 ty2  -> quant_fun ty1 || quant_fun ty2
        -- representational equality is like a class constraint
      EqPred ReprEq ty1 ty2 -> tyCoVarsOfTypes [ty1, ty2] `intersectsVarSet` qtvs
      
      IrredPred ty          -> tyCoVarsOfType ty `intersectsVarSet` qtvs
      TuplePred {}          -> False
  where
    -- See Note [Quantifying over equality constraints]
    quant_fun ty
      = case tcSplitTyConApp_maybe ty of
          Just (tc, tys) | isTypeFamilyTyCon tc
                         -> tyCoVarsOfTypes tys `intersectsVarSet` qtvs
          _ -> False

-- Superclasses

mkMinimalBySCs :: [PredType] -> [PredType]
-- Remove predicates that can be deduced from others by superclasses
mkMinimalBySCs ptys = [ pty | pty <- ptys
                            , pty `not_in_preds` rec_scs ]
 where
   rec_scs           = concatMap trans_super_classes ptys
   not_in_preds p ps = not (any (eqType p) ps)

   trans_super_classes pred   -- Superclasses of pred, excluding pred itself
     = case classifyPredType pred of
         ClassPred cls tys -> transSuperClasses cls tys
         TuplePred ts      -> concatMap trans_super_classes ts
         _                 -> []

transSuperClasses :: Class -> [Type] -> [PredType]
transSuperClasses cls tys    -- Superclasses of (cls tys),
                             -- excluding (cls tys) itself
  = concatMap trans_sc (immSuperClasses cls tys)
  where
    trans_sc :: PredType -> [PredType]
    -- (trans_sc p) returns (p : p's superclasses)
    trans_sc p = case classifyPredType p of
                   ClassPred cls tys -> p : transSuperClasses cls tys
                   TuplePred ps      -> concatMap trans_sc ps
                   _                 -> [p]

immSuperClasses :: Class -> [Type] -> [PredType]
immSuperClasses cls tys
  = substTheta (zipTopTCvSubst tyvars tys) sc_theta
  where
    (tyvars,sc_theta,_,_) = classBigSig cls

{-
Note [Inheriting implicit parameters]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider this:

        f x = (x::Int) + ?y

where f is *not* a top-level binding.
From the RHS of f we'll get the constraint (?y::Int).
There are two types we might infer for f:

        f :: Int -> Int

(so we get ?y from the context of f's definition), or

        f :: (?y::Int) => Int -> Int

At first you might think the first was better, because then
?y behaves like a free variable of the definition, rather than
having to be passed at each call site.  But of course, the WHOLE
IDEA is that ?y should be passed at each call site (that's what
dynamic binding means) so we'd better infer the second.

BOTTOM LINE: when *inferring types* you must quantify over implicit
parameters, *even if* they don't mention the bound type variables.
Reason: because implicit parameters, uniquely, have local instance
declarations. See the predicate quantifyPred.

Note [Quantifying over equality constraints]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Should we quantify over an equality constraint (s ~ t)?  In general, we don't.
Doing so may simply postpone a type error from the function definition site to
its call site.  (At worst, imagine (Int ~ Bool)).

However, consider this
         forall a. (F [a] ~ Int) => blah
Should we quantify over the (F [a] ~ Int).  Perhaps yes, because at the call
site we will know 'a', and perhaps we have instance  F [Bool] = Int.
So we *do* quantify over a type-family equality where the arguments mention
the quantified variables.

************************************************************************
*                                                                      *
\subsection{Predicates}
*                                                                      *
************************************************************************
-}

isSigmaTy :: TcType -> Bool
-- isSigmaTy returns true of any qualified type.  It doesn't
-- *necessarily* have any foralls.  E.g
--        f :: (?x::Int) => Int -> Int
isSigmaTy ty | Just ty' <- tcView ty = isSigmaTy ty'
isSigmaTy (ForAllTy (Named {}) _) = True
isSigmaTy (ForAllTy (Anon a) _)   = isPredTy a
isSigmaTy _                       = False

isRhoTy :: TcType -> Bool   -- True of TcRhoTypes; see Note [TcRhoType]
isRhoTy ty | Just ty' <- tcView ty = isRhoTy ty'
isRhoTy (ForAllTy (Named {}) _) = False
isRhoTy (ForAllTy (Anon a) r)   = not (isPredTy a) && isRhoTy r
isRhoTy _                       = True

isOverloadedTy :: Type -> Bool
-- Yes for a type of a function that might require evidence-passing
-- Used only by bindLocalMethods
isOverloadedTy ty | Just ty' <- tcView ty = isOverloadedTy ty'
isOverloadedTy (ForAllTy (Named {}) ty) = isOverloadedTy ty
isOverloadedTy (ForAllTy (Anon a) _)    = isPredTy a
isOverloadedTy _                        = False

isFloatTy, isDoubleTy, isIntegerTy, isIntTy, isWordTy, isBoolTy,
    isUnitTy, isCharTy, isAnyTy :: Type -> Bool
isFloatTy      = is_tc floatTyConKey
isDoubleTy     = is_tc doubleTyConKey
isIntegerTy    = is_tc integerTyConKey
isIntTy        = is_tc intTyConKey
isWordTy       = is_tc wordTyConKey
isBoolTy       = is_tc boolTyConKey
isUnitTy       = is_tc unitTyConKey
isCharTy       = is_tc charTyConKey
isAnyTy        = is_tc anyTyConKey

isStringTy :: Type -> Bool
isStringTy ty
  = case tcSplitTyConApp_maybe ty of
      Just (tc, [arg_ty]) -> tc == listTyCon && isCharTy arg_ty
      _                   -> False

is_tc :: Unique -> Type -> Bool
-- Newtypes are opaque to this
is_tc uniq ty = case tcSplitTyConApp_maybe ty of
                        Just (tc, _) -> uniq == getUnique tc
                        Nothing      -> False

-- | Does the given tyvar appear in the given type outside of any
-- non-newtypes? Assume we're looking for @a@. Says "yes" for
-- @a@, @N a@, @b a@, @a b@, @b (N a)@. Says "no" for
-- @[a]@, @Maybe a@, @T a@, where @N@ is a newtype and @T@ is a datatype.
isTyVarExposed :: TcTyVar -> TcType -> Bool
isTyVarExposed tv (TyVarTy tv')   = tv == tv'
isTyVarExposed tv (TyConApp tc tys)
  | isNewTyCon tc                 = any (isTyVarExposed tv) tys
  | otherwise                     = False
isTyVarExposed _  (LitTy {})      = False
isTyVarExposed tv (AppTy fun arg) = isTyVarExposed tv fun
                                 || isTyVarExposed tv arg
isTyVarExposed _  (ForAllTy {})   = False
isTyVarExposed tv (CastTy ty _)   = isTyVarExposed tv ty
isTyVarExposed _  (CoercionTy {}) = False

{-
************************************************************************
*                                                                      *
\subsection{Misc}
*                                                                      *
************************************************************************
-}

deNoteType :: Type -> Type
-- Remove all *outermost* type synonyms and other notes
deNoteType ty | Just ty' <- tcView ty = deNoteType ty'
deNoteType ty = ty

{-
Find the free tycons and classes of a type.  This is used in the front
end of the compiler.
-}

orphNamesOfTyCon :: TyCon -> NameSet
orphNamesOfTyCon tycon = unitNameSet (getName tycon) `unionNameSet` case tyConClass_maybe tycon of
    Nothing  -> emptyNameSet
    Just cls -> unitNameSet (getName cls)

orphNamesOfType :: Type -> NameSet
orphNamesOfType ty | Just ty' <- tcView ty = orphNamesOfType ty'
                -- Look through type synonyms (Trac #4912)
orphNamesOfType (TyVarTy _)          = emptyNameSet
orphNamesOfType (LitTy {})           = emptyNameSet
orphNamesOfType (TyConApp tycon tys) = orphNamesOfTyCon tycon
                                       `unionNameSet` orphNamesOfTypes tys
orphNamesOfType (ForAllTy bndr res)  = orphNamesOfTyCon funTyCon   -- NB!  See Trac #8535
                                       `unionNameSet` orphNamesOfType (binderType bndr)
                                       `unionNameSet` orphNamesOfType res
orphNamesOfType (AppTy fun arg)      = orphNamesOfType fun `unionNameSet` orphNamesOfType arg
orphNamesOfType (CastTy ty co)       = orphNamesOfType ty `unionNameSet` orphNamesOfCo co
orphNamesOfType (CoercionTy co)      = orphNamesOfCo co

orphNamesOfThings :: (a -> NameSet) -> [a] -> NameSet
orphNamesOfThings f = foldr (unionNameSet . f) emptyNameSet

orphNamesOfTypes :: [Type] -> NameSet
orphNamesOfTypes = orphNamesOfThings orphNamesOfType

orphNamesOfDFunHead :: Type -> NameSet
-- Find the free type constructors and classes
-- of the head of the dfun instance type
-- The 'dfun_head_type' is because of
--      instance Foo a => Baz T where ...
-- The decl is an orphan if Baz and T are both not locally defined,
--      even if Foo *is* locally defined
orphNamesOfDFunHead dfun_ty
  = case tcSplitSigmaTy dfun_ty of
        (_, _, head_ty) -> orphNamesOfType head_ty

orphNamesOfCo :: Coercion -> NameSet
orphNamesOfCo (Refl _ ty)           = orphNamesOfType ty
orphNamesOfCo (TyConAppCo _ tc cos) = unitNameSet (getName tc) `unionNameSet` orphNamesOfCoArgs cos
orphNamesOfCo (AppCo co1 h co2)     = orphNamesOfCo co1 `unionNameSet` orphNamesOfCo h `unionNameSet` orphNamesOfCoArg co2
orphNamesOfCo (ForAllCo cobndr co)
  = orphNamesOfCo (coBndrKindCo cobndr) `unionNameSet` orphNamesOfCo co
orphNamesOfCo (CoVarCo _)           = emptyNameSet
orphNamesOfCo (AxiomInstCo con _ cos) = orphNamesOfCoCon con `unionNameSet` orphNamesOfCoArgs cos
orphNamesOfCo (PhantomCo h t1 t2)   = orphNamesOfCo h `unionNameSet` orphNamesOfType t1 `unionNameSet` orphNamesOfType t2
orphNamesOfCo (UnsafeCo _ _ ty1 ty2)= orphNamesOfType ty1 `unionNameSet` orphNamesOfType ty2
orphNamesOfCo (SymCo co)            = orphNamesOfCo co
orphNamesOfCo (TransCo co1 co2)     = orphNamesOfCo co1 `unionNameSet` orphNamesOfCo co2
orphNamesOfCo (NthCo _ co)          = orphNamesOfCo co
orphNamesOfCo (LRCo  _ co)          = orphNamesOfCo co
orphNamesOfCo (InstCo co arg)       = orphNamesOfCo co `unionNameSet` orphNamesOfCoArg arg
orphNamesOfCo (CoherenceCo co1 co2) = orphNamesOfCo co1 `unionNameSet` orphNamesOfCo co2
orphNamesOfCo (KindCo co)           = orphNamesOfCo co
orphNamesOfCo (KindAppCo co)        = orphNamesOfCo co
orphNamesOfCo (SubCo co)            = orphNamesOfCo co
orphNamesOfCo (AxiomRuleCo _ ts cs) = orphNamesOfTypes ts `unionNameSet`
                                      orphNamesOfCos cs

orphNamesOfCos :: [Coercion] -> NameSet
orphNamesOfCos = orphNamesOfThings orphNamesOfCo

orphNamesOfCoArg :: CoercionArg -> NameSet
orphNamesOfCoArg (TyCoArg co)          = orphNamesOfCo co
orphNamesOfCoArg (CoCoArg _ h co1 co2) = orphNamesOfCo h `unionNameSet`
                                         orphNamesOfCo co1 `unionNameSet`
                                         orphNamesOfCo co2

orphNamesOfCoArgs :: [CoercionArg] -> NameSet
orphNamesOfCoArgs = orphNamesOfThings orphNamesOfCoArg

orphNamesOfCoCon :: CoAxiom br -> NameSet
orphNamesOfCoCon (CoAxiom { co_ax_tc = tc, co_ax_branches = branches })
  = orphNamesOfTyCon tc `unionNameSet` orphNamesOfCoAxBranches branches

orphNamesOfCoAxBranches :: BranchList CoAxBranch br -> NameSet
orphNamesOfCoAxBranches = brListFoldr (unionNameSet . orphNamesOfCoAxBranch) emptyNameSet

orphNamesOfCoAxBranch :: CoAxBranch -> NameSet
orphNamesOfCoAxBranch (CoAxBranch { cab_lhs = lhs, cab_rhs = rhs })
  = orphNamesOfTypes lhs `unionNameSet` orphNamesOfType rhs

{-
************************************************************************
*                                                                      *
\subsection[TysWiredIn-ext-type]{External types}
*                                                                      *
************************************************************************

The compiler's foreign function interface supports the passing of a
restricted set of types as arguments and results (the restricting factor
being the )
-}

tcSplitIOType_maybe :: Type -> Maybe (TyCon, Type)
-- (tcSplitIOType_maybe t) returns Just (IO,t',co)
--              if co : t ~ IO t'
--              returns Nothing otherwise
tcSplitIOType_maybe ty
  = case tcSplitTyConApp_maybe ty of
        Just (io_tycon, [io_res_ty])
         | io_tycon `hasKey` ioTyConKey ->
            Just (io_tycon, io_res_ty)
        _ ->
            Nothing

isFFITy :: Type -> Bool
-- True for any TyCon that can possibly be an arg or result of an FFI call
isFFITy ty = isValid (checkRepTyCon legalFFITyCon ty empty)

isFFIArgumentTy :: DynFlags -> Safety -> Type -> Validity
-- Checks for valid argument type for a 'foreign import'
isFFIArgumentTy dflags safety ty
   = checkRepTyCon (legalOutgoingTyCon dflags safety) ty empty

isFFIExternalTy :: Type -> Validity
-- Types that are allowed as arguments of a 'foreign export'
isFFIExternalTy ty = checkRepTyCon legalFEArgTyCon ty empty

isFFIImportResultTy :: DynFlags -> Type -> Validity
isFFIImportResultTy dflags ty
  = checkRepTyCon (legalFIResultTyCon dflags) ty empty

isFFIExportResultTy :: Type -> Validity
isFFIExportResultTy ty = checkRepTyCon legalFEResultTyCon ty empty

isFFIDynTy :: Type -> Type -> Validity
-- The type in a foreign import dynamic must be Ptr, FunPtr, or a newtype of
-- either, and the wrapped function type must be equal to the given type.
-- We assume that all types have been run through normaliseFfiType, so we don't
-- need to worry about expanding newtypes here.
isFFIDynTy expected ty
    -- Note [Foreign import dynamic]
    -- In the example below, expected would be 'CInt -> IO ()', while ty would
    -- be 'FunPtr (CDouble -> IO ())'.
    | Just (tc, [ty']) <- splitTyConApp_maybe ty
    , tyConUnique tc `elem` [ptrTyConKey, funPtrTyConKey]
    , eqType ty' expected
    = IsValid
    | otherwise
    = NotValid (vcat [ ptext (sLit "Expected: Ptr/FunPtr") <+> pprParendType expected <> comma
                     , ptext (sLit "  Actual:") <+> ppr ty ])

isFFILabelTy :: Type -> Validity
-- The type of a foreign label must be Ptr, FunPtr, or a newtype of either.
isFFILabelTy ty = checkRepTyCon ok ty extra
  where
    ok tc = tc `hasKey` funPtrTyConKey || tc `hasKey` ptrTyConKey
    extra = ptext (sLit "A foreign-imported address (via &foo) must have type (Ptr a) or (FunPtr a)")

isFFIPrimArgumentTy :: DynFlags -> Type -> Validity
-- Checks for valid argument type for a 'foreign import prim'
-- Currently they must all be simple unlifted types, or the well-known type
-- Any, which can be used to pass the address to a Haskell object on the heap to
-- the foreign function.
isFFIPrimArgumentTy dflags ty
  | isAnyTy ty = IsValid
  | otherwise  = checkRepTyCon (legalFIPrimArgTyCon dflags) ty empty

isFFIPrimResultTy :: DynFlags -> Type -> Validity
-- Checks for valid result type for a 'foreign import prim'
-- Currently it must be an unlifted type, including unboxed tuples.
isFFIPrimResultTy dflags ty
   = checkRepTyCon (legalFIPrimResultTyCon dflags) ty empty

isFunPtrTy :: Type -> Bool
isFunPtrTy ty = isValid (checkRepTyCon (`hasKey` funPtrTyConKey) ty empty)

-- normaliseFfiType gets run before checkRepTyCon, so we don't
-- need to worry about looking through newtypes or type functions
-- here; that's already been taken care of.
checkRepTyCon :: (TyCon -> Bool) -> Type -> SDoc -> Validity
checkRepTyCon check_tc ty extra
  = case splitTyConApp_maybe ty of
      Just (tc, tys)
        | isNewTyCon tc -> NotValid (hang msg 2 (mk_nt_reason tc tys $$ nt_fix))
        | check_tc tc   -> IsValid
        | otherwise     -> NotValid (msg $$ extra)
      Nothing -> NotValid (quotes (ppr ty) <+> ptext (sLit "is not a data type") $$ extra)
  where
    msg = quotes (ppr ty) <+> ptext (sLit "cannot be marshalled in a foreign call")
    mk_nt_reason tc tys
      | null tys  = ptext (sLit "because its data construtor is not in scope")
      | otherwise = ptext (sLit "because the data construtor for")
                    <+> quotes (ppr tc) <+> ptext (sLit "is not in scope")
    nt_fix = ptext (sLit "Possible fix: import the data constructor to bring it into scope")

{-
Note [Foreign import dynamic]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A dynamic stub must be of the form 'FunPtr ft -> ft' where ft is any foreign
type.  Similarly, a wrapper stub must be of the form 'ft -> IO (FunPtr ft)'.

We use isFFIDynTy to check whether a signature is well-formed. For example,
given a (illegal) declaration like:

foreign import ccall "dynamic"
  foo :: FunPtr (CDouble -> IO ()) -> CInt -> IO ()

isFFIDynTy will compare the 'FunPtr' type 'CDouble -> IO ()' with the curried
result type 'CInt -> IO ()', and return False, as they are not equal.


----------------------------------------------
These chaps do the work; they are not exported
----------------------------------------------
-}

legalFEArgTyCon :: TyCon -> Bool
legalFEArgTyCon tc
  -- It's illegal to make foreign exports that take unboxed
  -- arguments.  The RTS API currently can't invoke such things.  --SDM 7/2000
  = boxedMarshalableTyCon tc

legalFIResultTyCon :: DynFlags -> TyCon -> Bool
legalFIResultTyCon dflags tc
  | tc == unitTyCon         = True
  | otherwise               = marshalableTyCon dflags tc

legalFEResultTyCon :: TyCon -> Bool
legalFEResultTyCon tc
  | tc == unitTyCon         = True
  | otherwise               = boxedMarshalableTyCon tc

legalOutgoingTyCon :: DynFlags -> Safety -> TyCon -> Bool
-- Checks validity of types going from Haskell -> external world
legalOutgoingTyCon dflags _ tc
  = marshalableTyCon dflags tc

legalFFITyCon :: TyCon -> Bool
-- True for any TyCon that can possibly be an arg or result of an FFI call
legalFFITyCon tc
  | isUnLiftedTyCon tc = True
  | tc == unitTyCon    = True
  | otherwise          = boxedMarshalableTyCon tc

marshalableTyCon :: DynFlags -> TyCon -> Bool
marshalableTyCon dflags tc
  |  (xopt Opt_UnliftedFFITypes dflags
      && isUnLiftedTyCon tc
      && not (isUnboxedTupleTyCon tc)
      && case tyConPrimRep tc of        -- Note [Marshalling VoidRep]
           VoidRep -> False
           _       -> True)
  = True
  | otherwise
  = boxedMarshalableTyCon tc

boxedMarshalableTyCon :: TyCon -> Bool
boxedMarshalableTyCon tc
   | getUnique tc `elem` [ intTyConKey, int8TyConKey, int16TyConKey
                         , int32TyConKey, int64TyConKey
                         , wordTyConKey, word8TyConKey, word16TyConKey
                         , word32TyConKey, word64TyConKey
                         , floatTyConKey, doubleTyConKey
                         , ptrTyConKey, funPtrTyConKey
                         , charTyConKey
                         , stablePtrTyConKey
                         , boolTyConKey
                         ]
  = True

  | otherwise = False

legalFIPrimArgTyCon :: DynFlags -> TyCon -> Bool
-- Check args of 'foreign import prim', only allow simple unlifted types.
-- Strictly speaking it is unnecessary to ban unboxed tuples here since
-- currently they're of the wrong kind to use in function args anyway.
legalFIPrimArgTyCon dflags tc
  | xopt Opt_UnliftedFFITypes dflags
    && isUnLiftedTyCon tc
    && not (isUnboxedTupleTyCon tc)
  = True
  | otherwise
  = False

legalFIPrimResultTyCon :: DynFlags -> TyCon -> Bool
-- Check result type of 'foreign import prim'. Allow simple unlifted
-- types and also unboxed tuple result types '... -> (# , , #)'
legalFIPrimResultTyCon dflags tc
  | xopt Opt_UnliftedFFITypes dflags
    && isUnLiftedTyCon tc
    && (isUnboxedTupleTyCon tc
        || case tyConPrimRep tc of      -- Note [Marshalling VoidRep]
           VoidRep -> False
           _       -> True)
  = True
  | otherwise
  = False

{-
Note [Marshalling VoidRep]
~~~~~~~~~~~~~~~~~~~~~~~~~~
We don't treat State# (whose PrimRep is VoidRep) as marshalable.
In turn that means you can't write
        foreign import foo :: Int -> State# RealWorld

Reason: the back end falls over with panic "primRepHint:VoidRep";
        and there is no compelling reason to permit it
-}
