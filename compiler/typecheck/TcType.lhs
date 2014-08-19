%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section[TcType]{Types used in the typechecker}

This module provides the Type interface for front-end parts of the
compiler.  These parts

        * treat "source types" as opaque:
                newtypes, and predicates are meaningful.
        * look through usage types

The "tc" prefix is for "TypeChecker", because the type checker
is the principal client.

\begin{code}
{-# LANGUAGE CPP #-}

module TcType (
  --------------------------------
  -- Types
  TcType, TcSigmaType, TcRhoType, TcTauType, TcPredType, TcThetaType,
  TcTyVar, TcTyVarSet, TcTyCoVarSet, TcKind, TcCoVar, TcTyCoVar,

  -- Untouchables
  Untouchables(..), noUntouchables, pushUntouchables, isTouchable,

  --------------------------------
  -- MetaDetails
  UserTypeCtxt(..), pprUserTypeCtxt,
  TcTyVarDetails(..), pprTcTyVarDetails, vanillaSkolemTv, superSkolemTv,
  MetaDetails(Flexi, Indirect), MetaInfo(..),
  isImmutableTyVar, isSkolemTyVar, isSkolemTyCoVar,
  isMetaTyVar,  isMetaTyVarTy, isTyVarTy,
  isSigTyVar, isOverlappableTyVar,  isTyConableTyVar, isFlatSkolTyVar,
  isAmbiguousTyVar, metaTvRef, metaTyVarInfo,
  isFlexi, isIndirect, isRuntimeUnkSkol,
  metaTyVarUntouchables, setMetaTyVarUntouchables,
  isTouchableMetaTyVar, isFloatedTouchableMetaTyVar,

  --------------------------------
  -- Builders
  mkPhiTy, mkInvSigmaTy, mkSigmaTy, mkTcEqPred,

  --------------------------------
  -- Splitters
  -- These are important because they do not look through newtypes
  tcView,
  tcSplitForAllTys, tcSplitNamedForAllTys, tcSplitNamedForAllTysB,
  tcIsDepPiTy,
  tcSplitPhiTy, tcSplitPredFunTy_maybe,
  tcSplitFunTy_maybe, tcSplitFunTys, tcFunArgTy, tcFunResultTy, tcSplitFunTysN,
  tcSplitTyConApp, tcSplitTyConApp_maybe, tcTyConAppTyCon, tcTyConAppArgs,
  tcSplitAppTy_maybe, tcSplitAppTy, tcSplitAppTys, repSplitAppTy_maybe,
  tcInstHeadTyNotSynonym, tcInstHeadTyAppAllTyVars,
  tcGetTyVar_maybe, tcGetTyCoVar_maybe, tcGetTyVar,
  tcSplitSigmaTy, tcDeepSplitSigmaTy_maybe,

  ---------------------------------
  -- Predicates.
  -- Again, newtypes are opaque
  eqType, eqTypes, eqPred, cmpType, cmpTypes, cmpPred, eqTypeX,
  pickyEqType, tcEqType, tcEqKind,
  isSigmaTy, isOverloadedTy,
  isDoubleTy, isFloatTy, isIntTy, isWordTy, isStringTy,
  isIntegerTy, isBoolTy, isUnitTy, isCharTy,
  isTauTy, isTauTyCon, tcIsTyVarTy, tcIsPiTy,
  isSynFamilyTyConApp,
  isPredTy, isTyVarClassPred,

  ---------------------------------
  -- Misc type manipulators
  deNoteType, occurCheckExpand, OccCheckResult(..),
  orphNamesOfType, orphNamesOfDFunHead, orphNamesOfCo,
  orphNamesOfTypes, orphNamesOfCoCon,
  getDFunTyKey,
  evVarPred_maybe, evVarPred,

  ---------------------------------
  -- Predicate types
  mkMinimalBySCs, transSuperClasses, immSuperClasses,

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
  isFFIDotnetTy,       -- :: DynFlags -> Type -> Bool
  isFFIDotnetObjTy,    -- :: Type -> Bool
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
  mkTyConApp, mkAppTy, mkAppTys, applyTy, applyTys,
  mkTyCoVarTy, mkTyCoVarTys, mkTyConTy, mkOnlyTyVarTy,
  mkOnlyTyVarTys,

  isClassPred, isEqPred, isIPPred,
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

  tyVarsOnlyOfType, tyVarsOnlyOfTypes, tyCoVarsOfType, tyCoVarsOfTypes,
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
import BasicTypes
import Util
import Maybes
import ListSetOps
import Outputable
import FastString
import Pair

import Data.IORef
import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))
\end{code}

%************************************************************************
%*                                                                      *
\subsection{Types}
%*                                                                      *
%************************************************************************

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

\begin{code}
type TcTyVar = TyVar    -- Used only during type inference
type TcCoVar = CoVar    -- Used only during type inference
type TcType = Type      -- A TcType can have mutable type variables
type TcTyCoVar = Var    -- Either a TcTyVar or a CoVar
        -- Invariant on TcTypes:
        --      forall a. T
        -- a cannot occur inside a MutTyVar in T; that is,
        -- T is "flattened" before quantifying over a
type TcBinder = Binder

-- These types do not have boxy type variables in them
type TcPredType     = PredType
type TcThetaType    = ThetaType
type TcSigmaType    = TcType
type TcRhoType      = TcType
type TcTauType      = TcType
type TcKind         = Kind
type TcTyVarSet     = TyVarSet
type TcTyCoVarSet   = TyCoVarSet

-- | A 'TcPhaseType' is a 'DependenceFlag' paired with a 'TcType'
type TcPhaseType      = (DependenceFlag, TcType)
type TcPhaseSigmaType = TcPhaseType
type TcPhaseRhoType   = TcPhaseType

phaseType :: TcDepType -> TcType
phaseType = snd

phaseDep :: TcDepType -> DependenceFlag
phaseDep = fst
\end{code}


%************************************************************************
%*                                                                      *
\subsection{TyVarDetails}
%*                                                                      *
%************************************************************************

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

\begin{code}
-- A TyVarDetails is inside a TyVar
data TcTyVarDetails
  = SkolemTv      -- A skolem
       Bool       -- True <=> this skolem type variable can be overlapped
                  --          when looking up instances
                  -- See Note [Binding when looking up instances] in InstEnv

  | RuntimeUnk    -- Stands for an as-yet-unknown type in the GHCi
                  -- interactive context

  | FlatSkol TcType
           -- The "skolem" obtained by flattening during
           -- constraint simplification

           -- In comments we will use the notation alpha[flat = ty]
           -- to represent a flattening skolem variable alpha
           -- identified with type ty.

  | MetaTv { mtv_info  :: MetaInfo
           , mtv_ref   :: IORef MetaDetails
           , mtv_untch :: Untouchables }  -- See Note [Untouchable type variables]

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
   = TauTv         -- This MetaTv is an ordinary unification variable
                   -- A TauTv is always filled in with a tau-type, which
                   -- never contains any ForAlls

   | PolyTv        -- Like TauTv, but can unify with a sigma-type

   | SigTv         -- A variant of TauTv, except that it should not be
                   -- unified with a type, only with a type variable
                   -- SigTvs are only distinguished to improve error messages
                   --      see Note [Signature skolems]
                   --      The MetaDetails, if filled in, will
                   --      always be another SigTv or a SkolemTv

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
  | LamPatSigCtxt               -- Type sig in lambda pattern
                        --      f (x::t) = ...
  | BindPatSigCtxt      -- Type sig in pattern binding pattern
                        --      (x::t, y) = e
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
\end{code}


-- Notes re TySynCtxt
-- We allow type synonyms that aren't types; e.g.  type List = []
--
-- If the RHS mentions tyvars that aren't in scope, we'll
-- quantify over them:
--      e.g.    type T = a->a
-- will become  type T = forall a. a->a
--
-- With gla-exts that's right, but for H98 we should complain.


%************************************************************************
%*                                                                      *
                Untoucable type variables
%*                                                                      *
%************************************************************************

Note [Untouchable type variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* Each unification variable (MetaTv)
  and each Implication
  has a level number (of type Untouchables)

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
                numbers are LESS THAN the ic_untch of the implication


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
first solveInteract step leaves 'uf' un-unified. Then we move inside
the implication where a new constraint
       uf  ~  beta
emerges. If we (wrongly) spontaneously solved it to get uf := beta,
the whole implication disappears but when we pop out again we are left with
(F Int ~ uf) which will be unified by our final solveCTyFunEqs stage and
uf will get unified *once more* to (F Int).

\begin{code}
newtype Untouchables = Untouchables Int
  -- See Note [Untouchable type variables] for what this Int is

noUntouchables :: Untouchables
noUntouchables = Untouchables 0   -- 0 = outermost level

pushUntouchables :: Untouchables -> Untouchables
pushUntouchables (Untouchables us) = Untouchables (us+1)

isFloatedTouchable :: Untouchables -> Untouchables -> Bool
isFloatedTouchable (Untouchables ctxt_untch) (Untouchables tv_untch)
  = ctxt_untch < tv_untch

isTouchable :: Untouchables -> Untouchables -> Bool
isTouchable (Untouchables ctxt_untch) (Untouchables tv_untch)
  = ctxt_untch == tv_untch   -- NB: invariant ctxt_untch >= tv_untch
                             --     So <= would be equivalent

checkTouchableInvariant :: Untouchables -> Untouchables -> Bool
-- Checks (MetaTvInv) from Note [Untouchable type variables]
checkTouchableInvariant (Untouchables ctxt_untch) (Untouchables tv_untch)
  = ctxt_untch >= tv_untch

instance Outputable Untouchables where
  ppr (Untouchables us) = ppr us
\end{code}


%************************************************************************
%*                                                                      *
                Pretty-printing
%*                                                                      *
%************************************************************************

\begin{code}
pprTcTyVarDetails :: TcTyVarDetails -> SDoc
-- For debugging
pprTcTyVarDetails (SkolemTv True)  = ptext (sLit "ssk")
pprTcTyVarDetails (SkolemTv False) = ptext (sLit "sk")
pprTcTyVarDetails (RuntimeUnk {})  = ptext (sLit "rt")
pprTcTyVarDetails (FlatSkol {})    = ptext (sLit "fsk")
pprTcTyVarDetails (MetaTv { mtv_info = info, mtv_untch = untch })
  = pp_info <> brackets (ppr untch)
  where
    pp_info = case info of
                PolyTv -> ptext (sLit "poly")
                TauTv  -> ptext (sLit "tau")
                SigTv  -> ptext (sLit "sig")

pprUserTypeCtxt :: UserTypeCtxt -> SDoc
pprUserTypeCtxt (InfSigCtxt n)    = ptext (sLit "the inferred type for") <+> quotes (ppr n)
pprUserTypeCtxt (FunSigCtxt n)    = ptext (sLit "the type signature for") <+> quotes (ppr n)
pprUserTypeCtxt (RuleSigCtxt n)   = ptext (sLit "a RULE for") <+> quotes (ppr n)
pprUserTypeCtxt ExprSigCtxt       = ptext (sLit "an expression type signature")
pprUserTypeCtxt (ConArgCtxt c)    = ptext (sLit "the type of the constructor") <+> quotes (ppr c)
pprUserTypeCtxt (TySynCtxt c)     = ptext (sLit "the RHS of the type synonym") <+> quotes (ppr c)
pprUserTypeCtxt ThBrackCtxt       = ptext (sLit "a Template Haskell quotation [t|...|]")
pprUserTypeCtxt LamPatSigCtxt     = ptext (sLit "a pattern type signature")
pprUserTypeCtxt BindPatSigCtxt    = ptext (sLit "a pattern type signature")
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
\end{code}


%************************************************************************
%*                  *


    Finding type family instances
%*                  *
%************************************************************************

\begin{code}
-- | Finds outermost type-family applications occuring in a type,
-- after expanding synonyms.
tcTyFamInsts :: Type -> [(TyCon, [Type])]
tcTyFamInsts ty
  | Just exp_ty <- tcView ty    = tcTyFamInsts exp_ty
tcTyFamInsts (TyVarTy _)        = []
tcTyFamInsts (TyConApp tc tys)
  | isSynFamilyTyCon tc         = [(tc, tys)]
  | otherwise                   = concat (map tcTyFamInsts tys)
tcTyFamInsts (LitTy {})         = []
tcTyFamInsts (PiTy bndr ty)     = tcTyFamInsts (binderType bndr)
                                  ++ tcTyFamInsts ty
tcTyFamInsts (AppTy ty1 ty2)    = tcTyFamInsts ty1 ++ tcTyFamInsts ty2
tcTyFamInsts (CastTy ty co)     = tcTyFamInsts ty ++ tcTyFamInstsCo co
tcTyFamInsts (CoercionTy co)    = tcTyFamInstsCo co

tcTyFamInstsCo :: Coercion -> [(TyCon, [Type])]
tcTyFamInstsCo = go
  where
    go (Refl _ ty)           = tcTyFamInsts ty
    go co@(TyConAppCo _ tc args)
      | isSynFamilyTyCon tc  = let Pair tyl tyr = coercionKind co
                                   (_tc1, tysl) = splitTyConApp tyl
                                   (_tc2, tysr) = splitTyConApp tyr in
                               ASSERT( tc == _tc1 && tc == _tc2 )
                               [(tc, tysl), (tc, tysr)]
      | otherwise            = concatMap go_arg args
    go (AppCo co arg)        = go co ++ go_arg arg
    go (PiCo cobndr co)
      | Just (h, _, _) <- splitHeteroCoBndr_maybe cobndr
                             = go h ++ go co
      | otherwise            = go co
    go (CoVarCo _)           = []
    go (AxiomInstCo _ _ cos) = concatMap go_arg cos
    go (PhantomCo h ty1 ty2) = go h ++ tcTyFamInsts ty1 ++ tcTyFamInsts ty2
    go (UnsafeCo _ ty1 ty2)  = tcTyFamInsts ty1 ++ tcTyFamInsts ty2
    go (SymCo co)            = go co
    go (TransCo co1 co2)     = go co1 ++ go co2
    go (NthCo _ co)          = go co
    go (LRCo _ co)           = go co
    go (InstCo co arg)       = go co ++ go_arg arg
    go (CoherenceCo co1 co2) = go co1 ++ go co2
    go (KindCo co)           = go co
    go (SubCo co)            = go co
    go (AxiomRuleCo _ ts cs) = concatMap tcTyFamInsts ts ++ concatMap go cs

    go_arg (TyCoArg co)        = go co
    go_arg (CoCoArg _ co1 co2) = go co1 ++ go co2

\end{code}

%************************************************************************
%*                  *
          The "exact" free variables of a type
%*                  *
%************************************************************************

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

\begin{code}
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
    go (PiTy bndr ty)       = delBinderVar (go ty) bndr `unionVarSet` go (binderType bndr)
    go (CastTy ty co)       = go ty `unionVarSet` goCo co
    go (CoercionTy co)      = goCo co

    goCo (Refl _ ty)        = go ty
    goCo (TyConAppCo _ _ args)= goCoArgs args
    goCo (AppCo co arg)     = goCo co `unionVarSet` goCoArg arg
    goCo (PiCo bndr co)
      = let (vars, kinds) = coBndrVarsKinds bndr in
        goCo co `delVarSetList` vars `unionVarSet` exactTyCoVarsOfTypes kinds
    goCo (CoVarCo v)         = unitVarSet v
    goCo (AxiomInstCo _ _ args) = goCoArgs args
    goCo (PhantomCo h t1 t2) = goCo h `unionVarSet` go t1 `unionVarSet` go t2
    goCo (UnsafeCo _ t1 t2)  = go t1 `unionVarSet` go t2
    goCo (SymCo co)          = goCo co
    goCo (TransCo co1 co2)   = goCo co1 `unionVarSet` goCo co2
    goCo (NthCo _ co)        = goCo co
    goCo (LRCo _ co)         = goCo co
    goCo (InstCo co arg)     = goCo co `unionVarSet` goCoArg arg
    goCo (CoherenceCo c1 c2) = goCo c1 `unionVarSet` goCo c2
    goCo (KindCo co)         = goCo co
    goCo (SubCo co)          = goCo co
    goCo (AxiomRuleCo _ t c) = exactTyCoVarsOfTypes t `unionVarSet` goCos c

    goCos cos = foldr (unionVarSet . goCo) emptyVarSet cos

    goCoArg (TyCoArg co)        = goCo co
    goCoArg (CoCoArg _ co1 co2) = goCo co1 `unionVarSet` goCo co2

    goCoArgs args            = foldr (unionVarSet . goCoArg) emptyVarSet args

exactTyCoVarsOfTypes :: [Type] -> TyVarSet
exactTyCoVarsOfTypes tys = foldr (unionVarSet . exactTyCoVarsOfType) emptyVarSet tys
\end{code}

%************************************************************************
%*                                                                      *
                Predicates
%*                                                                      *
%************************************************************************

\begin{code}
isTouchableMetaTyVar :: Untouchables -> TcTyVar -> Bool
isTouchableMetaTyVar ctxt_untch tv
  | isTyVar tv
  = ASSERT2( isTcTyVar tv, ppr tv )
    case tcTyVarDetails tv of
      MetaTv { mtv_untch = tv_untch }
        -> ASSERT2( checkTouchableInvariant ctxt_untch tv_untch,
                    ppr tv $$ ppr tv_untch $$ ppr ctxt_untch )
           isTouchable ctxt_untch tv_untch
      _ -> False
  | otherwise = False

isFloatedTouchableMetaTyVar :: Untouchables -> TcTyVar -> Bool
isFloatedTouchableMetaTyVar ctxt_untch tv
  | isTyVar tv
  = ASSERT2( isTcTyVar tv, ppr tv )
    case tcTyVarDetails tv of
      MetaTv { mtv_untch = tv_untch } -> isFloatedTouchable ctxt_untch tv_untch
      _ -> False
  | otherwise = False

isImmutableTyVar :: TyCoVar -> Bool
isImmutableTyVar tv
  | isTcTyVar tv = isSkolemTyVar tv
  | otherwise    = True

isTyConableTyVar, isSkolemTyVar, isSkolemTyCoVar, isOverlappableTyVar,
  isMetaTyVar, isAmbiguousTyVar, isFlatSkolTyVar :: TcTyVar -> Bool

isTyConableTyVar tv
        -- True of a meta-type variable that can be filled in
        -- with a type constructor application; in particular,
        -- not a SigTv
  | isTyVar tv
  = ASSERT( isTcTyVar tv)
    case tcTyVarDetails tv of
        MetaTv { mtv_info = SigTv } -> False
        _                           -> True
  | otherwise = True

isFlatSkolTyVar tv
  = ASSERT2( isTcTyVar tv, ppr tv )
    case tcTyVarDetails tv of
        FlatSkol {} -> True
        _           -> False

isSkolemTyVar tv
  = ASSERT2( isTcTyVar tv, ppr tv )
    case tcTyVarDetails tv of
        SkolemTv {}   -> True
        FlatSkol {}   -> True
        RuntimeUnk {} -> True
        MetaTv {}     -> False

isSkolemTyCoVar tv
  = isCoVar tv || isSkolemTyVar tv

isOverlappableTyVar tv
  | isTyVar tv
  = ASSERT( isTcTyVar tv )
    case tcTyVarDetails tv of
        SkolemTv overlappable -> overlappable
        _                     -> False
  | otherwise = False

isMetaTyVar tv
  | isTyVar tv
  = ASSERT2( isTcTyVar tv, ppr tv )
    case tcTyVarDetails tv of
        MetaTv {} -> True
        _         -> False
  | otherwise = False

-- isAmbiguousTyVar is used only when reporting type errors
-- It picks out variables that are unbound, namely meta
-- type variables and the RuntimUnk variables created by
-- RtClosureInspect.zonkRTTIType.  These are "ambiguous" in
-- the sense that they stand for an as-yet-unknown type
isAmbiguousTyVar tv
  | isTyVar tv
  = ASSERT2( isTcTyVar tv, ppr tv )
    case tcTyVarDetails tv of
        MetaTv {}     -> True
        RuntimeUnk {} -> True
        _             -> False
  | otherwise = False

isMetaTyVarTy :: TcType -> Bool
isMetaTyVarTy (TyVarTy tv) = isMetaTyVar tv
isMetaTyVarTy _            = False

metaTyVarInfo :: TcTyVar -> MetaInfo
metaTyVarInfo tv
  = ASSERT( isTcTyVar tv )
    case tcTyVarDetails tv of
      MetaTv { mtv_info = info } -> info
      _ -> pprPanic "metaTyVarInfo" (ppr tv)

metaTyVarUntouchables :: TcTyVar -> Untouchables
metaTyVarUntouchables tv
  = ASSERT( isTcTyVar tv )
    case tcTyVarDetails tv of
      MetaTv { mtv_untch = untch } -> untch
      _ -> pprPanic "metaTyVarUntouchables" (ppr tv)

setMetaTyVarUntouchables :: TcTyVar -> Untouchables -> TcTyVar
setMetaTyVarUntouchables tv untch
  = ASSERT( isTcTyVar tv )
    case tcTyVarDetails tv of
      details@(MetaTv {}) -> setTcTyVarDetails tv (details { mtv_untch = untch })
      _ -> pprPanic "metaTyVarUntouchables" (ppr tv)

isSigTyVar :: Var -> Bool
isSigTyVar tv
  = ASSERT( isTcTyVar tv )
    case tcTyVarDetails tv of
        MetaTv { mtv_info = SigTv } -> True
        _                           -> False

metaTvRef :: TyVar -> IORef MetaDetails
metaTvRef tv
  = ASSERT2( isTcTyVar tv, ppr tv )
    case tcTyVarDetails tv of
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
\end{code}


%************************************************************************
%*                                                                      *
\subsection{Tau, sigma and rho}
%*                                                                      *
%************************************************************************

\begin{code}
mkSigmaTy :: [Binder] -> [PredType] -> Type -> Type
mkSigmaTy bndrs theta tau = mkForAllTys bndrs (mkPhiTy theta tau)

mkInvSigmaTy :: [TyCoVar] -> [PredType] -> Type -> Type
mkInvSigmaTy tyvars
  = mkSigmaTy (zipWith mkNamedBinder tyvars (repeat Invisible))

mkPhiTy :: [PredType] -> Type -> Type
mkPhiTy theta ty = foldr mkFunTy ty theta

mkTcEqPred :: TcType -> TcType -> Type
-- During type checking we build equalities between
-- type variables with OpenKind or ArgKind.  Ultimately
-- they will all settle, but we want the equality predicate
-- itself to have kind '*'.  I think.
--
-- But for now we call mkTyConApp, not mkEqPred, because the invariants
-- of the latter might not be satisfied during type checking.
-- Notably when we form an equalty   (a : OpenKind) ~ (Int : *)
--
-- But this is horribly delicate: what about type variables
-- that turn out to be bound to Int#?
mkTcEqPred ty1 ty2
  = mkTyConApp eqTyCon [k, ty1, ty2]
  where
    k = typeKind ty1
\end{code}

@isTauTy@ tests to see if a type is "simple".  It should not be called on a boxy type.

\begin{code}
isTauTy :: Type -> Bool
isTauTy ty | Just ty' <- tcView ty = isTauTy ty'
isTauTy (TyVarTy _)           = True
isTauTy (LitTy {})            = True
isTauTy (TyConApp tc tys)     = all isTauTy tys && isTauTyCon tc
isTauTy (AppTy a b)           = isTauTy a && isTauTy b
isTauTy (PiTy bndr b)
  | not (isDependentBinder bndr) = isTauTy (binderType bndr) && isTauTy b
  | otherwise                    = False
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
getDFunTyKey (PiTy bndr ty)
  | not (isDependentBinder bndr)     = getOccName funTyCon
  | otherwise                        = getDFunTyKey ty
getDFunTyKey (CastTy ty _)           = getDFunTyKey ty
getDFunTyKey t@(CoercionTy _)        = pprPanic "getDFunTyKey" (ppr t)

getDFunTyLitKey :: TyLit -> OccName
getDFunTyLitKey (NumTyLit n) = mkOccName Name.varName (show n)
getDFunTyLitKey (StrTyLit n) = mkOccName Name.varName (show n)  -- hm
\end{code}


%************************************************************************
%*                                                                      *
\subsection{Expanding and splitting}
%*                                                                      *
%************************************************************************

These tcSplit functions are like their non-Tc analogues, but
        *) they do not look through newtypes

However, they are non-monadic and do not follow through mutable type
variables.  It's up to you to make sure this doesn't matter.

\begin{code}
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

tcIsPiTy :: Type -> Bool
tcIsPiTy ty | Just ty' <- tcView ty = tcIsPiTy ty'
tcIsPiTy (PiTy {}) = True
tcIsPiTy _         = False

-- | Is this a dependent PiTy?
tcIsDepPiTy :: Type -> Bool
tcIsDepPiTy ty | Just ty' <- tcView ty = tcIsDepPiTy ty'
tcIsDepPiTy (PiTy bndr _) = isDependentBinder bndr
tcIsDepPiTy _             = False

tcSplitPredFunTy_maybe :: Type -> Maybe (PredType, Type)
-- Split off the first predicate argument from a type
tcSplitPredFunTy_maybe ty
  | Just ty' <- tcView ty = tcSplitPredFunTy_maybe ty'
tcSplitPredFunTy_maybe (PiTy bndr res)
  | not (isDependentBinder bndr)
  , let arg = binderType bndr
  , isPredTy arg
  = Just (arg, res)
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
  :: TcSigmaType
  -> Maybe ( [TcBinder]       -- visible arguments
           , [TcBinder]       -- invisible arguments
           , TcSigmaType)
-- Looks for a *non-trivial* quantified type (that is, with at least one
-- invisible argument), under zero or more visible binders

tcDeepSplitSigmaTy_maybe ty
  | Just (bndr, res) <- tcSplitPiTy_maybe ty
  , isVisibleBinder bndr
  , Just (vis, invis, sigma) <- tcDeepSplitSigmaTy_maybe res
  = Just (bndr:vis, invis, sigma)

  | (invis, sigma) <- tcSplitInvisPiTy ty
  , not (null invis)
  = Just ([], invis, sigma)

  | otherwise
  = Nothing

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
tcSplitTyConApp_maybe (PiTy bndr res)
  | not (isDependentBinder bndr)
  = Just (funTyCon, [binderType bndr, res])
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
tcSplitFunTy_maybe (PiTy bndr res)
  | not (isDependentBinder bndr)
  , let arg = binderType bndr
  , not (isPredTy arg)
  = Just (arg, res)
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
tcIsTyVarTy ty = isJust (tcGetTyVar_maybe ty)

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
        PiTy bndr res | not (isDependentBinder bndr)
                                -> ok [binderType bndr, res]
        _                       -> False
  where
        -- Check that all the types are type variables,
        -- and that each is distinct
    ok tys = equalLength tvs tys && hasNoDups tvs
           where
             tvs = mapMaybe get_tv tys

    get_tv (TyVarTy tv)  = Just tv      -- through synonyms
    get_tv _             = Nothing
\end{code}

\begin{code}
tcEqKind :: TcKind -> TcKind -> Bool
tcEqKind = tcEqType

tcEqType :: TcType -> TcType -> Bool
-- tcEqType is a proper, sensible type-equality function, that does
-- just what you'd expect The function Type.eqType (currently) has a
-- grotesque hack that makes Constraint = *, and that is NOT what we
-- want in the type checker! 
-- See also Trac #8553.

tcEqType ty1 ty2
  = go init_env ty1 ty2
  where
    init_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfType ty1 `unionVarSet` tyCoVarsOfType ty2))
    go env t1 t2 | Just t1' <- tcView t1 = go env t1' t2
                 | Just t2' <- tcView t2 = go env t1 t2'
    go env (TyVarTy tv1)       (TyVarTy tv2)     = rnOccL env tv1 == rnOccR env tv2
    go _   (LitTy lit1)        (LitTy lit2)      = lit1 == lit2
    go env (PiTy bndr1 t1)     (PiTy bndr2 t2)
      =  go env (binderType bndr1) (binderType bndr2)
      && let env' = rnBinderVar2 env (binderPayload bndr1) (binderPayload bndr2)
         in go env' t1 t2
      && compatibleBinder bndr1 bndr2
    go env (AppTy s1 t1)       (AppTy s2 t2)     = go env s1 s2 && go env t1 t2
    go env (TyConApp tc1 ts1) (TyConApp tc2 ts2) = (tc1 == tc2) && gos env ts1 ts2
    go env (CastTy t1 c1)      (CastTy t2 c2)    = go env t1 t2 && go_co env c1 c2
    go env (CoercionTy c1)     (CoercionTy c2)   = go_co env c1 c2
    go _ _ _ = False

    gos _   []       []       = True
    gos env (t1:ts1) (t2:ts2) = go env t1 t2 && gos env ts1 ts2
    gos _ _ _ = False

    go_co env (Refl r1 t1)              (Refl r2 t2) = r1 == r2 && go env t1 t2
    go_co env (TyConAppCo r1 tc1 args1) (TyConAppCo r2 tc2 args2)
      = r1 == r2 && tc1 == tc2 && go_args env args1 args2
    go_co env (AppCo col1 cor1)         (AppCo col2 cor2)
      = go_co env col1 col2 && go_arg env cor1 cor2
    go_co env (PiCo cobndr1 co1)        (PiCo cobndr2 co2)
      =  go_cobndr env cobndr1 cobndr2
      && go_co (rnCoBndr2 env cobndr1 cobndr2) co1 co2
    go_co env (CoVarCo cv1)             (CoVarCo cv2)
      = rnOccL env cv1 == rnOccR env cv2
    go_co env (AxiomInstCo x1 i1 cos1)  (AxiomInstCo x2 i2 cos2)
      = x1 == x2 && i1 == i2 && go_args env cos1 cos2
    go_co env (PhantomCo h1 tl1 tr1)    (PhantomCo h2 tl2 tr2)
      = go_co env h1 h2 && go env tl1 tl2 && go env tr1 tr2
    go_co env (UnsafeCo r1 tl1 tr1)     (UnsafeCo r2 tl2 tr2)
      = r1 == r2 && go env tl1 tl2 && go env tr1 tr2
    go_co env (SymCo co1)               (SymCo co2) = go_co env co1 co2
    go_co env (TransCo col1 cor1)       (TransCo col2 cor2)
      = go_co env col1 col2 && go_co env cor1 cor2
    go_co env (NthCo d1 co1)            (NthCo d2 co2)
      = d1 == d2 && go_co env co1 co2
    go_co env (LRCo lr1 co1)            (LRCo lr2 co2)
      = lr1 == lr2 && go_co env co1 co2
    go_co env (InstCo co1 arg1)         (InstCo co2 arg2)
      = go_co env co1 co2 && go_arg env arg1 arg2
    go_co env (CoherenceCo col1 cor1)   (CoherenceCo col2 cor2)
      = go_co env col1 col2 && go_co env cor1 cor2
    go_co env (KindCo co1)              (KindCo co2) = go_co env co1 co2
    go_co env (SubCo co1)               (SubCo co2) = go_co env co1 co2
    go_co env (AxiomRuleCo ax1 ts1 cs1) (AxiomRuleCo ax2 ts2 cs2)
      = ax1 == ax2 && gos env ts1 ts2 && go_cos env cs1 cs2
    go_co _ _ _ = False

    go_arg env (TyCoArg co1)          (TyCoArg co2) = go_co env co1 co2
    go_arg env (CoCoArg r1 col1 cor1) (CoCoArg r2 col2 cor2)
      = r1 == r2 && go_co env col1 col2 && go_co env cor1 cor2
    go_arg _ _ _ = False

    go_cos _   []       []       = True
    go_cos env (c1:cs1) (c2:cs2) = go_co env c1 c2 && go_cos env cs1 cs2
    go_cos _   _        _        = False

    go_args _   []       []       = True
    go_args env (a1:as1) (a2:as2) = go_arg env a1 a2 && go_args env as1 as2
    go_args _   _        _        = False

    go_cobndr env (TyHomo tv1)               (TyHomo tv2)
      = compatibleBinder tv1 tv2 && go env (binderType tv1) (binderType tv2)
    go_cobndr env (TyHetero co1 pbndr1 _) (TyHetero co2 pbndr2 _)
      = let Pair tvl1 tvr1 = binderPayload pbndr1
            Pair tvl2 tvr2 = binderPayload pbndr2
        in
        compatibleBinder pbndr1 pbndr2 &&
        go_co env co1 co2 && go env (binderVarType tvl1) (binderVarType tvl2)
                          && go env (binderVarType tvr1) (binderVarType tvr2)
    go_cobndr env (CoHomo cv1)               (CoHomo cv2)
      = go env (binderType cv1) (binderType cv2)
    go_cobndr env (CoHetero co1 pbndr1)   (CoHetero co2 pbndr2)
      = let Pair cvl1 cvr1 = binderPayload pbndr1
            Pair cvl2 cvr2 = binderPAyload pbndr2
        in
        go_co env co1 co2 && go env (binderVarType cvl1) (binderVarType cvl2)
                          && go env (binderVarType cvr1) (binderVarType cvr2)
    go_cobndr _ _ _ = False

pickyEqType :: TcType -> TcType -> Bool
-- Check when two types _look_ the same, _including_ synonyms.
-- So (pickyEqType String [Char]) returns False
pickyEqType ty1 ty2
  = go init_env ty1 ty2
  where
    init_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfType ty1 `unionVarSet` tyCoVarsOfType ty2))
    go env (TyVarTy tv1)       (TyVarTy tv2)     = rnOccL env tv1 == rnOccR env tv2
    go _   (LitTy lit1)        (LitTy lit2)      = lit1 == lit2
    go env (PiTy bndr1 t1)     (PiTy bndr2 t2)
      =  go env (binderType bndr1) (binderType bndr2)
      && let env' = rnBinderVar2 env (binderPayload bndr1) (binderPayload bndr2)
         in go env' t1 t2
      && compatibleBinder bndr1 bndr2
    go env (AppTy s1 t1)       (AppTy s2 t2)     = go env s1 s2 && go env t1 t2
    go env (TyConApp tc1 ts1) (TyConApp tc2 ts2) = (tc1 == tc2) && gos env ts1 ts2
    go env (CastTy ty1 co1)    (CastTy ty2 co2)  = go env ty1 ty2 && go_co env co1 co2
    go env (CoercionTy co1)    (CoercionTy co2)  = go_co env co1 co2
    go _ _ _ = False

    gos _   []       []       = True
    gos env (t1:ts1) (t2:ts2) = go env t1 t2 && gos env ts1 ts2
    gos _ _ _ = False

    go_co env (Refl r1 ty1)    (Refl r2 ty2)    = r1 == r2 && go env ty1 ty2
    go_co env (TyConAppCo r1 tc1 args1) (TyConAppCo r2 tc2 args2) = (r1 == r2) && (tc1 == tc2) && go_args env args1 args2
    go_co env (AppCo co1 arg1) (AppCo co2 arg2) = go_co env co1 co2 && go_arg env arg1 arg2
    go_co env (PiCo cobndr1 co1) (PiCo cobndr2 co2)
      = go_cobndr env cobndr1 cobndr2 &&
        go_co (rnBndrs2 env (coBndrVars cobndr1) (coBndrVars cobndr2)) co1 co2
    go_co env (CoVarCo cv1)    (CoVarCo cv2)    = rnOccL env cv1 == rnOccR env cv2
    go_co env (AxiomInstCo ax1 ind1 args1) (AxiomInstCo ax2 ind2 args2)
      = (ax1 == ax2) && (ind1 == ind2) && (go_args env args1 args2)
    go_co env (PhantomCo h1 t1 s1) (PhantomCo h2 t2 s2) = go_co env h1 h2 && go env t1 t2 && go env s1 s2
    go_co env (UnsafeCo r1 s1 t1) (UnsafeCo r2 s2 t2) = r1 == r2 && go env s1 s2 && go env t1 t2
    go_co env (SymCo co1)      (SymCo co2)      = go_co env co1 co2
    go_co env (TransCo c1 d1)  (TransCo c2 d2)  = go_co env c1 c2 && go_co env d1 d2
    go_co env (NthCo n1 co1)   (NthCo n2 co2)   = (n1 == n2) && go_co env co1 co2
    go_co env (LRCo lr1 co1)   (LRCo lr2 co2)   = (lr1 == lr2) && go_co env co1 co2
    go_co env (InstCo c1 a1)   (InstCo c2 a2)   = go_co env c1 c2 && go_arg env a1 a2
    go_co env (CoherenceCo c1 d1) (CoherenceCo c2 d2) = go_co env c1 c2 && go_co env d1 d2
    go_co env (KindCo co1)     (KindCo co2)    = go_co env co1 co2
    go_co env (SubCo co1)      (SubCo co2)     = go_co env co1 co2
    go_co env (AxiomRuleCo ax1 ts1 cs1) (AxiomRuleCo ax2 ts2 cs2)
      = ax1 == ax2 && gos env ts1 ts2 && go_cos env cs1 cs2
    go_co _   _                _               = False

    go_cos _   []       []       = True
    go_cos env (c1:cs1) (c2:cs2) = go_co env c1 c2 && go_cos env cs1 cs2
    go_cos _   _        _        = False

    go_arg env (TyCoArg co1   )   (TyCoArg co2)      = go_co env co1 co2
    go_arg env (CoCoArg r1 c1 d1) (CoCoArg r2 c2 d2)
      = r1 == r2 && go_co env c1 c2 && go_co env d1 d2
    go_arg _   _               _               = False
    
    go_args _   []             []              = True
    go_args env (a1:args1)     (a2:args2)      = go_arg env a1 a2 && go_args env args1 args2
    go_args _   _              _               = False

    go_cobndr env (TyHomo tv1)               (TyHomo tv2)
      = compatibleBinder tv1 tv2 && go env (binderType tv1) (binderType tv2)
    go_cobndr env (TyHetero co1 pbndr1 _) (TyHetero co2 pbndr2 _)
      = let Pair tvl1 tvr1 = binderPayload pbndr1
            Pair tvl2 tvr2 = binderPayload pbndr2
        in
        compatibleBinder pbndr1 pbndr2 &&
        go_co env co1 co2 && go env (binderVarType tvl1) (binderVarType tvl2)
                          && go env (binderVarType tvr1) (binderVarType tvr2)
    go_cobndr env (CoHomo cv1)               (CoHomo cv2)
      = go env (binderType cv1) (binderType cv2)
    go_cobndr env (CoHetero co1 pbndr1)   (CoHetero co2 pbndr2)
      = let Pair cvl1 cvr1 = binderPayload pbndr1
            Pair cvl2 cvr2 = binderPAyload pbndr2
        in
        go_co env co1 co2 && go env (binderVarType cvl1) (binderVarType cvl2)
                          && go env (binderVarType cvr1) (binderVarType cvr2)
    go_cobndr _ _ _ = False
    
\end{code}

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

\begin{code}
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
--                                     or it's a PolyTv
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
    details = ASSERT2( isTcTyVar tv, ppr tv ) tcTyVarDetails tv

    impredicative
      = case details of
          MetaTv { mtv_info = PolyTv } -> True
          MetaTv { mtv_info = SigTv }  -> False
          MetaTv { mtv_info = TauTv }  -> xopt Opt_ImpredicativeTypes dflags
          _other                       -> True
          -- We can have non-meta tyvars in given constraints

    -- Check 'ty' is a tyvar, or can be expanded into one
    go_sig_tv ty@(TyVarTy {})            = OC_OK ty
    go_sig_tv ty | Just ty' <- tcView ty = go_sig_tv ty'
    go_sig_tv _                          = OC_NonTyVar

    -- True => fine
    fast_check (LitTy {})          = True
    fast_check (TyVarTy tv')       = tv /= tv'
    fast_check (TyConApp _ tys)    = all fast_check tys
    fast_check (PiTy b r)
      | not (isDependentBinder b)  = fast_check (binderType b) && fast_check r
      | otherwise                  = impredicative
                                   && fast_check (binderType b)
                                   && (binder_matches || fast_check r)
      where binder_matches
              | Just tv' <- binderVar_maybe b = tv' == tv
              | otherwise                     = False
    fast_check (AppTy fun arg)     = fast_check fun && fast_check arg
    fast_check (CastTy ty co)      = fast_check ty && fast_check_co co
    fast_check (CoercionTy co)     = fast_check_co co

    fast_check_co (Refl _ ty)            = fast_check ty
    fast_check_co (TyConAppCo _ _ args)  = all fast_check_co_arg args
    fast_check_co (AppCo co arg)         = fast_check_co co && fast_check_co_arg arg
    fast_check_co (PiCo cobndr co)
      | Just v <- getHomoBinder_maybe cobndr
      = impredicative && fast_check (binderType v) && (tv `isBoundBy` v || fast_check_co co)
      | Just (h, bv1, bv2) <- splitHeteroCoBndr_maybe cobndr
      = impredicative && fast_check_co h && fast_check (binderVarType v1)
                      && fast_check (binderVarType v2) && (tv `isBoundByBV` v1 || tv `isBoundByBV` v2 || fast_check_co co)
      | otherwise
      = pprPanic "fast_check_co" (ppr cobndr)
    fast_check_co (CoVarCo _)            = True
    fast_check_co (AxiomInstCo _ _ args) = all fast_check_co_arg args
    fast_check_co (PhantomCo h t1 t2)    = fast_check_co h && fast_check t1
                                                           && fast_check t2
    fast_check_co (UnsafeCo _ ty1 ty2)   = fast_check ty1 && fast_check ty2
    fast_check_co (SymCo co)             = fast_check_co co
    fast_check_co (TransCo co1 co2)      = fast_check_co co1 && fast_check_co co2
    fast_check_co (InstCo co arg)        = fast_check_co co && fast_check_co_arg arg
    fast_check_co (NthCo _ co)           = fast_check_co co
    fast_check_co (LRCo _ co)            = fast_check_co co
    fast_check_co (CoherenceCo co1 co2)  = fast_check_co co1 && fast_check_co co2
    fast_check_co (KindCo co)            = fast_check_co co
    fast_check_co (SubCo co)             = fast_check_co co
    fast_check_co (AxiomRuleCo _ ts cs)
      = all fast_check ts && all fast_check_co cs

    fast_check_co_arg (TyCoArg co)         = fast_check_co co
    fast_check_co_arg (CoCoArg _ co1 co2)  = fast_check_co co1 && fast_check_co co2

      -- Invariant: the env *does not map* tv, the tyvar of interest
    go env (TyVarTy tv') | tv == tv' = OC_Occurs
                         | otherwise = return (substTyVar env tv')
    go _   ty@(LitTy {}) = return ty
    go env (AppTy ty1 ty2) = do { ty1' <- go env ty1
                                ; ty2' <- go env ty2
                                ; return (mkAppTy ty1' ty2') }
    go env (PiTy bndr1 ty2)
      | not (isDependentBinder bndr1)
                       = do { ty1' <- go env (binderType bndr1)
                            ; ty2' <- go env ty2 
                            ; return (mkFunTy ty1' ty2') }
      | not impredicative = OC_Forall
      | otherwise
      = do { let bndr_ty = binderType bndr1
           ; bndr_ty' <- occurCheckExpand dflags tv (substTy env bndr_ty)
           ; let bndr1' = setBinderType bndr1 bndr_ty'
                 env' | bndr_ty' `eqType` bndr_ty
                      = env
                      | otherwise
                      = extendTCvSubstBinder env bndr1
                          (mkOnlyTyVarTy $
                           setTyVarKind (binderVar bndr1) bndr_ty')
                          -- the binderVar will fail on anon. binders,
                          -- but that's OK because extendTCvSubstBinder
                          -- won't look in that case!

           ; case binderVar_maybe bndr of
             { Just tv' | tv' == tv -> -- the local tv' shadows tv
                 in return $ PiTy bndr1' (substTy env' ty2)
             ; _ -> -- no shadowing
        do { 
      | otherwise = do { ty2' <- go env' ty2
                       ; return (PiTy bndr1' ty2') }

    -- For a type constructor application, first try expanding away the
    -- offending variable from the arguments.  If that doesn't work, next
    -- see if the type constructor is a type synonym, and if so, expand
    -- it and try again.
    go env ty@(TyConApp tc tys)
      = case do { tys <- mapM (go env) tys; return (mkTyConApp tc tys) } of
          OC_OK ty -> return ty  -- First try to eliminate the tyvar from the args
          bad | Just ty' <- tcView ty -> go env ty'
              | otherwise             -> bad
                      -- Failing that, try to expand a synonym

    go env (CastTy ty co) =  do { ty' <- go env ty
                                ; co' <- go_co env co
                                ; return (mkCastTy ty' co') }
    go env (CoercionTy co) = do { co' <- go_co env co
                                ; return (mkCoercionTy co') }

    go_co env (Refl r ty)           = do { ty' <- go env ty
                                         ; return (mkReflCo r ty') }
      -- Note: Coercions do not contain type synonyms
    go_co env (TyConAppCo r tc args)= do { args' <- mapM (go_arg env) args
                                         ; return (mkTyConAppCo r tc args') }
    go_co env (AppCo co arg)        = do { co' <- go_co env co
                                         ; arg' <- go_arg env arg
                                         ; return (mkAppCo co' arg') }
      -- TODO (RAE): This is broken. Either make like PiTy above (where
      -- we recur properly into kinds) or expand all type synonyms in
      -- PiCoBndr kinds upon creation
    go_co env (PiCo cobndr co)
      | not (all fast_check (map varType (coBndrVars cobndr)))
                                    = OC_Occurs
      | tv `elem` coBndrVars cobndr = return (substCo env co)
      | otherwise = do { cobndr' <- case splitHeteroCoBndr_maybe cobndr of
                                      Just (h, _, _) -> do { h' <- go_co env h
                                                      ; return (setCoBndrEta cobndr h') }
                                      _              -> return cobndr
                       ; co' <- go_co env co
                       ; return (mkPiCo cobndr' co') }
    go_co env co@(CoVarCo {})       = return (substCo env co)
    go_co env (AxiomInstCo ax ind args)
                                    = do { args' <- mapM (go_arg env) args
                                         ; return (mkAxiomInstCo ax ind args') }
    go_co env (PhantomCo h ty1 ty2) = do { h' <- go_co env h
                                         ; ty1' <- go env ty1
                                         ; ty2' <- go env ty2
                                         ; return (mkPhantomCo h' ty1' ty2') }
    go_co env (UnsafeCo r ty1 ty2)  = do { ty1' <- go env ty1
                                         ; ty2' <- go env ty2
                                         ; return (mkUnsafeCo r ty1' ty2') }
    go_co env (SymCo co)            = do { co' <- go_co env co
                                         ; return (mkSymCo co') }
    go_co env (TransCo co1 co2)     = do { co1' <- go_co env co1
                                         ; co2' <- go_co env co2
                                         ; return (mkTransCo co1' co2') }
    go_co env (NthCo n co)          = do { co' <- go_co env co
                                         ; return (mkNthCo n co') }
    go_co env (LRCo lr co)          = do { co' <- go_co env co
                                         ; return (mkLRCo lr co') }
    go_co env (InstCo co arg)       = do { co' <- go_co env co
                                         ; arg' <- go_arg env arg
                                         ; return (mkInstCo co' arg') }
    go_co env (CoherenceCo co1 co2) = do { co1' <- go_co env co1
                                         ; co2' <- go_co env co2
                                         ; return (mkCoherenceCo co1' co2') }
    go_co env (KindCo co)           = do { co' <- go_co env co
                                         ; return (mkKindCo co') }
    go_co env (SubCo co)            = do { co' <- go_co env co
                                         ; return (mkSubCo co') }
    go_co env (AxiomRuleCo ax ts cs)= do { ts' <- mapM (go env) ts
                                         ; cs' <- mapM (go_co env) cs
                                         ; return (AxiomRuleCo ax ts' cs') }

    go_arg env (TyCoArg co)         = do { co' <- go_co env co
                                         ; return (TyCoArg co') }
    go_arg env (CoCoArg r co1 co2)  = do { co1' <- go_co env co1
                                         ; co2' <- go_co env co2
                                         ; return (CoCoArg r co1' co2') }
\end{code}

%************************************************************************
%*                                                                      *
\subsection{Predicate types}
%*                                                                      *
%************************************************************************

Deconstructors and tests on predicate types

\begin{code}
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
\end{code}

Superclasses

\begin{code}
mkMinimalBySCs :: [PredType] -> [PredType]
-- Remove predicates that can be deduced from others by superclasses
mkMinimalBySCs ptys = [ ploc |  ploc <- ptys
                             ,  ploc `not_in_preds` rec_scs ]
 where
   rec_scs = concatMap trans_super_classes ptys
   not_in_preds p ps = not (any (eqPred p) ps)

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
\end{code}


%************************************************************************
%*                                                                      *
\subsection{Predicates}
%*                                                                      *
%************************************************************************

isSigmaTy returns true of any qualified type.  It doesn't *necessarily* have
any foralls.  E.g.
        f :: (?x::Int) => Int -> Int

\begin{code}
isSigmaTy :: Type -> Bool
isSigmaTy ty | Just ty' <- tcView ty = isSigmaTy ty'
isSigmaTy (PiTy bndr _) = isDependentBinder bndr || isPredTy (binderType bndr)
isSigmaTy _             = False

isOverloadedTy :: Type -> Bool
-- Yes for a type of a function that might require evidence-passing
-- Used only by bindLocalMethods
isOverloadedTy ty | Just ty' <- tcView ty = isOverloadedTy ty'
-- TODO (RAE): This might be subtler. See commented-out original below.
isOverloadedTy (PiTy bndr ty) = isPredTy (binderType bndr)
                             || (isDependentBinder binder && isOverloadedTy ty)
-- isOverloadedTy (ForAllTy (Named {}) ty) = isOverloadedTy ty
-- isOverloadedTy (ForAllTy (Anon a) _)    = isPredTy a
isOverloadedTy _                        = False
\end{code}

\begin{code}
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
\end{code}

\begin{code}
-- NB: Currently used in places where we have already expanded type synonyms;
--     hence no 'coreView'.  This could, however, be changed without breaking
--     any code.
isSynFamilyTyConApp :: TcTauType -> Bool
isSynFamilyTyConApp (TyConApp tc tys) = isSynFamilyTyCon tc &&
                                      length tys == tyConArity tc
isSynFamilyTyConApp _other            = False
\end{code}


%************************************************************************
%*                                                                      *
\subsection{Misc}
%*                                                                      *
%************************************************************************

\begin{code}
deNoteType :: Type -> Type
-- Remove all *outermost* type synonyms and other notes
deNoteType ty | Just ty' <- tcView ty = deNoteType ty'
deNoteType ty = ty
\end{code}

Find the free tycons and classes of a type.  This is used in the front
end of the compiler.

\begin{code}
orphNamesOfTyCon :: TyCon -> NameSet
orphNamesOfTyCon tycon = unitNameSet (getName tycon) `unionNameSets` case tyConClass_maybe tycon of
    Nothing  -> emptyNameSet
    Just cls -> unitNameSet (getName cls)

orphNamesOfType :: Type -> NameSet
orphNamesOfType ty | Just ty' <- tcView ty = orphNamesOfType ty'
                -- Look through type synonyms (Trac #4912)
orphNamesOfType (TyVarTy _)          = emptyNameSet
orphNamesOfType (LitTy {})           = emptyNameSet
orphNamesOfType (TyConApp tycon tys) = orphNamesOfTyCon tycon
                                       `unionNameSets` orphNamesOfTypes tys
orphNamesOfType (PiTy bndr res)
  = (if isDependentBinder bndr then emptyNameSet else orphNamesOfTyCon funTyCon)
      -- NB!  See Trac #8535
    `unionNameSets` orphNamesOfType (binderType bndr)
    `unionNameSets` orphNamesOfType res
orphNamesOfType (AppTy fun arg)      = orphNamesOfType fun `unionNameSets` orphNamesOfType arg
orphNamesOfType (CastTy ty co)       = orphNamesOfType ty `unionNameSets` orphNamesOfCo co
orphNamesOfType (CoercionTy co)      = orphNamesOfCo co

orphNamesOfThings :: (a -> NameSet) -> [a] -> NameSet
orphNamesOfThings f = foldr (unionNameSets . f) emptyNameSet

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
orphNamesOfCo (TyConAppCo _ tc cos) = unitNameSet (getName tc) `unionNameSets` orphNamesOfCoArgs cos
orphNamesOfCo (AppCo co1 co2)       = orphNamesOfCo co1 `unionNameSets` orphNamesOfCoArg co2
orphNamesOfCo (PiCo cobndr co)
  | Just (h, _, _) <- splitHeteroCoBndr_maybe cobndr
  = orphNamesOfCo h `unionNameSets` orphNamesOfCo co
  | otherwise
  = orphNamesOfCo co
orphNamesOfCo (CoVarCo _)           = emptyNameSet
orphNamesOfCo (AxiomInstCo con _ cos) = orphNamesOfCoCon con `unionNameSets` orphNamesOfCoArgs cos
orphNamesOfCo (PhantomCo h t1 t2)   = orphNamesOfCo h `unionNameSets` orphNamesOfType t1 `unionNameSets` orphNamesOfType t2
orphNamesOfCo (UnsafeCo _ ty1 ty2)  = orphNamesOfType ty1 `unionNameSets` orphNamesOfType ty2
orphNamesOfCo (SymCo co)            = orphNamesOfCo co
orphNamesOfCo (TransCo co1 co2)     = orphNamesOfCo co1 `unionNameSets` orphNamesOfCo co2
orphNamesOfCo (NthCo _ co)          = orphNamesOfCo co
orphNamesOfCo (LRCo  _ co)          = orphNamesOfCo co
orphNamesOfCo (InstCo co arg)       = orphNamesOfCo co `unionNameSets` orphNamesOfCoArg arg
orphNamesOfCo (CoherenceCo co1 co2) = orphNamesOfCo co1 `unionNameSets` orphNamesOfCo co2
orphNamesOfCo (KindCo co)           = orphNamesOfCo co
orphNamesOfCo (SubCo co)            = orphNamesOfCo co
orphNamesOfCo (AxiomRuleCo _ ts cs) = orphNamesOfTypes ts `unionNameSets`
                                      orphNamesOfCos cs

orphNamesOfCos :: [Coercion] -> NameSet
orphNamesOfCos = orphNamesOfThings orphNamesOfCo

orphNamesOfCoArg :: CoercionArg -> NameSet
orphNamesOfCoArg (TyCoArg co)        = orphNamesOfCo co
orphNamesOfCoArg (CoCoArg _ co1 co2) = orphNamesOfCo co1 `unionNameSets` orphNamesOfCo co2

orphNamesOfCoArgs :: [CoercionArg] -> NameSet
orphNamesOfCoArgs = orphNamesOfThings orphNamesOfCoArg

orphNamesOfCoCon :: CoAxiom br -> NameSet
orphNamesOfCoCon (CoAxiom { co_ax_tc = tc, co_ax_branches = branches })
  = orphNamesOfTyCon tc `unionNameSets` orphNamesOfCoAxBranches branches

orphNamesOfCoAxBranches :: BranchList CoAxBranch br -> NameSet
orphNamesOfCoAxBranches = brListFoldr (unionNameSets . orphNamesOfCoAxBranch) emptyNameSet

orphNamesOfCoAxBranch :: CoAxBranch -> NameSet
orphNamesOfCoAxBranch (CoAxBranch { cab_lhs = lhs, cab_rhs = rhs })
  = orphNamesOfTypes lhs `unionNameSets` orphNamesOfType rhs
\end{code}


%************************************************************************
%*                                                                      *
\subsection[TysWiredIn-ext-type]{External types}
%*                                                                      *
%************************************************************************

The compiler's foreign function interface supports the passing of a
restricted set of types as arguments and results (the restricting factor
being the )

\begin{code}
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
isFFITy ty = checkRepTyCon legalFFITyCon ty

isFFIArgumentTy :: DynFlags -> Safety -> Type -> Bool
-- Checks for valid argument type for a 'foreign import'
isFFIArgumentTy dflags safety ty
   = checkRepTyCon (legalOutgoingTyCon dflags safety) ty

isFFIExternalTy :: Type -> Bool
-- Types that are allowed as arguments of a 'foreign export'
isFFIExternalTy ty = checkRepTyCon legalFEArgTyCon ty

isFFIImportResultTy :: DynFlags -> Type -> Bool
isFFIImportResultTy dflags ty
  = checkRepTyCon (legalFIResultTyCon dflags) ty

isFFIExportResultTy :: Type -> Bool
isFFIExportResultTy ty = checkRepTyCon legalFEResultTyCon ty

isFFIDynTy :: Type -> Type -> Bool
-- The type in a foreign import dynamic must be Ptr, FunPtr, or a newtype of
-- either, and the wrapped function type must be equal to the given type.
-- We assume that all types have been run through normalizeFfiType, so we don't
-- need to worry about expanding newtypes here.
isFFIDynTy expected ty
    -- Note [Foreign import dynamic]
    -- In the example below, expected would be 'CInt -> IO ()', while ty would
    -- be 'FunPtr (CDouble -> IO ())'.
    | Just (tc, [ty']) <- splitTyConApp_maybe ty
    , tyConUnique tc `elem` [ptrTyConKey, funPtrTyConKey]
    , eqType ty' expected
    = True
    | otherwise
    = False

isFFILabelTy :: Type -> Bool
-- The type of a foreign label must be Ptr, FunPtr, or a newtype of either.
isFFILabelTy = checkRepTyConKey [ptrTyConKey, funPtrTyConKey]

isFFIPrimArgumentTy :: DynFlags -> Type -> Bool
-- Checks for valid argument type for a 'foreign import prim'
-- Currently they must all be simple unlifted types, or the well-known type
-- Any, which can be used to pass the address to a Haskell object on the heap to
-- the foreign function.
isFFIPrimArgumentTy dflags ty
   = isAnyTy ty || checkRepTyCon (legalFIPrimArgTyCon dflags) ty

isFFIPrimResultTy :: DynFlags -> Type -> Bool
-- Checks for valid result type for a 'foreign import prim'
-- Currently it must be an unlifted type, including unboxed tuples.
isFFIPrimResultTy dflags ty
   = checkRepTyCon (legalFIPrimResultTyCon dflags) ty

isFFIDotnetTy :: DynFlags -> Type -> Bool
isFFIDotnetTy dflags ty
  = checkRepTyCon (\ tc -> (legalFIResultTyCon dflags tc ||
                           isFFIDotnetObjTy ty || isStringTy ty)) ty
        -- NB: isStringTy used to look through newtypes, but
        --     it no longer does so.  May need to adjust isFFIDotNetTy
        --     if we do want to look through newtypes.

isFFIDotnetObjTy :: Type -> Bool
isFFIDotnetObjTy ty
  = checkRepTyCon check_tc t_ty
  where
   (_, t_ty) = tcSplitNamedForAllTys ty
   check_tc tc = getName tc == objectTyConName

isFunPtrTy :: Type -> Bool
isFunPtrTy = checkRepTyConKey [funPtrTyConKey]

-- normaliseFfiType gets run before checkRepTyCon, so we don't
-- need to worry about looking through newtypes or type functions
-- here; that's already been taken care of.
checkRepTyCon :: (TyCon -> Bool) -> Type -> Bool
checkRepTyCon check_tc ty
    | Just (tc, _) <- splitTyConApp_maybe ty
    = check_tc tc
    | otherwise
    = False

checkRepTyConKey :: [Unique] -> Type -> Bool
-- Like checkRepTyCon, but just looks at the TyCon key
checkRepTyConKey keys
  = checkRepTyCon (\tc -> tyConUnique tc `elem` keys)
\end{code}

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

\begin{code}
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
  = isUnLiftedTyCon tc || boxedMarshalableTyCon tc || tc == unitTyCon

marshalableTyCon :: DynFlags -> TyCon -> Bool
marshalableTyCon dflags tc
  =  (xopt Opt_UnliftedFFITypes dflags
      && isUnLiftedTyCon tc
      && not (isUnboxedTupleTyCon tc)
      && case tyConPrimRep tc of        -- Note [Marshalling VoidRep]
           VoidRep -> False
           _       -> True)
  || boxedMarshalableTyCon tc

boxedMarshalableTyCon :: TyCon -> Bool
boxedMarshalableTyCon tc
   = getUnique tc `elem` [ intTyConKey, int8TyConKey, int16TyConKey
                         , int32TyConKey, int64TyConKey
                         , wordTyConKey, word8TyConKey, word16TyConKey
                         , word32TyConKey, word64TyConKey
                         , floatTyConKey, doubleTyConKey
                         , ptrTyConKey, funPtrTyConKey
                         , charTyConKey
                         , stablePtrTyConKey
                         , boolTyConKey
                         ]

legalFIPrimArgTyCon :: DynFlags -> TyCon -> Bool
-- Check args of 'foreign import prim', only allow simple unlifted types.
-- Strictly speaking it is unnecessary to ban unboxed tuples here since
-- currently they're of the wrong kind to use in function args anyway.
legalFIPrimArgTyCon dflags tc
  = xopt Opt_UnliftedFFITypes dflags
    && isUnLiftedTyCon tc
    && not (isUnboxedTupleTyCon tc)

legalFIPrimResultTyCon :: DynFlags -> TyCon -> Bool
-- Check result type of 'foreign import prim'. Allow simple unlifted
-- types and also unboxed tuple result types '... -> (# , , #)'
legalFIPrimResultTyCon dflags tc
  = xopt Opt_UnliftedFFITypes dflags
    && isUnLiftedTyCon tc
    && (isUnboxedTupleTyCon tc
        || case tyConPrimRep tc of      -- Note [Marshalling VoidRep]
           VoidRep -> False
           _       -> True)
\end{code}

Note [Marshalling VoidRep]
~~~~~~~~~~~~~~~~~~~~~~~~~~
We don't treat State# (whose PrimRep is VoidRep) as marshalable.
In turn that means you can't write
        foreign import foo :: Int -> State# RealWorld

Reason: the back end falls over with panic "primRepHint:VoidRep";
        and there is no compelling reason to permit it
