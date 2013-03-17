%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1998
%
\section[TyCoRep]{Type and Coercion - friends' interface}

Note [The Type-related module hierarchy]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  Class
  CoAxiom
  TyCon    imports Class, CoAxiom
  TyCoRep  imports Class, CoAxiom, TyCon
  TysPrim  imports TyCoRep ( including mkTyConTy )
  Kind     imports TysPrim ( mainly for primitive kinds )
  Type     imports Kind
  Coercion imports Type

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

-- We expose the relevant stuff from this module via the Type module
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module TyCoRep (
        TyThing(..),
        Type(..),
        TyLit(..),
        KindOrType, Kind, SuperKind,
        PredType, ThetaType,      -- Synonyms

        -- Coercions
        Coercion(..), CoercionArg(..), LeftOrRight(..), ForAllCoBndr(..),

        -- Functions over types
        mkNakedTyConApp, mkTyConTy, mkOnlyTyVarTy, mkOnlyTyVarTys,
        mkTyCoVarTy, mkTyCoVarTys,
        isLiftedTypeKind, isSuperKind, isTypeVar, isKindVar,
        isCoercionType,

        -- Functions over coercions
        setCoBndrEta, eqCoBndrSort, pickLR, coBndrVars, coBndrVarsKinds,
        
        -- Pretty-printing
	pprType, pprParendType, pprTypeApp, pprTCvBndr, pprTCvBndrs,
	pprTyThing, pprTyThingCategory, pprSigmaType,
	pprEqPred, pprTheta, pprForAll, pprThetaArrowTy, pprClassPred,
        pprKind, pprParendKind, pprTyLit,
	Prec(..), maybeParen, pprTcApp, pprTypeNameApp, 
        pprPrefixApp, pprArrowChain, ppr_type,

        -- Free variables
        tyCoVarsOfType, tyCoVarsOfTypes, tyVarsOnlyOfType, tyVarsOnlyOfTypes,
        tyVarsOnlyOfCo, tyVarsOnlyOfCos, coVarsOfType, coVarsOfTypes,
        coVarsOfCo, coVarsOfCos, tyCoVarsOfCoArg, tyCoVarsOfCoArgs,
        tyCoVarsOfCo, tyCoVarsOfCos,
        
        -- Substitutions
        TCvSubst(..), TvSubstEnv, CvSubstEnv,
        emptyTvSubstEnv, emptyCvSubstEnv, composeTCvSubstEnv, emptyTCvSubst,
        mkEmptyTCvSubst, isEmptyTCvSubst, mkTCvSubst, getTvSubstEnv,
        getCvSubstEnv, getTCvInScope, isInScope, notElemTCvSubst,
        setTvSubstEnv, setCvSubstEnv, zapTCvSubst,
        extendTCvInScope, extendTCvInScopeList,
        extendTCvSubst, extendTCvSubstList,
        unionTCvSubst, zipTyCoEnv,
        mkOpenTCvSubst, zipOpenTCvSubst, mkTopTCvSubst, zipTopTCvSubst,

        substTyWith, substKiWith, substTysWith, substKisWith, substTy,
        substTys, substTheta, substTyCoVar, substTyCoVars,
        lookupTyVar, lookupVar, substTyVarBndr,
        substCo, substCos, substCoVar, substCoVars, lookupCoVar,
        substTyCoVarBndr, substCoVarBndr, cloneTyVarBndr,
        substCoWithIS, substCoWith, substTyVar, substTyVars,
        substForAllCoBndr,
        substTyVarBndrCallback, substForAllCoBndrCallback,
        substCoVarBndrCallback,

        -- * Tidying type related things up for printing
        tidyType,      tidyTypes,
        tidyOpenType,  tidyOpenTypes,
        tidyOpenKind,
        tidyTyCoVarBndr, tidyTyCoVarBndrs, tidyFreeTyCoVars,
        tidyOpenTyCoVar, tidyOpenTyCoVars,
        tidyTyVarOcc,
        tidyTopType,
        tidyKind,
        tidyCo, tidyCos
    ) where

#include "HsVersions.h"

import {-# SOURCE #-} DataCon( DataCon, dataConTyCon, dataConName )
import {-# SOURCE #-} Type( noParenPred, isPredTy, isCoercionTy, mkAppTy ) -- Transitively pulls in a LOT of stuff, better to break the loop
import {-# SOURCE #-} Coercion

-- friends:
import Var
import VarEnv
import VarSet
import Name hiding ( varName )
import BasicTypes
import TyCon
import Class
import CoAxiom

-- others
import PrelNames
import Outputable
import FastString
import Pair
import StaticFlags( opt_PprStyle_Debug )
import Util

-- libraries
import qualified Data.Data        as Data hiding ( TyCon )
import Data.List
\end{code}


%************************************************************************
%*									*
\subsection{The data type}
%*									*
%************************************************************************


\begin{code}
-- | The key representation of types within the compiler

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
data Type
  = TyVarTy Var	-- ^ Vanilla type or kind variable (*never* a coercion variable)

  | AppTy         -- See Note [AppTy invariant]
	Type
	Type		-- ^ Type application to something other than a 'TyCon'. Parameters:
	                --
                        --  1) Function: must /not/ be a 'TyConApp',
                        --     must be another 'AppTy', or 'TyVarTy'
	                --
	                --  2) Argument type

  | TyConApp      -- See Note [AppTy invariant]
	TyCon
	[KindOrType]	-- ^ Application of a 'TyCon', including newtypes /and/ synonyms.
	                -- Invariant: saturated appliations of 'FunTyCon' must
	                -- use 'FunTy' and saturated synonyms must use their own
                        -- constructors. However, /unsaturated/ 'FunTyCon's
                        -- do appear as 'TyConApp's.
	                -- Parameters:
	                --
	                -- 1) Type constructor being applied to.
	                --
                        -- 2) Type arguments. Might not have enough type arguments
                        --    here to saturate the constructor.
                        --    Even type synonyms are not necessarily saturated;
                        --    for example unsaturated type synonyms
	                --    can appear as the right hand side of a type synonym.

  | FunTy
	Type		
	Type		-- ^ Special case of 'TyConApp': @TyConApp FunTyCon [t1, t2]@
			-- See Note [Equality-constrained types]

  | ForAllTy            -- See Note [Type abstractions over coercions]
	TyCoVar         -- ^ type, kind, or coercion variable
	Type	        -- ^ A polymorphic type

  | LitTy TyLit     -- ^ Type literals are simillar to type constructors.

  | CastTy
        Type        -- ^ Type whose kind is to be casted ...
        Coercion    -- ^ ... by this coercion among kinds

  | CoercionTy      -- ^ Injection of a Coercion into a type
                    -- This should only ever be used in the RHS of an AppTy,
                    -- in the list of a TyConApp, or in a FunTy
        Coercion

  deriving (Data.Data, Data.Typeable)


-- NOTE:  Other parts of the code assume that type literals do not contain
-- types or type variables.
data TyLit
  = NumTyLit Integer
  | StrTyLit FastString
  deriving (Eq, Ord, Data.Data, Data.Typeable)

type KindOrType = Type -- See Note [Arguments to type constructors]

-- | The key type representing kinds in the compiler.
-- Invariant: a kind is always in one of these forms:
--
-- > FunTy k1 k2
-- > TyConApp PrimTyCon [...]
-- > TyVar kv   -- (during inference only)
-- > ForAll ... -- (for top-level coercions)
type Kind = Type

-- | "Super kinds", used to help encode 'Kind's as types.
-- Invariant: a super kind is always of this form:
--
-- > TyConApp SuperKindTyCon ...
type SuperKind = Type
\end{code}

Note [The kind invariant]
~~~~~~~~~~~~~~~~~~~~~~~~~
The kinds
   #          UnliftedTypeKind
   OpenKind   super-kind of *, #

can never appear under an arrow or type constructor in a kind; they
can only be at the top level of a kind.  It follows that primitive TyCons,
which have a naughty pseudo-kind
   State# :: * -> #
must always be saturated, so that we can never get a type whose kind
has a UnliftedTypeKind or ArgTypeKind underneath an arrow.

Nor can we abstract over a type variable with any of these kinds.

    k :: = kk | # | ArgKind | (#) | OpenKind 
    kk :: = * | kk -> kk | T kk1 ... kkn

So a type variable can only be abstracted kk.

Note [Arguments to type constructors]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Because of kind polymorphism, in addition to type application we now
have kind instantiation. We reuse the same notations to do so.

For example:

  Just (* -> *) Maybe
  Right * Nat Zero

are represented by:

  TyConApp (PromotedDataCon Just) [* -> *, Maybe]
  TyConApp (PromotedDataCon Right) [*, Nat, (PromotedDataCon Zero)]

Important note: Nat is used as a *kind* and not as a type. This can be
confusing, since type-level Nat and kind-level Nat are identical. We
use the kind of (PromotedDataCon Right) to know if its arguments are
kinds or types.

This kind instantiation only happens in TyConApp currently.

Note [Type abstraction over coercions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Types can be abstracted over coercions, and thus in many places where we used
to consider only tyvars, we must now also consider the possibility of covars.
But where, really, can these covars appear? In precisely these locations:
  - the kind of a promoted GADT data constructor
  - the existential variables of a data constructor (TODO (RAE): Really?? ~ vs ~#)
  - the type of the constructor Eq# (in type (~))
  - the quantified vars for an axiom branch
  - the type of an id

That's it. In particular, coercion variables MAY NOT appear in the quantified
tyvars of a TyCon (other than a promoted data constructor), of a class, of a
type synonym (regular or family).

Note [Equality-constrained types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The type   forall ab. (a ~ [b]) => blah
is encoded like this:

   ForAllTy (a:*) $ ForAllTy (b:*) $
   FunTy (TyConApp (~) [*, *, a, [b]]) $
   blah

Note that there are two equality types, boxed (~) and unboxed (~#).
'Coercion's have a type built with (~#). 'TcCoercion's have a type built with
(~). Only 'Coercion's can be quantified over in a ForAllTy, never
'TcCoercion's. To simplify equality among types, we then forbid having
a type constructed with (~#) on the left of a FunTy. Instead, use a ForAllTy
with a wildcard variable.

So, to summarize:

      ForAllTy  |  FunTy
----------------+-------
(~)  |   no     |   yes
(~#) |  yes     |   no

-------------------------------------
 		Note [PredTy]

\begin{code}
-- | A type of the form @p@ of kind @Constraint@ represents a value whose type is
-- the Haskell predicate @p@, where a predicate is what occurs before 
-- the @=>@ in a Haskell type.
--
-- We use 'PredType' as documentation to mark those types that we guarantee to have
-- this kind.
--
-- It can be expanded into its representation, but: 
--
-- * The type checker must treat it as opaque
--
-- * The rest of the compiler treats it as transparent
--
-- Consider these examples:
--
-- > f :: (Eq a) => a -> Int
-- > g :: (?x :: Int -> Int) => a -> Int
-- > h :: (r\l) => {r} => {l::Int | r}
--
-- Here the @Eq a@ and @?x :: Int -> Int@ and @r\l@ are all called \"predicates\"
type PredType = Type

-- | A collection of 'PredType's
type ThetaType = [PredType]
\end{code}

(We don't support TREX records yet, but the setup is designed
to expand to allow them.)

A Haskell qualified type, such as that for f,g,h above, is
represented using 
	* a FunTy for the double arrow
	* with a type of kind Constraint as the function argument

The predicate really does turn into a real extra argument to the
function.  If the argument has type (p :: Constraint) then the predicate p is
represented by evidence of type p.

%************************************************************************
%*									*
            Simple constructors
%*									*
%************************************************************************

These functions are here so that they can be used by TysPrim,
which in turn is imported by Type

\begin{code}
-- named with "Only" to prevent naive use of mkTyVarTy
mkOnlyTyVarTy  :: TyVar   -> Type
mkOnlyTyVarTy v = ASSERT( isTyVar v ) TyVarTy v

mkOnlyTyVarTys :: [TyVar] -> [Type]
mkOnlyTyVarTys = map mkOnlyTyVarTy -- a common use of mkOnlyTyVarTy

mkTyCoVarTy :: TyCoVar -> Type
mkTyCoVarTy v
  | isTyVar v
  = TyVarTy v
  | otherwise
  = ASSERT( isCoVar v )
    CoercionTy (CoVarCo v)

mkTyCoVarTys :: [TyCoVar] -> [Type]
mkTyCoVarTys = map mkTyCoVarTy

mkNakedTyConApp :: TyCon -> [Type] -> Type
-- Builds a TyConApp 
--   * without being strict in TyCon,
--   * the TyCon should never be a saturated FunTyCon 
-- Type.mkTyConApp is the usual one
mkNakedTyConApp tc tys
  = TyConApp (ASSERT( not (isFunTyCon tc && length tys == 2) ) tc) tys

isCoercionType :: Type -> Bool
isCoercionType (TyConApp tc tys)
  | tc `hasKey` eqPrimTyConKey
  , length tys == 4
  = True
isCoercionType _ = False

-- | Create the plain type constructor type which has been applied to no type arguments at all.
mkTyConTy :: TyCon -> Type
mkTyConTy tycon = TyConApp tycon []
\end{code}

Some basic functions, put here to break loops eg with the pretty printer

\begin{code}
isLiftedTypeKind :: Kind -> Bool
isLiftedTypeKind (TyConApp tc []) = tc `hasKey` liftedTypeKindTyConKey
isLiftedTypeKind _                = False

-- | Is this a super-kind (i.e. a type-of-kinds)?
isSuperKind :: Type -> Bool
isSuperKind (TyConApp skc []) = skc `hasKey` superKindTyConKey
isSuperKind _                 = False

isTypeVar :: Var -> Bool
isTypeVar v = isTKVar v && not (isSuperKind (varType v))

isKindVar :: Var -> Bool 
isKindVar v = isTKVar v && isSuperKind (varType v)


\end{code}

%************************************************************************
%*									*
            Coercions
%*									*
%************************************************************************

\begin{code}
-- | A 'Coercion' is concrete evidence of the equality/convertibility
-- of two types.

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
data Coercion 
  -- These ones mirror the shape of types
  = Refl Type  -- See Note [Refl invariant]
          -- Invariant: applications of (Refl T) to a bunch of identity coercions
          --            always show up as Refl.
          -- For example  (Refl T) (Refl a) (Refl b) shows up as (Refl (T a b)).

          -- Invariant: The type in a Refl will never be headed by CoercionTy

          -- Applications of (Refl T) to some coercions, at least one of
          -- which is NOT the identity, show up as TyConAppCo.
          -- (They may not be fully saturated however.)
          -- ConAppCo coercions (like all coercions other than Refl)
          -- are NEVER the identity.

  -- These ones simply lift the correspondingly-named 
  -- Type constructors into Coercions
  | TyConAppCo TyCon [CoercionArg]    -- lift TyConApp 
    	       -- The TyCon is never a synonym; 
	       -- we expand synonyms eagerly
	       -- But it can be a type function

  | AppCo Coercion CoercionArg        -- lift AppTy

  -- See Note [Forall coercions]
  | ForAllCo ForAllCoBndr Coercion

  -- These are special
  | CoVarCo CoVar
  | AxiomInstCo (CoAxiom Branched) BranchIndex [CoercionArg]
     -- See also [CoAxiom index]
     -- The coercion arguments always *precisely* saturate
     -- arity of (that branch of) the CoAxiom. If there are
     -- any left over, we use AppCo.
     -- See [Coercion axioms applied to coercions]

  | UnsafeCo Type Type
  | SymCo Coercion
  | TransCo Coercion Coercion

  -- These are destructors
  | NthCo  Int         Coercion     -- Zero-indexed; decomposes (T t0 ... tn)
  | LRCo   LeftOrRight Coercion     -- Decomposes (t_left t_right)

  -- InstCo lifts forall-instantiation
  | InstCo Coercion CoercionArg 

  -- Coherence applies a coercion to the left-hand type of another coercion
  -- See Note [Coherence]
  | CoherenceCo Coercion Coercion

  -- Extract a kind coercion from a (heterogeneous) type coercion
  | KindCo Coercion
  deriving (Data.Data, Data.Typeable)

-- | A 'ForAllCoBndr' is a binding form for a quantified coercion. It is 
-- necessary when lifting quantified types into coercions.  See Note
-- [Forall coercions]

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
data ForAllCoBndr
  = TyHomo TyVar
  | TyHetero Coercion TyVar TyVar CoVar
  | CoHomo CoVar
  | CoHetero Coercion CoVar CoVar
  deriving (Data.Data, Data.Typeable)

-- returns the variable bound in a ForAllCoBndr
coBndrVars :: ForAllCoBndr -> [TyCoVar]
coBndrVars (TyHomo tv)             = [tv]
coBndrVars (TyHetero _ tv1 tv2 cv) = [tv1, tv2, cv]
coBndrVars (CoHomo cv)             = [cv]
coBndrVars (CoHetero _ cv1 cv2)    = [cv1, cv2]

-- returns the variables with their types
coBndrVarsKinds :: ForAllCoBndr -> ([TyCoVar], [Type])
coBndrVarsKinds bndr = (vars, map varType vars)
  where vars = coBndrVars bndr

-- changes the "eta" coercion in a hetero CoBndr
setCoBndrEta :: ForAllCoBndr -> Coercion -> ForAllCoBndr
setCoBndrEta (TyHetero _ tv1 tv2 cv) h = mkTyHeteroCoBndr h tv1 tv2 cv
setCoBndrEta (CoHetero _ cv1 cv2)    h = mkCoHeteroCoBndr h cv1 cv2
setCoBndrEta cobndr                  _ = pprPanic "setCoBndrEta" (ppr cobndr)

-- are two ForAllCoBndrs the same sort of binder?
eqCoBndrSort :: ForAllCoBndr -> ForAllCoBndr -> Bool
eqCoBndrSort (TyHomo {})   (TyHomo {})   = True
eqCoBndrSort (TyHetero {}) (TyHetero {}) = True
eqCoBndrSort (CoHomo {})   (CoHomo {})   = True
eqCoBndrSort (CoHetero {}) (CoHetero {}) = True
eqCoBndrSort _             _             = False

-- | A CoercionArg is an argument to a coercion. It may be a coercion (lifted from
-- a type) or a pair of coercions (lifted from a coercion). See
-- Note [Coercion arguments]

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
data CoercionArg
  = TyCoArg Coercion
  | CoCoArg Coercion Coercion
  deriving ( Data.Data, Data.Typeable )

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
data LeftOrRight = CLeft | CRight 
                 deriving( Eq, Data.Data, Data.Typeable )

pickLR :: LeftOrRight -> (a,a) -> a
pickLR CLeft  (l,_) = l
pickLR CRight (_,r) = r
\end{code}


Note [Refl invariant]
~~~~~~~~~~~~~~~~~~~~~
Invariant 1:

Coercions have the following invariant 
     Refl is always lifted as far as possible.  

You might think that a consequencs is:
     Every identity coercions has Refl at the root

But that's not quite true because of coercion variables.  Consider
     g         where g :: Int~Int
     Left h    where h :: Maybe Int ~ Maybe Int
etc.  So the consequence is only true of coercions that
have no coercion variables.

Invariant 2:

All coercions other than Refl are guaranteed to coerce between two
*distinct* types.

Note [Coercion axioms applied to coercions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The reason coercion axioms can be applied to coercions and not just
types is to allow for better optimization.  There are some cases where
we need to be able to "push transitivity inside" an axiom in order to
expose further opportunities for optimization.  

For example, suppose we have

  C a : t[a] ~ F a
  g   : b ~ c

and we want to optimize

  sym (C b) ; t[g] ; C c

which has the kind

  F b ~ F c

(stopping through t[b] and t[c] along the way).

We'd like to optimize this to just F g -- but how?  The key is
that we need to allow axioms to be instantiated by *coercions*,
not just by types.  Then we can (in certain cases) push
transitivity inside the axiom instantiations, and then react
opposite-polarity instantiations of the same axiom.  In this
case, e.g., we match t[g] against the LHS of (C c)'s kind, to
obtain the substitution  a |-> g  (note this operation is sort
of the dual of lifting!) and hence end up with

  C g : t[b] ~ F c

which indeed has the same kind as  t[g] ; C c.

Now we have

  sym (C b) ; C g

which can be optimized to F g.

Note [Coercion arguments]
~~~~~~~~~~~~~~~~~~~~~~~~~
As explained in the above note, a coercion lifted from a type
is applied to a coercion, not a type. But, what if that type
itself expected to be applied to a coercion? Consider

  t : forall c: * ~ s. (* |> c)

Then, we get

 <t> : (forall c: * ~ s. (* |> c)) ~ (forall c: * ~ s. (* |> c))

We can't just apply <t> to a coercion, because then the components
of <t>'s kind will get applied to types, and that doesn't work out.
Note that we don't have coercions among coercions (thankfully), so
that isn't the answer. The answer is that <t> must be applied to
a pair of coercions, one for the left-hand type and one for the
right-hand type:

  <t> (g1, g2) : (* |> g1) ~ (* |> g2)

Thus, we have the CoercionArg type, which is either a single
coercion (for the normal case) or a pair of coercions (for the case
described here).

Note [CoAxiom index]
~~~~~~~~~~~~~~~~~~~~
A CoAxiom has 1 or more branches. Each branch has contains a list
of the free type variables in that branch, the LHS type patterns,
and the RHS type for that branch. When we apply an axiom to a list
of coercions, we must choose which branch of the axiom we wish to
use, as the different branches may have different numbers of free
type variables. (The number of type patterns is always the same
among branches, but that doesn't quite concern us here.)

The Int in the AxiomInstCo constructor is the 0-indexed number
of the chosen branch.

Note [Forall coercions]
~~~~~~~~~~~~~~~~~~~~~~~
Constructing coercions between forall-types can be a bit tricky.
Currently, the situation is as follows:

  1) ForAllCo (TyHetero Coercion TyVar TyVar CoVar) Coercion
  2) ForAllCo (CoHetero Coercion CoVar CoVar)       Coercion
  3) ForAllCo (TyHomo TyVar)                        Coercion
  4) ForAllCo (CoHomo CoVar)                        Coercion

We'll take these one at a time.

1) This form represents a coercion between two forall-types-over-types,
say (forall v1:k1.t1) and (forall v2:k2.t2). The difficulty comes about
because k1 might not be the same as k2. So, we will need three variables:
one of kind k1, one of kind k2, and one representing the coercion between
a1 and a2, which will be bound to the coercion stored in the TyHetero.

The typing rule is thus:

     h : k1 ~ k2  a1 : k1    a2 : k2    c : a1 ~ a2    g : t1 ~ t2
  -------------------------------------------------------------------
  ForAllCo (TyHetero h a1 a2 c) g : (all a1:k1.t1) ~ (all v2:k2.t2)

2) This form represents a coercion between two forall-types-over-coercions,
say (forall c1:phi1.t1) and (forall c2:phi2.t2). Because phi1 might not
equal phi2, we need two variables, one of kind phi1 and one of kind phi2.
Because of proof irrelevance (or the absence of coercions among coercions),
we won't need to refer to the witness showing phi1 and phi2 are coercible.

The typing rule is thus:

      h : phi1 ~ phi2   c1 : phi1     c2 : phi2     g : t1 ~ t2
  -----------------------------------------------------------------
  ForAllCo (CoHetero h c1 c2) g : (all c1:phi1.t1) ~ (all c2:phi2.t2)

3) This form is a simplification when the two kinds of the types in a
TyHetero are actually the same. The coercion variable would not normally
appear in the coercion. The typing rule is:

      a : k     g : t1 ~ t2
  ---------------------------------------------------
  ForAllCo (TyHomo a) g : (all a:k.t1) ~ (all a:k.t2)

4) Similarly, the CoHomo form is for homogeneous coercion quantification.
The typing rule is:

      c : phi        g : t1 ~ t2
  -------------------------------------------------------
  ForAllCo (CoHomo c) g : (all c:phi.t1) ~ (all c:phi.t2)

Note that is is an *invariant* that the kinds of the variables in a "Hetero"
construction are different.

Note [Coherence]
~~~~~~~~~~~~~~~~
The Coherence typing rule is thus:

  g1 : s ~ t    s : k1    g2 : k1 ~ k2
  ------------------------------------
  CoherenceCo g1 g2 : (s |> g2) ~ t

While this look (and is) unsymmetric, a combination of other coercion
combinators can make the symmetric version.

Note [Predicate coercions]
~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have
   g :: a~b
How can we coerce between types
   ([c]~a) => [a] -> c
and
   ([c]~b) => [b] -> c
where the equality predicate *itself* differs?

Answer: we simply treat (~) as an ordinary type constructor, so these
types really look like

   ((~) [c] a) -> [a] -> c
   ((~) [c] b) -> [b] -> c

So the coercion between the two is obviously

   ((~) [c] g) -> [g] -> c

Another way to see this to say that we simply collapse predicates to
their representation type (see Type.coreView and Type.predTypeRep).

This collapse is done by mkPredCo; there is no PredCo constructor
in Coercion.  This is important because we need Nth to work on 
predicates too:
    Nth 1 ((~) [c] g) = g
See Simplify.simplCoercionF, which generates such selections.


%************************************************************************
%*									*
			Free variables of types and coercions
%*									*
%************************************************************************

\begin{code}
tyVarsOnlyOfType :: Type -> TyVarSet
-- ^ NB: for type synonyms tyVarsOnlyOfType does /not/ expand the synonym
-- tyVarsOnlyOfType returns only the free variables of a type
-- For example, tyVarsOnlyOfType (a::k) returns {a}, not including the
-- kind variable {k}
tyVarsOnlyOfType (TyVarTy v)         = unitVarSet v
tyVarsOnlyOfType (TyConApp _ tys)    = tyVarsOnlyOfTypes tys
tyVarsOnlyOfType (LitTy {})          = emptyVarSet
tyVarsOnlyOfType (FunTy arg res)     = tyVarsOnlyOfType arg `unionVarSet` tyVarsOnlyOfType res
tyVarsOnlyOfType (AppTy fun arg)     = tyVarsOnlyOfType fun `unionVarSet` tyVarsOnlyOfType arg
tyVarsOnlyOfType (ForAllTy tyvar ty) = delVarSet (tyVarsOnlyOfType ty) tyvar
                                   `unionVarSet` tyVarsOnlyOfType (tyVarKind tyvar)
tyVarsOnlyOfType (CastTy ty co)      = tyVarsOnlyOfType ty `unionVarSet` tyVarsOnlyOfCo co
tyVarsOnlyOfType (CoercionTy co)     = tyVarsOnlyOfCo co

tyVarsOnlyOfTypes :: [Type] -> TyVarSet
tyVarsOnlyOfTypes tys = foldr (unionVarSet . tyVarsOnlyOfType) emptyVarSet tys

tyVarsOnlyOfCo :: Coercion -> TyCoVarSet
-- Extracts type and coercion variables from a coercion
tyVarsOnlyOfCo (Refl ty)           = tyVarsOnlyOfType ty
tyVarsOnlyOfCo (TyConAppCo _ args) = tyVarsOnlyOfCoArgs args
tyVarsOnlyOfCo (AppCo co arg)      = tyVarsOnlyOfCo co `unionVarSet` tyVarsOnlyOfCoArg arg
tyVarsOnlyOfCo (ForAllCo cobndr co)
  = let (vars, kinds) = coBndrVarsKinds cobndr in
    tyVarsOnlyOfCo co `delVarSetList` vars `unionVarSet` tyVarsOnlyOfTypes kinds
tyVarsOnlyOfCo (CoVarCo _)         = emptyVarSet
tyVarsOnlyOfCo (AxiomInstCo _ _ cos) = tyVarsOnlyOfCoArgs cos
tyVarsOnlyOfCo (UnsafeCo ty1 ty2)  = tyVarsOnlyOfType ty1 `unionVarSet` tyVarsOnlyOfType ty2
tyVarsOnlyOfCo (SymCo co)          = tyVarsOnlyOfCo co
tyVarsOnlyOfCo (TransCo co1 co2)   = tyVarsOnlyOfCo co1 `unionVarSet` tyVarsOnlyOfCo co2
tyVarsOnlyOfCo (NthCo _ co)        = tyVarsOnlyOfCo co
tyVarsOnlyOfCo (LRCo _ co)         = tyVarsOnlyOfCo co
tyVarsOnlyOfCo (InstCo co arg)     = tyVarsOnlyOfCo co `unionVarSet` tyVarsOnlyOfCoArg arg
tyVarsOnlyOfCo (CoherenceCo c1 c2) = tyVarsOnlyOfCo c1 `unionVarSet` tyVarsOnlyOfCo c2
tyVarsOnlyOfCo (KindCo co)         = tyVarsOnlyOfCo co

tyVarsOnlyOfCos :: [Coercion] -> TyCoVarSet
tyVarsOnlyOfCos cos = foldr (unionVarSet . tyVarsOnlyOfCo) emptyVarSet cos

tyVarsOnlyOfCoArg :: CoercionArg -> TyCoVarSet
tyVarsOnlyOfCoArg (TyCoArg co)    = tyVarsOnlyOfCo co
tyVarsOnlyOfCoArg (CoCoArg c1 c2) = tyVarsOnlyOfCo c1 `unionVarSet` tyVarsOnlyOfCo c2

tyVarsOnlyOfCoArgs :: [CoercionArg] -> TyCoVarSet
tyVarsOnlyOfCoArgs args = foldr (unionVarSet . tyVarsOnlyOfCoArg) emptyVarSet args


tyCoVarsOfType :: Type -> TyCoVarSet
-- ^ NB: for type synonyms tyCoVarsOfType does /not/ expand the synonym
-- tyCoVarsOfType returns only the free variables of a type
-- For example, tyCoVarsOfType (a::k) returns {a}, not including the
-- kind variable {k}
tyCoVarsOfType (TyVarTy v)         = unitVarSet v
tyCoVarsOfType (TyConApp _ tys)    = tyCoVarsOfTypes tys
tyCoVarsOfType (LitTy {})          = emptyVarSet
tyCoVarsOfType (FunTy arg res)     = tyCoVarsOfType arg `unionVarSet` tyCoVarsOfType res
tyCoVarsOfType (AppTy fun arg)     = tyCoVarsOfType fun `unionVarSet` tyCoVarsOfType arg
tyCoVarsOfType (ForAllTy tyvar ty) = delVarSet (tyCoVarsOfType ty) tyvar
                                   `unionVarSet` tyCoVarsOfType (tyVarKind tyvar)
tyCoVarsOfType (CastTy ty co)      = tyCoVarsOfType ty `unionVarSet` tyCoVarsOfCo co
tyCoVarsOfType (CoercionTy co)     = tyCoVarsOfCo co

tyCoVarsOfTypes :: [Type] -> TyCoVarSet
tyCoVarsOfTypes tys = foldr (unionVarSet . tyCoVarsOfType) emptyVarSet tys

tyCoVarsOfCo :: Coercion -> TyCoVarSet
-- Extracts type and coercion variables from a coercion
tyCoVarsOfCo (Refl ty)           = tyCoVarsOfType ty
tyCoVarsOfCo (TyConAppCo _ args) = tyCoVarsOfCoArgs args
tyCoVarsOfCo (AppCo co arg)      = tyCoVarsOfCo co `unionVarSet` tyCoVarsOfCoArg arg
tyCoVarsOfCo (ForAllCo cobndr co)
  = let (vars, kinds) = coBndrVarsKinds cobndr in
    tyCoVarsOfCo co `delVarSetList` vars `unionVarSet` tyCoVarsOfTypes kinds
tyCoVarsOfCo (CoVarCo v)         = unitVarSet v
tyCoVarsOfCo (AxiomInstCo _ _ cos) = tyCoVarsOfCoArgs cos
tyCoVarsOfCo (UnsafeCo ty1 ty2)
  = tyCoVarsOfType ty1 `unionVarSet` tyCoVarsOfType ty2
tyCoVarsOfCo (SymCo co)          = tyCoVarsOfCo co
tyCoVarsOfCo (TransCo co1 co2)   = tyCoVarsOfCo co1 `unionVarSet` tyCoVarsOfCo co2
tyCoVarsOfCo (NthCo _ co)        = tyCoVarsOfCo co
tyCoVarsOfCo (LRCo _ co)         = tyCoVarsOfCo co
tyCoVarsOfCo (InstCo co arg)     = tyCoVarsOfCo co `unionVarSet` tyCoVarsOfCoArg arg
tyCoVarsOfCo (CoherenceCo c1 c2) = tyCoVarsOfCo c1 `unionVarSet` tyCoVarsOfCo c2
tyCoVarsOfCo (KindCo co)         = tyCoVarsOfCo co

tyCoVarsOfCos :: [Coercion] -> TyCoVarSet
tyCoVarsOfCos cos = foldr (unionVarSet . tyCoVarsOfCo) emptyVarSet cos

tyCoVarsOfCoArg :: CoercionArg -> TyCoVarSet
tyCoVarsOfCoArg (TyCoArg co)    = tyCoVarsOfCo co
tyCoVarsOfCoArg (CoCoArg c1 c2) = tyCoVarsOfCo c1 `unionVarSet` tyCoVarsOfCo c2

tyCoVarsOfCoArgs :: [CoercionArg] -> TyCoVarSet
tyCoVarsOfCoArgs args = foldr (unionVarSet . tyCoVarsOfCoArg) emptyVarSet args

coVarsOfType :: Type -> CoVarSet
coVarsOfType (TyVarTy _)         = emptyVarSet
coVarsOfType (TyConApp _ tys)    = coVarsOfTypes tys
coVarsOfType (LitTy {})          = emptyVarSet
coVarsOfType (FunTy arg res)     = coVarsOfType arg `unionVarSet` coVarsOfType res
coVarsOfType (AppTy fun arg)     = coVarsOfType fun `unionVarSet` coVarsOfType arg
coVarsOfType (ForAllTy tyvar ty) = delVarSet (coVarsOfType ty) tyvar
                                   `unionVarSet` coVarsOfType (tyVarKind tyvar)
coVarsOfType (CastTy ty co)      = coVarsOfType ty `unionVarSet` coVarsOfCo co
coVarsOfType (CoercionTy co)     = coVarsOfCo co

coVarsOfTypes :: [Type] -> TyCoVarSet
coVarsOfTypes tys = foldr (unionVarSet . coVarsOfType) emptyVarSet tys

coVarsOfCo :: Coercion -> CoVarSet
-- Extract *coercion* variables only.  Tiresome to repeat the code, but easy.
coVarsOfCo (Refl ty)           = coVarsOfType ty
coVarsOfCo (TyConAppCo _ args) = coVarsOfCoArgs args
coVarsOfCo (AppCo co arg)      = coVarsOfCo co `unionVarSet` coVarsOfCoArg arg
coVarsOfCo (ForAllCo cobndr co)
  = let (vars, kinds) = coBndrVarsKinds cobndr in
    coVarsOfCo co `delVarSetList` vars `unionVarSet` coVarsOfTypes kinds
coVarsOfCo (CoVarCo v)         = unitVarSet v
coVarsOfCo (AxiomInstCo _ _ args) = coVarsOfCoArgs args
coVarsOfCo (UnsafeCo ty1 ty2)  = coVarsOfTypes [ty1, ty2]
coVarsOfCo (SymCo co)          = coVarsOfCo co
coVarsOfCo (TransCo co1 co2)   = coVarsOfCo co1 `unionVarSet` coVarsOfCo co2
coVarsOfCo (NthCo _ co)        = coVarsOfCo co
coVarsOfCo (LRCo _ co)         = coVarsOfCo co
coVarsOfCo (InstCo co arg)     = coVarsOfCo co `unionVarSet` coVarsOfCoArg arg
coVarsOfCo (CoherenceCo c1 c2) = coVarsOfCos [c1, c2]
coVarsOfCo (KindCo co)         = coVarsOfCo co

coVarsOfCos :: [Coercion] -> CoVarSet
coVarsOfCos cos = foldr (unionVarSet . coVarsOfCo) emptyVarSet cos

coVarsOfCoArg :: CoercionArg -> CoVarSet
coVarsOfCoArg (TyCoArg co)    = coVarsOfCo co
coVarsOfCoArg (CoCoArg c1 c2) = coVarsOfCos [c1, c2]

coVarsOfCoArgs :: [CoercionArg] -> CoVarSet
coVarsOfCoArgs args = foldr (unionVarSet . coVarsOfCoArg) emptyVarSet args
\end{code}

%************************************************************************
%*									*
			TyThing
%*									*
%************************************************************************

Despite the fact that DataCon has to be imported via a hi-boot route, 
this module seems the right place for TyThing, because it's needed for
funTyCon and all the types in TysPrim.

Note [ATyCon for classes]
~~~~~~~~~~~~~~~~~~~~~~~~~
Both classes and type constructors are represented in the type environment
as ATyCon.  You can tell the difference, and get to the class, with
   isClassTyCon :: TyCon -> Bool
   tyConClass_maybe :: TyCon -> Maybe Class
The Class and its associated TyCon have the same Name.

\begin{code}
-- | A typecheckable-thing, essentially anything that has a name
data TyThing 
  = AnId     Id
  | ADataCon DataCon
  | ATyCon   TyCon       -- TyCons and classes; see Note [ATyCon for classes]
  | ACoAxiom (CoAxiom Branched)
  deriving (Eq, Ord)

instance Outputable TyThing where 
  ppr = pprTyThing

pprTyThing :: TyThing -> SDoc
pprTyThing thing = pprTyThingCategory thing <+> quotes (ppr (getName thing))

pprTyThingCategory :: TyThing -> SDoc
pprTyThingCategory (ATyCon tc)
  | isClassTyCon tc = ptext (sLit "Class")
  | otherwise       = ptext (sLit "Type constructor")
pprTyThingCategory (ACoAxiom _) = ptext (sLit "Coercion axiom")
pprTyThingCategory (AnId   _)   = ptext (sLit "Identifier")
pprTyThingCategory (ADataCon _) = ptext (sLit "Data constructor")


instance NamedThing TyThing where	-- Can't put this with the type
  getName (AnId id)     = getName id	-- decl, because the DataCon instance
  getName (ATyCon tc)   = getName tc	-- isn't visible there
  getName (ACoAxiom cc) = getName cc
  getName (ADataCon dc) = dataConName dc

\end{code}


%************************************************************************
%*									*
			Substitutions
      Data type defined here to avoid unnecessary mutual recursion
%*									*
%************************************************************************

\begin{code}
-- | Type & coercion substitution
--
-- #tcvsubst_invariant#
-- The following invariants must hold of a 'TCvSubst':
-- 
-- 1. The in-scope set is needed /only/ to
-- guide the generation of fresh uniques
--
-- 2. In particular, the /kind/ of the type variables in 
-- the in-scope set is not relevant
--
-- 3. The substition is only applied ONCE! This is because
-- in general such application will not reached a fixed point.
data TCvSubst 		
  = TCvSubst InScopeSet -- The in-scope type and kind variables
	     TvSubstEnv -- Substitutes both type and kind variables
             CvSubstEnv -- Substitutes coercion variables
	-- See Note [Apply Once]
	-- and Note [Extending the TvSubstEnv]
        -- and Note [Substituting types and coercions]

-- | A substitition of 'Type's for 'TyVar's
--                 and 'Kind's for 'KindVar's
type TvSubstEnv = TyVarEnv Type
	-- A TvSubstEnv is used both inside a TCvSubst (with the apply-once
	-- invariant discussed in Note [Apply Once]), and also independently
	-- in the middle of matching, and unification (see Types.Unify)
	-- So you have to look at the context to know if it's idempotent or
	-- apply-once or whatever

-- | A substitution of 'Coercion's for 'CoVar's
type CvSubstEnv = CoVarEnv Coercion

\end{code}

Note [Apply Once]
~~~~~~~~~~~~~~~~~
We use TCvSubsts to instantiate things, and we might instantiate
	forall a b. ty
\with the types
	[a, b], or [b, a].
So the substition might go [a->b, b->a].  A similar situation arises in Core
when we find a beta redex like
	(/\ a /\ b -> e) b a
Then we also end up with a substition that permutes type variables. Other
variations happen to; for example [a -> (a, b)].  

	****************************************************
	*** So a TCvSubst must be applied precisely once ***
	****************************************************

A TCvSubst is not idempotent, but, unlike the non-idempotent substitution
we use during unifications, it must not be repeatedly applied.

Note [Extending the TvSubstEnv]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
See #tcvsubst_invariant# for the invariants that must hold.

This invariant allows a short-cut when the subst envs are empty:
if the TvSubstEnv and CvSubstEnv are empty --- i.e. (isEmptyTCvSubst subst)
holds --- then (substTy subst ty) does nothing.

For example, consider:
	(/\a. /\b:(a~Int). ...b..) Int
We substitute Int for 'a'.  The Unique of 'b' does not change, but
nevertheless we add 'b' to the TvSubstEnv, because b's kind does change

This invariant has several crucial consequences:

* In substTyVarBndr, we need extend the TvSubstEnv 
	- if the unique has changed
	- or if the kind has changed

* In substTyCoVar, we do not need to consult the in-scope set;
  the TvSubstEnv is enough

* In substTy, substTheta, we can short-circuit when the TvSubstEnv is empty

Note [Substituting types and coercions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Types and coercions are mutually recursive, and either may have variables
"belonging" to the other. Thus, every time we wish to substitute in a
type, we may also need to substitute in a coercion, and vice versa.
However, the constructor used to create type variables is distinct from
that of coercion variables, so we carry two VarEnvs in a TCvSubst. Note
that it would be possible to use the CoercionTy constructor to combine
these environments, but that seems like a false economy.

Note that the TvSubstEnv should *never* map a CoVar (built with the Id
constructor) and the CvSubstEnv should *never* map a TyVar. Furthermore,
the range of the TvSubstEnv should *never* include a type headed with
CoercionTy.

\begin{code}

emptyTvSubstEnv :: TvSubstEnv
emptyTvSubstEnv = emptyVarEnv

emptyCvSubstEnv :: CvSubstEnv
emptyCvSubstEnv = emptyVarEnv

composeTCvSubstEnv :: InScopeSet
                   -> (TvSubstEnv, CvSubstEnv)
                   -> (TvSubstEnv, CvSubstEnv)
                   -> (TvSubstEnv, CvSubstEnv)
-- ^ @(compose env1 env2)(x)@ is @env1(env2(x))@; i.e. apply @env2@ then @env1@.
-- It assumes that both are idempotent.
-- Typically, @env1@ is the refinement to a base substitution @env2@
composeTCvSubstEnv in_scope (tenv1, cenv1) (tenv2, cenv2)
  = ( tenv1 `plusVarEnv` mapVarEnv (substTy subst1) tenv2
    , cenv1 `plusVarEnv` mapVarEnv (substCo subst1) cenv2 )
	-- First apply env1 to the range of env2
	-- Then combine the two, making sure that env1 loses if
	-- both bind the same variable; that's why env1 is the
	--  *left* argument to plusVarEnv, because the right arg wins
  where
    subst1 = TCvSubst in_scope tenv1 cenv1

emptyTCvSubst :: TCvSubst
emptyTCvSubst = TCvSubst emptyInScopeSet emptyTvSubstEnv emptyCvSubstEnv

mkEmptyTCvSubst :: InScopeSet -> TCvSubst
mkEmptyTCvSubst is = TCvSubst is emptyTvSubstEnv emptyCvSubstEnv

isEmptyTCvSubst :: TCvSubst -> Bool
	 -- See Note [Extending the TvSubstEnv]
isEmptyTCvSubst (TCvSubst _ tenv cenv) = isEmptyVarEnv tenv && isEmptyVarEnv cenv

mkTCvSubst :: InScopeSet -> TvSubstEnv -> CvSubstEnv -> TCvSubst
mkTCvSubst = TCvSubst

getTvSubstEnv :: TCvSubst -> TvSubstEnv
getTvSubstEnv (TCvSubst _ env _) = env

getCvSubstEnv :: TCvSubst -> CvSubstEnv
getCvSubstEnv (TCvSubst _ _ env) = env

getTCvInScope :: TCvSubst -> InScopeSet
getTCvInScope (TCvSubst in_scope _ _) = in_scope

isInScope :: Var -> TCvSubst -> Bool
isInScope v (TCvSubst in_scope _ _) = v `elemInScopeSet` in_scope

notElemTCvSubst :: Var -> TCvSubst -> Bool
notElemTCvSubst v (TCvSubst _ tenv cenv)
  | isTyVar v
  = not (v `elemVarEnv` tenv)
  | otherwise
  = not (v `elemVarEnv` cenv)

setTvSubstEnv :: TCvSubst -> TvSubstEnv -> TCvSubst
setTvSubstEnv (TCvSubst in_scope _ cenv) tenv = TCvSubst in_scope tenv cenv

setCvSubstEnv :: TCvSubst -> CvSubstEnv -> TCvSubst
setCvSubstEnv (TCvSubst in_scope tenv _) cenv = TCvSubst in_scope tenv cenv

zapTCvSubst :: TCvSubst -> TCvSubst
zapTCvSubst (TCvSubst in_scope _ _) = TCvSubst in_scope emptyVarEnv emptyVarEnv

extendTCvInScope :: TCvSubst -> Var -> TCvSubst
extendTCvInScope (TCvSubst in_scope tenv cenv) var
  = TCvSubst (extendInScopeSet in_scope var) tenv cenv

extendTCvInScopeList :: TCvSubst -> [Var] -> TCvSubst
extendTCvInScopeList (TCvSubst in_scope tenv cenv) vars
  = TCvSubst (extendInScopeSetList in_scope vars) tenv cenv

extendSubstEnvs :: (TvSubstEnv, CvSubstEnv) -> Var -> Type
                -> (TvSubstEnv, CvSubstEnv)
extendSubstEnvs (tenv, cenv) v ty
  | isTyVar v
  = ASSERT( not $ isCoercionTy ty )
    (extendVarEnv tenv v ty, cenv)
  | CoercionTy co <- ty
  = (tenv, extendVarEnv cenv v co)
  | otherwise
  = pprPanic "extendSubstEnvs" (ppr v <+> ptext (sLit "|->") <+> ppr ty)

extendTCvSubst :: TCvSubst -> Var -> Type -> TCvSubst
extendTCvSubst (TCvSubst in_scope tenv cenv) tv ty
  = TCvSubst in_scope tenv' cenv'
  where (tenv', cenv') = extendSubstEnvs (tenv, cenv) tv ty

extendTCvSubstList :: TCvSubst -> [Var] -> [Type] -> TCvSubst
extendTCvSubstList subst tvs tys 
  = foldl2 extendTCvSubst subst tvs tys

unionTCvSubst :: TCvSubst -> TCvSubst -> TCvSubst
-- Works when the ranges are disjoint
unionTCvSubst (TCvSubst in_scope1 tenv1 cenv1) (TCvSubst in_scope2 tenv2 cenv2)
  = ASSERT( not (tenv1 `intersectsVarEnv` tenv2)
         && not (cenv1 `intersectsVarEnv` cenv2) )
    TCvSubst (in_scope1 `unionInScope` in_scope2)
             (tenv1     `plusVarEnv`   tenv2)
             (cenv1     `plusVarEnv`   cenv2)

-- mkOpenTCvSubst and zipOpenTCvSubst generate the in-scope set from
-- the types given; but it's just a thunk so with a bit of luck
-- it'll never be evaluated

-- Note [Generating the in-scope set for a substitution]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- If we want to substitute [a -> ty1, b -> ty2] I used to 
-- think it was enough to generate an in-scope set that includes
-- fv(ty1,ty2).  But that's not enough; we really should also take the
-- free vars of the type we are substituting into!  Example:
--	(forall b. (a,b,x)) [a -> List b]
-- Then if we use the in-scope set {b}, there is a danger we will rename
-- the forall'd variable to 'x' by mistake, getting this:
--	(forall x. (List b, x, x))
-- Urk!  This means looking at all the calls to mkOpenTCvSubst....


-- | Generates an in-scope set from the free variables in a list of types
-- and a list of coercions
mkTyCoInScopeSet :: [Type] -> [Coercion] -> InScopeSet
mkTyCoInScopeSet tys cos
  = mkInScopeSet (tyCoVarsOfTypes tys `unionVarSet` tyCoVarsOfCos cos)

-- | Generates the in-scope set for the 'TCvSubst' from the types in the incoming
-- environment, hence "open"
mkOpenTCvSubst :: TvSubstEnv -> CvSubstEnv -> TCvSubst
mkOpenTCvSubst tenv cenv
  = TCvSubst (mkTyCoInScopeSet (varEnvElts tenv) (varEnvElts cenv)) tenv cenv

-- | Generates the in-scope set for the 'TCvSubst' from the types in the incoming
-- environment, hence "open"
zipOpenTCvSubst :: [Var] -> [Type] -> TCvSubst
zipOpenTCvSubst tyvars tys 
  | debugIsOn && (length tyvars /= length tys)
  = pprTrace "zipOpenTCvSubst" (ppr tyvars $$ ppr tys) emptyTCvSubst
  | otherwise
  = TCvSubst (mkInScopeSet (tyCoVarsOfTypes tys)) tenv cenv
  where (tenv, cenv) = zipTyCoEnv tyvars tys

-- | Called when doing top-level substitutions. Here we expect that the 
-- free vars of the range of the substitution will be empty.
mkTopTCvSubst :: [(TyVar, Type)] -> TCvSubst
mkTopTCvSubst prs = TCvSubst emptyInScopeSet tenv cenv
  where (tenv, cenv) = foldl extend (emptyTvSubstEnv, emptyCvSubstEnv) prs
        extend envs (v, ty) = extendSubstEnvs envs v ty

zipTopTCvSubst :: [TyVar] -> [Type] -> TCvSubst
zipTopTCvSubst tyvars tys 
  | debugIsOn && (length tyvars /= length tys)
  = pprTrace "zipTopTCvSubst" (ppr tyvars $$ ppr tys) emptyTCvSubst
  | otherwise
  = TCvSubst emptyInScopeSet tenv cenv
  where (tenv, cenv) = zipTyCoEnv tyvars tys

zipTyCoEnv :: [TyVar] -> [Type] -> (TvSubstEnv, CvSubstEnv)
zipTyCoEnv tyvars tys
  | debugIsOn && (length tyvars /= length tys)
  = pprTrace "zipTyCoEnv" (ppr tyvars $$ ppr tys)
    (emptyVarEnv, emptyVarEnv)
  | otherwise
  = zip_ty_co_env tyvars tys (emptyVarEnv, emptyVarEnv)

-- Later substitutions in the list over-ride earlier ones, 
-- but there should be no loops
zip_ty_co_env :: [TyVar] -> [Type]
              -> (TvSubstEnv, CvSubstEnv)
              -> (TvSubstEnv, CvSubstEnv)
zip_ty_co_env []       []       envs = envs
zip_ty_co_env (tv:tvs) (ty:tys) (tenv, cenv)
  = zip_ty_co_env tvs tys (tenv', cenv')
  where (tenv', cenv') = extendSubstEnvs (tenv, cenv) tv ty
	-- There used to be a special case for when 
	--	ty == TyVarTy tv
	-- (a not-uncommon case) in which case the substitution was dropped.
	-- But the type-tidier changes the print-name of a type variable without
	-- changing the unique, and that led to a bug.   Why?  Pre-tidying, we had 
	-- a type {Foo t}, where Foo is a one-method class.  So Foo is really a newtype.
	-- And it happened that t was the type variable of the class.  Post-tiding, 
	-- it got turned into {Foo t2}.  The ext-core printer expanded this using
	-- sourceTypeRep, but that said "Oh, t == t2" because they have the same unique,
	-- and so generated a rep type mentioning t not t2.  
	--
	-- Simplest fix is to nuke the "optimisation"
zip_ty_co_env tvs      tys      envs   = pprTrace "Var/Type length mismatch: " (ppr tvs $$ ppr tys) envs

instance Outputable TCvSubst where
  ppr (TCvSubst ins tenv cenv)
    = brackets $ sep[ ptext (sLit "TCvSubst"),
		      nest 2 (ptext (sLit "In scope:") <+> ppr ins), 
		      nest 2 (ptext (sLit "Type env:") <+> ppr tenv),
                      nest 2 (ptext (sLit "Co env:") <+> ppr cenv) ]
\end{code}

%************************************************************************
%*									*
		Performing type or kind substitutions
%*									*
%************************************************************************

Note [Sym and ForAllCo]
~~~~~~~~~~~~~~~~~~~~~~~
In OptCoercion, we try to push "sym" out to the leaves of a coercion. But,
how do we push sym into a ForAllCo? It's a little ugly. Let's consider the
heterogeneous cases first, as it's easier to understand the homogeneous
cases as a specialization.

Here is the typing rule for TyHetero:

h : k1 ~# k2
tv1 : k1              tv2 : k2
cv : tv1 ~# tv2
tv1, tv2, cv |- g : ty1 ~# ty2
ForAllTy tv1 ty1 : *
ForAllTy tv2 ty2 : *
-----------------------------------------------------------------------------
ForAllCo (TyHetero h tv1 tv2 cv) g : (ForAllTy tv1 ty1) ~# (ForAllTy tv2 ty2)

Here is what we want:

ForAllCo (TyHetero h' tv1' tv2' cv') g' : (ForAllTy tv2 ty2) ~# (ForAllTy tv1 ty1)

Because the kinds of the type variables to the right of the colon are the kinds
coerced by h', we know (h' : k2 ~# k1). Thus, (h' = sym h).

Then, because the kinds of the type variables in the TyHetero are related by
the coercion in the TyHetero (i.e. h'), we need to swap these type variables:
(tv2' = tv1) and (tv1' = tv2).

Then, because the coercion variable in the TyHetero must coerce the two type
variables, *in order*, that appear in the TyHetero, we must have
(cv' : tv1' ~# tv2') = (cv' : tv2 ~# tv1).

But, g is well-typed only in a context where (cv : tv1 ~# tv2). So, to use
cv' in g, we must perform the substitution [cv |-> sym cv'].

Lastly, to get ty1 and ty2 to work out, we must apply sym to g.

Putting it all together, we get this:

sym (ForAllCo (TyHetero h tv1 tv2 cv) g)
==>
ForAllCo (TyHetero (sym h) tv2 tv1 (cv' : tv2 ~# tv1)) (sym (g[cv |-> sym cv']))

This is done in opt_co (in OptCoercion), supported by substForAllCoBndrCallback
and substCoVarBndrCallback.


The rule for CoHetero is similar, but there is no coercion variable analogous
to cv, so it's much simpler. Similarly, the TyHomo and CoHomo cases are
straightforward once you understand the rule above. 

\begin{code}
-- | Type substitution making use of an 'TCvSubst' that
-- is assumed to be open, see 'zipOpenTCvSubst'
substTyWith :: [TyVar] -> [Type] -> Type -> Type
substTyWith tvs tys = ASSERT( length tvs == length tys )
		      substTy (zipOpenTCvSubst tvs tys)

substKiWith :: [KindVar] -> [Kind] -> Kind -> Kind
substKiWith = substTyWith

-- | Type substitution making use of an 'TCvSubst' that
-- is assumed to be open, see 'zipOpenTCvSubst'
substTysWith :: [TyVar] -> [Type] -> [Type] -> [Type]
substTysWith tvs tys = ASSERT( length tvs == length tys )
		       substTys (zipOpenTCvSubst tvs tys)

substKisWith :: [KindVar] -> [Kind] -> [Kind] -> [Kind]
substKisWith = substTysWith

-- | Substitute within a 'Type'
substTy :: TCvSubst -> Type  -> Type
substTy subst ty | isEmptyTCvSubst subst = ty
		 | otherwise             = subst_ty subst ty

-- | Substitute within several 'Type's
substTys :: TCvSubst -> [Type] -> [Type]
substTys subst tys | isEmptyTCvSubst subst = tys
	           | otherwise             = map (subst_ty subst) tys

-- | Substitute within a 'ThetaType'
substTheta :: TCvSubst -> ThetaType -> ThetaType
substTheta = substTys

subst_ty :: TCvSubst -> Type -> Type
-- subst_ty is the main workhorse for type substitution
--
-- Note that the in_scope set is poked only if we hit a forall
-- so it may often never be fully computed 
subst_ty subst ty
   = go ty
  where
    go (TyVarTy tv)      = substTyCoVar subst tv
    go (AppTy fun arg)   = mkAppTy (go fun) $! (go arg)
                -- The mkAppTy smart constructor is important
                -- we might be replacing (a Int), represented with App
                -- by [Int], represented with TyConApp
    go (TyConApp tc tys) = let args = map go tys
                           in  args `seqList` TyConApp tc args
    go (FunTy arg res)   = (FunTy $! (go arg)) $! (go res)
    go (ForAllTy tv ty)  = case substTyCoVarBndr subst tv of
                              (subst', tv') ->
                                 ForAllTy tv' $! (subst_ty subst' ty)
    go (LitTy n)         = LitTy $! n
    go (CastTy ty co)    = (CastTy $! (go ty)) $! (subst_co subst co)
    go (CoercionTy co)   = CoercionTy $! (subst_co subst co)

substTyVar :: TCvSubst -> TyVar -> Type
substTyVar (TCvSubst _ tenv _) tv
  = case lookupVarEnv tenv tv of
      Just ty -> ty
      Nothing -> TyVarTy tv

substTyVars :: TCvSubst -> [TyVar] -> [Type]
substTyVars subst = map $ substTyVar subst

substTyCoVars :: TCvSubst -> [TyCoVar] -> [Type]
substTyCoVars subst = map $ substTyCoVar subst

-- See Note [Apply Once]
substTyCoVar :: TCvSubst -> TyCoVar -> Type
substTyCoVar (TCvSubst _ tenv cenv) tv
  | isTyVar tv
  = case lookupVarEnv tenv tv of
      Just ty -> ty
      Nothing -> TyVarTy tv
  | otherwise
  = case lookupVarEnv cenv tv of
      Just co -> CoercionTy co
      Nothing -> CoercionTy (CoVarCo tv)
  -- We do not require that the tyvar is in scope
  -- Reason: we do quite a bit of (substTyWith [tv] [ty] tau)
  -- and it's a nuisance to bring all the free vars of tau into
  -- scope --- and then force that thunk at every tyvar
  -- Instead we have an ASSERT in substTyVarBndr to check for capture


lookupTyVar :: TCvSubst -> TyVar  -> Maybe Type
	-- See Note [Extending the TCvSubst]
lookupTyVar (TCvSubst _ tenv _) tv
  = ASSERT( isTyVar tv )
    lookupVarEnv tenv tv

lookupVar :: TCvSubst -> TyCoVar -> Maybe Type
lookupVar (TCvSubst _ tenv cenv) tv
  | isTyVar tv
  = lookupVarEnv tenv tv
  | Just co <- lookupVarEnv cenv tv
  = Just (CoercionTy co)
  | otherwise
  = Nothing

-- | Substitute within a 'Coercion'
substCo :: TCvSubst -> Coercion -> Coercion
substCo subst co | isEmptyTCvSubst subst = co
                 | otherwise             = subst_co subst co

-- | Substitute within several 'Coercion's
substCos :: TCvSubst -> [Coercion] -> [Coercion]
substCos subst cos | isEmptyTCvSubst subst = cos
                   | otherwise             = map (substCo subst) cos

-- | Substitute within a Coercion, with respect to given TyCoVar/Type pairs
substCoWith :: [TyCoVar] -> [Type] -> Coercion -> Coercion
substCoWith tvs tys = ASSERT( length tvs == length tys )
                      substCo (zipOpenTCvSubst tvs tys)

-- | Substitute within a Coercion, with respect to a given InScopeSet and
-- TyCoVar/Type pairs.
substCoWithIS :: InScopeSet -> [TyCoVar] -> [Type] -> Coercion -> Coercion
substCoWithIS in_scope tvs tys
  = let (tsubst, csubst) = zipTyCoEnv tvs tys
        in_scope' = in_scope `unionInScope` (mkInScopeSet (tyCoVarsOfTypes tys)) in
    subst_co (TCvSubst in_scope' tsubst csubst)

subst_co :: TCvSubst -> Coercion -> Coercion
subst_co subst co
  = go co
  where
    go_ty :: Type -> Type
    go_ty = subst_ty subst

    go :: Coercion -> Coercion
    go (Refl ty)             = mkReflCo $! go_ty ty
    go (TyConAppCo tc args)  = let args' = map go_arg args
                               in  args' `seqList` mkTyConAppCo tc args'
    go (AppCo co arg)        = mkAppCo (go co) $! go_arg arg
    go (ForAllCo cobndr co)
      = case substForAllCoBndr subst cobndr of { (subst', cobndr') ->
          (mkForAllCo $! cobndr') $! subst_co subst' co }
    go (CoVarCo cv)          = substCoVar subst cv
    go (AxiomInstCo con ind cos) = mkAxiomInstCo con ind $! map go_arg cos
    go (UnsafeCo ty1 ty2)    = (mkUnsafeCo $! go_ty ty1) $! go_ty ty2
    go (SymCo co)            = mkSymCo (go co)
    go (TransCo co1 co2)     = mkTransCo (go co1) (go co2)
    go (NthCo d co)          = mkNthCo d (go co)
    go (LRCo lr co)          = mkLRCo lr (go co)
    go (InstCo co arg)       = mkInstCo (go co) $! go_arg arg
    go (CoherenceCo co1 co2) = mkCoherenceCo (go co1) (go co2)
    go (KindCo co)           = mkKindCo (go co)

    go_arg :: CoercionArg -> CoercionArg
    go_arg (TyCoArg co)      = TyCoArg $! go co
    go_arg (CoCoArg co1 co2) = (CoCoArg $! go co1) $! go co2

substForAllCoBndr :: TCvSubst -> ForAllCoBndr -> (TCvSubst, ForAllCoBndr)
substForAllCoBndr = substForAllCoBndrCallback False substTy (const substCo)

-- See Note [Sym and ForAllCo]
substForAllCoBndrCallback :: Bool -- apply "sym" to the binder?
                          -> (TCvSubst -> Type -> Type)
                          -> (Bool -> TCvSubst -> Coercion -> Coercion)
                          -> TCvSubst -> ForAllCoBndr -> (TCvSubst, ForAllCoBndr)
substForAllCoBndrCallback _ sty _ subst (TyHomo tv)
  = case substTyVarBndrCallback sty subst tv of
      (subst', tv') -> (subst', TyHomo tv')
substForAllCoBndrCallback sym sty sco subst (TyHetero h tv1 tv2 cv)
  = case substTyVarBndrCallback     sty subst  tv1 of { (subst1, tv1') ->
    case substTyVarBndrCallback     sty subst1 tv2 of { (subst2, tv2') ->
    case substCoVarBndrCallback sym sty subst2 cv  of { (subst3, cv') ->
    let h' = sco sym subst h in -- just subst, not any of the others
    if isReflCo h'
    then let subst4 = extendTCvSubstList subst3
                        [tv2,                cv]
                        [mkOnlyTyVarTy tv1', CoercionTy $
                                             mkReflCo (tyVarKind tv1')] in
         (subst4, TyHomo tv1')
    else if sym
         then (subst3, (TyHetero $! h') tv2' tv1' cv')
         else (subst3, (TyHetero $! h') tv1' tv2' cv') }}}
substForAllCoBndrCallback _ sty _ subst (CoHomo cv)
  = case substCoVarBndrCallback False sty subst cv of
      (subst', cv') -> (subst', CoHomo cv')
substForAllCoBndrCallback sym sty sco subst (CoHetero h cv1 cv2)
  = case substCoVarBndrCallback False sty subst  cv1 of { (subst1, cv1') ->
    case substCoVarBndrCallback False sty subst1 cv2 of { (subst2, cv2') ->
    let h' = sco sym subst h in
    if isReflCo h'
    then let subst3 = extendTCvSubst subst2 cv2 (mkTyCoVarTy cv1') in
         (subst3, CoHomo cv1')
    else if sym
         then (subst2, (CoHetero $! h') cv2' cv1')
         else (subst2, (CoHetero $! h') cv1' cv2') }}

substCoVar :: TCvSubst -> CoVar -> Coercion
substCoVar (TCvSubst in_scope _ cenv) cv
  | Just co  <- lookupVarEnv cenv cv      = co
  | Just cv1 <- lookupInScope in_scope cv = ASSERT( isCoVar cv1 ) CoVarCo cv1
  | otherwise = WARN( True, ptext (sLit "substCoVar not in scope") <+> ppr cv $$ ppr in_scope)
                ASSERT( isCoVar cv ) CoVarCo cv

substCoVars :: TCvSubst -> [CoVar] -> [Coercion]
substCoVars subst cvs = map (substCoVar subst) cvs

lookupCoVar :: TCvSubst -> Var  -> Maybe Coercion
lookupCoVar (TCvSubst _ _ cenv) v = lookupVarEnv cenv v

substTyCoVarBndr :: TCvSubst -> TyCoVar -> (TCvSubst, TyCoVar)
substTyCoVarBndr subst v
  | isTyVar v = substTyVarBndr subst v
  | otherwise = substCoVarBndr subst v

substTyVarBndr :: TCvSubst -> TyVar -> (TCvSubst, TyVar)
substTyVarBndr = substTyVarBndrCallback substTy

substTyVarBndrCallback :: (TCvSubst -> Type -> Type)
                       -> TCvSubst -> TyVar -> (TCvSubst, TyVar)
substTyVarBndrCallback subst_fn subst@(TCvSubst in_scope tenv cenv) old_var
  = ASSERT2( _no_capture, ppr old_var $$ ppr subst ) 
    ASSERT( isTyVar old_var )
    (TCvSubst (in_scope `extendInScopeSet` new_var) new_env cenv, new_var)
  where
    new_env | no_change = delVarEnv tenv old_var
	    | otherwise = extendVarEnv tenv old_var (TyVarTy new_var)

    _no_capture = not (new_var `elemVarSet` tyCoVarsOfTypes (varEnvElts tenv))
    -- Assertion check that we are not capturing something in the substitution

    old_ki = tyVarKind old_var
    no_kind_change = isEmptyVarSet (tyCoVarsOfType old_ki) -- verify that kind is closed
    no_change = no_kind_change && (new_var == old_var)
	-- no_change means that the new_var is identical in
	-- all respects to the old_var (same unique, same kind)
	-- See Note [Extending the TCvSubst]
	--
	-- In that case we don't need to extend the substitution
	-- to map old to new.  But instead we must zap any 
	-- current substitution for the variable. For example:
	--	(\x.e) with id_subst = [x |-> e']
	-- Here we must simply zap the substitution for x

    new_var | no_kind_change = uniqAway in_scope old_var
            | otherwise = uniqAway in_scope $ updateTyVarKind (subst_fn subst) old_var
	-- The uniqAway part makes sure the new variable is not already in scope

substCoVarBndr :: TCvSubst -> CoVar -> (TCvSubst, CoVar)
substCoVarBndr = substCoVarBndrCallback False substTy

substCoVarBndrCallback :: Bool -- apply "sym" to the covar?
                       -> (TCvSubst -> Type -> Type)
                       -> TCvSubst -> CoVar -> (TCvSubst, CoVar)
substCoVarBndrCallback sym subst_fun subst@(TCvSubst in_scope tenv cenv) old_var
  = ASSERT( isCoVar old_var )
    (TCvSubst (in_scope `extendInScopeSet` new_var) tenv new_cenv, new_var)
  where
    -- When we substitute (co :: t1 ~ t2) we may get the identity (co :: t ~ t)
    -- In that case, mkCoVarCo will return a ReflCoercion, and
    -- we want to substitute that (not new_var) for old_var
    new_co    = mkCoVarCo new_var
    no_change = new_var == old_var && not (isReflCo new_co)

    new_cenv | no_change = delVarEnv cenv old_var
             | otherwise = extendVarEnv cenv old_var new_co

    new_var = uniqAway in_scope subst_old_var
    subst_old_var = mkCoVar (varName old_var) new_var_type
 
    (t1, t2) = coVarTypes old_var
    t1' = subst_fun subst t1
    t2' = subst_fun subst t2
    new_var_type = uncurry mkCoercionType (if sym then (t2', t1') else (t1', t2'))
		  -- It's important to do the substitution for coercions,
		  -- because they can have free type variables

cloneTyVarBndr :: TCvSubst -> TyVar -> Unique -> (TCvSubst, TyVar)
cloneTyVarBndr (TCvSubst in_scope tv_env cv_env) tv uniq
  | isTyVar tv
  = (TCvSubst (extendInScopeSet in_scope tv')
              (extendVarEnv tv_env tv (mkOnlyTyVarTy tv')) cv_env, tv')
  | otherwise
  = (TCvSubst (extendInScopeSet in_scope tv')
              tv_env (extendVarEnv cv_env tv (mkCoVarCo tv')), tv')
  where
    tv' = setVarUnique tv uniq	-- Simply set the unique; the kind
    	  	       	  	-- has no type variables to worry about
\end{code}

%************************************************************************
%*									*
                   Pretty-printing types

       Defined very early because of debug printing in assertions
%*                                                                      *
%************************************************************************

@pprType@ is the standard @Type@ printer; the overloaded @ppr@ function is
defined to use this.  @pprParendType@ is the same, except it puts
parens around the type, except for the atomic cases.  @pprParendType@
works just by setting the initial context precedence very high.

\begin{code}
data Prec = TopPrec 	-- No parens
	  | FunPrec 	-- Function args; no parens for tycon apps
	  | TyConPrec 	-- Tycon args; no parens for atomic
	  deriving( Eq, Ord )

maybeParen :: Prec -> Prec -> SDoc -> SDoc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise		   = parens pretty

------------------
pprType, pprParendType :: Type -> SDoc
pprType       ty = ppr_type TopPrec ty
pprParendType ty = ppr_type TyConPrec ty

pprTyLit :: TyLit -> SDoc
pprTyLit = ppr_tylit TopPrec

pprKind, pprParendKind :: Kind -> SDoc
pprKind       = pprType
pprParendKind = pprParendType

------------------
pprEqPred :: Pair Type -> SDoc
-- NB: Maybe move to Coercion? It's only called after coercionKind anyway. 
pprEqPred (Pair ty1 ty2) 
  = sep [ ppr_type FunPrec ty1
        , nest 2 (ptext (sLit "~#"))
        , ppr_type FunPrec ty2]
    -- Precedence looks like (->) so that we get
    --    Maybe a ~ Bool
    --    (a->a) ~ Bool
    -- Note parens on the latter!

------------
pprClassPred :: Class -> [Type] -> SDoc
pprClassPred = ppr_class_pred ppr_type

ppr_class_pred :: (Prec -> a -> SDoc) -> Class -> [a] -> SDoc
ppr_class_pred pp clas tys = pprTypeNameApp TopPrec pp (getName clas) tys

------------
pprTheta :: ThetaType -> SDoc
-- pprTheta [pred] = pprPred pred	 -- I'm in two minds about this
pprTheta theta  = parens (sep (punctuate comma (map (ppr_type TopPrec) theta)))

pprThetaArrowTy :: ThetaType -> SDoc
pprThetaArrowTy []      = empty
pprThetaArrowTy [pred]
      | noParenPred pred = ppr_type TopPrec pred <+> darrow
pprThetaArrowTy preds   = parens (fsep (punctuate comma (map (ppr_type TopPrec) preds)))
                            <+> darrow
    -- Notice 'fsep' here rather that 'sep', so that
    -- type contexts don't get displayed in a giant column
    -- Rather than
    --  instance (Eq a,
    --            Eq b,
    --            Eq c,
    --            Eq d,
    --            Eq e,
    --            Eq f,
    --            Eq g,
    --            Eq h,
    --            Eq i,
    --            Eq j,
    --            Eq k,
    --            Eq l) =>
    --           Eq (a, b, c, d, e, f, g, h, i, j, k, l)
    -- we get
    --
    --  instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h, Eq i,
    --            Eq j, Eq k, Eq l) =>
    --           Eq (a, b, c, d, e, f, g, h, i, j, k, l)

------------------
instance Outputable Type where
    ppr ty = pprType ty

instance Outputable TyLit where
   ppr = pprTyLit

------------------
	-- OK, here's the main printer

ppr_type :: Prec -> Type -> SDoc
ppr_type _ (TyVarTy tv)	      = ppr_tvar tv

ppr_type _ (TyConApp tc [LitTy (StrTyLit n),ty])
  | tc `hasKey` ipClassNameKey
  = char '?' <> ftext n <> ptext (sLit "::") <> ppr_type TopPrec ty

ppr_type p (TyConApp tc tys)  = pprTcApp p ppr_type tc tys

ppr_type p (LitTy l)          = ppr_tylit p l
ppr_type p ty@(ForAllTy {})   = ppr_forall_type p ty

ppr_type p (AppTy t1 t2) = maybeParen p TyConPrec $
			   pprType t1 <+> ppr_type TyConPrec t2

ppr_type p fun_ty@(FunTy ty1 ty2)
  | isPredTy ty1
  = ppr_forall_type p fun_ty
  | otherwise
  = pprArrowChain p (ppr_type FunPrec ty1 : ppr_fun_tail ty2)
  where
    -- We don't want to lose synonyms, so we mustn't use splitFunTys here.
    ppr_fun_tail (FunTy ty1 ty2)
      | not (isPredTy ty1) = ppr_type FunPrec ty1 : ppr_fun_tail ty2
    ppr_fun_tail other_ty = [ppr_type TopPrec other_ty]

ppr_type _ (CastTy ty co)
  = parens (ppr_type TopPrec ty <+> ptext (sLit "|>") <+> ppr co)

ppr_type _ (CoercionTy co)
  = parens (ppr co) -- TODO (RAE): do we need these parens?

ppr_forall_type :: Prec -> Type -> SDoc
ppr_forall_type p ty
  = maybeParen p FunPrec $ (ppr_sigma_type True ty)

ppr_tvar :: TyVar -> SDoc
ppr_tvar tv  -- Note [Infix type variables]
  = parenSymOcc (getOccName tv) (ppr tv)

ppr_tylit :: Prec -> TyLit -> SDoc
ppr_tylit _ tl =
  case tl of
    NumTyLit n -> integer n
    StrTyLit s -> text (show s)

-------------------
ppr_sigma_type :: Bool -> Type -> SDoc
-- Bool <=> Show the foralls
ppr_sigma_type show_foralls ty
  =  sep [ if show_foralls then pprForAll tvs else empty
        , pprThetaArrowTy ctxt
        , pprType tau ]
  where
    (tvs,  rho) = split1 [] ty
    (ctxt, tau) = split2 [] rho

    split1 tvs (ForAllTy tv ty) = split1 (tv:tvs) ty
    split1 tvs ty          = (reverse tvs, ty)
 
    split2 ps (ty1 `FunTy` ty2) | isPredTy ty1 = split2 (ty1:ps) ty2
    split2 ps ty                               = (reverse ps, ty)


pprSigmaType :: Type -> SDoc
pprSigmaType ty = ppr_sigma_type opt_PprStyle_Debug ty

pprForAll :: [TyCoVar] -> SDoc
pprForAll []  = empty
pprForAll tvs = ptext (sLit "forall") <+> pprTCvBndrs tvs <> dot

pprTCvBndrs :: [TyCoVar] -> SDoc
pprTCvBndrs tvs = sep (map pprTCvBndr tvs)

pprTCvBndr :: TyCoVar -> SDoc
pprTCvBndr tv 
  | isLiftedTypeKind kind = ppr_tvar tv
  | otherwise	          = parens (ppr_tvar tv <+> dcolon <+> pprKind kind)
	     where
	       kind = tyVarKind tv

-----------------
instance Outputable Coercion where -- defined here to avoid orphans
  ppr = pprCo
instance Outputable ForAllCoBndr where
  ppr = pprCoBndr
instance Outputable CoercionArg where
  ppr = pprCoArg
instance Outputable LeftOrRight where
  ppr CLeft    = ptext (sLit "Left")
  ppr CRight   = ptext (sLit "Right")

\end{code}

Note [Infix type variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
With TypeOperators you can say

   f :: (a ~> b) -> b

and the (~>) is considered a type variable.  However, the type
pretty-printer in this module will just see (a ~> b) as

   App (App (TyVarTy "~>") (TyVarTy "a")) (TyVarTy "b")

So it'll print the type in prefix form.  To avoid confusion we must
remember to parenthesise the operator, thus

   (~>) a b -> b

See Trac #2766.

\begin{code}
pprTcApp :: Prec -> (Prec -> a -> SDoc) -> TyCon -> [a] -> SDoc
pprTcApp _ pp tc [ty]
  | tc `hasKey` listTyConKey = pprPromotionQuote tc <> brackets   (pp TopPrec ty)
  | tc `hasKey` parrTyConKey = pprPromotionQuote tc <> paBrackets (pp TopPrec ty)

pprTcApp p pp tc tys
  | isTupleTyCon tc && tyConArity tc == length tys
  = pprPromotionQuote tc <>
    tupleParens (tupleTyConSort tc) (sep (punctuate comma (map (pp TopPrec) tys)))

  | Just dc <- isPromotedDataCon_maybe tc
  , let dc_tc = dataConTyCon dc
  , isTupleTyCon dc_tc 
  , let arity = tyConArity dc_tc    -- E.g. 3 for (,,) k1 k2 k3 t1 t2 t3
        ty_args = drop arity tys    -- Drop the kind args
  , ty_args `lengthIs` arity        -- Result is saturated
  = pprPromotionQuote tc <>
    (tupleParens (tupleTyConSort dc_tc) $
     sep (punctuate comma (map (pp TopPrec) ty_args)))

  | not opt_PprStyle_Debug
  , getUnique tc == eqTyConKey || getUnique tc == eqPrimTyConKey
                           -- We need to special case the type equality TyCons because
  , [_, _, ty1,ty2] <- tys    -- with kind polymorphism it has 4 args, so won't get printed infix
                           -- With -dppr-debug switch this off so we can see the kind
  = pprInfixApp p pp (ppr tc) ty1 ty2

  | otherwise
  = ppr_type_name_app p pp (getName tc) (ppr tc) tys

----------------
pprTypeApp :: TyCon -> [Type] -> SDoc
pprTypeApp tc tys 
  = ppr_type_name_app TopPrec ppr_type (getName tc) (ppr tc) tys
        -- We have to to use ppr on the TyCon (not its name)
        -- so that we get promotion quotes in the right place

pprTypeNameApp :: Prec -> (Prec -> a -> SDoc) -> Name -> [a] -> SDoc
-- Used for classes and coercions as well as types; that's why it's separate from pprTcApp
pprTypeNameApp p pp name tys
  = ppr_type_name_app p pp name (ppr name) tys

ppr_type_name_app :: Prec -> (Prec -> a -> SDoc) -> Name -> SDoc -> [a] -> SDoc
ppr_type_name_app p pp nm_tc pp_tc tys
  | not (isSymOcc (nameOccName nm_tc))
  = pprPrefixApp p pp_tc (map (pp TyConPrec) tys)
  | [ty1,ty2] <- tys  -- Infix, two arguments;
                      -- we know nothing of precedence though
  = pprInfixApp p pp pp_tc ty1 ty2

  |  nm_tc `hasKey` liftedTypeKindTyConKey 
  || nm_tc `hasKey` unliftedTypeKindTyConKey 
  = ASSERT( null tys ) pp_tc   -- Do not wrap *, # in parens

  | otherwise
  = pprPrefixApp p (parens pp_tc) (map (pp TyConPrec) tys)

----------------
pprInfixApp :: Prec -> (Prec -> a -> SDoc) -> SDoc -> a -> a -> SDoc
pprInfixApp p pp pp_tc ty1 ty2
  = maybeParen p FunPrec $
    sep [pp FunPrec ty1, pprInfixVar True pp_tc <+> pp FunPrec ty2]

pprPrefixApp :: Prec -> SDoc -> [SDoc] -> SDoc
pprPrefixApp p pp_fun pp_tys 
  | null pp_tys = pp_fun
  | otherwise   = maybeParen p TyConPrec $
                  hang pp_fun 2 (sep pp_tys)
----------------
pprArrowChain :: Prec -> [SDoc] -> SDoc
-- pprArrowChain p [a,b,c]  generates   a -> b -> c
pprArrowChain _ []         = empty
pprArrowChain p (arg:args) = maybeParen p FunPrec $
                             sep [arg, sep (map (arrow <+>) args)]
\end{code}

%************************************************************************
%*									*
\subsection{TidyType}
%*									*
%************************************************************************

\begin{code}

-- | This tidies up a type for printing in an error message, or in
-- an interface file.
-- 
-- It doesn't change the uniques at all, just the print names.
tidyTyCoVarBndrs :: TidyEnv -> [TyCoVar] -> (TidyEnv, [TyCoVar])
tidyTyCoVarBndrs env tvs = mapAccumL tidyTyCoVarBndr env tvs

tidyTyCoVarBndr :: TidyEnv -> TyCoVar -> (TidyEnv, TyCoVar)
tidyTyCoVarBndr tidy_env@(occ_env, subst) tyvar
  = case tidyOccName occ_env occ1 of
      (tidy', occ') -> ((tidy', subst'), tyvar')
	where
          subst' = extendVarEnv subst tyvar tyvar'
          tyvar' = setTyVarKind (setTyVarName tyvar name') kind'
          name'  = tidyNameOcc name occ'
          kind'  = tidyKind tidy_env (tyVarKind tyvar)
  where
    name = tyVarName tyvar
    occ  = getOccName name
    -- System Names are for unification variables;
    -- when we tidy them we give them a trailing "0" (or 1 etc)
    -- so that they don't take precedence for the un-modified name
    occ1 | isSystemName name = if isTyVar tyvar
                               then mkTyVarOcc (occNameString occ ++ "0")
                               else mkVarOcc   (occNameString occ ++ "0")
         | otherwise         = occ


---------------
tidyFreeTyCoVars :: TidyEnv -> TyCoVarSet -> TidyEnv
-- ^ Add the free 'TyVar's to the env in tidy form,
-- so that we can tidy the type they are free in
tidyFreeTyCoVars (full_occ_env, var_env) tyvars 
  = fst (tidyOpenTyCoVars (full_occ_env, var_env) (varSetElems tyvars))

        ---------------
tidyOpenTyCoVars :: TidyEnv -> [TyCoVar] -> (TidyEnv, [TyCoVar])
tidyOpenTyCoVars env tyvars = mapAccumL tidyOpenTyCoVar env tyvars

---------------
tidyOpenTyCoVar :: TidyEnv -> TyCoVar -> (TidyEnv, TyCoVar)
-- ^ Treat a new 'TyCoVar' as a binder, and give it a fresh tidy name
-- using the environment if one has not already been allocated. See
-- also 'tidyTyCoVarBndr'
tidyOpenTyCoVar env@(_, subst) tyvar
  = case lookupVarEnv subst tyvar of
	Just tyvar' -> (env, tyvar')              -- Already substituted
	Nothing	    -> tidyTyCoVarBndr env tyvar  -- Treat it as a binder

---------------
tidyTyVarOcc :: TidyEnv -> TyVar -> TyVar
tidyTyVarOcc (_, subst) tv
  = case lookupVarEnv subst tv of
	Nothing  -> tv
	Just tv' -> tv'

---------------
tidyTypes :: TidyEnv -> [Type] -> [Type]
tidyTypes env tys = map (tidyType env) tys

---------------
tidyType :: TidyEnv -> Type -> Type
tidyType _   (LitTy n)            = LitTy n
tidyType env (TyVarTy tv)	  = TyVarTy (tidyTyVarOcc env tv)
tidyType env (TyConApp tycon tys) = let args = tidyTypes env tys
 		                    in args `seqList` TyConApp tycon args
tidyType env (AppTy fun arg)	  = (AppTy $! (tidyType env fun)) $! (tidyType env arg)
tidyType env (FunTy fun arg)	  = (FunTy $! (tidyType env fun)) $! (tidyType env arg)
tidyType env (ForAllTy tv ty)	  = ForAllTy tvp $! (tidyType envp ty)
			          where
			            (envp, tvp) = tidyTyCoVarBndr env tv
tidyType env (CastTy ty co)       = (CastTy $! tidyType env ty) $! (tidyCo env co)
tidyType env (CoercionTy co)      = CoercionTy $! (tidyCo env co)

---------------
-- | Grabs the free type variables, tidies them
-- and then uses 'tidyType' to work over the type itself
tidyOpenType :: TidyEnv -> Type -> (TidyEnv, Type)
tidyOpenType env ty
  = (env', tidyType (trimmed_occ_env, var_env) ty)
  where
    (env'@(_, var_env), tvs') = tidyOpenTyCoVars env (varSetElems (tyCoVarsOfType ty))
    trimmed_occ_env = initTidyOccEnv (map getOccName tvs')
      -- The idea here was that we restrict the new TidyEnv to the 
      -- _free_ vars of the type, so that we don't gratuitously rename
      -- the _bound_ variables of the type.

---------------
tidyOpenTypes :: TidyEnv -> [Type] -> (TidyEnv, [Type])
tidyOpenTypes env tys = mapAccumL tidyOpenType env tys

---------------
-- | Calls 'tidyType' on a top-level type (i.e. with an empty tidying environment)
tidyTopType :: Type -> Type
tidyTopType ty = tidyType emptyTidyEnv ty

---------------
tidyOpenKind :: TidyEnv -> Kind -> (TidyEnv, Kind)
tidyOpenKind = tidyOpenType

tidyKind :: TidyEnv -> Kind -> Kind
tidyKind = tidyType

----------------
tidyCo :: TidyEnv -> Coercion -> Coercion
tidyCo env@(_, subst) co
  = go co
  where
    go (Refl ty)             = Refl (tidyType env ty)
    go (TyConAppCo tc cos)   = let args = map go_arg cos
                               in args `seqList` TyConAppCo tc args
    go (AppCo co1 co2)       = (AppCo $! go co1) $! go_arg co2
    go (ForAllCo cobndr co)  = ForAllCo cobndrp $! (tidyCo envp co)
                               where
                                 (envp, cobndrp) = go_bndr cobndr
    go (CoVarCo cv)          = case lookupVarEnv subst cv of
                                 Nothing  -> CoVarCo cv
                                 Just cv' -> CoVarCo cv'
    go (AxiomInstCo con ind cos) = let args = map go_arg cos
                               in  args `seqList` AxiomInstCo con ind args
    go (UnsafeCo ty1 ty2)    = (UnsafeCo $! tidyType env ty1) $! tidyType env ty2
    go (SymCo co)            = SymCo $! go co
    go (TransCo co1 co2)     = (TransCo $! go co1) $! go co2
    go (NthCo d co)          = NthCo d $! go co
    go (LRCo lr co)          = LRCo lr $! go co
    go (InstCo co ty)        = (InstCo $! go co) $! go_arg ty
    go (CoherenceCo co1 co2) = (CoherenceCo $! go co1) $! go co2
    go (KindCo co)           = KindCo $! go co

    go_arg (TyCoArg co)      = TyCoArg $! go co
    go_arg (CoCoArg co1 co2) = (CoCoArg $! go co1) $! go co2

    go_bndr cobndr
      | Just v <- getHomoVar_maybe cobndr
      = let (envp, vp) = tidyTyCoVarBndr env v in
        (envp, mkHomoCoBndr vp)
      | TyHetero h tv1 tv2 cv <- cobndr
      = let h' = go h
            (envp, [tv1', tv2', cv']) = tidyTyCoVarBndrs env [tv1, tv2, cv] in
        (envp, mkTyHeteroCoBndr h' tv1' tv2' cv')
      | CoHetero h cv1 cv2 <- cobndr
      = let h' = go h
            (envp, [cv1', cv2']) = tidyTyCoVarBndrs env [cv1, cv2] in
        (envp, mkCoHeteroCoBndr h' cv1' cv2')

      | otherwise
      = pprPanic "tidyCo#go_bndr" (ppr cobndr)

tidyCos :: TidyEnv -> [Coercion] -> [Coercion]
tidyCos env = map (tidyCo env)

\end{code}
