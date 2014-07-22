%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1998
%
\section[DataCon]{@DataCon@: Data Constructors}

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://ghc.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module DataCon (
        -- * Main data types
	DataCon, DataConRep(..), HsBang(..), StrictnessMark(..),
	ConTag, EqSpec,
	
	-- ** Type construction
	mkDataCon, fIRST_TAG,
	
	-- ** Type deconstruction
	dataConRepType, dataConSig, dataConFullSig,
	dataConName, dataConIdentity, dataConTag, dataConTyCon, 
        dataConOrigTyCon, dataConUserType,
	dataConUnivTyVars, dataConExTyCoVars,
	dataConTheta,
	dataConStupidTheta,  
	dataConInstArgTys, dataConOrigArgTys, dataConOrigResTy,
	dataConInstOrigArgTys, dataConRepArgTys, 
	dataConFieldLabels, dataConFieldType,
	dataConStrictMarks, 
	dataConSourceArity, dataConRepArity, dataConRepRepArity,
	dataConIsInfix,
	dataConWorkId, dataConWrapId, dataConWrapId_maybe, dataConImplicitIds,
	dataConRepStrictness, dataConRepBangs, dataConBoxer,

	splitDataProductType_maybe,

        tyConsOfTyCon,

	-- ** Predicates on DataCons
	isNullarySrcDataCon, isNullaryRepDataCon, isTupleDataCon, isUnboxedTupleCon,
	isVanillaDataCon, classDataCon, dataConCannotMatch,
        isBanged, isMarkedStrict, eqHsBang,

        -- ** Promotion related functions
        promoteDataCon
    ) where

#include "HsVersions.h"

import {-# SOURCE #-} MkId( DataConBoxer )
import Type
import Coercion
import Unify
import TyCon
import Class
import Name
import Var
import Outputable
import Unique
import ListSetOps
import Util
import BasicTypes
import FastString
import Module
import NameEnv

import qualified Data.Data as Data
import qualified Data.Typeable
import Data.Char
import Data.Word
\end{code}


Data constructor representation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider the following Haskell data type declaration

	data T = T !Int ![Int]

Using the strictness annotations, GHC will represent this as

	data T = T Int# [Int]

That is, the Int has been unboxed.  Furthermore, the Haskell source construction

	T e1 e2

is translated to

	case e1 of { I# x -> 
	case e2 of { r ->
	T x r }}

That is, the first argument is unboxed, and the second is evaluated.  Finally,
pattern matching is translated too:

	case e of { T a b -> ... }

becomes

	case e of { T a' b -> let a = I# a' in ... }

To keep ourselves sane, we name the different versions of the data constructor
differently, as follows.


Note [Data Constructor Naming]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Each data constructor C has two, and possibly up to four, Names associated with it:

		   OccName   Name space	  Name of   Notes
 ---------------------------------------------------------------------------
 The "data con itself" 	 C     DataName	  DataCon   In dom( GlobalRdrEnv )
 The "worker data con"	 C     VarName	  Id        The worker
 The "wrapper data con"	 $WC   VarName	  Id        The wrapper
 The "newtype coercion"  :CoT  TcClsName  TyCon
 
EVERY data constructor (incl for newtypes) has the former two (the
data con itself, and its worker.  But only some data constructors have a
wrapper (see Note [The need for a wrapper]).

Each of these three has a distinct Unique.  The "data con itself" name
appears in the output of the renamer, and names the Haskell-source
data constructor.  The type checker translates it into either the wrapper Id
(if it exists) or worker Id (otherwise).

The data con has one or two Ids associated with it:

The "worker Id", is the actual data constructor.
* Every data constructor (newtype or data type) has a worker

* The worker is very like a primop, in that it has no binding.

* For a *data* type, the worker *is* the data constructor;
  it has no unfolding

* For a *newtype*, the worker has a compulsory unfolding which 
  does a cast, e.g.
	newtype T = MkT Int
	The worker for MkT has unfolding
		\\(x:Int). x `cast` sym CoT
  Here CoT is the type constructor, witnessing the FC axiom
	axiom CoT : T = Int

The "wrapper Id", \$WC, goes as follows

* Its type is exactly what it looks like in the source program. 

* It is an ordinary function, and it gets a top-level binding 
  like any other function.

* The wrapper Id isn't generated for a data type if there is
  nothing for the wrapper to do.  That is, if its defn would be
	\$wC = C

Note [The need for a wrapper]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Why might the wrapper have anything to do?  Two reasons:

* Unboxing strict fields (with -funbox-strict-fields)
	data T = MkT !(Int,Int)
	\$wMkT :: (Int,Int) -> T
	\$wMkT (x,y) = MkT x y
  Notice that the worker has two fields where the wapper has 
  just one.  That is, the worker has type
		MkT :: Int -> Int -> T

* Equality constraints for GADTs
	data T a where { MkT :: a -> T [a] }

  The worker gets a type with explicit equality
  constraints, thus:
	MkT :: forall a b. (a=[b]) => b -> T a

  The wrapper has the programmer-specified type:
	\$wMkT :: a -> T [a]
	\$wMkT a x = MkT [a] a [a] x
  The third argument is a coerion
	[a] :: [a]~[a]

INVARIANT: the dictionary constructor for a class
	   never has a wrapper.


A note about the stupid context
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Data types can have a context:
	
	data (Eq a, Ord b) => T a b = T1 a b | T2 a

and that makes the constructors have a context too
(notice that T2's context is "thinned"):

	T1 :: (Eq a, Ord b) => a -> b -> T a b
	T2 :: (Eq a) => a -> T a b

Furthermore, this context pops up when pattern matching
(though GHC hasn't implemented this, but it is in H98, and
I've fixed GHC so that it now does):

	f (T2 x) = x
gets inferred type
	f :: Eq a => T a b -> a

I say the context is "stupid" because the dictionaries passed
are immediately discarded -- they do nothing and have no benefit.
It's a flaw in the language.

	Up to now [March 2002] I have put this stupid context into the
	type of the "wrapper" constructors functions, T1 and T2, but
	that turned out to be jolly inconvenient for generics, and
	record update, and other functions that build values of type T
	(because they don't have suitable dictionaries available).

	So now I've taken the stupid context out.  I simply deal with
	it separately in the type checker on occurrences of a
	constructor, either in an expression or in a pattern.

	[May 2003: actually I think this decision could evasily be
	reversed now, and probably should be.  Generics could be
	disabled for types with a stupid context; record updates now
	(H98) needs the context too; etc.  It's an unforced change, so
	I'm leaving it for now --- but it does seem odd that the
	wrapper doesn't include the stupid context.]

[July 04] With the advent of generalised data types, it's less obvious
what the "stupid context" is.  Consider
	C :: forall a. Ord a => a -> a -> T (Foo a)
Does the C constructor in Core contain the Ord dictionary?  Yes, it must:

	f :: T b -> Ordering
	f = /\b. \x:T b. 
	    case x of
		C a (d:Ord a) (p:a) (q:a) -> compare d p q

Note that (Foo a) might not be an instance of Ord.

%************************************************************************
%*									*
\subsection{Data constructors}
%*									*
%************************************************************************

\begin{code}
-- | A data constructor
data DataCon
  = MkData {
	dcName    :: Name,	-- This is the name of the *source data con*
				-- (see "Note [Data Constructor Naming]" above)
	dcUnique :: Unique, 	-- Cached from Name
	dcTag    :: ConTag,     -- ^ Tag, used for ordering 'DataCon's

	-- Running example:
	--
	-- 	*** As declared by the user
	--  data T (a :: k) where
	--    MkT :: forall (x :: Proxy a) y. (Ord y) => Proxy x -> y -> T [y]
        --
	-- 	*** As represented internally
	--  data T :: pi k. k -> * where
	--    MkT :: forall k (a :: k).
        --           forall (c :: k ~# *) (x :: Proxy * (a |> c)) y.
        --           ((a|>c)~[y],Ord y) => Proxy (Proxy * (a|>c)) x -> y
        --                              -> T k a
	--
        -- There are many details to notice here!
        --
        -- The first is that the universally-quantified parameters to MkT
        -- must match up with the parameters to T. Thus, even though the
        -- definition of MkT constrains `a` to be `[y]`, of kind *, we still
        -- have (a :: k) in the internal type of MkT.
        --
        -- The definition of MkT forces two GADT equalities: it forces k
        -- to be *, and it forces `a` to be [y]. These two equalities are
        -- handled in different ways, however: the first is a dependent
        -- equality (it is referenced later on in the type), whereas the
        -- latter is a non-dependent equality. Because (k ~ *) is needed
        -- to type-check the rest of the type, it is named and included as
        -- an *existential* parameter to MkT. This is the parameter `c`.
        -- We also see that, given that we really want to consider k to be
        -- * in this type, every use of `a` requires a cast by `c`, to get
        -- its kind correct. We don't just declare `a` to be of kind * because
        -- that would mis-align the datacon parameters with the tycon
        -- parameters.
        --
        -- The GADT equality ((a|>c)~[y]) appears as an ordinary constraint.
        -- Note that (~) is *homo*geneous, meaning that the kinds of the two
        -- types being equated must already be the same. This works out with
        -- the `|> c` cast -- both (a|>c) and [y] are of kind *.
        --
        -- Due to this differing treatment of the GADT equalities
        -- (implemented in rejigConRes in TcTyClsDecls), dependent equalities
        -- are *not* deferred with -fdefer-type-errors.
        
	-- Five fields express the type of the constructor, in pieces
	-- e.g.
	--
	--	dcUnivTyVars  = [k,a]
	--	dcExTyCoVars  = [c,x,y]
	--	dcTheta       = [(a |> c) ~ [y], Ord y]	
	--	dcOrigArgTys  = [Proxy x, y]
	--	dcRepTyCon    = T

	dcVanilla :: Bool,	-- True <=> This is a vanilla Haskell 98 data constructor
				--	    Its type is of form
				--	        forall a1..an . t1 -> ... tm -> T a1..an
				-- 	    No existentials, no coercions, nothing.
				-- That is: dcExTyCoVars = dcTheta = []
		-- NB 1: newtypes always have a vanilla data con
		-- NB 2: a vanilla constructor can still be declared in GADT-style 
		--	 syntax, provided its type looks like the above.
		--       The declaration format is held in the TyCon (algTcGadtSyntax)

	dcStupidTheta :: ThetaType,	-- The context of the data type declaration 
					--	data Eq a => T a = ...
					-- or, rather, a "thinned" version thereof
		-- "Thinned", because the Report says
		-- to eliminate any constraints that don't mention
		-- tyvars free in the arg types for this constructor
		--
		-- INVARIANT: the free tyvars of dcStupidTheta are a subset of dcUnivTyVars
		-- Reason: dcStupidTeta is gotten by thinning the stupid theta from the tycon
		-- 
		-- "Stupid", because the dictionaries aren't used for anything.  
		-- Indeed, [as of March 02] they are no longer in the type of 
		-- the wrapper Id, because that makes it harder to use the wrap-id 
		-- to rebuild values after record selection or in generics.

        dcUnivTyVars :: [TyVar],
           -- NB: These are the "rejigged" universally-quantified tyvars.
           -- They will be the tyConTyVars for non-GADT declarations, or
           -- other tyvars for GADT declarations.
           -- length (dcUnivTyVars) == length (tyConTyVars)
           -- But, the actual vars might be different if GADT syntax named
           -- them differently.

           -- This list includes tyvars that are *not* mentioned in the
           -- source in the case of a GADT-constrained tyvar.
         
        dcExTyCoVars     :: [TyCoVar],
           -- Existential type and coercion variables, including dependent
           -- GADT equalities.

        dcGADTEqualities :: ThetaType,
           -- The non-dependent GADT equalities derived from rejigging.
        
        dcOrigTheta      :: ThetaType,
           -- Original, user-specified theta. Note that GADT-like equalities
           -- specified by the user might appear here.
        
        dcOrigArgTys     :: [Type],
           -- Original, user-specified list of arguments, before any
           -- flattening.
        
        dcOrigResTy      :: Type,
           -- Original, user-specified return type. For a non-GADT constructor,
           -- this is just the datacon's tycon applied to its univ tyvars.

		-- NB: for a data instance, the original user result type may 
		-- differ from the DataCon's representation TyCon.  Example
		--	data instance T [a] where MkT :: a -> T [a]
		-- The OrigResTy is T [a], but the dcRepTyCon might be :T123

	-- Now the strictness annotations and field labels of the constructor
        -- See Note [Bangs on data constructor arguments]
	dcArgBangs :: [HsBang],
		-- Strictness annotations as decided by the compiler.  
		-- Matches 1-1 with the dcOrigArgTys

	dcFields  :: [FieldLabel],
		-- Field labels for this constructor, in the
		-- same order as the dcOrigArgTys; 
		-- length = 0 (if not a record) or dataConSourceArity.

	-- The curried worker function that corresponds to the constructor:
	-- It doesn't have an unfolding; the code generator saturates these Ids
	-- and allocates a real constructor when it finds one.
	dcWorkId :: Id,

	-- Constructor representation
        dcRep      :: DataConRep,

        -- Cached
          -- dcRepArity == length dataConRepArgTys + count isId dcExTyCoVars
        dcRepArity    :: Arity,
          -- dcSourceArity == length dcOrigArgTys
        dcSourceArity :: Arity,

	-- Result type of constructor is T t1..tn
	dcRepTyCon  :: TyCon,		-- Result tycon, T

	dcRepType   :: Type,	-- Type of the constructor
				-- 	forall a x y. (a~(x,y), x~y, Ord x) =>
                                --        x -> y -> T a
				-- (this is *not* of the constructor wrapper Id:
				--  see Note [Data con representation] below)
	-- Notice that the existential type parameters come *second*.  
	-- Reason: in a case expression we may find:
	--	case (e :: T t) of
        --        MkT x y co1 co2 (d:Ord x) (v:r) (w:F s) -> ...
	-- It's convenient to apply the rep-type of MkT to 't', to get
	--	forall x y. (t~(x,y), x~y, Ord x) => x -> y -> T t
	-- and use that to check the pattern.  Mind you, this is really only
	-- used in CoreLint.


	dcInfix :: Bool,	-- True <=> declared infix
				-- Used for Template Haskell and 'deriving' only
				-- The actual fixity is stored elsewhere

        dcPromoted :: TyCon    -- The promoted TyCon
                               -- See Note [Promoted data constructors] in TyCon
  }
  deriving Data.Typeable.Typeable

data DataConRep 
  = NoDataConRep              -- No wrapper

  | DCR { dcr_wrap_id :: Id   -- Takes src args, unboxes/flattens, 
                              -- and constructs the representation

        , dcr_boxer   :: DataConBoxer

        , dcr_arg_tys  :: [Type]  -- Final, representation argument types, 
                                  -- after unboxing and flattening,
                                  -- including any constraints
               -- The dcr_arg_tys use the same variables as the dcOrigArgTys.

        , dcr_stricts :: [StrictnessMark]  -- 1-1 with dcr_arg_tys
		-- See also Note [Data-con worker strictness] in MkId.lhs

        , dcr_bangs :: [HsBang]  -- The actual decisions made (including failures)
                                 -- 1-1 with orig_arg_tys
                                 -- See Note [Bangs on data constructor arguments]

    }
-- Algebraic data types always have a worker, and
-- may or may not have a wrapper, depending on whether
-- the wrapper does anything.  
--
-- Data types have a worker with no unfolding
-- Newtypes just have a worker, which has a compulsory unfolding (just a cast)

-- _Neither_ the worker _nor_ the wrapper take the dcStupidTheta dicts as arguments

-- The wrapper (if it exists) has type dcOrigType
-- The worker takes dataConRepArgTys as its arguments
-- If the worker is absent, dataConRepArgTys is the same as dcOrigArgTys

-- The 'NoDataConRep' case is important
-- Not only is this efficient,
-- but it also ensures that the wrapper is replaced
-- by the worker (because it *is* the worker)
-- even when there are no args. E.g. in
-- 		f (:) x
-- the (:) *is* the worker.
-- This is really important in rule matching,
-- (We could match on the wrappers,
-- but that makes it less likely that rules will match
-- when we bring bits of unfoldings together.)

-------------------------
-- HsBang describes what the *programmer* wrote
-- This info is retained in the DataCon.dcStrictMarks field
data HsBang 
  = HsUserBang   -- The user's source-code request
       (Maybe Bool)       -- Just True    {-# UNPACK #-}
                          -- Just False   {-# NOUNPACK #-}
                          -- Nothing      no pragma
       Bool               -- True <=> '!' specified

  | HsNoBang	          -- Lazy field
                          -- HsUserBang Nothing False means the same as HsNoBang

  | HsUnpack              -- Definite commitment: this field is strict and unboxed
       (Maybe Coercion)   --    co :: arg-ty ~ product-ty

  | HsStrict              -- Definite commitment: this field is strict but not unboxed
  deriving (Data.Data, Data.Typeable)

-------------------------
-- StrictnessMark is internal only, used to indicate strictness 
-- of the DataCon *worker* fields
data StrictnessMark = MarkedStrict | NotMarkedStrict

\end{code}

Note [Data con representation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The dcRepType field contains the type of the representation of a contructor
This may differ from the type of the contructor *Id* (built
by MkId.mkDataConId) for two reasons:
	a) the constructor Id may be overloaded, but the dictionary isn't stored
	   e.g.    data Eq a => T a = MkT a a

	b) the constructor may store an unboxed version of a strict field.

Here's an example illustrating both:
	data Ord a => T a = MkT Int! a
Here
	T :: Ord a => Int -> a -> T a
but the rep type is
	Trep :: Int# -> a -> T a
Actually, the unboxed part isn't implemented yet!

Note [Bangs on data constructor arguments]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
  data T = MkT !Int {-# UNPACK #-} !Int Bool
Its dcArgBangs field records the *users* specifications, in this case
    [ HsUserBang Nothing True
    , HsUserBang (Just True) True
    , HsNoBang]
See the declaration of HsBang in BasicTypes

The dcr_bangs field of the dcRep field records the *actual, decided*
representation of the data constructor.  Without -O this might be
    [HsStrict, HsStrict, HsNoBang]
With -O it might be
    [HsStrict, HsUnpack, HsNoBang]
With -funbox-small-strict-fields it might be
    [HsUnpack, HsUnpack, HsNoBang]

For imported data types, the dcArgBangs field is just the same as the
dcr_bangs field; we don't know what the user originally said.


%************************************************************************
%*									*
\subsection{Instances}
%*									*
%************************************************************************

\begin{code}
instance Eq DataCon where
    a == b = getUnique a == getUnique b
    a /= b = getUnique a /= getUnique b

instance Ord DataCon where
    a <= b = getUnique a <= getUnique b
    a <	 b = getUnique a <  getUnique b
    a >= b = getUnique a >= getUnique b
    a >	 b = getUnique a > getUnique b
    compare a b = getUnique a `compare` getUnique b

instance Uniquable DataCon where
    getUnique = dcUnique

instance NamedThing DataCon where
    getName = dcName

instance Outputable DataCon where
    ppr con = ppr (dataConName con)

instance OutputableBndr DataCon where
    pprInfixOcc con = pprInfixName (dataConName con)
    pprPrefixOcc con = pprPrefixName (dataConName con)

instance Data.Data DataCon where
    -- don't traverse?
    toConstr _   = abstractConstr "DataCon"
    gunfold _ _  = error "gunfold"
    dataTypeOf _ = mkNoRepType "DataCon"

instance Outputable HsBang where
    ppr HsNoBang               = empty
    ppr (HsUserBang prag bang) = pp_unpk prag <+> ppWhen bang (char '!')
    ppr (HsUnpack Nothing)     = ptext (sLit "Unpk")
    ppr (HsUnpack (Just co))   = ptext (sLit "Unpk") <> parens (ppr co)
    ppr HsStrict               = ptext (sLit "SrictNotUnpacked")

pp_unpk :: Maybe Bool -> SDoc
pp_unpk Nothing      = empty
pp_unpk (Just True)  = ptext (sLit "{-# UNPACK #-}")
pp_unpk (Just False) = ptext (sLit "{-# NOUNPACK #-}")

instance Outputable StrictnessMark where
  ppr MarkedStrict     = ptext (sLit "!")
  ppr NotMarkedStrict  = empty


eqHsBang :: HsBang -> HsBang -> Bool
eqHsBang HsNoBang             HsNoBang             = True
eqHsBang HsStrict             HsStrict             = True
eqHsBang (HsUserBang u1 b1)   (HsUserBang u2 b2)   = u1==u2 && b1==b2
eqHsBang (HsUnpack Nothing)   (HsUnpack Nothing)   = True
eqHsBang (HsUnpack (Just c1)) (HsUnpack (Just c2)) = eqType (coercionType c1) (coercionType c2)
eqHsBang _ _ = False

isBanged :: HsBang -> Bool
isBanged HsNoBang                  = False
isBanged (HsUserBang Nothing bang) = bang
isBanged _                         = True

isMarkedStrict :: StrictnessMark -> Bool
isMarkedStrict NotMarkedStrict = False
isMarkedStrict _               = True   -- All others are strict
\end{code}


%************************************************************************
%*									*
\subsection{Construction}
%*									*
%************************************************************************

\begin{code}
-- | Build a new data constructor
mkDataCon :: Name 
	  -> Bool	        -- ^ Is the constructor declared infix?
	  -> [HsBang]           -- ^ Strictness annotations written in the source file
	  -> [FieldLabel]       -- ^ Field labels for the constructor, if it is a record, 
				--   otherwise empty
          -> [TyVar]            -- ^ Universal tyvars
          -> [TyVar]            -- ^ Existential type and coercion vars
          -> ThetaType          -- ^ derived GADT equalities
          -> ThetaType          -- ^ Other, user-specified constraints
          -> [Type]             -- ^ User-specified argument types
          -> Type               -- ^ User-specified result type
	  -> TyCon              -- ^ Representation type constructor
	  -> ThetaType          -- ^ The "stupid theta", context of the data declaration 
				--   e.g. @data Eq a => T a ...@
          -> Id                 -- ^ Worker Id
	  -> DataConRep         -- ^ Representation
	  -> DataCon
  -- Can get the tag from the TyCon

mkDataCon name declared_infix
	  arg_stricts	-- Must match orig_arg_tys 1-1
	  fields
	  univ_tvs ex_tvs gadt_theta orig_theta orig_arg_tys orig_res_ty
          rep_tycon
	  stupid_theta work_id rep
-- Warning: mkDataCon is not a good place to check invariants. 
-- If the programmer writes the wrong result type in the decl, thus:
--	data T a where { MkT :: S }
-- then it's possible that the univ_tvs may hit an assertion failure
-- if you pull on univ_tvs.  This case is checked by checkValidDataCon,
-- so the error is detected properly... it's just that asaertions here
-- are a little dodgy.

  = con
  where
    is_vanilla = null ex_tvs && null gadt_theta && null orig_theta
    con = MkData {dcName = name, dcUnique = nameUnique name, dcTag = tag, 
		  dcVanilla = is_vanilla, 
		  dcStupidTheta = stupid_theta,
                  dcUnivTyVars = univ_tvs, dcExTyCoVars = ex_tvs,
                  dcGADTEqualities = gadt_theta, dcOrigTheta = orig_theta,
                  dcOrigArgTys = orig_arg_tys, dcOrigResTy = orig_res_ty
                  dcArgBangs = arg_stricts, 
		  dcFields = fields,
		  dcWorkId = work_id,
                  dcRep = rep, 
                  dcRepArity = rep_arity, dcSourceArity = orig_arity,
                  dcRepTyCon = rep_tycon, dcRepType = rep_ty,
                  dcInfix = declared_infix, dcPromoted = promoted }

	-- The 'arg_stricts' passed to mkDataCon are simply those for the
	-- source-language arguments.  We add extra ones for the
	-- dictionary arguments right here.

    tag = assoc "mkDataCon" (tyConDataCons rep_tycon `zip` [fIRST_TAG..]) con

    rep_arg_tys = dataConRepArgTys con
    rep_ty = mkInvForAllTys univ_tvs $
             mkInvForAllTys ex_tvs $
             mkFunTys rep_arg_tys $
             mkTyConApp rep_tycon (mkOnlyTyVarTys univ_tvs)

    rep_arity = length rep_arg_tys + count isId ex_tvs

    promoted   -- See Note [Promoted data constructors] in TyCon
               -- TODO (RAE): Update note.
      = mkPromotedDataCon con name (getUnique name) (dataConUserType con) roles

                -- covars have role P
                -- TODO (RAE): I think we need role inference here for the
                -- dependent params. Should they all be nominal? I think "no".
    roles = map (\tv -> if isTyVar tv then Nominal else Phantom)
                (univ_tvs ++ ex_tvs) ++
            map (const Representational) orig_arg_tys

\end{code}

Note [Unpack equality predicates]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we have a GADT with a contructor C :: (a~[b]) => b -> T a
we definitely want that equality predicate *unboxed* so that it
takes no space at all.  This is easily done: just give it
an UNPACK pragma. The rest of the unpack/repack code does the
heavy lifting.  This one line makes every GADT take a word less
space for each equality predicate, so it's pretty important!

\begin{code}
-- | The 'Name' of the 'DataCon', giving it a unique, rooted identification
dataConName :: DataCon -> Name
dataConName = dcName

-- | The tag used for ordering 'DataCon's
dataConTag :: DataCon -> ConTag
dataConTag  = dcTag

-- | The type constructor that we are building via this data constructor
dataConTyCon :: DataCon -> TyCon
dataConTyCon = dcRepTyCon

-- | The original type constructor used in the definition of this data
-- constructor.  In case of a data family instance, that will be the family
-- type constructor.
dataConOrigTyCon :: DataCon -> TyCon
dataConOrigTyCon dc 
  | Just (tc, _) <- tyConFamInst_maybe (dcRepTyCon dc) = tc
  | otherwise                                          = dcRepTyCon dc

-- | The representation type of the data constructor, i.e. the sort
-- type that will represent values of this type at runtime
dataConRepType :: DataCon -> Type
dataConRepType = dcRepType

-- | Should the 'DataCon' be presented infix?
dataConIsInfix :: DataCon -> Bool
dataConIsInfix = dcInfix

-- | The universally-quantified type variables of the construtor.
dataConUnivTyVars :: DataCon -> [TyVar]
dataConUnivTyVars = dcUnivTyVars

-- | The existentially-quantified type variables of the worker. These
-- may include dependent GADT equalities.
dataConExTyCoVars :: DataCon -> [TyCoVar]
dataConExTyCoVars = dcExTyCoVars

-- | Get the Id of the 'DataCon' worker: a function that is the "actual"
-- constructor and has no top level binding in the program. The type may
-- be different from the obvious one written in the source program. Panics
-- if there is no such 'Id' for this 'DataCon'
dataConWorkId :: DataCon -> Id
dataConWorkId dc = dcWorkId dc

-- | Get the Id of the 'DataCon' wrapper: a function that wraps the "actual"
-- constructor so it has the type visible in the source program: c.f. 'dataConWorkId'.
-- Returns Nothing if there is no wrapper, which occurs for an algebraic data constructor 
-- and also for a newtype (whose constructor is inlined compulsorily)
dataConWrapId_maybe :: DataCon -> Maybe Id
dataConWrapId_maybe dc = case dcRep dc of
                           NoDataConRep -> Nothing
                           DCR { dcr_wrap_id = wrap_id } -> Just wrap_id

-- | Returns an Id which looks like the Haskell-source constructor by using
-- the wrapper if it exists (see 'dataConWrapId_maybe') and failing over to
-- the worker (see 'dataConWorkId')
dataConWrapId :: DataCon -> Id
dataConWrapId dc = case dcRep dc of
                     NoDataConRep-> dcWorkId dc    -- worker=wrapper
                     DCR { dcr_wrap_id = wrap_id } -> wrap_id

-- | Find all the 'Id's implicitly brought into scope by the data constructor. Currently,
-- the union of the 'dataConWorkId' and the 'dataConWrapId'
dataConImplicitIds :: DataCon -> [Id]
dataConImplicitIds (MkData { dcWorkId = work, dcRep = rep})
  = case rep of
       NoDataConRep               -> [work]
       DCR { dcr_wrap_id = wrap } -> [wrap,work]

-- | The labels for the fields of this particular 'DataCon'
dataConFieldLabels :: DataCon -> [FieldLabel]
dataConFieldLabels = dcFields

-- | Extract the type for any given labelled field of the 'DataCon'
dataConFieldType :: DataCon -> FieldLabel -> Type
dataConFieldType con label
  = case lookup label (dcFields con `zip` dcOrigArgTys con) of
      Just ty -> ty
      Nothing -> pprPanic "dataConFieldType" (ppr con <+> ppr label)

-- | The strictness markings decided on by the compiler.  Does not include those for
-- existential dictionaries.  The list is in one-to-one correspondence with the arity of the 'DataCon'
dataConStrictMarks :: DataCon -> [HsBang]
dataConStrictMarks = dcArgBangs

-- | Source-level arity of the data constructor
dataConSourceArity :: DataCon -> Arity
dataConSourceArity (MkData { dcSourceArity = arity }) = arity

-- | Gives the number of actual fields in the /representation/ of the 
-- data constructor. This may be more than appear in the source code;
-- the extra ones are the existentially quantified dictionaries
dataConRepArity :: DataCon -> Arity
dataConRepArity (MkData { dcRepArity = arity }) = arity


-- | The number of fields in the /representation/ of the constructor
-- AFTER taking into account the unpacking of any unboxed tuple fields
dataConRepRepArity :: DataCon -> RepArity
dataConRepRepArity dc = typeRepArity (dataConRepArity dc) (dataConRepType dc)

-- | Return whether there are any argument types for this 'DataCon's original source type
isNullarySrcDataCon :: DataCon -> Bool
isNullarySrcDataCon dc = null (dcOrigArgTys dc)

-- | Return whether there are any argument types for this 'DataCon's runtime representation type
isNullaryRepDataCon :: DataCon -> Bool
isNullaryRepDataCon dc = dataConRepArity dc == 0

dataConRepStrictness :: DataCon -> [StrictnessMark]
-- ^ Give the demands on the arguments of a
-- Core constructor application (Con dc args)
dataConRepStrictness dc = case dcRep dc of
                            NoDataConRep -> [NotMarkedStrict | _ <- dataConRepArgTys dc]
                            DCR { dcr_stricts = strs } -> strs

dataConRepBangs :: DataCon -> [HsBang]
dataConRepBangs dc = case dcRep dc of
                       NoDataConRep -> dcArgBangs dc
                       DCR { dcr_bangs = bangs } -> bangs

dataConBoxer :: DataCon -> Maybe DataConBoxer
dataConBoxer (MkData { dcRep = DCR { dcr_boxer = boxer } }) = Just boxer
dataConBoxer _ = Nothing 

-- | The \"signature\" of the 'DataCon' returns, in order:
--
-- 1) The result of 'dataConRepTyVars'
--
-- 2) The result of 'dataConTheta'
--
-- 3) The original, unflattened type arguments to the constructor
--
-- 4) The /original/ result type of the 'DataCon'
dataConSig :: DataCon -> ([TyVar], ThetaType, [Type], Type)
dataConSig (MkData { dcUnivTyVars     = univ_tvs
                   , dcExTyCoVars     = ex_tvs
                   , dcGADTEqualities = gadt_theta
                   , dcOrigTheta      = orig_theta
                   , dcOrigArgTys     = arg_tys
                   , dcOrigResTy      = res_ty })
  = ( univ_tvs ++ ex_tvs, gadt_theta ++ orig_theta, arg_tys, res_ty )
                       
-- | The \"full signature\" of the 'DataCon' returns, in order:
--
-- 1) The result of 'dataConUnivTyVars'
--
-- 2) The result of 'dataConExTyCoVars'
--
-- 3) Non-dependent GADT equalities
--
-- 3) The original, user-specified constraints
--
-- 4) The original argument types to the 'DataCon' (i.e. before 
--    any change of the representation of the type)
--
-- 5) The original result type of the 'DataCon'
dataConFullSig :: DataCon 
	       -> ([TyVar], [TyCoVar], ThetaType, ThetaType, [Type], Type)
dataConFullSig (MkData { dcUnivTyVars     = univ_tvs
                       , dcExTyCoVars     = ex_tvs
                       , dcGADTEqualities = gadt_theta
                       , dcOrigTheta      = orig_theta
                       , dcOrigArgTys     = orig_arg_tys
                       , dcOrigResTy      = orig_res_ty })
  = ( univ_tvs, ex_tvs, gadt_theta, orig_theta, orig_arg_tys, orig_res_ty )
                        
dataConOrigResTy :: DataCon -> Type
dataConOrigResTy dc = dcOrigResTy dc

-- | The \"stupid theta\" of the 'DataCon', such as @data Eq a@ in:
--
-- > data Eq a => T a = ...
dataConStupidTheta :: DataCon -> ThetaType
dataConStupidTheta dc = dcStupidTheta dc

dataConUserType :: DataCon -> Type
-- ^ The user-declared type of the data constructor
-- in the nice-to-read form:
--
-- > T :: forall a b. a -> b -> T [a]
--
-- rather than:
--
-- > T :: forall a c. forall b. (c~[a]) => a -> b -> T c
--
-- NB: If the constructor is part of a data instance, the result type
-- mentions the family tycon, not the internal one.
dataConUserType (MkData { dcOrigTyVars = tvs
                        , dcOrigTheta  = theta
                        , dcOrigArgTys = arg_tys
                        , dcOrigResTy  = res_ty })
  = mkInvForAllTys tvs $ mkFunTys theta $ mkFunTys arg_tys res_ty

-- | Finds the instantiated types of the arguments required to construct a 'DataCon' representation
-- NB: these INCLUDE any dictionary args
--     but EXCLUDE the data-declaration context, which is discarded
-- It's all post-flattening etc; this is a representation type
dataConInstArgTys :: DataCon	-- ^ A datacon with no existentials or equality constraints
				-- However, it can have a dcTheta (notably it can be a 
				-- class dictionary, with superclasses)
	      	  -> [Type] 	-- ^ Instantiated at these types
	      	  -> [Type]
dataConInstArgTys dc@(MkData { dcOrigTyVars = orig_tvs
                             , dcOrigTheta  = orig_theta
                             , dcOrigArgTys = orig_arg_tys
                             , dcRep        = rep }) inst_tys
 = case rep of
     NoDataConRep ->
       ASSERT2( length orig_tvs == length inst_tys
              , text "dataConInstArgTys" <+> ppr dc $$ ppr univ_tvs $$ ppr inst_tys)
       map (substTyWith orig_tvs inst_tys)
           (orig_theta ++ orig_arg_tys)
     DCR { dcr_univ_tvs = univ_tvs
         , dcr_ex_tvs   = _ex_tvs
         , dcr_theta    = theta
         , dcr_arg_tys  = arg_tys } ->
       ASSERT2( null _ex_tvs, ppr dc )
       map (substTyWith univ_tvs inst_tys)
           (theta ++ arg_tys)
  
-- | Returns just the instantiated /value/ argument types of a 'DataCon',
-- (excluding dictionary args)
dataConInstOrigArgTys 
	:: DataCon	-- Works for any DataCon
	-> [Type]	-- Includes existential tyvar args, but NOT
			-- equality constraints or dicts
	-> [Type]
-- For vanilla datacons, it's all quite straightforward
-- But for the call in MatchCon, we really do want just the value args
dataConInstOrigArgTys dc@(MkData {dcOrigArgTys = arg_tys,
			          dcOrigTyVars = all_tvs} ) inst_tys
  = ASSERT2( length all_tvs == length inst_tys
           , ptext (sLit "dataConInstOrigArgTys") <+> ppr dc $$ ppr all_tvs $$ ppr inst_tys )
    map (substTyWith all_tvs inst_tys) arg_tys
\end{code}

\begin{code}
-- | Returns the argument types of the wrapper, excluding all dictionary arguments
-- and without substituting for any type variables
dataConOrigArgTys :: DataCon -> [Type]
dataConOrigArgTys dc = dcOrigArgTys dc

-- | Returns the arg types of the worker, including *all* evidence, after any 
-- flattening has been done and without substituting for any type variables
dataConRepArgTys :: DataCon -> [Type]
dataConRepArgTys (MkData { dcRep = rep
                         , dcGADTEqualities = gadt_theta
                         , dcOrigTheta = orig_theta
		         , dcOrigArgTys = orig_arg_tys })
  = case rep of
      NoDataConRep -> ASSERT( null gadt_theta ) orig_theta ++ orig_arg_tys
      DCR { dcr_arg_tys = arg_tys } -> arg_tys
\end{code}

\begin{code}
-- | The string @package:module.name@ identifying a constructor, which is attached
-- to its info table and used by the GHCi debugger and the heap profiler
dataConIdentity :: DataCon -> [Word8]
-- We want this string to be UTF-8, so we get the bytes directly from the FastStrings.
dataConIdentity dc = bytesFS (packageIdFS (modulePackageId mod)) ++ 
                  fromIntegral (ord ':') : bytesFS (moduleNameFS (moduleName mod)) ++
                  fromIntegral (ord '.') : bytesFS (occNameFS (nameOccName name))
  where name = dataConName dc
        mod  = ASSERT( isExternalName name ) nameModule name
\end{code}

\begin{code}
isTupleDataCon :: DataCon -> Bool
isTupleDataCon (MkData {dcRepTyCon = tc}) = isTupleTyCon tc
	
isUnboxedTupleCon :: DataCon -> Bool
isUnboxedTupleCon (MkData {dcRepTyCon = tc}) = isUnboxedTupleTyCon tc

-- | Vanilla 'DataCon's are those that are nice boring Haskell 98 constructors
isVanillaDataCon :: DataCon -> Bool
isVanillaDataCon dc = dcVanilla dc
\end{code}

\begin{code}
classDataCon :: Class -> DataCon
classDataCon clas = case tyConDataCons (classTyCon clas) of
		      (dict_constr:no_more) -> ASSERT( null no_more ) dict_constr 
		      [] -> panic "classDataCon"
\end{code}

\begin{code}
dataConCannotMatch :: [Type] -> DataCon -> Bool
-- Returns True iff the data con *definitely cannot* match a 
--		    scrutinee of type (T tys)
--		    where T is the dcRepTyCon for the data con
dataConCannotMatch tys con
  | null eqs          = False	-- Common
  | all isTyVarTy tys = False	-- Also common
  | otherwise
  = typesCantMatch [(Type.substTy subst ty1, Type.substTy subst ty2)
                   | (ty1, ty2) <- eqs ]
  where
    (subst, eqs) = case rep of
      NoDataConRep -> ( zipTopTCvSubst orig_univ_tvs tys
                      , concatMap predEqs orig_theta )
      DCR { dcr_univ_tvs = univ_tvs
          , dcr_ex_tvs   = ex_tvs
          , dcr_theta    = theta }
        -> ( zipTopTCvSubst univ_tvs tys
           , mapMaybe (splitCoercionType_maybe . tyVarKind) ex_tvs
             ++ concatMap predEqs theta )

    -- TODO: could gather equalities from superclasses too
    predEqs pred = case classifyPredType pred of
                     EqPred ty1 ty2 -> [(ty1, ty2)]
                     TuplePred ts   -> concatMap predEqs ts
                     _              -> []
\end{code}

%************************************************************************
%*                                                                      *
        Promoting of data types to the kind level
%*                                                                      *
%************************************************************************

These two 'promoted..' functions are here because
 * They belong together
 * 'promoteDataCon' depends on DataCon stuff

\begin{code}
promoteDataCon :: DataCon -> TyCon
promoteDataCon (MkData { dcPromoted = tc }) = tc
\end{code}

%************************************************************************
%*									*
\subsection{Splitting products}
%*									*
%************************************************************************

\begin{code}
-- | Extract the type constructor, type argument, data constructor and it's
-- /representation/ argument types from a type if it is a product type.
--
-- Precisely, we return @Just@ for any type that is all of:
--
--  * Concrete (i.e. constructors visible)
--
--  * Single-constructor
--
--  * Not existentially quantified
--
-- Whether the type is a @data@ type or a @newtype@
splitDataProductType_maybe
	:: Type 			-- ^ A product type, perhaps
	-> Maybe (TyCon, 		-- The type constructor
		  [Type],		-- Type args of the tycon
		  DataCon,		-- The data constructor
		  [Type])		-- Its /representation/ arg types

	-- Rejecing existentials is conservative.  Maybe some things
	-- could be made to work with them, but I'm not going to sweat
	-- it through till someone finds it's important.

splitDataProductType_maybe ty
  | Just (tycon, ty_args) <- splitTyConApp_maybe ty
  , Just con <- isDataProductTyCon_maybe tycon
  = Just (tycon, ty_args, con, dataConInstArgTys con ty_args)
  | otherwise
  = Nothing

-- | All type constructors used in the definition of this type constructor,
--   recursively. This is used to find out all the type constructors whose data
--   constructors need to be in scope to be allowed to safely coerce under this
--   type constructor in Safe Haskell mode.
tyConsOfTyCon :: TyCon -> [TyCon]
tyConsOfTyCon tc = nameEnvElts (add tc emptyNameEnv)
  where
     go env tc = foldr add env (tyConDataCons tc >>= dataConOrigArgTys >>= tyConsOfType)
     add tc env | tyConName tc `elemNameEnv` env = env
                | otherwise = go (extendNameEnv env (tyConName tc) tc) tc
\end{code}

