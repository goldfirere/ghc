o%
% (c) The University of Glasgow 2006
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%

Monadic type operations

This module contains monadic operations over types that contain
mutable type variables

\begin{code}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://ghc.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

module TcMType (
  TcTyVar, TcKind, TcType, TcTauType, TcThetaType, TcTyVarSet,

  --------------------------------
  -- Creating new mutable type variables
  newFlexiTyVar,
  newFlexiTyVarTy,		-- Kind -> TcM TcType
  newFlexiTyVarTys,		-- Int -> Kind -> TcM [TcType]
  newPolyFlexiTyVarTy,
  newOpenFlexiTyVarTy,
  newMetaKindVar, newMetaKindVars,
  mkTcTyVarName, cloneMetaTyVar, 

  newMetaTyVar, readMetaTyVar, writeMetaTyVar, writeMetaTyVarRef,
  newMetaDetails, isFilledMetaTyVar, isFlexiMetaTyVar,

  --------------------------------
  -- Creating new evidence variables
  newEvVar, newEvVars, newEq, newDict,
  newWantedEvVar, newWantedEvVars,
  newTcEvBinds, addTcEvBind,
  newFlatWanted, newFlatWanteds,

  --------------------------------
  -- Instantiation
  tcInstTyCoVars, newSigTyVar,
  tcInstType,
  tcInstSkolTyCoVars, tcInstSkolTyCoVarsLoc, tcInstSuperSkolTyCoVarsX,
  tcInstSigTyCoVarsLoc, tcInstSigTyCoVars,
  tcInstSkolTyCoVar, tcInstSkolType,
  tcSkolDFunType, tcSuperSkolTyCoVars,

  --------------------------------
  -- Zonking
  zonkTcPredType, 
  skolemiseUnboundMetaTyVar,
  zonkTcTyCoVar, zonkTcTyCoVars, zonkTyCoVarsAndFV, zonkTcTypeAndFV,
  zonkQuantifiedTyCoVar, zonkQuantifiedTyCoVarOrType, quantifyTyCoVars,
  quantifyTyCoVars', defaultKindVar,
  zonkTcTyCoVarBndr, zonkTcType, zonkTcTypes, zonkTcThetaType, 

  zonkEvVar, zonkWC, zonkId, zonkCt, zonkCts, zonkSkolemInfo, zonkFlats,

  tcGetGlobalTyVars, 
  ) where

#include "HsVersions.h"

-- friends:
import TyCoRep
import TcType
import TcEvidence
import Type
import Coercion
import Class
import TyCon
import Var

-- others:
import TcRnMonad        -- TcType, amongst others
import Id
import Name
import VarSet
import TysWiredIn
import TysPrim
import VarEnv
import PrelNames
import Util
import Outputable
import FastString
import SrcLoc
import Bag
import DynFlags

import Control.Monad
import Data.List        ( mapAccumL, partition )
\end{code}


%************************************************************************
%*									*
	Kind variables
%*									*
%************************************************************************

\begin{code}
mkKindName :: Unique -> Name
mkKindName unique = mkSystemName unique kind_var_occ

kind_var_occ :: OccName	-- Just one for all MetaKindVars
			-- They may be jiggled by tidying
kind_var_occ = mkOccName tvName "k"

newMetaKindVar :: TcM TcKind
newMetaKindVar = do { uniq <- newUnique
		    ; details <- newMetaDetails TauTv
                    ; let kv = mkTcTyVar (mkKindName uniq) liftedTypeKind details
		    ; return (mkOnlyTyVarTy kv) }

newMetaKindVars :: Int -> TcM [TcKind]
newMetaKindVars n = mapM (\ _ -> newMetaKindVar) (nOfThem n ())
\end{code}


%************************************************************************
%*									*
     Evidence variables; range over constraints we can abstract over
%*									*
%************************************************************************

\begin{code}
newEvVars :: TcThetaType -> TcM [EvVar]
newEvVars theta = mapM newEvVar theta

newWantedEvVar :: TcPredType -> TcM EvVar 
newWantedEvVar = newEvVar

newWantedEvVars :: TcThetaType -> TcM [EvVar] 
newWantedEvVars theta = mapM newWantedEvVar theta 

--------------

newEvVar :: TcPredType -> TcRnIf gbl lcl EvVar
-- Creates new *rigid* variables for predicates
newEvVar ty = do { name <- newSysName (predTypeOccName ty) 
                 ; return (mkLocalId name ty) }

newEq :: TcType -> TcType -> TcM EvVar
newEq ty1 ty2
  = do { name <- newSysName (mkVarOccFS (fsLit "cobox"))
       ; return (mkLocalId name (mkTcEqPred ty1 ty2)) }

newDict :: Class -> [TcType] -> TcM DictId
newDict cls tys 
  = do { name <- newSysName (mkDictOcc (getOccName cls))
       ; return (mkLocalId name (mkClassPred cls tys)) }

predTypeOccName :: PredType -> OccName
predTypeOccName ty = case classifyPredType ty of
    ClassPred cls _ -> mkDictOcc (getOccName cls)
    EqPred _ _      -> mkVarOccFS (fsLit "cobox")
    TuplePred _     -> mkVarOccFS (fsLit "tup")
    IrredPred _     -> mkVarOccFS (fsLit "irred")
\end{code}

*********************************************************************************
*                                                                               * 
*                   Wanted constraints
*                                                                               *
*********************************************************************************

\begin{code}
newFlatWanted :: CtOrigin -> PredType -> TcM Ct
newFlatWanted orig pty
  = do loc <- getCtLoc orig
       v <- newWantedEvVar pty
       return $ mkNonCanonical $
            CtWanted { ctev_evar = v
                     , ctev_pred = pty
                     , ctev_loc = loc }

newFlatWanteds :: CtOrigin -> ThetaType -> TcM [Ct]
newFlatWanteds orig = mapM (newFlatWanted orig)
\end{code}

%************************************************************************
%*									*
	SkolemTvs (immutable)
%*									*
%************************************************************************

\begin{code}
tcInstType :: ([TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])) -- How to instantiate the type variables
	   -> TcType 					 -- Type to instantiate
	   -> TcM ([TcTyCoVar], TcThetaType, TcType)	 -- Result
		-- (type vars (excl coercion vars), preds (incl equalities), rho)
tcInstType inst_tyvars ty
  = case tcSplitNamedForAllTys ty of
	([],    rho) -> let	-- There may be overloading despite no type variables;
				-- 	(?x :: Int) => Int -> Int
			        (theta, tau) = tcSplitPhiTy rho
			    in
			    return ([], theta, tau)

	(tyvars, rho) -> do { (subst, tyvars') <- inst_tyvars tyvars
                 	    ; let (theta, tau) = tcSplitPhiTy (substTy subst rho)
			    ; return (tyvars', theta, tau) }

tcSkolDFunType :: Type -> TcM ([TcTyVar], TcThetaType, TcType)
-- Instantiate a type signature with skolem constants, but 
-- do *not* give them fresh names, because we want the name to
-- be in the type environment: it is lexically scoped.
tcSkolDFunType ty = tcInstType (\tvs -> return (tcSuperSkolTyCoVars tvs)) ty

tcSuperSkolTyCoVars :: [TyCoVar] -> (TCvSubst, [TcTyCoVar])
-- Make skolem constants, but do *not* give them new names, as above
-- Moreover, make them "super skolems"; see comments with superSkolemTv
-- see Note [Kind substitution when instantiating]
-- Precondition: tyvars should be ordered by scoping
tcSuperSkolTyCoVars = mapAccumL tcSuperSkolTyCoVar (mkTopTCvSubst [])

tcSuperSkolTyCoVar :: TCvSubst -> TyCoVar -> (TCvSubst, TcTyCoVar)
tcSuperSkolTyCoVar subst tv
  = (extendTCvSubst subst tv (mkTyCoVarTy new_tv), new_tv)
  where
    kind   = substTy subst (tyVarKind tv)
    new_tv | isTyVar tv = mkTcTyVar (tyVarName tv) kind superSkolemTv
           | otherwise  = uniqAway (getTCvInScope subst) (setVarType tv kind)

tcInstSkolTyCoVar :: SrcSpan -> Bool -> TCvSubst -> TyCoVar
                  -> TcRnIf gbl lcl (TCvSubst, TcTyCoVar)
-- Instantiate the tyvar, using 
--      * the occ-name and kind of the supplied tyvar, 
--      * the unique from the monad,
--      * the location either from the tyvar (skol_info = SigSkol)
--                     or from the monad (otherwise)
tcInstSkolTyCoVar loc overlappable subst tyvar
  | isTyVar tyvar
  = do  { uniq <- newUnique
        ; let new_name = mkInternalName uniq occ loc
              new_tv   = mkTcTyVar new_name kind (SkolemTv overlappable)
        ; return (extendTCvSubst subst tyvar (mkOnlyTyVarTy new_tv), new_tv) }
  | otherwise -- coercion variable
  = do  { ev_var <- newEvVar kind
        ; return (extendTCvSubst subst tyvar (mkTyCoVarTy ev_var), ev_var) }
  where
    old_name = tyVarName tyvar
    occ      = nameOccName old_name
    kind     = substTy subst (tyVarKind tyvar)

-- Wrappers
-- we need to be able to do this from outside the TcM monad:
tcInstSkolTyCoVarsLoc :: SrcSpan -> [TyCoVar] -> TcRnIf gbl lcl (TCvSubst, [TcTyCoVar])
tcInstSkolTyCoVarsLoc loc = mapAccumLM (tcInstSkolTyCoVar loc False) (mkTopTCvSubst [])

tcInstSkolTyCoVars :: [TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])
tcInstSkolTyCoVars = tcInstSkolTyCoVarsX (mkTopTCvSubst [])

tcInstSkolTyCoVarsX, tcInstSuperSkolTyCoVarsX
  :: TCvSubst -> [TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])
tcInstSkolTyCoVarsX      subst = tcInstSkolTyCoVars' False subst
tcInstSuperSkolTyCoVarsX subst = tcInstSkolTyCoVars' True  subst

tcInstSkolTyCoVars' :: Bool -> TCvSubst -> [TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])
-- Precondition: tyvars should be ordered (kind vars first)
-- see Note [Kind substitution when instantiating]
-- Get the location from the monad; this is a complete freshening operation
tcInstSkolTyCoVars' isSuperSkol subst tvs
  = do { loc <- getSrcSpanM
       ; mapAccumLM (tcInstSkolTyCoVar loc isSuperSkol) subst tvs }

tcInstSigTyCoVarsLoc :: SrcSpan -> [TyCoVar]
                     -> TcRnIf gbl lcl (TCvSubst, [TcTyCoVar])
-- We specify the location
tcInstSigTyCoVarsLoc loc = mapAccumLM (tcInstSkolTyCoVar loc False)
                                      (mkTopTCvSubst [])

tcInstSigTyCoVars :: [TyCoVar] -> TcRnIf gbl lcl (TCvSubst, [TcTyCoVar])
-- Get the location from the TyVar itself, not the monad
tcInstSigTyCoVars = mapAccumLM inst_tv (mkTopTCvSubst [])
  where
    inst_tv subst tv = tcInstSkolTyCoVar (getSrcSpan tv) False subst tv

tcInstSkolType :: TcType -> TcM ([TcTyCoVar], TcThetaType, TcType)
-- Instantiate a type with fresh skolem constants
-- Binding location comes from the monad
tcInstSkolType ty = tcInstType tcInstSkolTyCoVars ty

newSigTyVar :: Name -> Kind -> TcM TcTyVar
newSigTyVar name kind
  = do { uniq <- newUnique
       ; let name' = setNameUnique name uniq
                      -- Use the same OccName so that the tidy-er
                      -- doesn't gratuitously rename 'a' to 'a0' etc
       ; details <- newMetaDetails SigTv
       ; return (mkTcTyVar name' kind details) }

newMetaDetails :: MetaInfo -> TcM TcTyVarDetails
newMetaDetails info 
  = do { ref <- newMutVar Flexi
       ; untch <- getUntouchables
       ; return (MetaTv { mtv_info = info, mtv_ref = ref, mtv_untch = untch }) }
\end{code}

Note [Kind substitution when instantiating]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When we instantiate a bunch of kind and type variables, first we
expect them to be topologically sorted.
Then we have to instantiate the kind variables, build a substitution
from old variables to the new variables, then instantiate the type
variables substituting the original kind.

Exemple: If we want to instantiate
  [(k1 :: *), (k2 :: *), (a :: k1 -> k2), (b :: k1)]
we want
  [(?k1 :: *), (?k2 :: *), (?a :: ?k1 -> ?k2), (?b :: ?k1)]
instead of the buggous
  [(?k1 :: *), (?k2 :: *), (?a :: k1 -> k2), (?b :: k1)]


%************************************************************************
%*									*
	MetaTvs (meta type variables; mutable)
%*									*
%************************************************************************

\begin{code}
newMetaTyVar :: MetaInfo -> Kind -> TcM TcTyVar
-- Make a new meta tyvar out of thin air
newMetaTyVar meta_info kind
  = do	{ uniq <- newUnique
        ; let name = mkTcTyVarName uniq s
              s = case meta_info of
                        PolyTv -> fsLit "s"
                        TauTv  -> fsLit "t"
                        SigTv  -> fsLit "a"
        ; details <- newMetaDetails meta_info
	; return (mkTcTyVar name kind details) }

cloneMetaTyVar :: TcTyVar -> TcM TcTyVar
cloneMetaTyVar tv
  = ASSERT( isTcTyVar tv )
    do	{ uniq <- newUnique
        ; ref  <- newMutVar Flexi
        ; let name'    = setNameUnique (tyVarName tv) uniq
              details' = case tcTyVarDetails tv of 
                           details@(MetaTv {}) -> details { mtv_ref = ref }
                           _ -> pprPanic "cloneMetaTyVar" (ppr tv)
        ; return (mkTcTyVar name' (tyVarKind tv) details') }

mkTcTyVarName :: Unique -> FastString -> Name
-- Make sure that fresh TcTyVar names finish with a digit
-- leaving the un-cluttered names free for user names
mkTcTyVarName uniq str = mkSysTvName uniq str

-- Works for both type and kind variables
readMetaTyVar :: TyVar -> TcM MetaDetails
readMetaTyVar tyvar = ASSERT2( isMetaTyVar tyvar, ppr tyvar )
		      readMutVar (metaTvRef tyvar)

isFilledMetaTyVar :: TyVar -> TcM Bool
-- True of a filled-in (Indirect) meta type variable
isFilledMetaTyVar tv
  | not (isTcTyVar tv) = return False
  | MetaTv { mtv_ref = ref } <- tcTyVarDetails tv
  = do 	{ details <- readMutVar ref
	; return (isIndirect details) }
  | otherwise = return False

isFlexiMetaTyVar :: TyVar -> TcM Bool
-- True of a un-filled-in (Flexi) meta type variable
isFlexiMetaTyVar tv
  | not (isTcTyVar tv) = return False
  | MetaTv { mtv_ref = ref } <- tcTyVarDetails tv
  = do 	{ details <- readMutVar ref
	; return (isFlexi details) }
  | otherwise = return False

--------------------
-- Works with both type and kind variables
writeMetaTyVar :: TcTyVar -> TcType -> TcM ()
-- Write into a currently-empty MetaTyVar

writeMetaTyVar tyvar ty
  | not debugIsOn 
  = writeMetaTyVarRef tyvar (metaTvRef tyvar) ty

-- Everything from here on only happens if DEBUG is on
  | not (isTcTyVar tyvar)
  = WARN( True, text "Writing to non-tc tyvar" <+> ppr tyvar )
    return ()

  | MetaTv { mtv_ref = ref } <- tcTyVarDetails tyvar
  = writeMetaTyVarRef tyvar ref ty

  | otherwise
  = WARN( True, text "Writing to non-meta tyvar" <+> ppr tyvar )
    return ()

--------------------
writeMetaTyVarRef :: TcTyVar -> TcRef MetaDetails -> TcType -> TcM ()
-- Here the tyvar is for error checking only;
-- the ref cell must be for the same tyvar
writeMetaTyVarRef tyvar ref ty
  | not debugIsOn
  = do { traceTc "writeMetaTyVar" (ppr tyvar <+> dcolon <+> ppr (tyVarKind tyvar)
                                   <+> text ":=" <+> ppr ty)
       ; writeMutVar ref (Indirect ty) }

-- Everything from here on only happens if DEBUG is on
  | otherwise
  = do { meta_details <- readMutVar ref;
       -- Zonk kinds to allow the error check to work
       ; zonked_tv_kind <- zonkTcType tv_kind
       ; zonked_ty_kind <- zonkTcType ty_kind

       -- Check for double updates
       ; ASSERT2( isFlexi meta_details,
                  hang (text "Double update of meta tyvar")
                   2 (ppr tyvar $$ ppr meta_details) )

         traceTc "writeMetaTyVar" (ppr tyvar <+> text ":=" <+> ppr ty)
       ; writeMutVar ref (Indirect ty)
       ; when (   not (isPredTy tv_kind)
                    -- Don't check kinds for updates to coercion variables
               && not (zonked_ty_kind `tcEqKind` zonked_tv_kind))
       $ WARN( True, hang (text "Ill-kinded update to meta tyvar")
                        2 (    ppr tyvar <+> text "::" <+> (ppr tv_kind $$ ppr zonked_tv_kind)
                           <+> text ":="
                           <+> ppr ty    <+> text "::" <+> (ppr ty_kind $$ ppr zonked_ty_kind) ) )
         (return ()) }
  where
    tv_kind = tyVarKind tyvar
    ty_kind = typeKind ty
\end{code}


%************************************************************************
%*									*
	MetaTvs: TauTvs
%*									*
%************************************************************************

Note [Coercion variables in tcInstTyCoVarX]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
What do we do when we need to instantiate a coercion variable that a type
is quantified over? We create a new EvVar and emit a constraint so that
the EvVar is given the appropratie evidence after constraint solving. The
wrinkle here is that a type can be quantified over only *unboxed* coercions,
and the constraint solver works only with *boxed* coercions. So, what to do?
Our emitted wanted constraint uses a boxed coercion, but we must be careful
to unbox the coercion before passing it to any coercion-quantified type. This
is done by using an EvUnbox EvTerm in an HsWrapper. The mkWpTyApps function
used in instCall (frequently called soon after tcInstTyCoVars) does this
correctly. See also [Wrapping coercions embedded in types] in TcEvidence.

Note [Sort-polymorphic tyvars accept foralls]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Here is a common paradigm:
   foo :: (forall a. a -> a) -> Int
   foo = error "urk"
To make this work we need to instantiate 'error' with a polytype.
A similar case is
   bar :: Bool -> (forall a. a->a) -> Int
   bar True = \x. (x 3)
   bar False = error "urk"
Here we need to instantiate 'error' with a polytype. 

But 'error' has an sort-polymorphic type variable, precisely so that
we can instantiate it with Int#.  So we also allow such type variables
to be instantiate with foralls.  It's a bit of a hack, but seems
straightforward.

\begin{code}
newFlexiTyVar :: Kind -> TcM TcTyVar
newFlexiTyVar kind = newMetaTyVar TauTv kind

newFlexiTyVarTy  :: Kind -> TcM TcType
newFlexiTyVarTy kind = do
    tc_tyvar <- newFlexiTyVar kind
    return (TyVarTy tc_tyvar)

newFlexiTyVarTys :: Int -> Kind -> TcM [TcType]
newFlexiTyVarTys n kind = mapM newFlexiTyVarTy (nOfThem n kind)

newPolyFlexiTyVarTy :: TcM TcType
newPolyFlexiTyVarTy = do { tv <- newMetaTyVar PolyTv liftedTypeKind
                         ; return (TyVarTy tv) }

-- | Create a tyvar that can be a lifted or unlifted type.
newOpenFlexiTyVarTy :: TcM TcType
newOpenFlexiTyVarTy
  = do { lev <- newFlexiTyVarTy levityTy
       ; newFlexiTyVarTy (tYPE lev) }

tcInstTyCoVars :: CtOrigin -> [TyCoVar] -> TcM ([TcTyCoVar], [TcType], TCvSubst)
-- Instantiate with META type variables
-- Note that this works for a sequence of kind, type, and coercion variables
-- variables.  Eg    [ (k:*), (a:k->k) ]
--             Gives [ (k7:*), (a8:k7->k7) ]
tcInstTyCoVars = tcInstTyCoVarsX emptyTCvSubst
    -- emptyTCvSubst has an empty in-scope set, but that's fine here
    -- Since the tyvars are freshly made, they cannot possibly be
    -- captured by any existing for-alls.

tcInstTyCoVarsX :: TCvSubst -> CtOrigin -> [TyCoVar]
                -> TcM ([TcTyCoVar], [TcType], TCvSubst)
-- The "X" part is because of extending the substitution
tcInstTyCoVarsX subst origin tyvars =
  do { (subst', tyvars') <- mapAccumLM (tcInstTyCoVarX origin) subst tyvars
     ; return (tyvars', mkTyCoVarTys tyvars', subst') }

tcInstTyCoVarX :: CtOrigin -> TCvSubst -> TyCoVar -> TcM (TCvSubst, TcTyCoVar)
-- Make a new unification variable tyvar whose Name and Kind come from
-- an existing TyVar. We substitute kind variables in the kind.
tcInstTyCoVarX origin subst tyvar
  | isTyVar tyvar
  = do  { uniq <- newUnique
               -- See Note [
        ; let info = if isSortPolymorphic (tyVarKind tyvar)
                     then PolyTv
                     else TauTv
        ; details <- newMetaDetails info
        ; let name   = mkSystemName uniq (getOccName tyvar)
              kind   = substTy subst (tyVarKind tyvar)
              new_tv = mkTcTyVar name kind details
        ; return (extendTCvSubst subst tyvar (mkOnlyTyVarTy new_tv), new_tv) }
  | otherwise
  = do { new_cv <- newEvVar (substTy subst (varType tyvar))
         -- can't call unifyType, because we need to return a CoVar,
         -- and unification might result in a TcCoercion that's not a CoVar
         -- See Note [Coercion variables in tcInstTyCoVarX]
       ; loc <- getCtLoc origin
       ; let (ty1, ty2) = coVarTypes new_cv
             ctev = CtWanted { ctev_evar = new_cv
                             , ctev_pred = mkTcEqPred ty1 ty2
                                            -- TODO (RAE): the use of mkTcEqPred, as opposed to the (~#) former, is highly suspect
                             , ctev_loc  = loc }
       ; emitFlat $ mkNonCanonical ctev
       ; return (extendTCvSubst subst tyvar (mkTyCoVarTy new_cv), new_cv) }

\end{code}


%************************************************************************
%*									*
             Quantification
%*									*
%************************************************************************

Note [quantifyTyCoVars]
~~~~~~~~~~~~~~~~~~~~~~~
quantifyTyCoVars is give the free vars of a type that we
are about to wrap in a forall.

It takes these free type/kind variables and 
  1. Zonks them and remove globals
  2. Partitions into type and kind variables (kvs1, tvs)
  3. Extends kvs1 with free kind vars in the kinds of tvs (removing globals)
  4. Calls zonkQuantifiedTyVar on each

Step (3) is often unimportant, because the kind variable is often
also free in the type.  Eg
     Typeable k (a::k)
has free vars {k,a}.  But the type (see Trac #7916)
    (f::k->*) (a::k)
has free vars {f,a}, but we must add 'k' as well! Hence step (3).

\begin{code}
quantifyTyCoVars :: TcTyCoVarSet -> TcTyCoVarSet -> TcM [TcTyCoVar]
quantifyTyCoVars gbls tkvs = quantifyTyCoVars' gbls tkvs False

quantifyTyCoVars' :: TcTyCoVarSet   -- globals
                  -> TcTyCoVarSet   -- variables we're quantifying
                  -> Bool           -- True <=> all variables are kind
                                    -- variables; used for -XNoPolyKinds defaults
                  -> TcM [TcTyCoVar]
-- See Note [quantifyTyCoVars]
-- The input is a mixture of type and kind variables; a kind variable k 
--   may occur *after* a tyvar mentioning k in its kind
-- Can be given a mixture of TcTyVars and TyVars, in the case of
--   associated type declarations

quantifyTyCoVars' gbl_tvs tkvs all_kind_vars
  = do { tkvs    <- zonkTyCoVarsAndFV tkvs
       ; gbl_tvs <- zonkTyCoVarsAndFV gbl_tvs
       ; let dep_var_set
               = if all_kind_vars
                 then tkvs `minusVarSet` gbl_tvs
                 else closeOverKinds (unionVarSets $
                                      map (tyCoVarsOfType . tyVarKind) $
                                      varSetElems tkvs)
                      `minusVarSet` gbl_tvs
             nondep_var_set = tkvs `minusVarSet` dep_var_set `minusVarSet` gbl_tvs
             dep_vars       = varSetElemsWellScoped dep_var_set
             nondep_vars    = varSetElemsWellScoped nondep_var_set

                              -- NB kinds of tvs are zonked by zonkTyVarsAndFV

             -- In the non-PolyKinds case, default the kind variables
             -- to *, and zonk the tyvars as usual.  Notice that this
             -- may make quantifyTyCoVars return a shorter list
             -- than it was passed, but that's ok
       ; poly_kinds <- xoptM Opt_PolyKinds
       ; dep_vars2 <- if poly_kinds
                      then return dep_vars
                      else do { let (meta_kvs, skolem_kvs) = partition is_meta dep_vars
                                    is_meta kv = isTcTyVar kv && isMetaTyVar kv
                              
                              ; mapM_ defaultKindVar meta_kvs
                              ; return skolem_kvs }  -- should be empty

       ; mapMaybeM zonk_quant (dep_vars2 ++ nondep_vars) }
           -- Because of the order, any kind variables
           -- mentioned in the kinds of the type variables refer to
           -- the now-quantified versions
  where
    zonk_quant tkv
      | isTcTyCoVar tkv = zonkQuantifiedTyCoVar tkv
      | otherwise       = return $ Just tkv
      -- For associated types, we have the class variables 
      -- in scope, and they are TyVars not TcTyVars

zonkQuantifiedTyCoVar :: TcTyCoVar -> TcM (Maybe TcTyCoVar)
-- The quantified type variables often include meta type variables
-- we want to freeze them into ordinary type variables, and
-- default their kind (e.g. from TYPE v to TYPE Lifted)
-- The meta tyvar is updated to point to the new skolem TyVar.  Now any 
-- bound occurrences of the original type variable will get zonked to 
-- the immutable version.
--
-- We leave skolem TyVars alone; they are immutable.
--
-- This function is called on both kind and type variables,
-- but kind variables *only* if PolyKinds is on.
--
-- This returns a tyvar if it should be quantified over; otherwise,
-- it returns Nothing. Nothing is
-- returned only if zonkQuantifiedTyVar is passed a Levity meta-tyvar,
-- in order to default to Lifted.
zonkQuantifiedTyCoVar tv = left_only `liftM` zonkQuantifiedTyCoVarOrType tv
  where left_only :: Either a b -> Maybe a
        left_only (Left x) =  Just x
        left_only (Right _) = Nothing

-- | Like zonkQuantifiedTyCoVar, but if zonking reveals that the tyvar
-- should become a type (when defaulting a levity var to Lifted), it
-- returns the type instead.
zonkQuantifiedTyCoVarOrType :: TcTyCoVar -> TcM (Either TcTyCoVar TcType)
zonkQuantifiedTyCoVarOrType tv
  | isTyVar tv
  = ASSERT2( isTcTyVar tv, ppr tv ) 
    case tcTyVarDetails tv of
      SkolemTv {} -> do { kind <- zonkTcType (tyVarKind tv)
                        ; return $ Left $ setTyVarKind tv kind }
	-- It might be a skolem type variable, 
	-- for example from a user type signature

      MetaTv { mtv_ref = ref } ->
          do when debugIsOn $ do
                 -- [Sept 04] Check for non-empty.
                 -- See note [Silly Type Synonym]
                 cts <- readMutVar ref
                 case cts of
                     Flexi -> return ()
                     Indirect ty -> WARN( True, ppr tv $$ ppr ty )
                                    return ()
             if isLevityVar tv
             then do { writeMetaTyVar tv liftedDataConTy
                     ; return (Right liftedDataConTy) }
             else Left `liftM` skolemiseUnboundMetaTyVar tv vanillaSkolemTv
      _other -> pprPanic "zonkQuantifiedTyCoVar" (ppr tv) -- FlatSkol, RuntimeUnk

  | otherwise -- coercion variable
  = do { ty <- zonkTcType (coVarKind tv)
       ; return $ Left $ setVarType tv ty }

-- | Take an (unconstrained) meta tyvar and default it. Works only for
-- kind vars (of type BOX) and levity vars (of type Levity).
defaultKindVar :: TcTyVar -> TcM Kind
defaultKindVar kv
  | ASSERT( isMetaTyVar kv )
    isLevityVar kv
  = writeMetaTyVar kv liftedDataConTy >> return liftedDataConTy
  | otherwise
  = writeMetaTyVar kv liftedTypeKind >> return liftedTypeKind

skolemiseUnboundMetaTyVar :: TcTyVar -> TcTyVarDetails -> TcM TyVar
-- We have a Meta tyvar with a ref-cell inside it
-- Skolemise it, including giving it a new Name, so that
--   we are totally out of Meta-tyvar-land
-- We create a skolem TyVar, not a regular TyVar
--   See Note [Zonking to Skolem]
skolemiseUnboundMetaTyVar tv details
  = ASSERT2( isMetaTyVar tv, ppr tv ) 
    do  { span <- getSrcSpanM    -- Get the location from "here"
                                 -- ie where we are generalising
        ; uniq <- newUnique      -- Remove it from TcMetaTyVar unique land
        ; kind <- zonkTcType (tyVarKind tv)
        ; let final_name = mkInternalName uniq (getOccName tv) span
              final_tv   = mkTcTyVar final_name kind details

        ; writeMetaTyVar tv (mkTyCoVarTy final_tv)
        ; return final_tv }
\end{code}

Note [Zonking to Skolem]
~~~~~~~~~~~~~~~~~~~~~~~~
We used to zonk quantified type variables to regular TyVars.  However, this
leads to problems.  Consider this program from the regression test suite:

  eval :: Int -> String -> String -> String
  eval 0 root actual = evalRHS 0 root actual

  evalRHS :: Int -> a
  evalRHS 0 root actual = eval 0 root actual

It leads to the deferral of an equality (wrapped in an implication constraint)

  forall a. () => ((String -> String -> String) ~ a)

which is propagated up to the toplevel (see TcSimplify.tcSimplifyInferCheck).
In the meantime `a' is zonked and quantified to form `evalRHS's signature.
This has the *side effect* of also zonking the `a' in the deferred equality
(which at this point is being handed around wrapped in an implication
constraint).

Finally, the equality (with the zonked `a') will be handed back to the
simplifier by TcRnDriver.tcRnSrcDecls calling TcSimplify.tcSimplifyTop.
If we zonk `a' with a regular type variable, we will have this regular type
variable now floating around in the simplifier, which in many places assumes to
only see proper TcTyVars.

We can avoid this problem by zonking with a skolem.  The skolem is rigid
(which we require for a quantified variable), but is still a TcTyVar that the
simplifier knows how to deal with.

Note [Silly Type Synonyms]
~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider this:
	type C u a = u	-- Note 'a' unused

	foo :: (forall a. C u a -> C u a) -> u
	foo x = ...

	bar :: Num u => u
	bar = foo (\t -> t + t)

* From the (\t -> t+t) we get type  {Num d} =>  d -> d
  where d is fresh.

* Now unify with type of foo's arg, and we get:
	{Num (C d a)} =>  C d a -> C d a
  where a is fresh.

* Now abstract over the 'a', but float out the Num (C d a) constraint
  because it does not 'really' mention a.  (see exactTyVarsOfType)
  The arg to foo becomes
	\/\a -> \t -> t+t

* So we get a dict binding for Num (C d a), which is zonked to give
	a = ()
  [Note Sept 04: now that we are zonking quantified type variables
  on construction, the 'a' will be frozen as a regular tyvar on
  quantification, so the floated dict will still have type (C d a).
  Which renders this whole note moot; happily!]

* Then the \/\a abstraction has a zonked 'a' in it.

All very silly.   I think its harmless to ignore the problem.  We'll end up with
a \/\a in the final result but all the occurrences of a will be zonked to ()

%************************************************************************
%*									*
              Zonking
%*									*
%************************************************************************

@tcGetGlobalTyVars@ returns a fully-zonked set of tyvars free in the environment.
To improve subsequent calls to the same function it writes the zonked set back into
the environment.

\begin{code}
tcGetGlobalTyVars :: TcM TcTyVarSet
tcGetGlobalTyVars
  = do { (TcLclEnv {tcl_tyvars = gtv_var}) <- getLclEnv
       ; gbl_tvs  <- readMutVar gtv_var
       ; gbl_tvs' <- zonkTyCoVarsAndFV gbl_tvs
       ; writeMutVar gtv_var gbl_tvs'
       ; return gbl_tvs' }
  where
\end{code}

-----------------  Type variables

\begin{code}
zonkTcTypeAndFV :: TcType -> TcM TyCoVarSet
-- Zonk a type and take its free variables
-- With kind polymorphism it can be essential to zonk *first*
-- so that we find the right set of free variables.  Eg
--    forall k1. forall (a:k2). a
-- where k2:=k1 is in the substitution.  We don't want
-- k2 to look free in this type!
zonkTcTypeAndFV ty = do { ty <- zonkTcType ty; return (tyCoVarsOfType ty) }

zonkTyCoVar :: TyCoVar -> TcM TcType
-- Works on TyVars and TcTyVars
zonkTyCoVar tv | isTcTyVar tv = zonkTcTyCoVar tv
             | otherwise    = return (mkTyCoVarTy tv)
   -- Hackily, when typechecking type and class decls
   -- we have TyVars in scopeadded (only) in 
   -- TcHsType.tcTyClTyVars, but it seems
   -- painful to make them into TcTyVars there

zonkTyCoVarsAndFV :: TyCoVarSet -> TcM TyCoVarSet
zonkTyCoVarsAndFV tycovars = tyCoVarsOfTypes <$> mapM zonkTyCoVar (varSetElems tycovars)

zonkTcTyCoVars :: [TcTyCoVar] -> TcM [TcType]
zonkTcTyCoVars tyvars = mapM zonkTcTyCoVar tyvars

-----------------  Types
zonkTyCoVarKind :: TyCoVar -> TcM TyCoVar
zonkTyCoVarKind tv = do { kind' <- zonkTcType (tyVarKind tv)
                        ; return (setTyVarKind tv kind') }

zonkTcTypes :: [TcType] -> TcM [TcType]
zonkTcTypes tys = mapM zonkTcType tys

zonkTcThetaType :: TcThetaType -> TcM TcThetaType
zonkTcThetaType theta = mapM zonkTcPredType theta

zonkTcPredType :: TcPredType -> TcM TcPredType
zonkTcPredType = zonkTcType
\end{code}

---------------  Constraints

\begin{code}
zonkImplication :: Implication -> TcM (Bag Implication)
zonkImplication implic@(Implic { ic_untch  = untch
                               , ic_binds  = binds_var
                               , ic_skols  = skols
                               , ic_given  = given
                               , ic_wanted = wanted
                               , ic_info   = info })
  = do { skols'  <- mapM zonkTcTyCoVarBndr skols  -- Need to zonk their kinds!
                                                  -- as Trac #7230 showed
       ; given'  <- mapM zonkEvVar given
       ; info'   <- zonkSkolemInfo info
       ; wanted' <- zonkWCRec binds_var untch wanted
       ; if isEmptyWC wanted' 
         then return emptyBag
         else return $ unitBag $
              implic { ic_fsks   = []  -- Zonking removes all FlatSkol tyvars
                     , ic_skols  = skols'
                     , ic_given  = given'
                     , ic_wanted = wanted'
                     , ic_info   = info' } }

zonkEvVar :: EvVar -> TcM EvVar
zonkEvVar var = do { ty' <- zonkTcType (varType var)
                   ; return (setVarType var ty') }


zonkWC :: EvBindsVar -- May add new bindings for wanted family equalities in here
       -> WantedConstraints -> TcM WantedConstraints
zonkWC binds_var wc
  = do { untch <- getUntouchables
       ; zonkWCRec binds_var untch wc }

zonkWCRec :: EvBindsVar
          -> Untouchables
          -> WantedConstraints -> TcM WantedConstraints
zonkWCRec binds_var untch (WC { wc_flat = flat, wc_impl = implic, wc_insol = insol })
  = do { flat'   <- zonkFlats binds_var untch flat
       ; implic' <- flatMapBagM zonkImplication implic
       ; insol'  <- zonkCts insol -- No need to do the more elaborate zonkFlats thing
       ; return (WC { wc_flat = flat', wc_impl = implic', wc_insol = insol' }) }

zonkFlats :: EvBindsVar -> Untouchables -> Cts -> TcM Cts
-- This zonks and unflattens a bunch of flat constraints
-- See Note [Unflattening while zonking]
zonkFlats binds_var untch cts
  = do { -- See Note [How to unflatten]
         cts <- foldrBagM unflatten_one emptyCts cts
       ; zonkCts cts }
  where
    unflatten_one orig_ct cts
      = do { zct <- zonkCt orig_ct                -- First we need to fully zonk 
           ; mct <- try_zonk_fun_eq orig_ct zct   -- Then try to solve if family equation
           ; return $ maybe cts (`consBag` cts) mct }

    try_zonk_fun_eq orig_ct zct   -- See Note [How to unflatten]
      | EqPred ty_lhs ty_rhs <- classifyPredType (ctPred zct)
          -- NB: zonking de-classifies the constraint,
          --     so we can't look for CFunEqCan
      , Just tv <- getTyVar_maybe ty_rhs
      , ASSERT2( not (isFloatedTouchableMetaTyVar untch tv), ppr tv )
        isTouchableMetaTyVar untch tv
      , not (isSigTyVar tv) || isTyVarTy ty_lhs     -- Never unify a SigTyVar with a non-tyvar
      , typeKind ty_lhs `tcEqKind` tyVarKind tv  -- c.f. TcInteract.trySpontaneousEqOneWay
      , not (tv `elemVarSet` tyCoVarsOfType ty_lhs)   -- Do not construct an infinite type
      = ASSERT2( case tcSplitTyConApp_maybe ty_lhs of { Just (tc,_) -> isSynFamilyTyCon tc; _ -> False }, ppr orig_ct )
        do { writeMetaTyVar tv ty_lhs
           ; let evterm = EvCoercion (mkTcNomReflCo ty_lhs)
                 evvar  = ctev_evar (cc_ev zct)
           ; when (isWantedCt orig_ct) $         -- Can be derived (Trac #8129)
             addTcEvBind binds_var evvar evterm
           ; traceTc "zonkFlats/unflattening" $
             vcat [ text "zct = " <+> ppr zct,
                    text "binds_var = " <+> ppr binds_var ]
           ; return Nothing }
      | otherwise
      = return (Just zct)
\end{code}

Note [Unflattening while zonking]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A bunch of wanted constraints could contain wanted equations of the form
(F taus ~ alpha) where alpha is either an ordinary unification variable, or
a flatten unification variable.

These are ordinary wanted constraints and can/should be solved by
ordinary unification alpha := F taus. However the constraint solving
algorithm does not do that, as their 'inert' form is F taus ~ alpha.

Hence, we need an extra step to 'unflatten' these equations by
performing unification. This unification, if it happens at the end of
constraint solving, cannot produce any more interactions in the
constraint solver so it is safe to do it as the very very last step.

We choose therefore to do it during zonking, in the function
zonkFlats. This is in analogy to the zonking of given "flatten skolems"
which are eliminated in favor of the underlying type that they are
equal to.

Note that, because we now have to affect *evidence* while zonking
(setting some evidence binds to identities), we have to pass to the
zonkWC function an evidence variable to collect all the extra
variables.

Note [How to unflatten]
~~~~~~~~~~~~~~~~~~~~~~~
How do we unflatten during zonking.  Consider a bunch of flat constraints.
Consider them one by one.  For each such constraint C
  * Zonk C (to apply current substitution)
  * If C is of form F tys ~ alpha, 
       where alpha is touchable
       and   alpha is not mentioned in tys
    then unify alpha := F tys
         and discard C

After processing all the flat constraints, zonk them again to propagate
the inforamtion from later ones to earlier ones.  Eg
  Start:  (F alpha ~ beta, G Int ~ alpha)
  Then we get beta := F alpha
              alpha := G Int
  but we must apply the second unification to the first constraint.


\begin{code}
zonkCts :: Cts -> TcM Cts
zonkCts = mapBagM zonkCt

zonkCt :: Ct -> TcM Ct
zonkCt ct@(CHoleCan { cc_ev = ev })
  = do { ev' <- zonkCtEvidence ev
       ; return $ ct { cc_ev = ev' } }
zonkCt ct
  = do { fl' <- zonkCtEvidence (cc_ev ct)
       ; return (mkNonCanonical fl') }

zonkCtEvidence :: CtEvidence -> TcM CtEvidence
zonkCtEvidence ctev@(CtGiven { ctev_pred = pred }) 
  = do { pred' <- zonkTcType pred
       ; return (ctev { ctev_pred = pred'}) }
zonkCtEvidence ctev@(CtWanted { ctev_pred = pred })
  = do { pred' <- zonkTcType pred
       ; return (ctev { ctev_pred = pred' }) }
zonkCtEvidence ctev@(CtDerived { ctev_pred = pred })
  = do { pred' <- zonkTcType pred
       ; return (ctev { ctev_pred = pred' }) }

zonkSkolemInfo :: SkolemInfo -> TcM SkolemInfo
zonkSkolemInfo (SigSkol cx ty)  = do { ty' <- zonkTcType ty
                                     ; return (SigSkol cx ty') }
zonkSkolemInfo (InferSkol ntys) = do { ntys' <- mapM do_one ntys
                                     ; return (InferSkol ntys') }
  where
    do_one (n, ty) = do { ty' <- zonkTcType ty; return (n, ty') }
zonkSkolemInfo skol_info = return skol_info
\end{code}

%************************************************************************
%*									*
\subsection{Zonking -- the main work-horses: zonkTcType, zonkTcTyVar}
%*									*
%*		For internal use only!					*
%*									*
%************************************************************************

\begin{code}
-- zonkId is used *during* typechecking just to zonk the Id's type
zonkId :: TcId -> TcM TcId
zonkId id
  = do { ty' <- zonkTcType (idType id)
       ; return (Id.setIdType id ty') }

-- | Squeeze out any metavariables around. 
zonkTcType :: TcType -> TcM TcType
zonkTcType ty
  = go ty
  where
    go (TyConApp tc tys) = do tys' <- mapM go tys
                              return (TyConApp tc tys')
                -- Do NOT establish Type invariants, because
                -- doing so is strict in the TyCOn.
                -- See Note [Zonking inside the knot] in TcHsType

    go (LitTy n)         = return (LitTy n)

    go (AppTy fun arg)   = do fun' <- go fun
                              arg' <- go arg
                              return (AppTy fun' arg')
                -- See Note [Zonking inside the knot] in TcHsType

    go (CastTy ty co)    = do ty' <- go ty
                              co' <- go_co co
                              return (CastTy ty' co')

    go (CoercionTy co)   = do co' <- go_co co
                              return (CoercionTy co')

	-- The two interesting cases!
    go (TyVarTy tyvar) | isTcTyVar tyvar = zonkTcTyCoVar tyvar
		       | otherwise	 = TyVarTy <$> updateTyVarKindM go tyvar
		-- Ordinary (non Tc) tyvars occur inside quantified types

    go (PiTy bndr ty)
                         = do { bndr' <- zonkTcBinder bndr
                              ; ty' <- go ty
                              ; return (PiTy bndr' ty') }

    go_co (Refl r ty)               = Refl r <$> go ty
    go_co (TyConAppCo r tc args)    = TyConAppCo r tc <$> mapM go_arg args
    go_co (AppCo co arg)            = AppCo <$> go_co co <*> go_arg arg
    go_co (CoVarCo cv)              = CoVarCo <$> zonkTyCoVarKind cv
    go_co (AxiomInstCo ax ind args) = AxiomInstCo ax ind <$> mapM go_arg args
    go_co (PhantomCo h ty1 ty2)     = PhantomCo <$> go_co h <*> go ty1 <*> go ty2
    go_co (UnsafeCo r ty1 ty2)      = UnsafeCo r <$> go ty1 <*> go ty2
    go_co (SymCo co)                = SymCo <$> go_co co
    go_co (TransCo co1 co2)         = TransCo <$> go_co co1 <*> go_co co2
    go_co (NthCo n co)              = NthCo n <$> go_co co
    go_co (LRCo lr co)              = LRCo lr <$> go_co co
    go_co (InstCo co arg)           = InstCo <$> go_co co <*> go_arg arg
    go_co (CoherenceCo co1 co2)     = CoherenceCo <$> go_co co1 <*> go_co co2
    go_co (KindCo co)               = KindCo <$> go_co co
    go_co (SubCo co)                = SubCo <$> go_co co
    go_co (AxiomRuleCo ax ts cs)    = AxiomRuleCo ax <$> mapM go ts <*> mapM go_co cs

    go_co (PiCo cobndr co)
      | Just v <- getHomoBinder_maybe cobndr
      = do { v' <- zonkTcBinder v
           ; co' <- go_co co
           ; return (PiCo (mkHomoCoBndr v') co') }

      | TyHetero h pbndr m_cv <- cobndr
      = do { h' <- go_co h
           ; pbndr' <- zonk_pbndr pbndr
           ; m_cv' <- zonk_maybe m_cv
           ; co' <- go_co co
           ; return (mkPiCo (TyHetero h' pbndr' m_cv') co') }

      | CoHetero h pbndr <- cobndr
      = do { h' <- go_co h
           ; pbndr' <- zonk_pbndr pbndr
           ; co' <- go_co co
           ; return (mkPiCo (CoHetero h' pbndr') co') }

      | otherwise
      = pprPanic "zonkTcType" (ppr cobndr)

      where
        zonk_pbndr pbndr
          = do { let Pair bv1 bv2 = binderPayload pbndr
               ; bv1' <- zonk_bv bv1
               ; bv2' <- zonk_bv bv2
               ; return $ setBinderPayload pbndr (Pair bv1' bv2') }

        zonk_bv bv
          = case getBinderVar_maybe bv of
              Just v  -> mkBinderVar `liftM` zonkTcTyCoVarBndr v
              Nothing -> mkAnonBinderVar `liftM` go (binderVarType bv)

        zonk_maybe (Just cv) = Just `liftM` zonkTcTyCoVarBndr cv
        zonk_maybe Nothing   = return Nothing
                 

    go_arg (TyCoArg co)        = TyCoArg <$> go_co co
    go_arg (CoCoArg r co1 co2) = CoCoArg r <$> go_co co1 <*> go_co co2

zonkTcTyCoVarBndr :: TcTyCoVar -> TcM TcTyCoVar
-- A tyvar binder is never a unification variable (MetaTv),
-- rather it is always a skolems.  BUT it may have a kind 
-- that has not yet been zonked, and may include kind
-- unification variables.
zonkTcTyCoVarBndr tyvar
    -- can't use isCoVar, because it looks at a TyCon. Argh.
  = ASSERT2( isImmutableTyVar tyvar || (not $ isTyVar tyvar), ppr tyvar ) do
    updateTyVarKindM zonkTcType tyvar

-- | Zonk the kind of a binder
zonkTcBinder :: TcBinder -> TcM TcBinder
zonkTcBinder binder
  = updateBinderTypeM zonkTcType binder

zonkTcTyCoVar :: TcTyCoVar -> TcM TcType
-- Simply look through all Flexis
zonkTcTyCoVar tv
  | isTyVar tv
  = ASSERT2( isTcTyVar tv, ppr tv ) do
    case tcTyVarDetails tv of
      SkolemTv {}   -> zonk_kind_and_return
      RuntimeUnk {} -> zonk_kind_and_return
      FlatSkol ty   -> zonkTcType ty
      MetaTv { mtv_ref = ref }
         -> do { cts <- readMutVar ref
               ; case cts of
	            Flexi       -> zonk_kind_and_return
	            Indirect ty -> zonkTcType ty }

  | otherwise -- coercion variable
  = zonk_kind_and_return
  where
    zonk_kind_and_return = do { z_tv <- zonkTyCoVarKind tv
                              ; return (mkTyCoVarTy z_tv) }

\end{code}
