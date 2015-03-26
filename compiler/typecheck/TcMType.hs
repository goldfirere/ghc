{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998


Monadic type operations

This module contains monadic operations over types that contain
mutable type variables
-}

{-# LANGUAGE CPP #-}

module TcMType (
  TcTyVar, TcKind, TcType, TcTauType, TcThetaType, TcTyVarSet,

  --------------------------------
  -- Creating new mutable type variables
  newFlexiTyVar,
  newFlexiTyVarTy,              -- Kind -> TcM TcType
  newFlexiTyVarTys,             -- Int -> Kind -> TcM [TcType]
  newOpenFlexiTyVarTy,
  newReturnTyVar, newReturnTyVarTy,
  newMaybeReturnTyVarTy,
  newOpenReturnTyVar,
  newMetaKindVar, newMetaKindVars,
  mkTcTyVarName, cloneMetaTyVar, 

  newMetaTyVar, readMetaTyVar, writeMetaTyVar, writeMetaTyVarRef,
  unFillMetaTyVar,
  newMetaDetails, isFilledMetaTyVar, isUnfilledMetaTyVar,

  --------------------------------
  -- Creating new evidence variables
  newEvVar, newEvVars, newEq, newDict,
  emitWantedEvVar, emitWantedEvVars,
  newTcEvBinds, addTcEvBind,
  newSimpleWanted, newSimpleWanteds,

  --------------------------------
  -- Instantiation
  tcInstBinders, tcInstBindersX,
  tcInstTyCoVars, tcInstTyCoVarX, newSigTyVar,
  tcInstType,
  tcInstSkolTyCoVars, tcInstSkolTyCoVarsLoc, tcInstSuperSkolTyCoVarsX,
  tcInstSigTyCoVarsLoc, tcInstSigTyCoVars,
  tcInstSkolType,
  tcSkolDFunType, tcSuperSkolTyCoVars,

  instSkolTyCoVars, freshenTyCoVarBndrs,

  --------------------------------
  -- Zonking and tidying
  zonkTidyTcType, zonkTidyOrigin,
  mkTypeErrorThing,
  tidyEvVar, tidyCt, tidySkolemInfo,
  skolemiseUnboundMetaTyVar,
  zonkTcTyCoVar, zonkTcTyCoVars, zonkTyCoVarsAndFV, zonkTcTypeAndFV,
  zonkQuantifiedTyCoVar, zonkQuantifiedTyCoVarOrType, quantifyTyCoVars,
  defaultKindVar,
  zonkTcTyCoVarBndr, zonkTcType, zonkTcTypes, zonkCo,
  zonkTyCoVarKind, zonkTcTypeMapper,

  zonkEvVar, zonkWC, zonkSimples, zonkId, zonkCt, zonkSkolemInfo,

  tcGetGlobalTyVars,

  --------------------------------
  -- (Named) Wildcards
  newWildcardVar, newWildcardVarMetaKind
  ) where

#include "HsVersions.h"

-- friends:
import TcType
import Type
import Coercion
import Class
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
import BasicTypes    ( Boxity(..) )

import Control.Monad
import Data.List        ( mapAccumL, partition, foldl' )

{-
************************************************************************
*                                                                      *
        Kind variables
*                                                                      *
************************************************************************
-}

mkKindName :: Unique -> Name
mkKindName unique = mkSystemName unique kind_var_occ

kind_var_occ :: OccName -- Just one for all MetaKindVars
                        -- They may be jiggled by tidying
kind_var_occ = mkOccName tvName "k"

newMetaKindVar :: TcM TcKind
newMetaKindVar = do { uniq <- newUnique
                    ; details <- newMetaDetails (TauTv False)
                    ; let kv = mkTcTyVar (mkKindName uniq) liftedTypeKind details
                    ; return (mkOnlyTyVarTy kv) }

newMetaKindVars :: Int -> TcM [TcKind]
newMetaKindVars n = mapM (\ _ -> newMetaKindVar) (nOfThem n ())

{-
************************************************************************
*                                                                      *
     Evidence variables; range over constraints we can abstract over
*                                                                      *
************************************************************************
-}

newEvVars :: TcThetaType -> TcM [EvVar]
newEvVars theta = mapM newEvVar theta

--------------

newEvVar :: TcPredType -> TcRnIf gbl lcl EvVar
-- Creates new *rigid* variables for predicates
newEvVar ty = do { name <- newSysName (predTypeOccName ty) 
                 ; return (mkLocalIdOrCoVar name ty) }

-- | Creates a new EvVar and immediately emits it as a Wanted
emitWantedEvVar :: CtOrigin -> TcPredType -> TcM EvVar
emitWantedEvVar origin ty
  = do { new_cv <- newEvVar ty
       ; loc <- getCtLoc origin
       ; let ctev = CtWanted { ctev_evar = new_cv
                             , ctev_pred = ty
                             , ctev_loc  = loc }
       ; emitSimple $ mkNonCanonical ctev
       ; return new_cv }

emitWantedEvVars :: CtOrigin -> [TcPredType] -> TcM [EvVar]
emitWantedEvVars orig = mapM (emitWantedEvVar orig)

newEq :: TcType -> TcType -> TcM EvVar
newEq ty1 ty2
  = do { name <- newSysName (mkVarOccFS (fsLit "cobox"))
       ; return (mkLocalCoVar name (mkPrimEqPred ty1 ty2)) }

newDict :: Class -> [TcType] -> TcM DictId
newDict cls tys 
  = do { name <- newSysName (mkDictOcc (getOccName cls))
       ; return (mkLocalId name (mkClassPred cls tys)) }

predTypeOccName :: PredType -> OccName
predTypeOccName ty = case classifyPredType ty of
    ClassPred cls _ -> mkDictOcc (getOccName cls)
    EqPred _ _ _    -> mkVarOccFS (fsLit "cobox")
    TuplePred _     -> mkVarOccFS (fsLit "tup")
    IrredPred _     -> mkVarOccFS (fsLit "irred")

{-
*********************************************************************************
*                                                                               * 
*                   Wanted constraints
*                                                                               *
*********************************************************************************
-}

newSimpleWanted :: CtOrigin -> PredType -> TcM Ct
newSimpleWanted orig pty
  = do loc <- getCtLoc orig
       v <- newEvVar pty
       return $ mkNonCanonical $
            CtWanted { ctev_evar = v
                     , ctev_pred = pty
                     , ctev_loc = loc }

newSimpleWanteds :: CtOrigin -> ThetaType -> TcM [Ct]
newSimpleWanteds orig = mapM (newSimpleWanted orig)

{-
************************************************************************
*                                                                      *
        SkolemTvs (immutable)
*                                                                      *
************************************************************************
-}

tcInstType :: ([TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])) -- How to instantiate the type variables
           -> TcType                                     -- Type to instantiate
           -> TcM ([TcTyCoVar], TcThetaType, TcType)     -- Result
                -- (type vars (excl coercion vars), preds (incl equalities), rho)
tcInstType inst_tyvars ty
  = case tcSplitNamedForAllTys ty of
        ([],    rho) -> let     -- There may be overloading despite no type variables;
                                --      (?x :: Int) => Int -> Int
                                (theta, tau) = tcSplitPhiTy rho
                            in
                            return ([], theta, tau)

        (tyvars, rho) -> do { (subst, tyvars') <- inst_tyvars tyvars
                            ; let (theta, tau) = tcSplitPhiTy (substTy subst rho)
                            ; return (tyvars', theta, tau) }

tcSkolDFunType :: Type -> TcM ([TcTyVar], TcThetaType, TcType)
-- Instantiate a type signature with skolem constants.
-- We could give them fresh names, but no need to do so
tcSkolDFunType ty = tcInstType tcInstSuperSkolTyCoVars ty

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

-- Wrappers
-- we need to be able to do this from outside the TcM monad:
tcInstSkolTyCoVarsLoc :: SrcSpan -> [TyCoVar] -> TcRnIf gbl lcl (TCvSubst, [TcTyCoVar])
tcInstSkolTyCoVarsLoc loc = instSkolTyCoVars (mkTcSkolTyCoVar loc False)

tcInstSkolTyCoVars :: [TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])
tcInstSkolTyCoVars = tcInstSkolTyCoVars' False emptyTCvSubst

tcInstSuperSkolTyCoVars :: [TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])
tcInstSuperSkolTyCoVars = tcInstSuperSkolTyCoVarsX emptyTCvSubst

tcInstSuperSkolTyCoVarsX :: TCvSubst -> [TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])
tcInstSuperSkolTyCoVarsX subst = tcInstSkolTyCoVars' True subst

tcInstSkolTyCoVars' :: Bool -> TCvSubst -> [TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])
-- Precondition: tyvars should be ordered (kind vars first)
-- see Note [Kind substitution when instantiating]
-- Get the location from the monad; this is a complete freshening operation
tcInstSkolTyCoVars' overlappable subst tvs
  = do { loc <- getSrcSpanM
       ; instSkolTyCoVarsX (mkTcSkolTyCoVar loc overlappable) subst tvs }

mkTcSkolTyCoVar :: SrcSpan -> Bool -> Unique -> Name -> Kind -> TcTyCoVar
mkTcSkolTyCoVar loc overlappable uniq old_name kind
  | isCoercionType kind
  = mkLocalCoVar (mkSystemNameAt uniq (getOccName old_name) loc) kind

  | otherwise
  = mkTcTyVar (mkInternalName uniq (getOccName old_name) loc)
              kind
              (SkolemTv overlappable)

tcInstSigTyCoVarsLoc :: SrcSpan -> [TyCoVar]
                     -> TcRnIf gbl lcl (TCvSubst, [TcTyCoVar])
-- We specify the location
tcInstSigTyCoVarsLoc loc = instSkolTyCoVars (mkTcSkolTyCoVar loc False)

tcInstSigTyCoVars :: [TyCoVar] -> TcRnIf gbl lcl (TCvSubst, [TcTyCoVar])
-- Get the location from the TyVar itself, not the monad
tcInstSigTyCoVars
  = instSkolTyCoVars mk_tcv
  where
    mk_tcv uniq old_name kind
       | isCoercionType kind
       = mkLocalCoVar (setNameUnique old_name uniq) kind

       | otherwise
       = mkTcTyVar (setNameUnique old_name uniq) kind (SkolemTv False)

tcInstSkolType :: TcType -> TcM ([TcTyCoVar], TcThetaType, TcType)
-- Instantiate a type with fresh skolem constants
-- Binding location comes from the monad
tcInstSkolType ty = tcInstType tcInstSkolTyCoVars ty

------------------
freshenTyCoVarBndrs :: [TyCoVar] -> TcRnIf gbl lcl (TCvSubst, [TyCoVar])
-- ^ Give fresh uniques to a bunch of TyVars, but they stay
--   as TyVars, rather than becoming TcTyVars
-- Used in FamInst.newFamInst, and Inst.newClsInst
freshenTyCoVarBndrs = instSkolTyCoVars mk_tcv
  where
    mk_tcv uniq old_name kind
      | isCoercionType kind = mkCoVar (setNameUnique old_name uniq) kind
      | otherwise           = mkTyVar (setNameUnique old_name uniq) kind

------------------
instSkolTyCoVars :: (Unique -> Name -> Kind -> TyCoVar)
                 -> [TyVar] -> TcRnIf gbl lcl (TCvSubst, [TyCoVar])
instSkolTyCoVars mk_tcv = instSkolTyCoVarsX mk_tcv emptyTCvSubst

instSkolTyCoVarsX :: (Unique -> Name -> Kind -> TyCoVar)
                  -> TCvSubst -> [TyCoVar] -> TcRnIf gbl lcl (TCvSubst, [TyCoVar])
instSkolTyCoVarsX mk_tcv = mapAccumLM (instSkolTyCoVarX mk_tcv)

instSkolTyCoVarX :: (Unique -> Name -> Kind -> TyCoVar)
                 -> TCvSubst -> TyCoVar -> TcRnIf gbl lcl (TCvSubst, TyCoVar)
instSkolTyCoVarX mk_tcv subst tycovar
  = do  { uniq <- newUnique
        ; let new_tv = mk_tcv uniq old_name kind
        ; return (extendTCvSubst subst tycovar (mkTyCoVarTy new_tv), new_tv) }
  where
    old_name = tyVarName tycovar
    kind     = substTy subst (tyVarKind tycovar)

{-
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


************************************************************************
*                                                                      *
        MetaTvs (meta type variables; mutable)
*                                                                      *
************************************************************************
-}

newMetaTyVar :: MetaInfo -> Kind -> TcM TcTyVar
-- Make a new meta tyvar out of thin air
newMetaTyVar meta_info kind
  = do  { uniq <- newUnique
        ; let name = mkTcTyVarName uniq s
              s = case meta_info of
                        ReturnTv    -> fsLit "r"
                        TauTv True  -> fsLit "w"
                        TauTv False -> fsLit "t"
                        FlatMetaTv  -> fsLit "fmv"
                        SigTv       -> fsLit "a"
        ; details <- newMetaDetails meta_info
        ; return (mkTcTyVar name kind details) }

newNamedMetaTyVar :: Name -> MetaInfo -> Kind -> TcM TcTyVar
-- Make a new meta tyvar out of thin air
newNamedMetaTyVar name meta_info kind
  = do { details <- newMetaDetails meta_info
       ; return (mkTcTyVar name kind details) }

newSigTyVar :: Name -> Kind -> TcM TcTyVar
newSigTyVar name kind
  = do { details <- newMetaDetails SigTv
       ; return (mkTcTyVar name kind details) }

newMetaDetails :: MetaInfo -> TcM TcTyVarDetails
newMetaDetails info
  = do { ref <- newMutVar Flexi
       ; tclvl <- getTcLevel
       ; return (MetaTv { mtv_info = info, mtv_ref = ref, mtv_tclvl = tclvl }) }

cloneMetaTyVar :: TcTyVar -> TcM TcTyVar
cloneMetaTyVar tv
  = ASSERT( isTcTyVar tv )
    do  { uniq <- newUnique
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
  | MetaTv { mtv_ref = ref } <- tcTyVarDetails tv
  = do  { details <- readMutVar ref
        ; return (isIndirect details) }
  | otherwise = return False

isUnfilledMetaTyVar :: TyVar -> TcM Bool
-- True of a un-filled-in (Flexi) meta type variable
isUnfilledMetaTyVar tv
  | MetaTv { mtv_ref = ref } <- tcTyVarDetails tv
  = do  { details <- readMutVar ref
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
       ; writeTcRef ref (Indirect ty) }

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

-- | Wipes out the contents of a metatyvar, returning the wiped value
unFillMetaTyVar :: TcTyVar -> TcM TcType
unFillMetaTyVar tyvar
  = case tcTyVarDetails tyvar of
      MetaTv { mtv_ref = ref } ->
        do { cts <- readTcRef ref
           ; case cts of
               Indirect ty ->
                 do { traceTc "unFillMetaTyVar" (ppr tyvar <+> dcolon <+>
                                                 ppr (tyVarKind tyvar) <+>
                                                 text "/:=" <+> ppr ty)
                    ; writeTcRef ref Flexi
                    ; return ty }
               Flexi -> pprPanic "unFillMetaTyVar unfilled var" (ppr tyvar) }
      _ -> pprPanic "unFillMetaTyVar non-meta-tyvar" (ppr tyvar)
               
{-
************************************************************************
*                                                                      *
        MetaTvs: TauTvs
*                                                                      *
************************************************************************

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

Note [Never need to instantiate coercion variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
With coercion variables sloshing around in types, it might seem that we
sometimes need to instantiate coercion variables. This would be problematic,
because coercion variables inhabit unboxed equality (~#), and the constraint
solver thinks in terms only of boxed equality (~). The solution is that
we never need to instantiate coercion variables in the first place.

The tyvars that we need to instantiate come from the types of functions,
data constructors, and patterns. These will never be quantified over
coercion variables, except for the special case of the promoted Eq#. But,
that can't ever appear in user code, so we're safe!
-}

newFlexiTyVar :: Kind -> TcM TcTyVar
newFlexiTyVar kind = newMetaTyVar (TauTv False) kind

newFlexiTyVarTy  :: Kind -> TcM TcType
newFlexiTyVarTy kind = do
    tc_tyvar <- newFlexiTyVar kind
    return (mkOnlyTyVarTy tc_tyvar)

newFlexiTyVarTys :: Int -> Kind -> TcM [TcType]
newFlexiTyVarTys n kind = mapM newFlexiTyVarTy (nOfThem n kind)

newReturnTyVar :: Kind -> TcM TcTyVar
newReturnTyVar kind = newMetaTyVar ReturnTv kind

newReturnTyVarTy :: Kind -> TcM TcType
newReturnTyVarTy kind = mkOnlyTyVarTy <$> newReturnTyVar kind

-- | Either makes a normal Flexi or a ReturnTv Flexi
newMaybeReturnTyVarTy :: Bool  -- True <=> make a ReturnTv
                      -> Kind -> TcM TcType
newMaybeReturnTyVarTy True  = newReturnTyVarTy
newMaybeReturnTyVarTy False = newFlexiTyVarTy

-- | Create a tyvar that can be a lifted or unlifted type.
newOpenFlexiTyVarTy :: TcM TcType
newOpenFlexiTyVarTy
  = do { lev <- newFlexiTyVarTy levityTy
       ; newFlexiTyVarTy (tYPE lev) }

-- | Create a *return* tyvar that can be a lifted or unlifted type.
newOpenReturnTyVar :: TcM (TcTyVar, TcKind)
newOpenReturnTyVar
  = do { lev <- newFlexiTyVarTy levityTy  -- this doesn't need ReturnTv
       ; let k = tYPE lev
       ; tv <- newReturnTyVar k
       ; return (tv, k) }

-- TODO (RAE): This, and all call sites, will need to be updated when
-- there's more visibility stuff. Should probably take a list of binders
-- and args. Or something.
tcInstTyCoVars :: TypeOrKind -> [TyCoVar] -> TcM (TCvSubst, [TcTyCoVar])
-- Instantiate with META type variables
-- Note that this works for a sequence of kind, type, and coercion variables
-- variables.  Eg    [ (k:*), (a:k->k) ]
--             Gives [ (k7:*), (a8:k7->k7) ]
tcInstTyCoVars t_or_k = mapAccumLM (tcInstTyCoVarX t_or_k) emptyTCvSubst
    -- emptyTCvSubst has an empty in-scope set, but that's fine here
    -- Since the tyvars are freshly made, they cannot possibly be
    -- captured by any existing for-alls.

tcInstTyCoVarX :: TypeOrKind -> TCvSubst -> TyCoVar -> TcM (TCvSubst, TcTyCoVar)
-- Make a new unification variable tyvar whose Name and Kind come from
-- an existing TyVar. We substitute kind variables in the kind.
tcInstTyCoVarX t_or_k subst tyvar
  | isTyVar tyvar
  = do  { uniq <- newUnique
               -- See Note [    -- TODO (RAE): Finish this line of comment!
               -- TODO (RAE): See Note [OpenTypeKind accepts foralls] in TcType,
               -- but then delete that note
        ; let info = if isSortPolymorphic (tyVarKind tyvar)
                     then ReturnTv
                     else TauTv False
        ; details <- newMetaDetails info
        ; let name   = mkSystemName uniq (getOccName tyvar)
              kind   = substTy subst (tyVarKind tyvar)
              new_tv = mkTcTyVar name kind details
        ; return (extendTCvSubst subst tyvar (mkOnlyTyVarTy new_tv), new_tv) }
  | otherwise
  = do { let pred_ty    = substTy subst (varType tyvar)
             (act, exp) = getEqPredTys pred_ty
             origin     = TypeEqOrigin { uo_actual   = exp
                                       , uo_expected = act
                                       , uo_thing    = Nothing
                                       , uo_level    = t_or_k }
       ; new_cv <- emitWantedEvVar origin pred_ty
         -- can't call unifyType, because we need to return a CoVar,
         -- and unification might result in a TcCoercion that's not a CoVar
         -- See Note [Coercion variables in tcInstTyCoVarX]
         -- TODO (RAE): Improve now that unifyType *can* return a Coercion??

       ; return (extendTCvSubst subst tyvar (mkTyCoVarTy new_cv), new_cv) }

-- | This is used to instantiate binders when type-checking *types* only.
-- Precondition: all binders are invisible.
tcInstBinders :: [Binder] -> TcM (TCvSubst, [TcType])
tcInstBinders = tcInstBindersX emptyTCvSubst

-- | This is used to instantiate binders when type-checking *types* only.
-- Precondition: all binders are invisible.
tcInstBindersX :: TCvSubst -> [Binder] -> TcM (TCvSubst, [TcType])
tcInstBindersX subst bndrs
  = do { (subst, args) <- mapAccumLM tcInstBinderX subst bndrs
       ; traceTc "instantiating implicit dependent vars:"
           (vcat $ zipWith (\bndr arg -> ppr bndr <+> text ":=" <+> ppr arg)
                           bndrs args)
       ; return (subst, args) }

-- | Used only in *types*
tcInstBinderX :: TCvSubst -> Binder -> TcM (TCvSubst, TcType)
tcInstBinderX subst binder
  | Just tv <- binderVar_maybe binder
  = do { (subst', tv') <- tcInstTyCoVarX KindLevel subst tv
       ; return (subst', mkTyCoVarTy tv') }

     -- TODO (RAE): This is special-case handling of promoted, lifted
     -- equality. This is the *only* constraint currently handled in
     -- types. The special-casing makes me sad. Improve.
  | let ty = substTy subst (binderType binder)
  , Just (boxity, role, k1, k2) <- getEqPredTys_maybe ty
  = ASSERT( boxity == Boxed )   -- unboxed equality is always dependent
    do { let origin = TypeEqOrigin { uo_actual   = k1
                                   , uo_expected = k2
                                   , uo_thing    = Nothing
                                   , uo_level    = KindLevel }
       ; cv <- emitWantedEvVar origin (mkPrimEqPredRole role k1 k2)
       ; let arg' = mkEqBoxTy (mkCoVarCo cv)
       ; return (subst, arg') }

  | otherwise
  = pprPanic "visible binder in tcInstBinderX" (ppr binder)

{-
************************************************************************
*                                                                      *
             Quantification
*                                                                      *
************************************************************************

Note [quantifyTyCoVars]
~~~~~~~~~~~~~~~~~~~~~~~
TODO (RAE): Update Note.
quantifyTyCoVars is give the free vars of a type that we
are about to wrap in a forall.

It takes these free type/kind variables and 
  1. Zonks them and remove globals
  2. Partitions into type and kind variables (kvs1, tvs) (removing covars)
  3. Extends kvs1 with free kind vars in the kinds of tvs (removing globals)
  4. Calls zonkQuantifiedTyVar on each

Step (3) is often unimportant, because the kind variable is often
also free in the type.  Eg
     Typeable k (a::k)
has free vars {k,a}.  But the type (see Trac #7916)
    (f::k->*) (a::k)
has free vars {f,a}, but we must add 'k' as well! Hence step (3).

Note that this function can accept covars, but will never return them.
This is because we never want to infer a quantified covar!
-}

quantifyTyCoVars :: CvSubstEnv     -- any known values for covars
                 -> TcTyCoVarSet   -- global tvs
                 -> ( TcTyCoVarSet     -- dependent tvs       We only distinguish
                    , TcTyCoVarSet )   -- nondependent tvs    between these for
                                       --                     -XNoPolyKinds
                 -> TcM [TcTyCoVar]
-- See Note [quantifyTyCoVars]
-- Can be given a mixture of TcTyVars and TyVars, in the case of
--   associated type declarations

quantifyTyCoVars co_env gbl_tvs (dep_tkvs, nondep_tkvs)
  = do { dep_tkvs    <- apply_co_env <$> zonkTyCoVarsAndFV dep_tkvs
       ; nondep_tkvs <- (`minusVarSet` dep_tkvs) . apply_co_env <$>
                        zonkTyCoVarsAndFV nondep_tkvs
       ; gbl_tvs     <- apply_co_env <$> zonkTyCoVarsAndFV gbl_tvs

       ; let dep_kvs    = varSetElemsWellScoped $
                          dep_tkvs `minusVarSet` gbl_tvs
             nondep_tvs = varSetElemsWellScoped $
                          nondep_tkvs `minusVarSet` gbl_tvs

                          -- NB kinds of tvs are zonked by zonkTyCoVarsAndFV

             -- In the non-PolyKinds case, default the kind variables
             -- to *, and zonk the tyvars as usual.  Notice that this
             -- may make quantifyTyCoVars return a shorter list
             -- than it was passed, but that's ok
       ; poly_kinds <- xoptM Opt_PolyKinds
       ; dep_vars2 <- if poly_kinds
                      then return dep_kvs
                      else do { let (meta_kvs, skolem_kvs) = partition is_meta dep_kvs
                                    is_meta kv = isTcTyVar kv && isMetaTyVar kv
                              
                              ; mapM_ defaultKindVar meta_kvs
                              ; return skolem_kvs }  -- should be empty

       ; let quant_vars1 = dep_vars2 ++ nondep_tvs
             quant_vars2 = reverse $ foldl' quant_pred_telescope [] quant_vars1

       ; traceTc "quantifyTyCoVars"
           (vcat [ text "globals:" <+> ppr gbl_tvs
                 , text "nondep:" <+> ppr nondep_tvs
                 , text "dep:" <+> ppr dep_kvs
                 , text "dep2:" <+> ppr dep_vars2
                 , text "quant_vars1:" <+> ppr quant_vars1
                 , text "quant_vars2:" <+> ppr quant_vars2 ])
             
       ; mapMaybeM zonk_quant quant_vars2 }
           -- Because of the order, any kind variables
           -- mentioned in the kinds of the type variables refer to
           -- the now-quantified versions
  where
    -- Given a telescope of tyvars, filter out any that shouldn't
    -- be quantified over, by applying the quantifyPred test. This
    -- always passes proper TyVars through unchanged -- only affects
    -- CoVars.
    quant_pred_telescope :: [TcTyCoVar]   -- will quantify over (reversed)
                         -> TcTyCoVar     -- check this var
                         -> [TcTyCoVar]   -- combined list (reversed)
    quant_pred_telescope qtvs tcv
      |  isTyVar tcv
      || quantifyPred (mkVarSet qtvs) (varType tcv)
      =  tcv : qtvs
         
      |  otherwise
      =  qtvs
    
    zonk_quant tkv
      | isTcTyCoVar tkv = zonkQuantifiedTyCoVar tkv
      | otherwise       = return $ Just tkv
      -- For associated types, we have the class variables 
      -- in scope, and they are TyVars not TcTyVars

    apply_co_env = foldVarSet apply_co_env1 emptyVarSet
    apply_co_env1 v acc
      | Just co <- lookupVarEnv co_env v
      = acc `unionVarSet` tyCoVarsOfCo co
      | otherwise
      = acc `extendVarSet` v

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
  = case tcTyVarDetails tv of
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
-- Skolemise it, so that
--   we are totally out of Meta-tyvar-land
-- We create a skolem TyVar, not a regular TyVar
--   See Note [Zonking to Skolem]
skolemiseUnboundMetaTyVar tv details
  = ASSERT2( isMetaTyVar tv, ppr tv ) 
    do  { span <- getSrcSpanM    -- Get the location from "here"
                                 -- ie where we are generalising
        ; kind <- zonkTcType (tyVarKind tv)
        ; let tv_name     = getOccName tv
              tv_uniq     = getUnique tv
              new_tv_name = if isWildcardVar tv
                            then generaliseWildcardVarName tv_name
                            else tv_name

                -- NB: Use same Unique as original tyvar. This is
                -- important for TcHsType.splitTelescopeTvs to work properly
              final_name = mkInternalName tv_uniq new_tv_name span
              final_tv   = mkTcTyVar final_name kind details

        ; traceTc "Skolemising" (ppr tv <+> ptext (sLit ":=") <+> ppr final_tv)
        ; writeMetaTyVar tv (mkTyCoVarTy final_tv)
        ; return final_tv }
  where
    -- If a wildcard type called _a is generalised, we rename it to tw_a
    generaliseWildcardVarName :: OccName -> OccName
    generaliseWildcardVarName name | startsWithUnderscore name
      = mkOccNameFS (occNameSpace name) (appendFS (fsLit "w") (occNameFS name))
    generaliseWildcardVarName name = name

{-
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
        type C u a = u  -- Note 'a' unused

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

************************************************************************
*                                                                      *
              Zonking types
*                                                                      *
************************************************************************

@tcGetGlobalTyVars@ returns a fully-zonked set of tyvars free in the environment.
To improve subsequent calls to the same function it writes the zonked set back into
the environment.
-}

tcGetGlobalTyVars :: TcM TcTyVarSet
tcGetGlobalTyVars
  = do { (TcLclEnv {tcl_tyvars = gtv_var}) <- getLclEnv
       ; gbl_tvs  <- readMutVar gtv_var
       ; gbl_tvs' <- zonkTyCoVarsAndFV gbl_tvs
       ; writeMutVar gtv_var gbl_tvs'
       ; return gbl_tvs' }
  where

zonkTcTypeAndFV :: TcType -> TcM TyCoVarSet
-- Zonk a type and take its free variables
-- With kind polymorphism it can be essential to zonk *first*
-- so that we find the right set of free variables.  Eg
--    forall k1. forall (a:k2). a
-- where k2:=k1 is in the substitution.  We don't want
-- k2 to look free in this type!
-- NB: This might be called from within the knot, so don't use
-- smart constructors. See Note [Zonking within the knot] in TcHsType
zonkTcTypeAndFV ty
  = tyCoVarsOfType <$> mapType (zonkTcTypeMapper { tcm_smart = False }) () ty
    
zonkTyCoVar :: TyCoVar -> TcM TcType
-- Works on TyVars and TcTyVars
zonkTyCoVar tv | isTcTyVar tv = zonkTcTyCoVar tv
               | otherwise    = mkTyCoVarTy <$> zonkTyCoVarKind tv
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

{-
************************************************************************
*                                                                      *
              Zonking constraints
*                                                                      *
************************************************************************
-}

zonkImplication :: Implication -> TcM (Bag Implication)
zonkImplication implic@(Implic { ic_skols  = skols
                               , ic_given  = given
                               , ic_wanted = wanted
                               , ic_info   = info })
  = do { skols'  <- mapM zonkTcTyCoVarBndr skols  -- Need to zonk their kinds!
                                                  -- as Trac #7230 showed
       ; given'  <- mapM zonkEvVar given
       ; info'   <- zonkSkolemInfo info
       ; wanted' <- zonkWCRec wanted
       ; if isEmptyWC wanted'
         then return emptyBag
         else return $ unitBag $
              implic { ic_skols  = skols'
                     , ic_given  = given'
                     , ic_wanted = wanted'
                     , ic_info   = info' } }

zonkEvVar :: EvVar -> TcM EvVar
zonkEvVar var = do { ty' <- zonkTcType (varType var)
                   ; return (setVarType var ty') }


zonkWC :: WantedConstraints -> TcM WantedConstraints
zonkWC wc = zonkWCRec wc

zonkWCRec :: WantedConstraints -> TcM WantedConstraints
zonkWCRec (WC { wc_simple = simple, wc_impl = implic, wc_insol = insol })
  = do { simple' <- zonkSimples simple
       ; implic' <- flatMapBagM zonkImplication implic
       ; insol'  <- zonkSimples insol
       ; return (WC { wc_simple = simple', wc_impl = implic', wc_insol = insol' }) }

zonkSimples :: Cts -> TcM Cts
zonkSimples cts = do { cts' <- mapBagM zonkCt' cts
                     ; traceTc "zonkSimples done:" (ppr cts')
                     ; return cts' }

zonkCt' :: Ct -> TcM Ct
zonkCt' ct = zonkCt ct

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
zonkCtEvidence ctev@(CtWanted { ctev_pred = pred, ctev_evar = ev })
  = do { pred' <- zonkTcType pred
       ; let ev' = setVarType ev pred'  -- necessary in simplifyInfer
       ; return (ctev { ctev_pred = pred', ctev_evar = ev' }) }
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

{-
%************************************************************************
%*                                                                      *
\subsection{Zonking -- the main work-horses: zonkTcType, zonkTcTyVar}
*                                                                      *
*              For internal use only!                                  *
*                                                                      *
************************************************************************

-}

-- zonkId is used *during* typechecking just to zonk the Id's type
zonkId :: TcId -> TcM TcId
zonkId id
  = do { ty' <- zonkTcType (idType id)
       ; return (Id.setIdType id ty') }

-- | A suitable TyCoMapper for zonking a type inside the knot, and
-- before all metavars are filled in.
zonkTcTypeMapper :: TyCoMapper () TcM
zonkTcTypeMapper = TyCoMapper
-- TODO (RAE): Remove tcm_smart and zonkSigType.
  { tcm_smart = True
                -- Do NOT establish Type invariants, because
                -- doing so is strict in the TyCOn.
                -- See Note [Zonking inside the knot] in TcHsType
  , tcm_tyvar = const zonkTcTyCoVar
  , tcm_covar = const (\cv -> mkCoVarCo <$> zonkTyCoVarKind cv)
  , tcm_tycobinder = \_env tv _vis -> do { tv' <- zonkTcTyCoVarBndr tv
                                         ; return ((), tv') } }

-- For unbound, mutable tyvars, zonkType uses the function given to it
-- For tyvars bound at a for-all, zonkType zonks them to an immutable
--      type variable and zonks the kind too
zonkTcType :: TcType -> TcM TcType
zonkTcType = mapType zonkTcTypeMapper ()

-- | "Zonk" a coercion -- really, just zonk any types in the coercion
zonkCo :: Coercion -> TcM Coercion
zonkCo = mapCoercion zonkTcTypeMapper () 

zonkTcTyCoVarBndr :: TcTyCoVar -> TcM TcTyCoVar
-- A tyvar binder is never a unification variable (MetaTv),
-- rather it is always a skolems.  BUT it may have a kind 
-- that has not yet been zonked, and may include kind
-- unification variables.
zonkTcTyCoVarBndr tyvar
    -- can't use isCoVar, because it looks at a TyCon. Argh.
  = ASSERT2( isImmutableTyVar tyvar || (not $ isTyVar tyvar), ppr tyvar ) do
    updateTyVarKindM zonkTcType tyvar

zonkTcTyCoVar :: TcTyCoVar -> TcM TcType
-- Simply look through all Flexis
zonkTcTyCoVar tv
  | isTcTyVar tv
  = case tcTyVarDetails tv of
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

{-
%************************************************************************
%*                                                                      *
                 Tidying
*                                                                      *
************************************************************************
-}

zonkTidyTcType :: TidyEnv -> TcType -> TcM (TidyEnv, TcType)
zonkTidyTcType env ty = do { ty' <- zonkTcType ty
                           ; return (tidyOpenType env ty') }

-- | Make an 'ErrorThing' storing a type.
mkTypeErrorThing :: TcType -> ErrorThing
mkTypeErrorThing ty = ErrorThing ty zonkTidyTcType

zonkTidyOrigin :: TidyEnv -> CtOrigin -> TcM (TidyEnv, CtOrigin)
zonkTidyOrigin env (GivenOrigin skol_info)
  = do { skol_info1 <- zonkSkolemInfo skol_info
       ; let (env1, skol_info2) = tidySkolemInfo env skol_info1
       ; return (env1, GivenOrigin skol_info2) }
zonkTidyOrigin env orig@(TypeEqOrigin { uo_actual   = act
                                      , uo_expected = exp
                                      , uo_thing    = m_thing })
  = do { (env1, act') <- zonkTidyTcType env  act
       ; (env2, exp') <- zonkTidyTcType env1 exp
       ; (env3, m_thing') <- zonkTidyErrorThing env2 m_thing
       ; return ( env3, orig { uo_actual   = act'
                             , uo_expected = exp'
                             , uo_thing    = m_thing' }) }
zonkTidyOrigin env (KindEqOrigin ty1 ty2 orig)
  = do { (env1, ty1') <- zonkTidyTcType env  ty1
       ; (env2, ty2') <- zonkTidyTcType env1 ty2
       ; (env3, orig') <- zonkTidyOrigin env2 orig
       ; return (env3, KindEqOrigin ty1' ty2' orig') }
zonkTidyOrigin env (CoercibleOrigin ty1 ty2)
  = do { (env1, ty1') <- zonkTidyTcType env  ty1
       ; (env2, ty2') <- zonkTidyTcType env1 ty2
       ; return (env2, CoercibleOrigin ty1' ty2') }
zonkTidyOrigin env (FunDepOrigin1 p1 l1 p2 l2)
  = do { (env1, p1') <- zonkTidyTcType env  p1
       ; (env2, p2') <- zonkTidyTcType env1 p2
       ; return (env2, FunDepOrigin1 p1' l1 p2' l2) }
zonkTidyOrigin env (FunDepOrigin2 p1 o1 p2 l2)
  = do { (env1, p1') <- zonkTidyTcType env  p1
       ; (env2, p2') <- zonkTidyTcType env1 p2
       ; (env3, o1') <- zonkTidyOrigin env2 o1
       ; return (env3, FunDepOrigin2 p1' o1' p2' l2) }
zonkTidyOrigin env orig = return (env, orig)

zonkTidyErrorThing :: TidyEnv -> Maybe ErrorThing
                   -> TcM (TidyEnv, Maybe ErrorThing)
zonkTidyErrorThing env (Just (ErrorThing thing zonker))
  = do { (env', thing') <- zonker env thing
       ; return (env', Just $ ErrorThing thing' zonker) }
zonkTidyErrorThing env Nothing
  = return (env, Nothing)

----------------
tidyCt :: TidyEnv -> Ct -> Ct
-- Used only in error reporting
-- Also converts it to non-canonical
tidyCt env ct
  = case ct of
     CHoleCan { cc_ev = ev }
       -> ct { cc_ev = tidy_ev env ev }
     _ -> mkNonCanonical (tidy_ev env (ctEvidence ct))
  where
    tidy_ev :: TidyEnv -> CtEvidence -> CtEvidence
     -- NB: we do not tidy the ctev_evtm/var field because we don't
     --     show it in error messages
    tidy_ev env ctev@(CtGiven { ctev_pred = pred })
      = ctev { ctev_pred = tidyType env pred }
    tidy_ev env ctev@(CtWanted { ctev_pred = pred })
      = ctev { ctev_pred = tidyType env pred }
    tidy_ev env ctev@(CtDerived { ctev_pred = pred })
      = ctev { ctev_pred = tidyType env pred }

----------------
tidyEvVar :: TidyEnv -> EvVar -> EvVar
tidyEvVar env var = setVarType var (tidyType env (varType var))

----------------
tidySkolemInfo :: TidyEnv -> SkolemInfo -> (TidyEnv, SkolemInfo)
tidySkolemInfo env (SigSkol cx ty)
  = (env', SigSkol cx ty')
  where
    (env', ty') = tidyOpenType env ty

tidySkolemInfo env (InferSkol ids)
  = (env', InferSkol ids')
  where
    (env', ids') = mapAccumL do_one env ids
    do_one env (name, ty) = (env', (name, ty'))
       where
         (env', ty') = tidyOpenType env ty

tidySkolemInfo env (UnifyForAllSkol skol_tvs ty)
  = (env1, UnifyForAllSkol skol_tvs' ty')
  where
    env1 = tidyFreeTyCoVars env (tyCoVarsOfType ty `delVarSetList` skol_tvs)
    (env2, skol_tvs') = tidyTyCoVarBndrs env1 skol_tvs
    ty'               = tidyType env2 ty

tidySkolemInfo env info = (env, info)

{-
************************************************************************
*                                                                      *
        (Named) Wildcards
*                                                                      *
************************************************************************
-}

-- | Create a new meta var with the given kind. This meta var should be used
-- to replace a wildcard in a type. Such a wildcard meta var can be
-- distinguished from other meta vars with the 'isWildcardVar' function.
newWildcardVar :: Name -> Kind -> TcM TcTyVar
newWildcardVar name kind = newNamedMetaTyVar name (TauTv True) kind

-- | Create a new meta var (which can unify with a type of any kind). This
-- meta var should be used to replace a wildcard in a type. Such a wildcard
-- meta var can be distinguished from other meta vars with the 'isWildcardVar'
-- function.
newWildcardVarMetaKind :: Name -> TcM TcTyVar
newWildcardVarMetaKind name = do kind <- newMetaKindVar
                                 newWildcardVar name kind

-- | Return 'True' if the argument is a meta var created for a wildcard (by
-- 'newWildcardVar' or 'newWildcardVarMetaKind').
isWildcardVar :: TcTyVar -> Bool
isWildcardVar tv | MetaTv (TauTv True) _ _ <- tcTyVarDetails tv = True
isWildcardVar _ = False
