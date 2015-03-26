{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1993-1998


This module defines interface types and binders
-}

{-# LANGUAGE CPP #-}
module IfaceType (
        IfExtName, IfLclName,

        IfaceType(..), IfacePredType, IfaceKind, IfaceTyCon(..), IfaceCoercion(..),
        IfaceTyLit(..), IfaceTcArgs(..),
        IfaceContext, IfaceBndr(..), IfaceOneShot(..), IfaceLamBndr,
        IfaceTvBndr, IfaceIdBndr,
        IfaceForAllBndr(..), IfaceForAllCoBndr(..), VisibilityFlag(..),

        -- Conversion from Type -> IfaceType
        toIfaceType, toIfaceTypes, toIfaceKind, toIfaceTyVar,
        toIfaceContext, toIfaceBndr, toIfaceIdBndr,
        toIfaceTCvBndrs, toIfaceTyCon, toIfaceTyCon_name,
        toIfaceTcArgs, toIfaceTvBndrs,

        -- Conversion from IfaceTcArgs -> IfaceType
        tcArgsIfaceTypes,

        -- Conversion from Coercion -> IfaceCoercion
        toIfaceCoercion,

        -- Printing
        pprIfaceType, pprParendIfaceType,
        pprIfaceContext, pprIfaceContextArr, pprIfaceContextMaybe,
        pprIfaceIdBndr, pprIfaceLamBndr, pprIfaceTvBndr, pprIfaceTvBndrs,
        pprIfaceBndrs, pprIfaceTcArgs, pprParendIfaceTcArgs,
        pprIfaceForAllPart, pprIfaceForAll, pprIfaceSigmaType,
        pprIfaceCoercion, pprParendIfaceCoercion,
        splitIfaceSigmaTy, pprIfaceTypeApp, pprUserIfaceForAll,

        suppressIfaceInvisibles,
        stripIfaceInvisVars,
        stripInvisArgs,
        substIfaceType, substIfaceTyVar, substIfaceTcArgs, mkIfaceTySubst
    ) where

#include "HsVersions.h"

import Coercion
import DataCon ( dataConTyCon )
import TcType
import DynFlags
import TyCoRep  -- needs to convert core types to iface types
import Unique( hasKey )
import Util ( filterOut, lengthIs, zipWithEqual )
import TyCon hiding ( pprPromotionQuote )
import CoAxiom
import Id
import Var
-- import RnEnv( FastStringEnv, mkFsEnv, lookupFsEnv )
import TysWiredIn
import TysPrim
import PrelNames( funTyConKey, ipClassName )
import Name
import BasicTypes
import Binary
import Outputable
import FastString
import UniqSet
import VarEnv
import Data.Maybe

{-
************************************************************************
*                                                                      *
                Local (nested) binders
*                                                                      *
************************************************************************
-}

type IfLclName = FastString     -- A local name in iface syntax

type IfExtName = Name   -- An External or WiredIn Name can appear in IfaceSyn
                        -- (However Internal or System Names never should)

data IfaceBndr          -- Local (non-top-level) binders
  = IfaceIdBndr {-# UNPACK #-} !IfaceIdBndr
  | IfaceTvBndr {-# UNPACK #-} !IfaceTvBndr

type IfaceIdBndr  = (IfLclName, IfaceType)
type IfaceTvBndr  = (IfLclName, IfaceKind)

data IfaceOneShot    -- see Note [Preserve OneShotInfo]
  = IfaceNoOneShot
  | IfaceOneShot

type IfaceLamBndr
  = (IfaceBndr, IfaceOneShot)

{-
%************************************************************************
%*                                                                      *
                IfaceType
%*                                                                      *
%************************************************************************
-}

-------------------------------
type IfaceKind     = IfaceType

data IfaceType     -- A kind of universal type, used for types and kinds
  = IfaceTyVar    IfLclName               -- Type/coercion variable only, not tycon
  | IfaceAppTy    IfaceType IfaceType
  | IfaceFunTy    IfaceType IfaceType
  | IfaceDFunTy   IfaceType IfaceType
  | IfaceForAllTy IfaceForAllBndr IfaceType
  | IfaceTyConApp IfaceTyCon IfaceTcArgs  -- Not necessarily saturated
                                          -- Includes newtypes, synonyms, tuples
  | IfaceLitTy      IfaceTyLit
  | IfaceCastTy     IfaceType IfaceCoercion
  | IfaceCoercionTy IfaceCoercion

type IfacePredType = IfaceType
type IfaceContext = [IfacePredType]

data IfaceTyLit
  = IfaceNumTyLit Integer
  | IfaceStrTyLit FastString

data IfaceForAllBndr
  = IfaceTv IfaceTvBndr VisibilityFlag
  | IfaceCv IfaceIdBndr

-- See Note [Suppressing invisible arguments]
-- We use a new list type (rather than [(IfaceType,Bool)], because
-- it'll be more compact and faster to parse in interface
-- files. Rather than two bytes and two decisions (nil/cons, and
-- type/kind) there'll just be one.
data IfaceTcArgs
  = ITC_Nil
  | ITC_Vis   IfaceType IfaceTcArgs
  | ITC_Invis IfaceKind IfaceTcArgs

-- Encodes type constructors, kind constructors,
-- coercion constructors, the lot.
-- We have to tag them in order to pretty print them
-- properly.
data IfaceTyCon
  = IfaceTc              { ifaceTyConName :: IfExtName }
  | IfacePromotedDataCon { ifaceTyConName :: IfExtName }

data IfaceCoercion     -- represents Coercions and CoercionArgs
  = IfaceReflCo      Role IfaceType
  | IfaceFunCo       Role IfaceCoercion IfaceCoercion
  | IfaceTyConAppCo  Role IfaceTyCon [IfaceCoercion]
  | IfaceAppCo       IfaceCoercion IfaceCoercion IfaceCoercion
  | IfaceForAllCo    IfaceForAllCoBndr IfaceCoercion
  | IfaceCoVarCo     IfLclName
  | IfaceAxiomInstCo IfExtName BranchIndex [IfaceCoercion]
  | IfacePhantomCo   IfaceCoercion IfaceType IfaceType
  | IfaceUnsafeCo    FastString Role IfaceType IfaceType
  | IfaceSymCo       IfaceCoercion
  | IfaceTransCo     IfaceCoercion IfaceCoercion
  | IfaceNthCo       Int IfaceCoercion
  | IfaceLRCo        LeftOrRight IfaceCoercion
  | IfaceInstCo      IfaceCoercion IfaceCoercion
  | IfaceCoherenceCo IfaceCoercion IfaceCoercion
  | IfaceKindCo      IfaceCoercion
  | IfaceKindAppCo   IfaceCoercion
  | IfaceSubCo       IfaceCoercion
  | IfaceAxiomRuleCo IfLclName [IfaceType] [IfaceCoercion]
  | IfaceCoCoArg     Role IfaceCoercion IfaceCoercion IfaceCoercion

data IfaceForAllCoBndr
  = IfaceCoBndr IfaceCoercion IfaceTvBndr IfaceTvBndr (Maybe IfaceIdBndr)

{-
%************************************************************************
%*                                                                      *
                Functions over IFaceTypes
*                                                                      *
************************************************************************
-}

splitIfaceSigmaTy :: IfaceType -> ([IfaceForAllBndr], [IfacePredType], IfaceType)
-- Mainly for printing purposes
splitIfaceSigmaTy ty
  = (bndrs, theta, tau)
  where
    (bndrs, rho)   = split_foralls ty
    (theta, tau)   = split_rho rho

    split_foralls (IfaceForAllTy bndr ty)
        = case split_foralls ty of { (bndrs, rho) -> (bndr:bndrs, rho) }
    split_foralls rho = ([], rho)

    split_rho (IfaceDFunTy ty1 ty2)
        = case split_rho ty2 of { (ps, tau) -> (ty1:ps, tau) }
    split_rho tau = ([], tau)

suppressIfaceInvisibles :: DynFlags -> [IfaceForAllBndr] -> [a] -> [a]
  -- TODO (RAE): This is wrong just like Type.filterInvisibles
suppressIfaceInvisibles dflags tys xs
  | gopt Opt_PrintExplicitKinds dflags = xs
  | otherwise = suppress tys xs
    where
      suppress _       []      = []
      suppress []      a       = a
      suppress (k:ks) a@(_:xs)
        | isIfaceInvisBndr k = suppress ks xs
        | otherwise          = a

stripIfaceInvisVars :: DynFlags -> [IfaceForAllBndr] -> [IfaceForAllBndr]
stripIfaceInvisVars dflags tyvars
  | gopt Opt_PrintExplicitKinds dflags = tyvars
  | otherwise = filterOut isIfaceInvisBndr tyvars

isIfaceInvisBndr :: IfaceForAllBndr -> Bool
isIfaceInvisBndr (IfaceTv _ Visible) = False
isIfaceInvisBndr _                   = True

ifTyVarsOfType :: IfaceType -> UniqSet IfLclName
ifTyVarsOfType ty
  = case ty of
      IfaceTyVar v -> unitUniqSet v
      IfaceAppTy fun arg
        -> ifTyVarsOfType fun `unionUniqSets` ifTyVarsOfType arg
      IfaceFunTy arg res
        -> ifTyVarsOfType arg `unionUniqSets` ifTyVarsOfType res
      IfaceDFunTy arg res
        -> ifTyVarsOfType arg `unionUniqSets` ifTyVarsOfType res
      IfaceForAllTy bndr ty
        -> let (free, bound) = ifTyVarsOfForAllBndr bndr in
           delListFromUniqSet (ifTyVarsOfType ty) bound `unionUniqSets` free
      IfaceTyConApp _ args -> ifTyVarsOfArgs args
      IfaceLitTy    _      -> emptyUniqSet
      IfaceCastTy ty co
        -> ifTyVarsOfType ty `unionUniqSets` ifTyVarsOfCoercion co
      IfaceCoercionTy co -> ifTyVarsOfCoercion co

ifTyVarsOfForAllBndr :: IfaceForAllBndr
                     -> ( UniqSet IfLclName   -- names used free in the binder
                        , [IfLclName] )       -- names bound by this binder
ifTyVarsOfForAllBndr (IfaceTv (name, kind) _) = (ifTyVarsOfType kind, [name])
ifTyVarsOfForAllBndr (IfaceCv (name, kind))   = (ifTyVarsOfType kind, [name])

ifTyVarsOfForAllCoBndr :: IfaceForAllCoBndr
                       -> ( UniqSet IfLclName
                          , [IfLclName] )
ifTyVarsOfForAllCoBndr (IfaceCoBndr eta (tv1, kind1) (tv2, kind2) m_cv)
  = ( unionManyUniqSets [ ifTyVarsOfCoercion eta
                        , ifTyVarsOfType kind1
                        , ifTyVarsOfType kind2 ]
    , map fst (maybeToList m_cv) ++ [tv1, tv2] )
  -- don't need to check cv's kind because it always mentions just tv1 and tv2

ifTyVarsOfArgs :: IfaceTcArgs -> UniqSet IfLclName
ifTyVarsOfArgs args = argv emptyUniqSet args
   where
     argv vs (ITC_Vis   t ts) = argv (vs `unionUniqSets` (ifTyVarsOfType t)) ts
     argv vs (ITC_Invis k ks) = argv (vs `unionUniqSets` (ifTyVarsOfType k)) ks
     argv vs ITC_Nil          = vs

ifTyVarsOfCoercion :: IfaceCoercion -> UniqSet IfLclName
ifTyVarsOfCoercion = go
  where
    go (IfaceReflCo _ ty)         = ifTyVarsOfType ty
    go (IfaceFunCo _ c1 c2)       = go c1 `unionUniqSets` go c2
    go (IfaceTyConAppCo _ _ cos)  = ifTyVarsOfCoercions cos
    go (IfaceAppCo c1 h c2)       = go c1 `unionUniqSets`
                                    go h `unionUniqSets` go c2
    go (IfaceForAllCo bndr co)
     = let (free, bound) = ifTyVarsOfForAllCoBndr bndr in
        go co `delListFromUniqSet` bound `unionUniqSets` free
    go (IfaceCoVarCo cv)          = unitUniqSet cv
    go (IfaceAxiomInstCo _ _ cos) = ifTyVarsOfCoercions cos
    go (IfacePhantomCo h ty1 ty2) = go h `unionUniqSets`
                                    ifTyVarsOfType ty1 `unionUniqSets`
                                    ifTyVarsOfType ty2
    go (IfaceUnsafeCo _ _ ty1 ty2)
      = ifTyVarsOfType ty1 `unionUniqSets` ifTyVarsOfType ty2
    go (IfaceSymCo co)            = go co
    go (IfaceTransCo c1 c2)       = go c1 `unionUniqSets` go c2
    go (IfaceNthCo _ co)          = go co
    go (IfaceLRCo _ co)           = go co
    go (IfaceInstCo c1 c2)        = go c1 `unionUniqSets` go c2
    go (IfaceCoherenceCo c1 c2)   = go c1 `unionUniqSets` go c2
    go (IfaceKindCo co)           = go co
    go (IfaceKindAppCo co)        = go co
    go (IfaceSubCo co)            = go co
    go (IfaceAxiomRuleCo rule tys cos)
      = unionManyUniqSets
          [ unitUniqSet rule
          , foldr (unionUniqSets . ifTyVarsOfType) emptyUniqSet tys
          , ifTyVarsOfCoercions cos ]
    go (IfaceCoCoArg _ h c1 c2)   = go h `unionUniqSets`
                                    go c1 `unionUniqSets` go c2

ifTyVarsOfCoercions :: [IfaceCoercion] -> UniqSet IfLclName
ifTyVarsOfCoercions = foldr (unionUniqSets . ifTyVarsOfCoercion) emptyUniqSet

{-
Substitutions on IfaceType. This is only used during pretty-printing to construct
the result type of a GADT, and does not deal with binders (eg IfaceForAll), so
it doesn't need fancy capture stuff.
-}

type IfaceTySubst = FastStringEnv IfaceType

mkIfaceTySubst :: [IfaceTvBndr] -> [IfaceType] -> IfaceTySubst
mkIfaceTySubst tvs tys = mkFsEnv $ zipWithEqual "mkIfaceTySubst" (\(fs,_) ty -> (fs,ty)) tvs tys

substIfaceType :: IfaceTySubst -> IfaceType -> IfaceType
substIfaceType env ty
  = go ty
  where
    go (IfaceTyVar tv)        = substIfaceTyVar env tv
    go (IfaceAppTy  t1 t2)    = IfaceAppTy  (go t1) (go t2)
    go (IfaceFunTy  t1 t2)    = IfaceFunTy  (go t1) (go t2)
    go (IfaceDFunTy t1 t2)    = IfaceDFunTy (go t1) (go t2)
    go ty@(IfaceLitTy {})     = ty
    go (IfaceTyConApp tc tys) = IfaceTyConApp tc (substIfaceTcArgs env tys)
    go (IfaceForAllTy {})     = pprPanic "substIfaceType" (ppr ty)
      -- TODO (RAE): I think we need to write the following cases.
    go (IfaceCastTy {})       = pprPanic "substIfaceType:CastTy" (ppr ty)
    go (IfaceCoercionTy {})   = pprPanic "substIfaceType:CoercionTy" (ppr ty)

substIfaceTcArgs :: IfaceTySubst -> IfaceTcArgs -> IfaceTcArgs
substIfaceTcArgs env args
  = go args
  where
    go ITC_Nil            = ITC_Nil
    go (ITC_Vis ty tys)   = ITC_Vis   (substIfaceType env ty) (go tys)
    go (ITC_Invis ty tys) = ITC_Invis (substIfaceType env ty) (go tys)

substIfaceTyVar :: IfaceTySubst -> IfLclName -> IfaceType
substIfaceTyVar env tv
  | Just ty <- lookupFsEnv env tv = ty
  | otherwise                     = IfaceTyVar tv

{-
************************************************************************
*                                                                      *
                Functions over IFaceTcArgs
*                                                                      *
************************************************************************
-}

stripInvisArgs :: DynFlags -> IfaceTcArgs -> IfaceTcArgs
stripInvisArgs dflags tys
  | gopt Opt_PrintExplicitKinds dflags = tys
  | otherwise = suppress_invis tys
    where
      suppress_invis c
        = case c of
            ITC_Invis _ ts -> suppress_invis ts
            _ -> c

toIfaceTcArgs :: TyCon -> [Type] -> IfaceTcArgs
-- See Note [Suppressing invisible arguments]
toIfaceTcArgs tc ty_args
  = go (mkEmptyTCvSubst in_scope) (tyConKind tc) ty_args
  where
    in_scope = mkInScopeSet (tyCoVarsOfTypes ty_args)
    
    go _   _                   []     = ITC_Nil
    go env ty                  ts
      | Just ty' <- tcView ty
      = go env ty' ts
    go env (ForAllTy bndr res) (t:ts)
      | isVisibleBinder bndr = ITC_Vis   t' ts'
      | otherwise            = ITC_Invis t' ts'
      where
        t'  = toIfaceType t
        ts' = go (extendTCvSubstBinder env bndr t) res ts

    go env (TyVarTy tv) ts
      | Just ki <- lookupVar env tv = go env ki ts
    go env kind (t:ts) = WARN( True, ppr tc $$ ppr (tyConKind tc) $$ ppr ty_args )
                         ITC_Vis (toIfaceType t) (go env kind ts) -- Ill-kinded

tcArgsIfaceTypes :: IfaceTcArgs -> [IfaceType]
tcArgsIfaceTypes ITC_Nil = []
tcArgsIfaceTypes (ITC_Invis t ts) = t : tcArgsIfaceTypes ts
tcArgsIfaceTypes (ITC_Vis   t ts) = t : tcArgsIfaceTypes ts

{-
Note [Suppressing invisible arguments]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We use the IfaceTcArgs to specify which of the arguments to a type
constructor should be visible.
This in turn used to control suppression when printing types,
under the control of -fprint-explicit-kinds.  See also Type.filterInvisibles.
For example, given
    T :: forall k. (k->*) -> k -> *    -- Ordinary kind polymorphism
    'Just :: forall k. k -> 'Maybe k   -- Promoted
we want
  T * Tree Int    prints as    T Tree Int
  'Just *         prints as    Just *

%************************************************************************
%*                                                                      *
                Pretty-printing
*                                                                      *
************************************************************************
-}

pprIfaceInfixApp :: (TyPrec -> a -> SDoc) -> TyPrec -> SDoc -> a -> a -> SDoc
pprIfaceInfixApp pp p pp_tc ty1 ty2
  = maybeParen p FunPrec $
    sep [pp FunPrec ty1, pprInfixVar True pp_tc <+> pp FunPrec ty2]

pprIfacePrefixApp :: TyPrec -> SDoc -> [SDoc] -> SDoc
pprIfacePrefixApp p pp_fun pp_tys
  | null pp_tys = pp_fun
  | otherwise   = maybeParen p TyConPrec $
                  hang pp_fun 2 (sep pp_tys)

-- ----------------------------- Printing binders ------------------------------------

instance Outputable IfaceBndr where
    ppr (IfaceIdBndr bndr) = pprIfaceIdBndr bndr
    ppr (IfaceTvBndr bndr) = char '@' <+> pprIfaceTvBndr bndr

pprIfaceBndrs :: [IfaceBndr] -> SDoc
pprIfaceBndrs bs = sep (map ppr bs)

pprIfaceLamBndr :: IfaceLamBndr -> SDoc
pprIfaceLamBndr (b, IfaceNoOneShot) = ppr b
pprIfaceLamBndr (b, IfaceOneShot)   = ppr b <> text "[OneShot]"

pprIfaceIdBndr :: (IfLclName, IfaceType) -> SDoc
pprIfaceIdBndr (name, ty) = hsep [ppr name, dcolon, ppr ty]

pprIfaceTvBndr :: IfaceTvBndr -> SDoc
pprIfaceTvBndr (tv, IfaceTyConApp tc ITC_Nil)
  | ifaceTyConName tc == liftedTypeKindTyConName = ppr tv
pprIfaceTvBndr (tv, IfaceTyConApp tc (ITC_Vis (IfaceTyConApp lifted ITC_Nil) ITC_Nil))
  | ifaceTyConName tc     == tYPETyConName
  , ifaceTyConName lifted == liftedDataConName
  = ppr tv
pprIfaceTvBndr (tv, kind) = parens (ppr tv <+> dcolon <+> ppr kind)

pprIfaceTvBndrs :: [IfaceTvBndr] -> SDoc
pprIfaceTvBndrs tyvars = sep (map pprIfaceTvBndr tyvars)

instance Binary IfaceBndr where
    put_ bh (IfaceIdBndr aa) = do
            putByte bh 0
            put_ bh aa
    put_ bh (IfaceTvBndr ab) = do
            putByte bh 1
            put_ bh ab
    get bh = do
            h <- getByte bh
            case h of
              0 -> do aa <- get bh
                      return (IfaceIdBndr aa)
              _ -> do ab <- get bh
                      return (IfaceTvBndr ab)

instance Binary IfaceOneShot where
    put_ bh IfaceNoOneShot = do
            putByte bh 0
    put_ bh IfaceOneShot = do
            putByte bh 1
    get bh = do
            h <- getByte bh
            case h of
              0 -> do return IfaceNoOneShot
              _ -> do return IfaceOneShot

-- ----------------------------- Printing IfaceType ------------------------------------

---------------------------------
instance Outputable IfaceType where
  ppr ty = pprIfaceType ty

pprIfaceType, pprParendIfaceType ::IfaceType -> SDoc
pprIfaceType       = ppr_ty TopPrec
pprParendIfaceType = ppr_ty TyConPrec

ppr_ty :: TyPrec -> IfaceType -> SDoc
ppr_ty _         (IfaceTyVar tyvar)     = ppr tyvar
ppr_ty ctxt_prec (IfaceTyConApp tc tys) = sdocWithDynFlags (pprTyTcApp ctxt_prec tc tys)
ppr_ty _         (IfaceLitTy n)         = ppr_tylit n
        -- Function types
ppr_ty ctxt_prec (IfaceFunTy ty1 ty2)
  = -- We don't want to lose synonyms, so we mustn't use splitFunTys here.
    maybeParen ctxt_prec FunPrec $
    sep [ppr_ty FunPrec ty1, sep (ppr_fun_tail ty2)]
  where
    ppr_fun_tail (IfaceFunTy ty1 ty2)
      = (arrow <+> ppr_ty FunPrec ty1) : ppr_fun_tail ty2
    ppr_fun_tail other_ty
      = [arrow <+> pprIfaceType other_ty]

ppr_ty ctxt_prec (IfaceAppTy ty1 ty2)
  = maybeParen ctxt_prec TyConPrec $
    ppr_ty FunPrec ty1 <+> pprParendIfaceType ty2

ppr_ty ctxt_prec (IfaceCastTy ty co)
  = maybeParen ctxt_prec FunPrec $
    sep [ppr_ty FunPrec ty, ptext (sLit "`cast`"), ppr_co FunPrec co]

ppr_ty ctxt_prec (IfaceCoercionTy co)
  = ppr_co ctxt_prec co

ppr_ty ctxt_prec ty
  = maybeParen ctxt_prec FunPrec (ppr_iface_sigma_type True ty)

instance Outputable IfaceTcArgs where
  ppr tca = pprIfaceTcArgs tca

pprIfaceTcArgs, pprParendIfaceTcArgs :: IfaceTcArgs -> SDoc
pprIfaceTcArgs  = ppr_tc_args TopPrec
pprParendIfaceTcArgs = ppr_tc_args TyConPrec

ppr_tc_args :: TyPrec -> IfaceTcArgs -> SDoc
ppr_tc_args ctx_prec args
 = let pprTys t ts = ppr_ty ctx_prec t <+> ppr_tc_args ctx_prec ts
   in case args of
        ITC_Nil        -> empty
        ITC_Vis   t ts -> pprTys t ts
        ITC_Invis t ts -> pprTys t ts

-------------------
ppr_iface_sigma_type :: Bool -> IfaceType -> SDoc
ppr_iface_sigma_type show_foralls_unconditionally ty
  = ppr_iface_forall_part show_foralls_unconditionally tvs theta (ppr tau)
  where
    (tvs, theta, tau) = splitIfaceSigmaTy ty

-------------------
instance Outputable IfaceForAllBndr where
  ppr = pprIfaceForAllBndr

pprIfaceForAllPart :: [IfaceForAllBndr] -> [IfaceType] -> SDoc -> SDoc
pprIfaceForAllPart tvs ctxt sdoc = ppr_iface_forall_part False tvs ctxt sdoc

pprIfaceForAllCoPart :: [IfaceForAllCoBndr] -> SDoc -> SDoc
pprIfaceForAllCoPart tvs sdoc = sep [ pprIfaceForAllCo tvs
                                    , sdoc ]

ppr_iface_forall_part :: Outputable a
                      => Bool -> [IfaceForAllBndr] -> [a] -> SDoc -> SDoc
ppr_iface_forall_part show_foralls_unconditionally tvs ctxt sdoc
  = sep [ if show_foralls_unconditionally
          then pprIfaceForAll tvs
          else pprUserIfaceForAll tvs
        , pprIfaceContextArr ctxt
        , sdoc]

pprIfaceForAll :: [IfaceForAllBndr] -> SDoc
pprIfaceForAll []  = empty
pprIfaceForAll tvs = ptext (sLit "forall") <+> pprIfaceForAllBndrs tvs <> dot

pprIfaceForAllCo :: [IfaceForAllCoBndr] -> SDoc
pprIfaceForAllCo []  = empty
pprIfaceForAllCo tvs = text "forall" <+> pprIfaceForAllCoBndrs tvs <> dot

pprIfaceForAllBndrs :: [IfaceForAllBndr] -> SDoc
pprIfaceForAllBndrs bndrs = hsep $ map pprIfaceForAllBndr bndrs

pprIfaceForAllCoBndrs :: [IfaceForAllCoBndr] -> SDoc
pprIfaceForAllCoBndrs bndrs = hsep $ map pprIfaceForAllCoBndr bndrs

pprIfaceForAllBndr :: IfaceForAllBndr -> SDoc
 -- TODO (RAE): Make this work correctly.
pprIfaceForAllBndr (IfaceTv tv _) = pprIfaceTvBndr tv
pprIfaceForAllBndr (IfaceCv cv)   = pprIfaceIdBndr cv

pprIfaceForAllCoBndr :: IfaceForAllCoBndr -> SDoc
pprIfaceForAllCoBndr (IfaceCoBndr co tv1 tv2 m_cv)
  =  brackets (pprIfaceCoercion co)
  <> parens (sep (punctuate comma [pprIfaceTvBndr tv1,
                                   pprIfaceTvBndr tv2,
                                   maybe empty pprIfaceIdBndr m_cv]))

pprIfaceSigmaType :: IfaceType -> SDoc
pprIfaceSigmaType ty = ppr_iface_sigma_type False ty

pprUserIfaceForAll :: [IfaceForAllBndr] -> SDoc
pprUserIfaceForAll tvs
   = sdocWithDynFlags $ \dflags ->
     ppWhen (any tv_has_kind_var tvs || gopt Opt_PrintExplicitForalls dflags) $
     pprIfaceForAll tvs
   where
     tv_has_kind_var bndr
       = not (isEmptyUniqSet (fst (ifTyVarsOfForAllBndr bndr)))

-------------------

-- See equivalent function in TyCoRep.lhs
pprIfaceTyList :: TyPrec -> IfaceType -> IfaceType -> SDoc
-- Given a type-level list (t1 ': t2), see if we can print
-- it in list notation [t1, ...].
-- Precondition: Opt_PrintExplicitKinds is off
pprIfaceTyList ctxt_prec ty1 ty2
  = case gather ty2 of
      (arg_tys, Nothing)
        -> char '\'' <> brackets (fsep (punctuate comma
                        (map (ppr_ty TopPrec) (ty1:arg_tys))))
      (arg_tys, Just tl)
        -> maybeParen ctxt_prec FunPrec $ hang (ppr_ty FunPrec ty1)
           2 (fsep [ colon <+> ppr_ty FunPrec ty | ty <- arg_tys ++ [tl]])
  where
    gather :: IfaceType -> ([IfaceType], Maybe IfaceType)
     -- (gather ty) = (tys, Nothing) means ty is a list [t1, .., tn]
     --             = (tys, Just tl) means ty is of form t1:t2:...tn:tl
    gather (IfaceTyConApp tc tys)
      | tcname == consDataConName
      , (ITC_Invis _ (ITC_Vis ty1 (ITC_Vis ty2 ITC_Nil))) <- tys
      , (args, tl) <- gather ty2
      = (ty1:args, tl)
      | tcname == nilDataConName
      = ([], Nothing)
      where tcname = ifaceTyConName tc
    gather ty = ([], Just ty)

pprIfaceTypeApp :: IfaceTyCon -> IfaceTcArgs -> SDoc
pprIfaceTypeApp tc args = sdocWithDynFlags (pprTyTcApp TopPrec tc args)

pprTyTcApp :: TyPrec -> IfaceTyCon -> IfaceTcArgs -> DynFlags -> SDoc
pprTyTcApp ctxt_prec tc tys dflags
  | ifaceTyConName tc == ipClassName
  , ITC_Vis (IfaceLitTy (IfaceStrTyLit n)) (ITC_Vis ty ITC_Nil) <- tys
  = char '?' <> ftext n <> ptext (sLit "::") <> ppr_ty TopPrec ty

  | ifaceTyConName tc == consDataConName
  , not (gopt Opt_PrintExplicitKinds dflags)
  , ITC_Invis _ (ITC_Vis ty1 (ITC_Vis ty2 ITC_Nil)) <- tys
  = pprIfaceTyList ctxt_prec ty1 ty2

  | ifaceTyConName tc == tYPETyConName
  , ITC_Vis (IfaceTyConApp lev_tc ITC_Nil) ITC_Nil <- tys
  = let n = ifaceTyConName lev_tc in
    if n == liftedDataConName then char '*'
    else if n == unliftedDataConName then char '#'
         else pprPanic "IfaceType.pprTyTcApp" (ppr lev_tc)

  | otherwise
  = ppr_iface_tc_app ppr_ty ctxt_prec tc tys_wo_kinds
  where
    tys_wo_kinds = tcArgsIfaceTypes $ stripInvisArgs dflags tys

pprIfaceCoTcApp :: TyPrec -> IfaceTyCon -> [IfaceCoercion] -> SDoc
pprIfaceCoTcApp ctxt_prec tc tys = ppr_iface_tc_app ppr_co ctxt_prec tc tys

ppr_iface_tc_app :: (TyPrec -> a -> SDoc) -> TyPrec -> IfaceTyCon -> [a] -> SDoc
ppr_iface_tc_app pp _ tc [ty]
  | n == listTyConName = pprPromotionQuote tc <> brackets (pp TopPrec ty)
  | n == parrTyConName = pprPromotionQuote tc <> paBrackets (pp TopPrec ty)
  where
    n = ifaceTyConName tc

ppr_iface_tc_app pp ctxt_prec tc tys
  | Just (tup_sort, tup_args) <- is_tuple
                  -- drop the levity vars.
                  -- See Note [Unboxed tuple levity vars] in TyCon
  = let tup_args' = case tup_sort of UnboxedTuple ->
                                       drop (length tup_args `div` 2) tup_args
                                     _ -> tup_args
    in
    pprPromotionQuote tc <>
    tupleParens tup_sort (sep (punctuate comma (map (pp TopPrec) tup_args')))

  | not (isSymOcc (nameOccName tc_name))
  = pprIfacePrefixApp ctxt_prec (ppr tc) (map (pp TyConPrec) tys)

  | [ty1,ty2] <- tys  -- Infix, two arguments;
                      -- we know nothing of precedence though
  = pprIfaceInfixApp pp ctxt_prec (ppr tc) ty1 ty2

  | tc_name == liftedTypeKindTyConName || tc_name == unliftedTypeKindTyConName
  = ppr tc   -- Do not wrap *, # in parens

  | otherwise
  = pprIfacePrefixApp ctxt_prec (parens (ppr tc)) (map (pp TyConPrec) tys)
  where
    tc_name = ifaceTyConName tc

    is_tuple = case wiredInNameTyThing_maybe tc_name of
                 Just (ATyCon tc)
                   | Just sort <- tyConTuple_maybe tc
                   , tyConArity tc == length tys
                   -> Just (sort, tys)

                   | Just dc <- isPromotedDataCon_maybe tc
                   , let dc_tc = dataConTyCon dc
                   , isTupleTyCon dc_tc
                   , let arity = tyConArity dc_tc
                         ty_args = drop arity tys
                   , ty_args `lengthIs` arity
                   -> Just (tupleTyConSort tc, ty_args)

                 _ -> Nothing


ppr_tylit :: IfaceTyLit -> SDoc
ppr_tylit (IfaceNumTyLit n) = integer n
ppr_tylit (IfaceStrTyLit n) = text (show n)

pprIfaceCoercion, pprParendIfaceCoercion :: IfaceCoercion -> SDoc
pprIfaceCoercion = ppr_co TopPrec
pprParendIfaceCoercion = ppr_co TyConPrec

ppr_co :: TyPrec -> IfaceCoercion -> SDoc
ppr_co _         (IfaceReflCo r ty) = angleBrackets (ppr ty) <> ppr_role r
ppr_co ctxt_prec (IfaceFunCo r co1 co2)
  = maybeParen ctxt_prec FunPrec $
    sep (ppr_co FunPrec co1 : ppr_fun_tail co2)
  where
    ppr_fun_tail (IfaceFunCo r co1 co2)
      = (arrow <> ppr_role r <+> ppr_co FunPrec co1) : ppr_fun_tail co2
    ppr_fun_tail other_co
      = [arrow <> ppr_role r <+> pprIfaceCoercion other_co]

ppr_co _         (IfaceTyConAppCo r tc cos)
  = parens (pprIfaceCoTcApp TopPrec tc cos) <> ppr_role r
ppr_co ctxt_prec (IfaceAppCo co1 _ co2)
  = maybeParen ctxt_prec TyConPrec $
    ppr_co FunPrec co1 <+> pprParendIfaceCoercion co2
ppr_co ctxt_prec co@(IfaceForAllCo _ _)
  = maybeParen ctxt_prec FunPrec (pprIfaceForAllCoPart tvs (pprIfaceCoercion inner_co))
  where
    (tvs, inner_co) = split_co co

    split_co (IfaceForAllCo tv co')
      = let (tvs, co'') = split_co co' in (tv:tvs,co'')
    split_co co' = ([], co')

ppr_co _         (IfaceCoVarCo covar)       = ppr covar

ppr_co _         (IfacePhantomCo h ty1 ty2)
  = angleBrackets ( ppr ty1 <> comma <+> ppr ty2 ) <> char '_' <> pprParendIfaceCoercion h

ppr_co ctxt_prec (IfaceUnsafeCo s r ty1 ty2)
  = maybeParen ctxt_prec TyConPrec $
    ptext (sLit "UnsafeCo") <+> ftext s <+> ppr r <+>
    pprParendIfaceType ty1 <+> pprParendIfaceType ty2

ppr_co ctxt_prec (IfaceInstCo co ty)
  = maybeParen ctxt_prec TyConPrec $
    ptext (sLit "Inst") <+> pprParendIfaceCoercion co
                        <+> pprParendIfaceCoercion ty

ppr_co ctxt_prec (IfaceAxiomRuleCo tc tys cos)
  = maybeParen ctxt_prec TyConPrec
               (sep [ppr tc, nest 4 (sep (map pprParendIfaceType tys ++ map pprParendIfaceCoercion cos))])

ppr_co ctxt_prec co
  = ppr_special_co ctxt_prec doc cos
  where (doc, cos) = case co of
                     { IfaceAxiomInstCo n i cos -> (ppr n <> brackets (ppr i), cos)
                     ; IfaceSymCo co            -> (ptext (sLit "Sym"), [co])
                     ; IfaceTransCo co1 co2     -> (ptext (sLit "Trans"), [co1,co2])
                     ; IfaceNthCo d co          -> (ptext (sLit "Nth:") <> int d,
                                                    [co])
                     ; IfaceLRCo lr co          -> (ppr lr, [co])
                     ; IfaceSubCo co            -> (ptext (sLit "Sub"), [co])
                     ; _                        -> panic "pprIfaceCo" }

ppr_special_co :: TyPrec -> SDoc -> [IfaceCoercion] -> SDoc
ppr_special_co ctxt_prec doc cos
  = maybeParen ctxt_prec TyConPrec
               (sep [doc, nest 4 (sep (map pprParendIfaceCoercion cos))])

ppr_role :: Role -> SDoc
ppr_role r = underscore <> pp_role
  where pp_role = case r of
                    Nominal          -> char 'N'
                    Representational -> char 'R'
                    Phantom          -> char 'P'

-------------------
instance Outputable IfaceTyCon where
  ppr tc = pprPromotionQuote tc <> ppr (ifaceTyConName tc)

pprPromotionQuote :: IfaceTyCon -> SDoc
pprPromotionQuote (IfacePromotedDataCon _ ) = char '\''
pprPromotionQuote _                         = empty

instance Outputable IfaceCoercion where
  ppr = pprIfaceCoercion

instance Binary IfaceTyCon where
   put_ bh tc =
     case tc of
       IfaceTc n              -> putByte bh 0 >> put_ bh n
       IfacePromotedDataCon n -> putByte bh 1 >> put_ bh n

   get bh =
     do tc <- getByte bh
        case tc of
          0 -> get bh >>= return . IfaceTc
          1 -> get bh >>= return . IfacePromotedDataCon
          _ -> panic ("get IfaceTyCon " ++ show tc)

instance Outputable IfaceTyLit where
  ppr = ppr_tylit

instance Binary IfaceTyLit where
  put_ bh (IfaceNumTyLit n)  = putByte bh 1 >> put_ bh n
  put_ bh (IfaceStrTyLit n)  = putByte bh 2 >> put_ bh n

  get bh =
    do tag <- getByte bh
       case tag of
         1 -> do { n <- get bh
                 ; return (IfaceNumTyLit n) }
         2 -> do { n <- get bh
                 ; return (IfaceStrTyLit n) }
         _ -> panic ("get IfaceTyLit " ++ show tag)

instance Binary IfaceForAllBndr where
   put_ bh (IfaceTv tv vis) = do
     putByte bh 1
     put_ bh tv
     put_ bh vis
   put_ bh (IfaceCv cv) = do
     putByte bh 2
     put_ bh cv

   get bh = do
     c <- getByte bh
     case c of
       1 -> do
         tv <- get bh
         vis <- get bh
         return (IfaceTv tv vis)
       2 -> do
         cv <- get bh
         return (IfaceCv cv)
       _ -> panic ("get IfaceForAllBndr " ++ show c)

instance Binary IfaceForAllCoBndr where
   put_ bh (IfaceCoBndr co tv1 tv2 m_cv) = do
     put_ bh co
     put_ bh tv1
     put_ bh tv2
     put_ bh m_cv

   get bh = do
     co   <- get bh
     tv1  <- get bh
     tv2  <- get bh
     m_cv <- get bh
     return (IfaceCoBndr co tv1 tv2 m_cv)

instance Binary IfaceTcArgs where
  put_ bh tk =
    case tk of
      ITC_Vis   t ts -> putByte bh 0 >> put_ bh t >> put_ bh ts
      ITC_Invis t ts -> putByte bh 1 >> put_ bh t >> put_ bh ts
      ITC_Nil        -> putByte bh 2

  get bh =
    do c <- getByte bh
       case c of
         0 -> do
           t  <- get bh
           ts <- get bh
           return $! ITC_Vis t ts
         1 -> do
           t  <- get bh
           ts <- get bh
           return $! ITC_Invis t ts
         2 -> return ITC_Nil
         _ -> panic ("get IfaceTcArgs " ++ show c)

-------------------
pprIfaceContextArr :: Outputable a => [a] -> SDoc
-- Prints "(C a, D b) =>", including the arrow
pprIfaceContextArr = maybe empty (<+> darrow) . pprIfaceContextMaybe

pprIfaceContext :: Outputable a => [a] -> SDoc
pprIfaceContext = fromMaybe (parens empty) . pprIfaceContextMaybe

pprIfaceContextMaybe :: Outputable a => [a] -> Maybe SDoc
pprIfaceContextMaybe [] = Nothing
pprIfaceContextMaybe [pred] = Just $ ppr pred -- No parens
pprIfaceContextMaybe preds  = Just $ parens (fsep (punctuate comma (map ppr preds)))

instance Binary IfaceType where
    put_ bh (IfaceForAllTy aa ab) = do
            putByte bh 0
            put_ bh aa
            put_ bh ab
    put_ bh (IfaceTyVar ad) = do
            putByte bh 1
            put_ bh ad
    put_ bh (IfaceAppTy ae af) = do
            putByte bh 2
            put_ bh ae
            put_ bh af
    put_ bh (IfaceFunTy ag ah) = do
            putByte bh 3
            put_ bh ag
            put_ bh ah
    put_ bh (IfaceDFunTy ag ah) = do
            putByte bh 4
            put_ bh ag
            put_ bh ah
    put_ bh (IfaceTyConApp tc tys)
      = do { putByte bh 5; put_ bh tc; put_ bh tys }
    put_ bh (IfaceCastTy a b)
      = do { putByte bh 6; put_ bh a; put_ bh b }
    put_ bh (IfaceCoercionTy a)
      = do { putByte bh 7; put_ bh a }

    put_ bh (IfaceLitTy n)
      = do { putByte bh 30; put_ bh n }

    get bh = do
            h <- getByte bh
            case h of
              0 -> do aa <- get bh
                      ab <- get bh
                      return (IfaceForAllTy aa ab)
              1 -> do ad <- get bh
                      return (IfaceTyVar ad)
              2 -> do ae <- get bh
                      af <- get bh
                      return (IfaceAppTy ae af)
              3 -> do ag <- get bh
                      ah <- get bh
                      return (IfaceFunTy ag ah)
              4 -> do ag <- get bh
                      ah <- get bh
                      return (IfaceDFunTy ag ah)
              5 -> do { tc <- get bh; tys <- get bh
                      ; return (IfaceTyConApp tc tys) }
              6 -> do { a <- get bh; b <- get bh
                      ; return (IfaceCastTy a b) }
              7 -> do { a <- get bh
                      ; return (IfaceCoercionTy a) }

              30 -> do n <- get bh
                       return (IfaceLitTy n)

              _  -> panic ("get IfaceType " ++ show h)

instance Binary IfaceCoercion where
  put_ bh (IfaceReflCo a b) = do
          putByte bh 1
          put_ bh a
          put_ bh b
  put_ bh (IfaceFunCo a b c) = do
          putByte bh 2
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfaceTyConAppCo a b c) = do
          putByte bh 3
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfaceAppCo a b c) = do
          putByte bh 4
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfaceForAllCo a b) = do
          putByte bh 5
          put_ bh a
          put_ bh b
  put_ bh (IfaceCoVarCo a) = do
          putByte bh 6
          put_ bh a
  put_ bh (IfaceAxiomInstCo a b c) = do
          putByte bh 7
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfacePhantomCo a b c) = do
          putByte bh 8
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfaceUnsafeCo a b c d) = do
          putByte bh 9
          put_ bh a
          put_ bh b
          put_ bh c
          put_ bh d
  put_ bh (IfaceSymCo a) = do
          putByte bh 10
          put_ bh a
  put_ bh (IfaceTransCo a b) = do
          putByte bh 11
          put_ bh a
          put_ bh b
  put_ bh (IfaceNthCo a b) = do
          putByte bh 12
          put_ bh a
          put_ bh b
  put_ bh (IfaceLRCo a b) = do
          putByte bh 13
          put_ bh a
          put_ bh b
  put_ bh (IfaceInstCo a b) = do
          putByte bh 14
          put_ bh a
          put_ bh b
  put_ bh (IfaceCoherenceCo a b) = do
          putByte bh 15
          put_ bh a
          put_ bh b
  put_ bh (IfaceKindCo a) = do
          putByte bh 16
          put_ bh a
  put_ bh (IfaceKindAppCo a) = do
          putByte bh 17
          put_ bh a
  put_ bh (IfaceSubCo a) = do
          putByte bh 18
          put_ bh a
  put_ bh (IfaceAxiomRuleCo a b c) = do
          putByte bh 19
          put_ bh a
          put_ bh b
          put_ bh c
  put_ bh (IfaceCoCoArg a b c d) = do
          putByte bh 20
          put_ bh a
          put_ bh b
          put_ bh c
          put_ bh d

  get bh = do
      tag <- getByte bh
      case tag of
           1 -> do a <- get bh
                   b <- get bh
                   return $ IfaceReflCo a b
           2 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceFunCo a b c
           3 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceTyConAppCo a b c
           4 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceAppCo a b c
           5 -> do a <- get bh
                   b <- get bh
                   return $ IfaceForAllCo a b
           6 -> do a <- get bh
                   return $ IfaceCoVarCo a
           7 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceAxiomInstCo a b c
           8 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfacePhantomCo a b c
           9 -> do a <- get bh
                   b <- get bh
                   c <- get bh
                   d <- get bh
                   return $ IfaceUnsafeCo a b c d
           10-> do a <- get bh
                   return $ IfaceSymCo a
           11-> do a <- get bh
                   b <- get bh
                   return $ IfaceTransCo a b
           12-> do a <- get bh
                   b <- get bh
                   return $ IfaceNthCo a b
           13-> do a <- get bh
                   b <- get bh
                   return $ IfaceLRCo a b
           14-> do a <- get bh
                   b <- get bh
                   return $ IfaceInstCo a b
           15-> do a <- get bh
                   b <- get bh
                   return $ IfaceCoherenceCo a b
           16-> do a <- get bh
                   return $ IfaceKindCo a
           17-> do a <- get bh
                   return $ IfaceKindAppCo a
           18-> do a <- get bh
                   return $ IfaceSubCo a
           19-> do a <- get bh
                   b <- get bh
                   c <- get bh
                   return $ IfaceAxiomRuleCo a b c
           20-> do a <- get bh
                   b <- get bh
                   c <- get bh
                   d <- get bh
                   return $ IfaceCoCoArg a b c d
           _ -> panic ("get IfaceCoercion " ++ show tag)

{-
************************************************************************
*                                                                      *
        Conversion from Type to IfaceType
*                                                                      *
************************************************************************
-}

----------------
toIfaceTvBndr :: TyVar -> (IfLclName, IfaceKind)
toIfaceTvBndr tyvar   = ( occNameFS (getOccName tyvar)
                        , toIfaceKind (tyVarKind tyvar)
                        )

toIfaceIdBndr :: Id -> (IfLclName, IfaceType)
toIfaceIdBndr id      = (occNameFS (getOccName id),    toIfaceType (idType id))

toIfaceTvBndrs :: [TyVar] -> [IfaceTvBndr]
toIfaceTvBndrs = map toIfaceTvBndr

toIfaceTCvBndrs :: [TyCoVar] -> [IfaceBndr]
toIfaceTCvBndrs tyvars = map toIfaceBndr tyvars

toIfaceBndr :: Var -> IfaceBndr
toIfaceBndr var
  | isId var  = IfaceIdBndr (toIfaceIdBndr var)
  | otherwise = IfaceTvBndr (toIfaceTvBndr var)

toIfaceKind :: Type -> IfaceType
toIfaceKind = toIfaceType

---------------------
toIfaceType :: Type -> IfaceType
-- Synonyms are retained in the interface type
toIfaceType (TyVarTy tv)        = IfaceTyVar (toIfaceTyVar tv)
toIfaceType (AppTy t1 t2)       = IfaceAppTy (toIfaceType t1) (toIfaceType t2)
toIfaceType (ForAllTy (Anon t1) t2)
  | isPredTy t1 = IfaceDFunTy (toIfaceType t1) (toIfaceType t2)
  | otherwise   = IfaceFunTy  (toIfaceType t1) (toIfaceType t2)
toIfaceType (TyConApp tc tys)   = IfaceTyConApp (toIfaceTyCon tc) (toIfaceTcArgs tc tys)
toIfaceType (LitTy n)           = IfaceLitTy (toIfaceTyLit n)
toIfaceType (ForAllTy (Named tv vis) t)
  = IfaceForAllTy (varToIfaceForAllBndr tv vis) (toIfaceType t)
toIfaceType (CastTy ty co)      = IfaceCastTy (toIfaceType ty) (toIfaceCoercion co)
toIfaceType (CoercionTy co)     = IfaceCoercionTy (toIfaceCoercion co)

toIfaceTyVar :: TyVar -> FastString
toIfaceTyVar = occNameFS . getOccName

toIfaceCoVar :: CoVar -> FastString
toIfaceCoVar = occNameFS . getOccName

varToIfaceForAllBndr :: TyCoVar -> VisibilityFlag -> IfaceForAllBndr
varToIfaceForAllBndr v vis
  | isTyVar v = IfaceTv (toIfaceTvBndr v) vis
  | otherwise = IfaceCv (toIfaceIdBndr v)

----------------
toIfaceTyCon :: TyCon -> IfaceTyCon
toIfaceTyCon tc
  | isPromotedDataCon tc            = IfacePromotedDataCon tc_name
  | otherwise                       = IfaceTc tc_name
    where tc_name = tyConName tc
          
toIfaceTyCon_name :: Name -> IfaceTyCon
toIfaceTyCon_name = IfaceTc

toIfaceTyLit :: TyLit -> IfaceTyLit
toIfaceTyLit (NumTyLit x) = IfaceNumTyLit x
toIfaceTyLit (StrTyLit x) = IfaceStrTyLit x

----------------
toIfaceTypes :: [Type] -> [IfaceType]
toIfaceTypes ts = map toIfaceType ts

----------------
toIfaceContext :: ThetaType -> IfaceContext
toIfaceContext = toIfaceTypes

----------------
toIfaceCoercion :: Coercion -> IfaceCoercion
toIfaceCoercion (Refl r ty)         = IfaceReflCo r (toIfaceType ty)
toIfaceCoercion (TyConAppCo r tc cos)
  | tc `hasKey` funTyConKey
  , [arg,res] <- cos                = IfaceFunCo r (argToIfaceCoercion arg) (argToIfaceCoercion res)
  | otherwise                       = IfaceTyConAppCo r (toIfaceTyCon tc)
                                                        (map argToIfaceCoercion cos)
toIfaceCoercion (AppCo co1 h co2)   = IfaceAppCo  (toIfaceCoercion co1)
                                                  (toIfaceCoercion h)
                                                  (argToIfaceCoercion co2)
toIfaceCoercion (ForAllCo cobndr co)= IfaceForAllCo (toIfaceForAllCoBndr cobndr)
                                                    (toIfaceCoercion co)
toIfaceCoercion (CoVarCo cv)        = IfaceCoVarCo  (toIfaceCoVar cv)
toIfaceCoercion (AxiomInstCo con ind cos)
                                    = IfaceAxiomInstCo (coAxiomName con) ind
                                                       (map argToIfaceCoercion cos)
toIfaceCoercion (PhantomCo h t1 t2) = IfacePhantomCo (toIfaceCoercion h)
                                                     (toIfaceType t1)
                                                     (toIfaceType t2)
toIfaceCoercion (UnsafeCo s r t1 t2)= IfaceUnsafeCo s r (toIfaceType t1)
                                                        (toIfaceType t2)
toIfaceCoercion (SymCo co)          = IfaceSymCo (toIfaceCoercion co)
toIfaceCoercion (TransCo co1 co2)   = IfaceTransCo (toIfaceCoercion co1)
                                                   (toIfaceCoercion co2)
toIfaceCoercion (NthCo d co)        = IfaceNthCo d (toIfaceCoercion co)
toIfaceCoercion (LRCo lr co)        = IfaceLRCo lr (toIfaceCoercion co)
toIfaceCoercion (InstCo co arg)     = IfaceInstCo (toIfaceCoercion co)
                                                  (argToIfaceCoercion arg)
toIfaceCoercion (CoherenceCo c1 c2) = IfaceCoherenceCo (toIfaceCoercion c1)
                                                       (toIfaceCoercion c2)
toIfaceCoercion (KindCo c)          = IfaceKindCo (toIfaceCoercion c)
toIfaceCoercion (KindAppCo c)       = IfaceKindAppCo (toIfaceCoercion c)
toIfaceCoercion (SubCo co)          = IfaceSubCo (toIfaceCoercion co)
toIfaceCoercion (AxiomRuleCo co ts cs) = IfaceAxiomRuleCo
                                          (coaxrName co)
                                          (map toIfaceType ts)
                                          (map toIfaceCoercion cs)

argToIfaceCoercion :: CoercionArg -> IfaceCoercion
argToIfaceCoercion (TyCoArg co) = toIfaceCoercion co
argToIfaceCoercion (CoCoArg r kco co1 co2)
  = IfaceCoCoArg r (toIfaceCoercion kco) (toIfaceCoercion co1)
                   (toIfaceCoercion co2)

toIfaceForAllCoBndr :: ForAllCoBndr -> IfaceForAllCoBndr
toIfaceForAllCoBndr (ForAllCoBndr co tv1 tv2 m_cv)
  = IfaceCoBndr (toIfaceCoercion co)
                (toIfaceTvBndr tv1)
                (toIfaceTvBndr tv2)
                (fmap toIfaceIdBndr m_cv)


