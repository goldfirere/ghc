-- Apply the vectorisation transformation to types. This is the \mathcal{L}_t scheme in HtM.

module Vectorise.Type.Type
  ( vectTyCon
  , vectAndLiftType
  , vectType
  ) 
where

import Vectorise.Utils
import Vectorise.Monad
import Vectorise.Builtins
import TcType
import Type     hiding ( lookupVar )
import TyCoRep  hiding ( lookupVar )
import TyCon
import Control.Monad
import Control.Applicative
import Data.Maybe
import Outputable

-- |Vectorise a type constructor. Unless there is a vectorised version (stripped of embedded
-- parallel arrays), the vectorised version is the same as the original.
--
vectTyCon :: TyCon -> VM TyCon
vectTyCon tc = maybe tc id <$> lookupTyCon tc

-- |Produce the vectorised and lifted versions of a type.
--
-- NB: Here we are limited to properly handle predicates at the toplevel only.  Anything embedded
--     in what is called the 'body_ty' below will end up as an argument to the type family 'PData'.
--
vectAndLiftType :: Type -> VM (Type, Type)
vectAndLiftType ty | Just ty' <- coreView ty = vectAndLiftType ty'
vectAndLiftType ty
  = do { checkNoDependentProducts bndrs
       ; padicts  <- liftM catMaybes $ mapM paDictArgType bndrs
       ; vmono_ty <- vectType mono_ty
       ; lmono_ty <- mkPDataType vmono_ty
       ; return (abstractType bndrs (padicts ++ theta) vmono_ty,
                 abstractType bndrs (padicts ++ theta) lmono_ty)
       }
  where
    (bndrs, phiTy)   = splitDepPiTys ty
    (theta, mono_ty) = tcSplitPhiTy phiTy 

-- |Vectorise a type.
--
-- For each quantified var we need to add a PA dictionary out the front of the type.
-- So          forall a.         C  a => a -> a   
-- turns into  forall a. PA a => Cv a => a :-> a
--
vectType :: Type -> VM Type
vectType ty
  | Just ty'  <- coreView ty
  = vectType ty'
vectType (TyVarTy tv)      = return $ TyVarTy tv
vectType (LitTy l)         = return $ LitTy l
vectType (AppTy ty1 ty2)   = AppTy <$> vectType ty1 <*> vectType ty2
vectType (TyConApp tc tys) = TyConApp <$> vectTyCon tc <*> mapM vectType tys
vectType ty@(PiTy b1 ty2)
  | Just ty1 <- nonDependentType_maybe b1
  = if isPredTy ty1
    then mkFunTy <$> vectType ty1 <*> vectType ty2   -- don't build a closure for dictionary abstraction
    else TyConApp <$> builtin closureTyCon <*> mapM vectType [ty1, ty2]

  | not (isRelevantBinder b1)
  = do {   -- strip off consecutive foralls
      ; let (bndrs, tyBody) = splitDepPiTys ty

      ; checkDependentProducts bndrs

          -- vectorise the body
      ; vtyBody <- vectType tyBody

          -- make a PA dictionary for each of the type variables
      ; dictsPA <- liftM catMaybes $ mapM paDictArgType bndrs

          -- add the PA dictionaries after the foralls
      ; return $ abstractType bndrs dictsPA vtyBody
      }
vectType ty@(CastTy {})
  = pprSorry "Vectorise.Type.Type.vectType: CastTy" (ppr ty)
vectType ty@(CoercionTy {})
  = pprSorry "Vectorise.Type.Type.vectType: CoercionTy" (ppr ty)

-- |Add quantified vars and dictionary parameters to the front of a type.
--
abstractType :: [Binder] -> [Type] -> Type -> Type
abstractType bndrs dicts = mkPiTys bndrs . mkFunTys dicts

-- | Fail if any of the binders is relevant
checkDependentProducts :: [Binder] -> VM ()
checkDependentProducts bndrs
  = when (any isRelevantBinder bndrs) $
    noV $ "Cannot vectorise dependent types."
