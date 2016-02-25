module Type where
import TyCon
import Var ( TyVar, TyCoVar )
import VarSet ( TyCoVarSet )
import {-# SOURCE #-} TyCoRep( Type, Kind )

-- NB: Some of these functions can really be hammered on. Think carefully
-- about performance (vis-a-vis inlining) before putting a function here.

isPredTy :: Type -> Bool
isCoercionTy :: Type -> Bool

mkTyConApp :: TyCon -> [Type] -> Type
mkAppTy :: Type -> Type -> Type
piResultTy :: Type -> Type -> Type

typeKind :: Type -> Kind
eqType :: Type -> Type -> Bool

coreViewOneStarKind :: Type -> Maybe Type

partitionInvisibles :: TyCon -> Maybe (a -> Type) -> [a] -> ([a], [a])

coreView :: Type -> Maybe Type

tyCoVarsOfTypesWellScoped :: [Type] -> [TyVar]
varSetElemsWellScoped :: TyCoVarSet -> [TyCoVar]

splitTyConApp_maybe :: Type -> Maybe (TyCon, [Type])
tyConAppArgN :: Int -> Type -> Type
tyConAppTyCon :: Type -> TyCon
splitForAllTy_maybe :: Type -> Maybe (TyVar, Type)
splitAppTy :: Type -> (Type, Type)
