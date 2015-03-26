module Type where
import {-# SOURCE #-} TyCoRep( Type, Kind )

isPredTy :: Type -> Bool
isCoercionTy :: Type -> Bool

mkAppTy :: Type -> Type -> Type
piResultTy :: Type -> Type -> Type

typeKind :: Type -> Kind
eqType :: Type -> Type -> Bool

coreViewOneStarKind :: Type -> Maybe Type
