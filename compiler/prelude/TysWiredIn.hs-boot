module TysWiredIn where

import {-# SOURCE #-} TyCon      (TyCon)
import {-# SOURCE #-} TyCoRep    (Type)


eqTyCon, coercibleTyCon :: TyCon
typeNatKind, typeSymbolKind :: Type
mkBoxedTupleTy :: [Type] -> Type

levityTy, liftedDataConTy, unliftedDataConTy :: Type

