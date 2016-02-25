module Coercion where

import {-# SOURCE #-} TyCoRep
import {-# SOURCE #-} TyCon

import CoAxiom
import Var
import Outputable

-- NB: Some of these functions can really be hammered on. Think carefully
-- about performance (vis-a-vis inlining) before putting a function here.

mkReflCo :: Role -> Type -> Coercion
mkSymCo :: Coercion -> Coercion
mkTransCo :: Coercion -> Coercion -> Coercion

mkFunCos :: Role -> [Coercion] -> Coercion -> Coercion

isReflexiveCo :: Coercion -> Bool

coVarKindsTypesRole :: CoVar -> (Kind, Kind, Type, Type, Role)
mkCoercionType :: Role -> Type -> Type -> Type

tyConRolesX :: Role -> TyCon -> [Role]
tyConRolesRepresentational :: TyCon -> [Role]
nthRole :: Role -> TyCon -> Int -> Role

coercionSize :: Coercion -> Int
coercionType :: Coercion -> Type
seqCo :: Coercion -> ()

pprCo :: Coercion -> SDoc
pprCoRep :: CoercionRep -> SDoc
