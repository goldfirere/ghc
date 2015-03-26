module TyCoRep where

import Outputable (Outputable)

data Type
data Binder
data TyThing
data Coercion
data CoercionArg
data ForAllCoBndr
data LeftOrRight

type PredType = Type
type Kind = Type

instance Outputable Type

