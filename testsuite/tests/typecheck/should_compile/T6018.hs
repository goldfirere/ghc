{-# LANGUAGE TypeFamilies, DataKinds, UndecidableInstances, PolyKinds #-}

module T6018 where

import T6018a -- defines G, identical to F

type family F a b c = (result :: k) | result -> a b c
type instance F Int  Char Bool = Bool
type instance F Char Bool Int  = Int
type instance F Bool Int  Char = Char


type instance G Bool Int  Char = Char

type family I (a :: k) b (c :: k) = r | r -> a b
type instance I Int  Char Bool = Bool
type instance I Int  Char Int  = Bool
type instance I Bool Int  Int  = Int

-- this is injective - a type variables mentioned on LHS is not mentioned on RHS
-- but we don't claim injectivity in that argument.
type family J a (b :: k) = r | r -> a
type instance J Int b = Char

type MaybeSyn a = Maybe a
type family K a = r | r -> a
type instance K a = MaybeSyn a

-- Closed type families

-- these are simple conversions from open type families. They should behave the
-- same
type family FClosed a b c = result | result -> a b c where
    FClosed Int  Char Bool = Bool
    FClosed Char Bool Int  = Int
    FClosed Bool Int  Char = Char

type family IClosed (a :: *) (b :: *) (c :: *) = r | r -> a b where
    IClosed Int  Char Bool = Bool
    IClosed Int  Char Int  = Bool
    IClosed Bool Int  Int  = Int

type family JClosed a (b :: k) = r | r -> a where
    JClosed Int b = Char

type family KClosed a = r | r -> a where
    KClosed a = MaybeSyn a

-- Here the last equation might return both Int and Char but we have to
-- recognize that it is not possible due to equation overlap
type family Bak a = r | r -> a where
     Bak Int  = Char
     Bak Char = Int
     Bak a    = a

-- This is similar, except that the last equation contains concrete type.
type family Foo a = r | r -> a where
    Foo Int  = Bool
    Foo Bool = Int
    Foo Bool = Bool


-- this one is a strange beast. Last equation is unreachable but it generates
-- information used by injectivity. So we accept.
type family Bar a = r | r -> a where
    Bar Int  = Bool
    Bar Bool = Int
    Bar Bool = Char

-- Now let's use declared type families. All the below definitions should work

-- No ambiguity for any of the arguments - all are injective
f :: F a b c -> F a b c
f x = x

-- From 1st instance of F: a ~ Int, b ~ Char, c ~ Bool
fapp :: Bool
fapp = f True

-- now the closed variant of F
fc :: FClosed a b c -> FClosed a b c
fc x = x

fcapp :: Bool
fcapp = fc True

-- The last argument is not injective so it must be instantiated
i :: I a b Int -> I a b Int
i x = x

-- From 1st instance of I: a ~ Int, b ~ Char
iapp :: Bool
iapp = i True

-- again, closed variant of I
ic :: IClosed a b Int -> IClosed a b Int
ic x = x

icapp :: Bool
icapp = ic True

-- Now we have to test weird closed type families:
bak :: Bak a -> Bak a
bak x = x

bakapp1 :: Char
bakapp1 = bak 'c'

bakapp2 :: Double
bakapp2 = bak 1.0

bakapp3 :: ()
bakapp3 = bak ()

foo :: Foo a -> Foo a
foo x = x

fooapp1 :: Bool
fooapp1 = foo True

bar :: Bar a -> Bar a
bar x = x

barapp1 :: Bool
barapp1 = bar True

barapp2 :: Int
barapp2 = bar 1
