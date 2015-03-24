{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

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

-- Declarations below test more liberal RHSs of injectivity annotations:
-- permiting variables to appear in different order than the one in which they
-- were declared.
type family H a b = r | r -> b a
type family Hc a b = r | r -> b a where
  Hc a b = a b
class Hcl a b where
  type Ht a b = r | r -> b a

-- repeated tyvars in the RHS of injectivity annotation: no warnings or errors
-- (consistent with behaviour for functional dependencies)
type family Jx a b = r | r -> a a
type family Jcx a b = r | r -> a a where
  Jcx a b = a
class Jcl a b where
  type Jt a b = r | r -> a a

type family Kx a b = r | r -> a b b
type family Kcx a b = r | r -> a b b where
  Kcx a b = a b
class Kcl a b where
  type Kt a b = r | r -> a b b

-- Declaring kind injectivity. Here we only claim that knowing the RHS
-- determines the LHS kind but not the type.
type family L (a :: k1) = (r :: k2) | r -> k1 where
    L 'True  = Int
    L 'False = Int
    L Maybe  = 3
    L IO     = 3

data KProxy (a :: *) = KProxy
type family KP (kproxy :: KProxy k) = r | r -> k
type instance KP ('KProxy :: KProxy Bool) = Int
type instance KP ('KProxy :: KProxy *)    = Char

kproxy_id :: KP ('KProxy :: KProxy k) -> KP ('KProxy :: KProxy k)
kproxy_id x = x

kproxy_id_use = kproxy_id 'a'

type family Fa (a :: k) (b :: k) = r | r -> k where
    Fa a b = a

type family Fb (a :: k) (b :: k) = r | r -> k where
    Fb a b = b
