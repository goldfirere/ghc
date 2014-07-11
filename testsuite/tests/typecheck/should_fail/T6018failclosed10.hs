{-# LANGUAGE TypeFamilies, DataKinds, UndecidableInstances #-}

module T6018failclosed10 where

-- this one is a strange beast. Last equation is unreachable but it generates
-- information used by injectivity. So we accept it as a valid injective type
-- family but complain when the last equation is actually used
type family Bar a = r | r -> a where
    Bar Int  = Bool
    Bar Bool = Int
    Bar Bool = Char

bar :: Bar a -> Bar a
bar x = x

barapp2 :: Char
barapp2 = bar 'c'
