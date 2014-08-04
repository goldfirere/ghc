{-# LANGUAGE PolyKinds, MultiParamTypeClasses #-}

module T9200 where

class D a => C (f :: k) (a :: k2)
class C () a => D a
