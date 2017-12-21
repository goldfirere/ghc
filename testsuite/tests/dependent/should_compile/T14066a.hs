{-# LANGUAGE TypeFamilies, PolyKinds #-}

module T14066a where

type family Bar x y where
  Bar (x :: a) (y :: b) = x
  Bar (x :: c) (y :: d) = y   -- these should unify
