{-# LANGUAGE GADTs, TypeInType, ExplicitForAll #-}

module T14066b where

import Data.Proxy

  -- this is really a kind-index GADT. Reject.
data Prox2 a where
  MkProx2 :: forall k1 (k2 :: Proxy k1) (a :: Proxy k2). Prox2 a
