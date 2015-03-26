{-# LANGUAGE PolyKinds, DataKinds #-}

module Dep1 where

data Proxy k (a :: k) = P

x :: Proxy * Int
x = P

y :: Proxy Bool True
y = P


