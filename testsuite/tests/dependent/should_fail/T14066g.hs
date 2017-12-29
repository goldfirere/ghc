{-# LANGUAGE TypeInType #-}

module T14066g where

import Data.Proxy

type P k a = Proxy (a :: k)
