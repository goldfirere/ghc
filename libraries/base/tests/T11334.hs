{-# LANGUAGE DataKinds #-}
module Main (main) where

import Data.Typeable
import GHC.Types

main :: IO ()
main = do
  print (typeOf (Proxy :: Proxy 'Just))
  print (typeOf (Proxy :: Proxy (TYPE ('PtrRep 'Lifted))))
  print (typeOf (Proxy :: Proxy (TYPE ('PtrRep 'Unlifted))))
