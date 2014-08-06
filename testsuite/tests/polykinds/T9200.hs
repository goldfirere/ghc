{-# LANGUAGE PolyKinds, MultiParamTypeClasses, FlexibleContexts #-}

module T9200 where

class C (f :: k) (a :: k2) where
  c_meth :: D a => ()
  
class C () a => D a
