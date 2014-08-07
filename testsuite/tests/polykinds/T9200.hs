{-# LANGUAGE PolyKinds, MultiParamTypeClasses, FlexibleContexts, DataKinds #-}

module T9200 where

------
-- test CUSK on classes

class C (f :: k) (a :: k2) where
  c_meth :: D a => ()
  
class C () a => D a


---------
--- test CUSK on type synonyms
data T1 a b c = MkT1 (S a b c)
data T2 p q r = MkT2 (S p q r)
data T3 x y q = MkT3 (S x y q)
type S (f :: k1) (g :: k2) (h :: k3) = ((T1 Int g h, T1 True g h, T2 f "fuzz" h, T2 f 5 h, T3 f g Nothing, T3 f g '()) :: *)
