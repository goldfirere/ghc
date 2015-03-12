module T9117_4 where

import Data.Coerce

newtype Bar a = Bar (Either a (Bar a))
newtype Age = MkAge Int

x :: Bar Age
x = coerce (Bar (Left (5 :: Int)))
