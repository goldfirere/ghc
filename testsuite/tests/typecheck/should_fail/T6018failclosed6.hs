{-# LANGUAGE TypeFamilies, DataKinds, UndecidableInstances #-}

module T6018failclosed6 where

-- Non-injective type variable mentioned in the RHS
type family QClosed a b = r | r -> a where
    QClosed Int b = b
