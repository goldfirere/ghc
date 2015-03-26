
{-# LANGUAGE KindSignatures, CPP #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE RoleAnnotations #-}
#endif

module CoAxiom where

#if __GLASGOW_HASKELL__ >= 707
type role CoAxiom nominal
#endif

data CoAxiom :: * -> *
type BranchIndex = Int

data Unbranched
data Branched

data Role

