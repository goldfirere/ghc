{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998
-}

{-# LANGUAGE ScopedTypeVariables, RankNTypes, TypeFamilies,
             GeneralizedNewtypeDeriving #-}
module TrieMap(
   CoreMap, emptyCoreMap, extendCoreMap, lookupCoreMap, foldCoreMap,
   TypeMap, emptyTypeMap, extendTypeMap, lookupTypeMap, foldTypeMap,
   LooseTypeMap,
   MaybeMap,
   ListMap,
   TrieMap(..), insertTM, deleteTM
 ) where

import CoreSyn
import Coercion
import Literal
import Name
import Type
import TyCoRep         -- builds maps based on internal structure of types
import Var
import UniqFM
import Unique( Unique )
import FastString(FastString)

import qualified Data.Map    as Map
import qualified Data.IntMap as IntMap
import VarEnv
import NameEnv
import Outputable
import Control.Monad( (>=>) )

{-
This module implements TrieMaps, which are finite mappings
whose key is a structured value like a CoreExpr or Type.

The code is very regular and boilerplate-like, but there is
some neat handling of *binders*.  In effect they are deBruijn
numbered on the fly.

************************************************************************
*                                                                      *
                   The TrieMap class
*                                                                      *
************************************************************************
-}

type XT a = Maybe a -> Maybe a  -- How to alter a non-existent elt (Nothing)
                                --               or an existing elt (Just)

class TrieMap m where
   type Key m :: *
   emptyTM  :: m a
   lookupTM :: forall b. Key m -> m b -> Maybe b
   alterTM  :: forall b. Key m -> XT b -> m b -> m b
   mapTM    :: (a->b) -> m a -> m b

   foldTM   :: (a -> b -> b) -> m a -> b -> b
      -- The unusual argument order here makes
      -- it easy to compose calls to foldTM;
      -- see for example fdE below

insertTM :: TrieMap m => Key m -> a -> m a -> m a
insertTM k v m = alterTM k (\_ -> Just v) m

deleteTM :: TrieMap m => Key m -> m a -> m a
deleteTM k m = alterTM k (\_ -> Nothing) m

----------------------
-- Recall that
--   Control.Monad.(>=>) :: (a -> Maybe b) -> (b -> Maybe c) -> a -> Maybe c

(>.>) :: (a -> b) -> (b -> c) -> a -> c
-- Reverse function composition (do f first, then g)
infixr 1 >.>
(f >.> g) x = g (f x)
infixr 1 |>, |>>

(|>) :: a -> (a->b) -> b     -- Reverse application
x |> f = f x

----------------------
(|>>) :: TrieMap m2
      => (XT (m2 a) -> m1 (m2 a) -> m1 (m2 a))
      -> (m2 a -> m2 a)
      -> m1 (m2 a) -> m1 (m2 a)
(|>>) f g = f (Just . g . deMaybe)

deMaybe :: TrieMap m => Maybe (m a) -> m a
deMaybe Nothing  = emptyTM
deMaybe (Just m) = m

{-
************************************************************************
*                                                                      *
                   IntMaps
*                                                                      *
************************************************************************
-}

instance TrieMap IntMap.IntMap where
  type Key IntMap.IntMap = Int
  emptyTM = IntMap.empty
  lookupTM k m = IntMap.lookup k m
  alterTM = xtInt
  foldTM k m z = IntMap.fold k z m
  mapTM f m = IntMap.map f m

xtInt :: Int -> XT a -> IntMap.IntMap a -> IntMap.IntMap a
xtInt k f m = IntMap.alter f k m

instance Ord k => TrieMap (Map.Map k) where
  type Key (Map.Map k) = k
  emptyTM = Map.empty
  lookupTM = Map.lookup
  alterTM k f m = Map.alter f k m
  foldTM k m z = Map.fold k z m
  mapTM f m = Map.map f m

instance TrieMap UniqFM where
  type Key UniqFM = Unique
  emptyTM = emptyUFM
  lookupTM k m = lookupUFM m k
  alterTM k f m = alterUFM f m k
  foldTM k m z = foldUFM k z m
  mapTM f m = mapUFM f m

{-
************************************************************************
*                                                                      *
                   Lists
*                                                                      *
************************************************************************

If              m is a map from k -> val
then (MaybeMap m) is a map from (Maybe k) -> val
-}

data MaybeMap m a = MM { mm_nothing  :: Maybe a, mm_just :: m a }

instance TrieMap m => TrieMap (MaybeMap m) where
   type Key (MaybeMap m) = Maybe (Key m)
   emptyTM  = MM { mm_nothing = Nothing, mm_just = emptyTM }
   lookupTM = lkMaybe lookupTM
   alterTM  = xtMaybe alterTM
   foldTM   = fdMaybe
   mapTM    = mapMb

mapMb :: TrieMap m => (a->b) -> MaybeMap m a -> MaybeMap m b
mapMb f (MM { mm_nothing = mn, mm_just = mj })
  = MM { mm_nothing = fmap f mn, mm_just = mapTM f mj }

lkMaybe :: TrieMap m => (forall b. k -> m b -> Maybe b)
        -> Maybe k -> MaybeMap m a -> Maybe a
lkMaybe _  Nothing  = mm_nothing
lkMaybe lk (Just x) = mm_just >.> lk x

xtMaybe :: TrieMap m => (forall b. k -> XT b -> m b -> m b)
        -> Maybe k -> XT a -> MaybeMap m a -> MaybeMap m a
xtMaybe _  Nothing  f m = m { mm_nothing  = f (mm_nothing m) }
xtMaybe tr (Just x) f m = m { mm_just = mm_just m |> tr x f }

fdMaybe :: TrieMap m => (a -> b -> b) -> MaybeMap m a -> b -> b
fdMaybe k m = foldMaybe k (mm_nothing m)
            . foldTM k (mm_just m)

--------------------
data ListMap m a
  = LM { lm_nil  :: Maybe a
       , lm_cons :: m (ListMap m a) }

instance TrieMap m => TrieMap (ListMap m) where
   type Key (ListMap m) = [Key m]
   emptyTM  = LM { lm_nil = Nothing, lm_cons = emptyTM }
   lookupTM = lkList lookupTM
   alterTM  = xtList alterTM
   foldTM   = fdList
   mapTM    = mapList

mapList :: TrieMap m => (a->b) -> ListMap m a -> ListMap m b
mapList f (LM { lm_nil = mnil, lm_cons = mcons })
  = LM { lm_nil = fmap f mnil, lm_cons = mapTM (mapTM f) mcons }

lkList :: TrieMap m => (forall b. k -> m b -> Maybe b)
        -> [k] -> ListMap m a -> Maybe a
lkList _  []     = lm_nil
lkList lk (x:xs) = lm_cons >.> lk x >=> lkList lk xs

xtList :: TrieMap m => (forall b. k -> XT b -> m b -> m b)
        -> [k] -> XT a -> ListMap m a -> ListMap m a
xtList _  []     f m = m { lm_nil  = f (lm_nil m) }
xtList tr (x:xs) f m = m { lm_cons = lm_cons m |> tr x |>> xtList tr xs f }

fdList :: forall m a b. TrieMap m
       => (a -> b -> b) -> ListMap m a -> b -> b
fdList k m = foldMaybe k          (lm_nil m)
           . foldTM    (fdList k) (lm_cons m)

foldMaybe :: (a -> b -> b) -> Maybe a -> b -> b
foldMaybe _ Nothing  b = b
foldMaybe k (Just a) b = k a b

{-
************************************************************************
*                                                                      *
                   Basic maps
*                                                                      *
************************************************************************
-}

lkNamed :: NamedThing n => n -> NameEnv a -> Maybe a
lkNamed n env = lookupNameEnv env (getName n)

xtNamed :: NamedThing n => n -> XT a -> NameEnv a -> NameEnv a
xtNamed tc f m = alterNameEnv f m (getName tc)

------------------------
type LiteralMap  a = Map.Map Literal a

emptyLiteralMap :: LiteralMap a
emptyLiteralMap = emptyTM

lkLit :: Literal -> LiteralMap a -> Maybe a
lkLit = lookupTM

xtLit :: Literal -> XT a -> LiteralMap a -> LiteralMap a
xtLit = alterTM

{-
************************************************************************
*                                                                      *
                   CoreMap
*                                                                      *
************************************************************************

Note [Binders]
~~~~~~~~~~~~~~
 * In general we check binders as late as possible because types are
   less likely to differ than expression structure.  That's why
      cm_lam :: CoreMap (TypeMap a)
   rather than
      cm_lam :: TypeMap (CoreMap a)

 * We don't need to look at the type of some binders, notalby
     - the case binder in (Case _ b _ _)
     - the binders in an alternative
   because they are totally fixed by the context

Note [Empty case alternatives]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* For a key (Case e b ty (alt:alts))  we don't need to look the return type
  'ty', because every alternative has that type.

* For a key (Case e b ty []) we MUST look at the return type 'ty', because
  otherwise (Case (error () "urk") _ Int  []) would compare equal to
            (Case (error () "urk") _ Bool [])
  which is utterly wrong (Trac #6097)

We could compare the return type regardless, but the wildly common case
is that it's unnecesary, so we have two fields (cm_case and cm_ecase)
for the two possibilities.  Only cm_ecase looks at the type.

See also Note [Empty case alternatives] in CoreSyn.
-}

data CoreMap a
  = EmptyCM
  | CM { cm_var   :: VarMap a
       , cm_lit   :: LiteralMap a
       , cm_co    :: CoercionMap a
       , cm_type  :: TypeMap a
       , cm_cast  :: CoreMap (CoercionMap a)
       , cm_tick  :: CoreMap (TickishMap a)
       , cm_app   :: CoreMap (CoreMap a)
       , cm_lam   :: CoreMap (TypeMap a)    -- Note [Binders]
       , cm_letn  :: CoreMap (CoreMap (BndrMap a))
       , cm_letr  :: ListMap CoreMap (CoreMap (ListMap BndrMap a))
       , cm_case  :: CoreMap (ListMap AltMap a)
       , cm_ecase :: CoreMap (TypeMap a)    -- Note [Empty case alternatives]
     }


wrapEmptyCM :: CoreMap a
wrapEmptyCM = CM { cm_var = emptyTM, cm_lit = emptyLiteralMap
                 , cm_co = emptyTM, cm_type = emptyTM
                 , cm_cast = emptyTM, cm_app = emptyTM
                 , cm_lam = emptyTM, cm_letn = emptyTM
                 , cm_letr = emptyTM, cm_case = emptyTM
                 , cm_ecase = emptyTM, cm_tick = emptyTM }

instance TrieMap CoreMap where
   type Key CoreMap = CoreExpr
   emptyTM  = EmptyCM
   lookupTM = lkE emptyCME
   alterTM  = xtE emptyCME
   foldTM   = fdE
   mapTM    = mapE

--------------------------
mapE :: (a->b) -> CoreMap a -> CoreMap b
mapE _ EmptyCM = EmptyCM
mapE f (CM { cm_var = cvar, cm_lit = clit
           , cm_co = cco, cm_type = ctype
           , cm_cast = ccast , cm_app = capp
           , cm_lam = clam, cm_letn = cletn
           , cm_letr = cletr, cm_case = ccase
           , cm_ecase = cecase, cm_tick = ctick })
  = CM { cm_var = mapTM f cvar, cm_lit = mapTM f clit
       , cm_co = mapTM f cco, cm_type = mapTM f ctype
       , cm_cast = mapTM (mapTM f) ccast, cm_app = mapTM (mapTM f) capp
       , cm_lam = mapTM (mapTM f) clam, cm_letn = mapTM (mapTM (mapTM f)) cletn
       , cm_letr = mapTM (mapTM (mapTM f)) cletr, cm_case = mapTM (mapTM f) ccase
       , cm_ecase = mapTM (mapTM f) cecase, cm_tick = mapTM (mapTM f) ctick }

--------------------------
lookupCoreMap :: CoreMap a -> CoreExpr -> Maybe a
lookupCoreMap cm e = lkE emptyCME e cm

extendCoreMap :: CoreMap a -> CoreExpr -> a -> CoreMap a
extendCoreMap m e v = xtE emptyCME e (\_ -> Just v) m

foldCoreMap :: (a -> b -> b) -> b -> CoreMap a -> b
foldCoreMap k z m = fdE k m z

emptyCoreMap :: CoreMap a
emptyCoreMap = EmptyCM

instance Outputable a => Outputable (CoreMap a) where
  ppr m = text "CoreMap elts" <+> ppr (foldCoreMap (:) [] m)

-------------------------
fdE :: (a -> b -> b) -> CoreMap a -> b -> b
fdE _ EmptyCM = \z -> z
fdE k m
  = foldTM k (cm_var m)
  . foldTM k (cm_lit m)
  . foldTM k (cm_co m)
  . foldTM k (cm_type m)
  . foldTM (foldTM k) (cm_cast m)
  . foldTM (foldTM k) (cm_tick m)
  . foldTM (foldTM k) (cm_app m)
  . foldTM (foldTM k) (cm_lam m)
  . foldTM (foldTM (foldTM k)) (cm_letn m)
  . foldTM (foldTM (foldTM k)) (cm_letr m)
  . foldTM (foldTM k) (cm_case m)
  . foldTM (foldTM k) (cm_ecase m)

lkE :: CmEnv -> CoreExpr -> CoreMap a -> Maybe a
-- lkE: lookup in trie for expressions
lkE env expr cm
  | EmptyCM <- cm = Nothing
  | otherwise     = go expr cm
  where
    go (Var v)              = cm_var  >.> lkVar env v
    go (Lit l)              = cm_lit  >.> lkLit l
    go (Type t)             = cm_type >.> lkT env t
    go (Coercion c)         = cm_co   >.> lkC env c
    go (Cast e c)           = cm_cast >.> lkE env e >=> lkC env c
    go (Tick tickish e)     = cm_tick >.> lkE env e >=> lkTickish tickish
    go (App e1 e2)          = cm_app  >.> lkE env e2 >=> lkE env e1
    go (Lam v e)            = cm_lam  >.> lkE (extendCME env v) e >=> lkBndr env v
    go (Let (NonRec b r) e) = cm_letn >.> lkE env r
                              >=> lkE (extendCME env b) e >=> lkBndr env b
    go (Let (Rec prs) e)    = let (bndrs,rhss) = unzip prs
                                  env1 = extendCMEs env bndrs
                              in cm_letr
                                 >.> lkList (lkE env1) rhss >=> lkE env1 e
                                 >=> lkList (lkBndr env1) bndrs
    go (Case e b ty as)     -- See Note [Empty case alternatives]
               | null as    = cm_ecase >.> lkE env e >=> lkT env ty
               | otherwise  = cm_case >.> lkE env e
                              >=> lkList (lkA (extendCME env b)) as

xtE :: CmEnv -> CoreExpr -> XT a -> CoreMap a -> CoreMap a
xtE env e              f EmptyCM = xtE env e f wrapEmptyCM
xtE env (Var v)              f m = m { cm_var  = cm_var m  |> xtVar env v f }
xtE env (Type t)             f m = m { cm_type = cm_type m |> xtT env t f }
xtE env (Coercion c)         f m = m { cm_co   = cm_co m   |> xtC env c f }
xtE _   (Lit l)              f m = m { cm_lit  = cm_lit m  |> xtLit l f }
xtE env (Cast e c)           f m = m { cm_cast = cm_cast m |> xtE env e |>>
                                                 xtC env c f }
xtE env (Tick t e)           f m = m { cm_tick = cm_tick m |> xtE env e |>> xtTickish t f }
xtE env (App e1 e2)          f m = m { cm_app = cm_app m |> xtE env e2 |>> xtE env e1 f }
xtE env (Lam v e)            f m = m { cm_lam = cm_lam m |> xtE (extendCME env v) e
                                                 |>> xtBndr env v f }
xtE env (Let (NonRec b r) e) f m = m { cm_letn = cm_letn m
                                                 |> xtE (extendCME env b) e
                                                 |>> xtE env r |>> xtBndr env b f }
xtE env (Let (Rec prs) e)    f m = m { cm_letr = let (bndrs,rhss) = unzip prs
                                                     env1 = extendCMEs env bndrs
                                                 in cm_letr m
                                                    |>  xtList (xtE env1) rhss
                                                    |>> xtE env1 e
                                                    |>> xtList (xtBndr env1) bndrs f }
xtE env (Case e b ty as)     f m
                     | null as   = m { cm_ecase = cm_ecase m |> xtE env e |>> xtT env ty f }
                     | otherwise = m { cm_case = cm_case m |> xtE env e
                                                 |>> let env1 = extendCME env b
                                                     in xtList (xtA env1) as f }

type TickishMap a = Map.Map (Tickish Id) a
lkTickish :: Tickish Id -> TickishMap a -> Maybe a
lkTickish = lookupTM

xtTickish :: Tickish Id -> XT a -> TickishMap a -> TickishMap a
xtTickish = alterTM

------------------------
data AltMap a   -- A single alternative
  = AM { am_deflt :: CoreMap a
       , am_data  :: NameEnv (CoreMap a)
       , am_lit   :: LiteralMap (CoreMap a) }

instance TrieMap AltMap where
   type Key AltMap = CoreAlt
   emptyTM  = AM { am_deflt = emptyTM
                 , am_data = emptyNameEnv
                 , am_lit  = emptyLiteralMap }
   lookupTM = lkA emptyCME
   alterTM  = xtA emptyCME
   foldTM   = fdA
   mapTM    = mapA

mapA :: (a->b) -> AltMap a -> AltMap b
mapA f (AM { am_deflt = adeflt, am_data = adata, am_lit = alit })
  = AM { am_deflt = mapTM f adeflt
       , am_data = mapNameEnv (mapTM f) adata
       , am_lit = mapTM (mapTM f) alit }

lkA :: CmEnv -> CoreAlt -> AltMap a -> Maybe a
lkA env (DEFAULT,    _, rhs)  = am_deflt >.> lkE env rhs
lkA env (LitAlt lit, _, rhs)  = am_lit >.> lkLit lit >=> lkE env rhs
lkA env (DataAlt dc, bs, rhs) = am_data >.> lkNamed dc >=> lkE (extendCMEs env bs) rhs

xtA :: CmEnv -> CoreAlt -> XT a -> AltMap a -> AltMap a
xtA env (DEFAULT, _, rhs)    f m = m { am_deflt = am_deflt m |> xtE env rhs f }
xtA env (LitAlt l, _, rhs)   f m = m { am_lit   = am_lit m   |> xtLit l |>> xtE env rhs f }
xtA env (DataAlt d, bs, rhs) f m = m { am_data  = am_data m  |> xtNamed d
                                                             |>> xtE (extendCMEs env bs) rhs f }

fdA :: (a -> b -> b) -> AltMap a -> b -> b
fdA k m = foldTM k (am_deflt m)
        . foldTM (foldTM k) (am_data m)
        . foldTM (foldTM k) (am_lit m)

{-
************************************************************************
*                                                                      *
                   Coercions
*                                                                      *
************************************************************************
-}

-- We should really never care about the contents of a coercion. Instead,
-- just look up the coercion's type.
newtype CoercionMap a = CoercionMap (CoreTypeMap a)

instance TrieMap CoercionMap where
   type Key CoercionMap = Coercion
   emptyTM  = CoercionMap EmptyTM
   lookupTM = lkC emptyCME
   alterTM  = xtC emptyCME
   foldTM f (CoercionMap core_tm)      = foldTM f core_tm
   mapTM f (CoercionMap core_tm)       = CoercionMap (mapTM f core_tm)

lkC :: CmEnv -> Coercion -> CoercionMap a -> Maybe a
lkC env co (CoercionMap core_tm) = lkCT env (coercionType co) core_tm

xtC :: CmEnv -> Coercion -> XT a -> CoercionMap a -> CoercionMap a
xtC env co f (CoercionMap m) = CoercionMap (xtCT env (coercionType co) f m)

{-
************************************************************************
*                                                                      *
                   Types
*                                                                      *
************************************************************************
-}

-- NB: This respects the Note [Non-trivial definitional equality] in
-- TyCoRep. CoreTypeMap assumes any queries are with types of the same
-- kind as those stored in the map. It thus ignores casts/coercions.
data CoreTypeMap a
  = EmptyTM
  | TM { tm_var    :: VarMap a
       , tm_app    :: CoreTypeMap (CoreTypeMap a)
       , tm_fun    :: CoreTypeMap (CoreTypeMap a)
       , tm_tc_app :: NameEnv (ListMap CoreTypeMap a)
       , tm_forall :: CoreTypeMap (BinderMap a)
       , tm_tylit  :: TyLitMap a
       , tm_coerce :: Maybe a
       }

-- This is the real, kinded type map. It just looks up a kind, followed
-- by the type. All kinds are of sort *, so the first lookup is guaranteed
-- to be well-kinded.
newtype TypeMap a
  = TypeMap (CoreTypeMap (CoreTypeMap a))

-- | A 'LooseTypeMap' doesn't do a kind-check. Thus, when lookup up (t |> g),
-- you'll find entries inserted under (t), even if (g) is non-reflexive.
newtype LooseTypeMap a
  = LooseTypeMap (CoreTypeMap a)

instance Outputable a => Outputable (TypeMap a) where
  ppr m = text "TypeMap elts" <+> ppr (foldTypeMap (:) [] m)

foldTypeMap :: (a -> b -> b) -> b -> TypeMap a -> b
foldTypeMap k z m = foldTM k m z

emptyTypeMap :: TypeMap a
emptyTypeMap = emptyTM

lookupTypeMap :: TypeMap a -> Type -> Maybe a
lookupTypeMap cm t = lookupTM t cm

extendTypeMap :: TypeMap a -> Type -> a -> TypeMap a
extendTypeMap m t v = alterTM t (\_ -> Just v) m

wrapEmptyTypeMap :: CoreTypeMap a
wrapEmptyTypeMap = TM { tm_var    = emptyTM
                      , tm_app    = emptyTM
                      , tm_fun    = emptyTM
                      , tm_tc_app = emptyNameEnv
                      , tm_forall = EmptyTM
                      , tm_tylit  = emptyTyLitMap
                      , tm_coerce = Nothing }

instance TrieMap CoreTypeMap where
   type Key CoreTypeMap = Type
   emptyTM  = EmptyTM
   lookupTM = lkCT emptyCME
   alterTM  = xtCT emptyCME
   foldTM   = fdCT
   mapTM    = mapCT

instance TrieMap TypeMap where
  type Key TypeMap = Type
  emptyTM = TypeMap EmptyTM
  lookupTM = lkT emptyCME
  alterTM  = xtT emptyCME

  mapTM f (TypeMap core_tm) = TypeMap (mapTM (mapTM f) core_tm)
  foldTM f (TypeMap core_tm) = foldTM (foldTM f) core_tm

instance TrieMap LooseTypeMap where
  type Key LooseTypeMap = Type
  emptyTM = LooseTypeMap emptyTM
  lookupTM ty (LooseTypeMap core_tm) = lookupTM ty core_tm
  alterTM ty xt (LooseTypeMap core_tm) = LooseTypeMap (alterTM ty xt core_tm)
  mapTM f (LooseTypeMap core_tm) = LooseTypeMap (mapTM f core_tm)
  foldTM f (LooseTypeMap core_tm) = foldTM f core_tm

mapCT :: (a->b) -> CoreTypeMap a -> CoreTypeMap b
mapCT _ EmptyTM = EmptyTM
mapCT f (TM { tm_var  = tvar, tm_app = tapp, tm_fun = tfun
            , tm_tc_app = ttcapp, tm_forall = tforall, tm_tylit = tlit
            , tm_coerce = tco })
  = TM { tm_var    = mapTM f tvar
       , tm_app    = mapTM (mapTM f) tapp
       , tm_fun    = mapTM (mapTM f) tfun
       , tm_tc_app = mapNameEnv (mapTM f) ttcapp
       , tm_forall = mapTM (mapTM f) tforall
       , tm_tylit  = mapTM f tlit
       , tm_coerce = fmap f tco
       }

-----------------
lkT :: CmEnv -> Type -> TypeMap a -> Maybe a
lkT env ty (TypeMap m) = lkCT env (typeKind ty) m >>= lkCT env ty

lkCT :: CmEnv -> Type -> CoreTypeMap a -> Maybe a
lkCT env ty m
  | EmptyTM <- m = Nothing
  | otherwise    = go ty m
  where
    go ty | Just ty' <- coreView ty = go ty'
    go (TyVarTy v)          = tm_var    >.> lkVar env v
    go (AppTy t1 t2)        = tm_app    >.> lkCT env t1 >=> lkCT env t2
    go (TyConApp tc tys)    = tm_tc_app >.> lkNamed tc >=> lkList (lkCT env) tys
    go (LitTy l)            = tm_tylit  >.> lkTyLit l
    go (ForAllTy bndr ty)   = tm_forall >.> lkCT env' ty >=> lkB env bndr
      where env'
              | Just tv <- binderVar_maybe bndr = extendCME env tv
              | otherwise                       = env
    go (CastTy ty _)        = go ty
    go (CoercionTy {})      = tm_coerce

-----------------
xtT :: CmEnv -> Type -> XT a -> TypeMap a -> TypeMap a
xtT env ty f (TypeMap m) = TypeMap (m |> xtCT env (typeKind ty) |>> xtCT env ty f)

xtCT :: CmEnv -> Type -> XT a -> CoreTypeMap a -> CoreTypeMap a
xtCT env ty f m
  | EmptyTM <- m            = xtCT env ty  f wrapEmptyTypeMap
  | Just ty' <- coreView ty = xtCT env ty' f m

xtCT env (TyVarTy v)       f  m     = m { tm_var    = tm_var m |> xtVar env v f }
xtCT env (AppTy t1 t2)     f  m     = m { tm_app    = tm_app m |> xtCT env t1 |>> xtCT env t2 f }
xtCT env (ForAllTy bndr ty) f m     = m { tm_forall = tm_forall m
                                                 |> xtCT env' ty
                                                 |>> xtB env bndr f }
  where env'
          | Just tv <- binderVar_maybe bndr = extendCME env tv
          | otherwise                       = env
xtCT env (TyConApp tc tys) f  m     = m { tm_tc_app = tm_tc_app m |> xtNamed tc
                                                 |>> xtList (xtCT env) tys f }
xtCT _   (LitTy l)         f  m     = m { tm_tylit  = tm_tylit m |> xtTyLit l f }
xtCT env (CastTy ty _)     f  m     = xtCT env ty f m
xtCT _   (CoercionTy {})   f  m     = m { tm_coerce = tm_coerce m |> f }

fdCT :: (a -> b -> b) -> CoreTypeMap a -> b -> b
fdCT _ EmptyTM = \z -> z
fdCT k m = foldTM k (tm_var m)
        . foldTM (foldTM k) (tm_app m)
        . foldTM (foldTM k) (tm_fun m)
        . foldTM (foldTM k) (tm_tc_app m)
        . foldTM (foldTM k) (tm_forall m)
        . foldTyLit k (tm_tylit m)
        . foldMaybe k (tm_coerce m)

------------------------
data BinderMap a
  = BM { bm_named_vis   :: VarMap a
       , bm_named_invis :: VarMap a
       , bm_anon        :: TypeMap a
       }

instance Outputable a => Outputable (BinderMap a) where
  ppr m = text "BinderMap elts" <+> ppr (foldBinderMap (:) [] m)

foldBinderMap :: (a -> b -> b) -> b -> BinderMap a -> b
foldBinderMap k z m = fdB k m z

emptyBinderMap :: BinderMap a
emptyBinderMap = BM { bm_named_vis   = emptyTM
                    , bm_named_invis = emptyTM
                    , bm_anon        = emptyTM }

instance TrieMap BinderMap where
   type Key BinderMap = Binder
   emptyTM  = emptyBinderMap
   lookupTM = lkB emptyCME
   alterTM  = xtB emptyCME
   foldTM   = fdB
   mapTM    = mapB

mapB :: (a->b) -> BinderMap a -> BinderMap b
mapB f (BM { bm_named_vis = n_vis, bm_named_invis = n_invis,
             bm_anon = anon })
  = BM { bm_named_vis   = mapTM f n_vis
       , bm_named_invis = mapTM f n_invis
       , bm_anon        = mapTM f anon
       }

lkB :: CmEnv -> Binder -> BinderMap a -> Maybe a
lkB env = go
  where
    go bndr
      | Just v <- binderVar_maybe bndr
      = case binderVisibility bndr of
          Visible   -> bm_named_vis   >.> lkVar env v
          Invisible -> bm_named_invis >.> lkVar env v
      | otherwise
      = bm_anon >.> lkT env (binderType bndr)

xtB :: CmEnv -> Binder -> XT a -> BinderMap a -> BinderMap a
xtB env bndr f m
  | Just v <- binderVar_maybe bndr
  = case binderVisibility bndr of
      Visible ->   m { bm_named_vis   = bm_named_vis m   |> xtVar env v f }
      Invisible -> m { bm_named_invis = bm_named_invis m |> xtVar env v f }
  | otherwise
  = m { bm_anon = bm_anon m |> xtT env (binderType bndr) f }

fdB :: (a -> b -> b) -> BinderMap a -> b -> b
fdB k m = foldTM k (bm_named_vis m)
        . foldTM k (bm_named_invis m)
        . foldTM k (bm_anon m)

------------------------
data TyLitMap a = TLM { tlm_number :: Map.Map Integer a
                      , tlm_string :: Map.Map FastString a
                      }

instance TrieMap TyLitMap where
   type Key TyLitMap = TyLit
   emptyTM  = emptyTyLitMap
   lookupTM = lkTyLit
   alterTM  = xtTyLit
   foldTM   = foldTyLit
   mapTM    = mapTyLit

emptyTyLitMap :: TyLitMap a
emptyTyLitMap = TLM { tlm_number = Map.empty, tlm_string = Map.empty }

mapTyLit :: (a->b) -> TyLitMap a -> TyLitMap b
mapTyLit f (TLM { tlm_number = tn, tlm_string = ts })
  = TLM { tlm_number = Map.map f tn, tlm_string = Map.map f ts }

lkTyLit :: TyLit -> TyLitMap a -> Maybe a
lkTyLit l =
  case l of
    NumTyLit n -> tlm_number >.> Map.lookup n
    StrTyLit n -> tlm_string >.> Map.lookup n

xtTyLit :: TyLit -> XT a -> TyLitMap a -> TyLitMap a
xtTyLit l f m =
  case l of
    NumTyLit n -> m { tlm_number = tlm_number m |> Map.alter f n }
    StrTyLit n -> m { tlm_string = tlm_string m |> Map.alter f n }

foldTyLit :: (a -> b -> b) -> TyLitMap a -> b -> b
foldTyLit l m = flip (Map.fold l) (tlm_string m)
              . flip (Map.fold l) (tlm_number m)

{-
************************************************************************
*                                                                      *
                   Variables
*                                                                      *
************************************************************************
-}

type BoundVar = Int  -- Bound variables are deBruijn numbered
type BoundVarMap a = IntMap.IntMap a

data CmEnv = CME { cme_next :: BoundVar
                 , cme_env  :: VarEnv BoundVar }

emptyCME :: CmEnv
emptyCME = CME { cme_next = 0, cme_env = emptyVarEnv }

extendCME :: CmEnv -> Var -> CmEnv
extendCME (CME { cme_next = bv, cme_env = env }) v
  = CME { cme_next = bv+1, cme_env = extendVarEnv env v bv }

extendCMEs :: CmEnv -> [Var] -> CmEnv
extendCMEs env vs = foldl extendCME env vs

lookupCME :: CmEnv -> Var -> Maybe BoundVar
lookupCME (CME { cme_env = env }) v = lookupVarEnv env v

--------- Variable binders -------------

-- | A 'BndrMap' is a 'TypeMap' which allows us to distinguish between
-- binding forms whose binders have different types.  For example,
-- if we are doing a 'TrieMap' lookup on @\(x :: Int) -> ()@, we should
-- not pick up an entry in the 'TrieMap' for @\(x :: Bool) -> ()@:
-- we can disambiguate this by matching on the type (or kind, if this
-- a binder in a type) of the binder.
type BndrMap = TypeMap

lkBndr :: CmEnv -> Var -> BndrMap a -> Maybe a
lkBndr env v m = lkT env (varType v) m

xtBndr :: CmEnv -> Var -> XT a -> BndrMap a -> BndrMap a
xtBndr env v f = xtT env (varType v) f

--------- Variable occurrence -------------
data VarMap a = VM { vm_bvar   :: BoundVarMap a  -- Bound variable
                   , vm_fvar   :: VarEnv a }      -- Free variable

instance TrieMap VarMap where
   type Key VarMap = Var
   emptyTM  = VM { vm_bvar = IntMap.empty, vm_fvar = emptyVarEnv }
   lookupTM = lkVar emptyCME
   alterTM  = xtVar emptyCME
   foldTM   = fdVar
   mapTM    = mapVar

mapVar :: (a->b) -> VarMap a -> VarMap b
mapVar f (VM { vm_bvar = bv, vm_fvar = fv })
  = VM { vm_bvar = mapTM f bv, vm_fvar = mapVarEnv f fv }

lkVar :: CmEnv -> Var -> VarMap a -> Maybe a
lkVar env v
  | Just bv <- lookupCME env v = vm_bvar >.> lookupTM bv
  | otherwise                  = vm_fvar >.> lkFreeVar v

xtVar :: CmEnv -> Var -> XT a -> VarMap a -> VarMap a
xtVar env v f m
  | Just bv <- lookupCME env v = m { vm_bvar = vm_bvar m |> xtInt bv f }
  | otherwise                  = m { vm_fvar = vm_fvar m |> xtFreeVar v f }

fdVar :: (a -> b -> b) -> VarMap a -> b -> b
fdVar k m = foldTM k (vm_bvar m)
          . foldTM k (vm_fvar m)

lkFreeVar :: Var -> VarEnv a -> Maybe a
lkFreeVar var env = lookupVarEnv env var

xtFreeVar :: Var -> XT a -> VarEnv a -> VarEnv a
xtFreeVar v f m = alterVarEnv f m v
