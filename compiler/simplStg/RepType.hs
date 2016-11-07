{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}

module RepType
  ( -- * Code generator views onto Types
    UnaryType, NvUnaryType, isNvUnaryType,
    RepType(..), repType, isUnaryRep, isMultiRep,

    -- * Predicates on types
    isVoidTy, typePrimRep,

    -- * Type representation for the code generator
    countConRepArgs, idFunRepArity, tyConPrimRep,

    -- * Unboxed sum representation type
    ubxSumRepType, lookupUbxSumSlots
  ) where

#include "HsVersions.h"

import BasicTypes (Arity, RepArity)
import DataCon
import Id
import Outputable
import PrelNames
import TyCon
import TyCoRep
import Type
import TysPrim
import TysWiredIn
import Util

import Data.List (foldl', sort)
import Data.Maybe (maybeToList)
import qualified Data.IntSet as IS

{- **********************************************************************
*                                                                       *
                Representation types
*                                                                       *
********************************************************************** -}

type UnaryType   = Type
     -- A value type; i.e. its kind is TYPE rr
     -- for some rr; moreover the rr is never a variable.
     --
     --   UnaryType   : never an unboxed tuple or sum, nor void

isUnaryType :: Type -> Bool
isUnaryType = isUnaryRep . repType

data RepType
  = MultiRep [PrimRep]   -- Represented by multiple values (e.g. unboxed tuple or sum);
                        -- INVARIANT: List is never a singleton (but may be empty)
  | UnaryRep UnaryType PrimRep
                        -- Represented by a single non-void value
                        -- The UnaryType in there has no foralls, newtypes, etc.

instance Outputable RepType where
  ppr (MultiRep reps) = text "MultiRep" <+> ppr reps
  ppr (UnaryRep ty)   = text "UnaryRep" <+> ppr ty

isMultiRep :: RepType -> Bool
isMultiRep (MultiRep _) = True
isMultiRep _            = False

isUnaryRep :: RepType -> Bool
isUnaryRep (UnaryRep _) = True
isUnaryRep _            = False

-- | 'repType' figure out how a type will be represented at runtime. It
-- simply looks at the kind of the type, as described in
-- Note [TYPE and RuntimeRep] in TysPrim
repType :: Type -> RepType
repType ty
  | [_] <- prim_reps
  = UnaryRep (unwrap ty)
  | otherwise
  = MultiRep prim_reps
  where
    prim_reps = kindRepType (text "repType ty" <+> ppr ty $$ ppr (typeKind ty))
                            (typeKind ty)

-- | Gets rid of the stuff that prevents us from understanding the
-- runtime representation of a type. Including:
--   1. Casts
--   2. Newtypes
--   3. Foralls
--   4. Synonyms
-- But not type/data families, because we don't have the envs to hand.
unwrap :: Type -> Type
unwrap ty
  | Just unwrapped <- topNormaliseTypeX stepper mappend inner_ty
  = unwrapped
  | otherwise
  = inner_ty
  where
    inner_ty = go ty

    go t | Just t' <- coreView t = go t'
    go (ForAllTy _ t)            = go t
    go (CastTy t _)              = go t
    go t                         = t

     -- cf. Coercion.unwrapNewTypeStepper
    stepper rec_nts tc tys
      | Just (ty', _) <- instNewTyCon_maybe tc tys
      = case checkRecTc rec_nts tc of
          Just rec_nts' -> NS_Step rec_nts' (go ty') ()
          Nothing       -> NS_Abort   -- infinite newtypes
      | otherwise
      = NS_Done

idFunRepArity :: Id -> RepArity
idFunRepArity x = countFunRepArgs (idArity x) (idType x)

countFunRepArgs :: Arity -> Type -> RepArity
countFunRepArgs 0 _
  = 0
countFunRepArgs n ty
  | FunTy arg res <- unwrap ty
  = length (typePrimRep arg) + countFunRepArgs (n - 1) res
  | otherwise
  = pprPanic "countFunRepArgs: arity greater than type can handle" (ppr (n, ty, repType ty))

countConRepArgs :: DataCon -> RepArity
countConRepArgs dc = go (dataConRepArity dc) (dataConRepType dc)
  where
    go :: Arity -> Type -> RepArity
    go 0 _
      = 0
    go n ty
      | UnaryRep (FunTy arg res) _ <- repType ty
      = length (repTypeSlots (repType arg)) + go (n - 1) res
      | otherwise
      = pprPanic "countConRepArgs: arity greater than type can handle" (ppr (n, ty, repType ty))

-- | True if the type has zero width.
isVoidTy :: Type -> Bool
isVoidTy ty = typePrimRep ty == VoidRep


{- **********************************************************************
*                                                                       *
                Unboxed sums
 See Note [Translating unboxed sums to unboxed tuples] in UnariseStg.hs
*                                                                       *
********************************************************************** -}

type SortedPrimReps = [PrimRep]

-- | Given the arguments of a sum type constructor application,
--   return the unboxed sum rep type.
--
-- E.g.
--
--   (# Int | Maybe Int | (# Int, Bool #) #)
--
-- We call `ubxSumRepType [ [PtrRep], [PtrRep], [PtrRep,PtrRep] ]`,
-- which returns [WordRep, PtrRep, PtrRep]
--
-- INVARIANT: Result slots are sorted (via compareSlots), except that at the head
-- of the list we have the slot for the tag.
ubxSumRepType :: [[PrimRep]] -> [PrimRep]
ubxSumRepType constrs0 =
  ASSERT2( length constrs0 > 1, ppr constrs0 ) -- otherwise it isn't a sum type
  let
    combine_alts :: [SortedPrimReps]  -- slots of constructors
                 -> SortedPrimReps    -- final slots
    combine_alts constrs = foldl' merge [] constrs

    merge :: SortedPrimReps -> SortedPrimReps -> SortedPrimReps
    merge existing_slots []
      = existing_slots
    merge [] needed_slots
      = needed_slots
    merge (es : ess) (s : ss)
      | Just s' <- s `fitsIn` es
      = -- found a slot, use it
        s' : merge ess ss
      | LT <- compareSlots s es
      = -- we need a new slot and this is the right place for it
        s : merge (es : ess) ss
      | otherwise
      = -- keep searching for a slot
        es : merge ess (s : ss)

    -- Nesting unboxed tuples and sums is OK, so we need to flatten first.
    rep :: [PrimRep] -> SortedPrimReps
    rep ty = sortBy compareSlots (typePrimRep ty)

    sumRep = WordRep : combine_alts (map rep constrs0)
             -- WordRep: for the tag of the sum
  in
    sumRep

lookupUbxSumSlots
       :: SortedPrimReps -- Layout of sum. Does not include tag.
                         -- We assume that they are in increasing order
       -> [PrimRep]      -- Reps of things we want to map to locations in the
                         -- sum layout
       -> [Int]          -- Where to map 'things' in the sum layout
lookupUbxSumSlots sum_slots0 arg_slots0 =
    go arg_slots0 IS.empty
  where
    go :: [PrimRep] -> IS.IntSet -> [Int]
    go [] _
      = []
    go (arg : args) used
      = let slot_idx = findSlot arg 0 sum_slots0 used
         in slot_idx : go args (IS.insert slot_idx used)

    findSlot :: PrimRep -> Int -> SortedPrimReps -> IS.IntSet -> Int
    findSlot arg slot_idx (slot : slots) useds
      | not (IS.member slot_idx useds)
      , Just EQ <- compareSlots slot <$> (arg `fitsIn` slot)
      = slot_idx
      | otherwise
      = findSlot arg (slot_idx + 1) slots useds
    findSlot _ _ [] _
      = pprPanic "findSlot" (text "Can't find slot" $$ ppr sum_slots0 $$ ppr arg_slots0)

--------------------------------------------------------------------------------

{- Note [Slot types]
~~~~~~~~~~~~~~~~~~~~
We have 5 kinds of slots:

  - Pointer slot: Only shared between actual pointers to Haskell heap (i.e.
    boxed objects)

  - Word slots: Shared between IntRep, WordRep, AddrRep.

  - Word64 slots: Shared between Int64Rep and Word64Rep

  - Float slots: FloatRep

  - Double slots: DoubleRep

Order is important! If slot A could fit into slot B
then slot A must occur first.  E.g.  FloatSlot before DoubleSlot

We are assuming that WordSlot is smaller than or equal to Word64Slot
(would not be true on a 128-bit machine)

At one point, there was a SlotTy type that had 5 constructors. But it
seems easier just to write the following function:
-}

-- | Compare PrimReps according to their "slot type"; see
-- Note [Slot types].
compareSlots :: PrimRep -> PrimRep -> Ordering
compareSlots = compare `on` get_slot
  where
    get_slot PtrRep = 1
    get_slot IntRep = 2
    get_slot WordRep = 2
    get_slot Int64Rep = 3
    get_slot Word64Rep = 3
    get_slot AddrRep = 2
    get_slot FloatRep = 4
    get_slot DoubleRep = 5
    get_slot (VecRep {}) = pprPanic "compareSlots" (text "No slot for VecRep")

-- | Returns the bigger type if one fits into the other. (commutative)
fitsIn :: PrimRep -> PrimRep -> Maybe PrimRep
fitsIn ty1 ty2
  | isWordRep ty1 && isWordRep ty2
  = Just bigger
  | isFloatRep ty1 && isFloatRep ty2
  = Just bigger
  | isPtrSlot ty1 && isPtrSlot ty2
  = Just PtrRep
  | otherwise
  = Nothing
  where
    bigger
      | LT <- compareSlots ty1 ty2 = ty2
      | otherwise                  = ty1

    isPtrRep PtrRep = True
    isPtrRep _      = False

    isWordRep Word64Rep = True
    isWordRep WordRep   = True
    isWordRep Int64Rep  = True
    isWordRep IntRep    = True
    isWordRep AddrRep   = True
    isWordRep _         = False

    isFloatRep DoubleRep = True
    isFloatRep FloatRep  = True
    isFloatRep _         = False


{- **********************************************************************
*                                                                       *
                   PrimRep
*                                                                       *
********************************************************************** -}

-- | Discovers the primitive representation of a more abstract 'UnaryType'
typePrimRep :: HasDebugCallStack => Type -> [PrimRep]
typePrimRep ty = kindPrimRep (text "kindRep ty" <+> ppr ty $$ ppr (typeKind ty))
                             (typeKind ty)

-- | Find the runtime representation of a 'TyCon', as a list of PrimReps
-- of the components of its runtime representation. Defined here to
-- avoid module loops.
-- NB: These days, this function /can/ handle unboxed tuples/sums.
tyConPrimRep :: HasDebugCallStack => TyCon -> [PrimRep]
tyConPrimRep tc
  = kindPrimRep (text "kindRep tc" <+> ppr tc $$ ppr res_kind)
                res_kind
  where
    res_kind = tyConResKind tc

-- | Returns the representation of types of this kind
kindPrimRep :: HasDebugCallStack => SDoc -> Kind -> [PrimRep]
kindPrimRep doc ki
  | Just ki' <- coreViewOneStarKind ki
  = kindPrimRep doc ki'
kindPrimRep _ (TyConApp typ [runtime_rep])
  = ASSERT( typ `hasKey` tYPETyConKey )
    go runtime_rep
  where
    go :: Type  -- of kind RuntimeRep
       -> [PrimRep]
    go = concat $ map_type_list go_unary

    go_unary :: Type  -- of kind UnaryRep
             -> [PrimRep]   -- returns a list b/c of UnboxedSumRep
    go_unary u | Just u' <- coreView u = go_unary u'
    go_unary (TyConApp u_dc args)
      | u_dc `hasKey` unboxedSumRepDataConKey
      , [rrs] <- args   -- rrs is a Type of kind [[UnaryRep]]
      = let prim_rep_lists = map_type_list go rrs
      | RuntimeRep fun <- tyConRuntimeRepInfo u_dc
      = fun args
    go_unary u
      = pprPanic "kindPrimRep.go_unary" (ppr u $$ doc)

    map_type_list :: (Type {- :: a -} -> b) -> Type {- :: [a] -} -> [b]
    map_type_list f ty
      | Just ty' <- coreView ty = map_type_list f ty'
    map_type_list _ (TyConApp nil _)
      | nil `hasKey` nilDataConKey
      = []
    map_type_list f (TyConApp cons [_ki, x, xs])
      = ASSERT( cons `hasKey` consDataConKey )
          -- if this fails, the call is ill-kinded
        f x : map_type_list f xs
    map_type_list _ ty
      = pprPanic "kindPrimRep.map_type_list" (ppr ty $$ doc)

kindPrimRep doc ki
  = WARN( True, text "kindPrimRep defaulting to PtrRep on" <+> ppr ki $$ doc )
    PtrRep  -- this can happen legitimately for, e.g., Any
            -- TODO (RAE): Check above comment.

-- | Convert a PrimRep to a Type with that representation.
-- This is needed during unarisation when we need to cons up fresh
-- Ids to take the place of components of an unboxed tuple.
primRepToType :: PrimRep -> Type
primRepToType rep
  = anyTypeOfKind (tYPE (mkPromotedListTy unaryRepTy [primRepToUnaryRep rep]))

-- | Convert a PrimRep to the corresponding promoted UnaryRep constructor
primRepToUnaryRep :: PrimRep -> Type -- of kind UnaryRep
  -- TODO (RAE): Why lifted? It's what was here before, but I'm skeptical
primRepToUnaryRep PtrRep       = ptrRepLiftedDataConTy
primRepToUnaryRep IntRep       = intRepDataConTy
primRepToUnaryRep WordRep      = wordRepDataConTy
primRepToUnaryRep Int64Rep     = int64RepDataConTy
primRepToUnaryRep Word64Rep    = word64RepDataConTy
primRepToUnaryRep AddrRep      = addrRepDataConTy
primRepToUnaryRep FloatRep     = floatRepDataConTy
primRepToUnaryRep DoubleRep    = doubleRepDataConTy
primRepToUnaryRep (VecRep c e) = mkTyConApp vecRepDataConTyCon [ to_count c
                                                               , to_elem e ]
  where
    to_count 2 = vec2DataConTy
    to_count 4 = vec4DataConTy
    to_count 8 = vec8DataConTy
    to_count 16 = vec16DataConTy
    to_count 32 = vec32DataConTy
    to_count 64 = vec64DataConTy

    to_elem Int8ElemRep   = int8ElemRepDataConTy
    to_elem Int16ElemRep  = int16ElemRepDataConTy
    to_elem Int32ElemRep  = int32ElemRepDataConTy
    to_elem Int64ElemRep  = int64ElemRepDataConTy
    to_elem Word8ElemRep  = word8ElemRepDataConTy
    to_elem Word16ElemRep = word16ElemRepDataConTy
    to_elem Word32ElemRep = word32ElemRepDataConTy
    to_elem Word64ElemRep = word64ElemRepDataConTy
    to_elem FloatElemRep  = floatElemRepDataConTy
    to_elem DoubleElemRep = doubleElemRepDataConTy
