{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}

module Data.Dependent.Map.Monoidal.NonEmpty
    ( MonoidalNonEmptyDMap(..)
    , DSum(..), Some(..)
    , GCompare(..), GOrdering(..)

    -- * non-empty specific
    , nonEmpty
    , toDMap

    -- * Operators
    , (!), (\\)

    -- * Query
    , null
    , size
    , member
    , notMember
    , lookup
    , findWithDefault

    -- * Construction
    , singleton

    -- ** Insertion
    , insert
    , insertWith
    , insertWith'
    , insertWithKey
    , insertWithKey'
    , insertLookupWithKey
    , insertLookupWithKey'

    -- ** Delete\/Update
    , delete
    , adjust
    , adjustF
    , adjustWithKey
    , adjustWithKey'
    , update
    , updateWithKey
    , updateLookupWithKey
    , alter
    , alterF

    -- * Combine

    -- ** Union
    --, union
    , unionWithKey
    --, unions
    , unionsWithKey

    -- ** Difference
    , difference
    , differenceWithKey

    -- ** Intersection
    --, intersection
    , intersectionWithKey

    -- * Traversal
    -- ** Map
    , map
    , mapWithKey
    , traverseWithKey
    , mapAccumLWithKey
    , mapAccumRWithKey
    , mapKeysWith
    , mapKeysMonotonic

    -- ** Fold
    --, foldWithKey
    , foldrWithKey
    , foldlWithKey
    -- , foldlWithKey'

    -- * Conversion
    , keys
    , assocs

    -- ** Lists
    , toList
    , fromList
    , fromListWithKey

    -- ** Ordered lists
    , toAscList
    , toDescList
    , fromAscList
    , fromAscListWithKey
    , fromDistinctAscList

    -- * Filter
    , filter
    , filterWithKey
    , partitionWithKey

    , mapMaybe
    , mapMaybeWithKey
    , mapEitherWithKey

    , split
    , splitLookup

    -- * Submap
    , isSubmapOf, isSubmapOfBy
    , isProperSubmapOf, isProperSubmapOfBy

    -- * Indexed
    , lookupIndex
    , findIndex
    , elemAt
    , updateAt
    , deleteAt

    -- * Min\/Max
    , findMin
    , findMax
    , lookupMin
    , lookupMax
    , deleteMin
    , deleteMax
    , deleteFindMin
    , deleteFindMax
    , updateMinWithKey
    , updateMaxWithKey
    , minViewWithKey
    , maxViewWithKey

    -- * Debugging
    , showTree
    , showTreeWith
    , valid
    ) where

import Prelude hiding (null, lookup, map)
import Data.Aeson
import Data.Coerce
import Data.Constraint.Extras
import Data.Constraint.Forall
import Data.Dependent.Map.NonEmpty (NonEmptyDMap)
import qualified Data.Dependent.Map.NonEmpty as NonEmptyDMap
import Data.Dependent.Map.Monoidal (MonoidalDMap (..))
import Data.Dependent.Sum
import Data.Dependent.Sum.Orphans ()
import Data.GADT.Compare
import Data.GADT.Show
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe
import Data.Semigroup
import Data.Some hiding (This)
import Text.Read
import Prelude hiding (lookup, map)

newtype MonoidalNonEmptyDMap (f :: k -> *) (g :: k -> *) = MonoidalNonEmptyDMap { unMonoidalNonEmptyDMap :: NonEmptyDMap f g }

instance forall f g. (Has' Eq f g, GCompare f) => Eq (MonoidalNonEmptyDMap f g) where
  MonoidalNonEmptyDMap m == MonoidalNonEmptyDMap m' = m == m'

instance forall f g. (Has' Eq f g, Has' Ord f g, GCompare f) => Ord (MonoidalNonEmptyDMap f g) where
  compare (MonoidalNonEmptyDMap m) (MonoidalNonEmptyDMap m') = compare m m'

instance (Show (DSum k f)) => Show (MonoidalNonEmptyDMap k f) where
    showsPrec p m = showParen (p>10)
        ( showString "fromList "
        . showsPrec 11 (coerce (toList m) :: NonEmpty (DSum k f))
        )

instance (GCompare k, Read (DSum k f)) => Read (MonoidalNonEmptyDMap k f) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    xs <- readPrec
    return . MonoidalNonEmptyDMap . NonEmptyDMap.fromList $ coerce (xs :: NonEmpty (DSum k f))
  readListPrec = readListPrecDefault

deriving instance (ToJSON (NonEmptyDMap f g)) => ToJSON (MonoidalNonEmptyDMap f g)

instance (Has' Semigroup f g, GCompare f) => Semigroup (MonoidalNonEmptyDMap f g) where
  (MonoidalNonEmptyDMap m) <> (MonoidalNonEmptyDMap n) =
    MonoidalNonEmptyDMap (NonEmptyDMap.unionWithKey (\f (u :: g a) v -> has' @Semigroup @g f (u <> v)) m n)

deriving instance (FromJSON (NonEmptyDMap f g)) => FromJSON (MonoidalNonEmptyDMap f g)

{--------------------------------------------------------------------
  NonEmpty* Specific
--------------------------------------------------------------------}

toDMap :: MonoidalNonEmptyDMap k f -> MonoidalDMap k f
toDMap = MonoidalDMap . NonEmptyDMap.toDMap . unMonoidalNonEmptyDMap

nonEmpty :: MonoidalDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
nonEmpty = fmap MonoidalNonEmptyDMap . NonEmptyDMap.nonEmpty . unMonoidalDMap

{--------------------------------------------------------------------
  Operators
--------------------------------------------------------------------}
infixl 9 !,\\ --

-- | /O(log n)/. Find the value at a key.
-- Calls 'error' when the element can not be found.
--
-- > fromList [(5,'a'), (3,'b')] ! 1    Error: element not in the map
-- > fromList [(5,'a'), (3,'b')] ! 5 == 'a'

(!) :: GCompare k => MonoidalNonEmptyDMap k f -> k v -> f v
(!) (MonoidalNonEmptyDMap m) k = m NonEmptyDMap.! k

-- | Same as 'difference'.
(\\) :: GCompare k => MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
(MonoidalNonEmptyDMap m1) \\ (MonoidalNonEmptyDMap m2) = fmap MonoidalNonEmptyDMap $ NonEmptyDMap.difference m1 m2

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | /O(1)/. A map with a single element.
--
-- > singleton 1 'a'        == fromList [(1, 'a')]
-- > size (singleton 1 'a') == 1
singleton :: k v -> f v -> MonoidalNonEmptyDMap k f
singleton k x = MonoidalNonEmptyDMap (NonEmptyDMap.singleton k x)

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- | /O(1)/. The number of elements in the map.
size :: MonoidalNonEmptyDMap k f -> Int
size (MonoidalNonEmptyDMap m) = NonEmptyDMap.size m

-- | /O(log n)/. Lookup the value at a key in the map.
--
-- The function will return the corresponding value as @('Just' value)@,
-- or 'Nothing' if the key isn't in the map.
lookup :: forall k f v. GCompare k => k v -> MonoidalNonEmptyDMap k f -> Maybe (f v)
lookup k (MonoidalNonEmptyDMap m) = NonEmptyDMap.lookup k m


-- | /O(log n)/. Delete and find the minimal element.
--
-- > deleteFindMin (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((3,"b"), fromList[(5,"a"), (10,"c")])
-- > deleteFindMin                                            Error: can not return the minimal element of an empty map

deleteFindMin :: MonoidalNonEmptyDMap k f -> (DSum k f, Maybe (MonoidalNonEmptyDMap k f))
deleteFindMin (MonoidalNonEmptyDMap m) =
  (fmap . fmap) MonoidalNonEmptyDMap $ NonEmptyDMap.deleteFindMin m

-- | /O(log n)/. Retrieves the minimal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
minViewWithKey :: forall k f . MonoidalNonEmptyDMap k f -> (DSum k f, Maybe (MonoidalNonEmptyDMap k f))
minViewWithKey (MonoidalNonEmptyDMap m) =
  (fmap . fmap) MonoidalNonEmptyDMap $ NonEmptyDMap.minViewWithKey m

-- | /O(log n)/. Retrieves the maximal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
maxViewWithKey :: forall k f . MonoidalNonEmptyDMap k f -> (DSum k f, Maybe (MonoidalNonEmptyDMap k f))
maxViewWithKey (MonoidalNonEmptyDMap m) =
  (fmap . fmap) MonoidalNonEmptyDMap $ NonEmptyDMap.maxViewWithKey m

-- | /O(log n)/. Delete and find the maximal element.
--
-- > deleteFindMax (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((10,"c"), fromList [(3,"b"), (5,"a")])
-- > deleteFindMax empty                                      Error: can not return the maximal element of an empty map

deleteFindMax :: MonoidalNonEmptyDMap k f -> (DSum k f, Maybe (MonoidalNonEmptyDMap k f))
deleteFindMax (MonoidalNonEmptyDMap m) =
  (fmap . fmap) MonoidalNonEmptyDMap $ NonEmptyDMap.deleteFindMax m

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- | /O(log n)/. Is the key a member of the map? See also 'notMember'.
member :: GCompare k => k a -> MonoidalNonEmptyDMap k f -> Bool
member k = isJust . lookup k

-- | /O(log n)/. Is the key not a member of the map? See also 'member'.
notMember :: GCompare k => k v -> MonoidalNonEmptyDMap k f -> Bool
notMember k m = not (member k m)

-- | /O(log n)/. Find the value at a key.
-- Calls 'error' when the element can not be found.
-- Consider using 'lookup' when elements may not be present.
find :: GCompare k => k v -> MonoidalNonEmptyDMap k f -> f v
find k m = case lookup k m of
    Nothing -> error "MonoidalNonEmptyDMap.find: element not in the map"
    Just v  -> v

-- | /O(log n)/. The expression @('findWithDefault' def k map)@ returns
-- the value at key @k@ or returns default value @def@
-- when the key is not in the map.
findWithDefault :: GCompare k => f v -> k v -> MonoidalNonEmptyDMap k f -> f v
findWithDefault def k m = case lookup k m of
    Nothing -> def
    Just v  -> v

{--------------------------------------------------------------------
  Insertion
--------------------------------------------------------------------}

-- | /O(log n)/. Insert a new key and value in the map.
-- If the key is already present in the map, the associated value is
-- replaced with the supplied value. 'insert' is equivalent to
-- @'insertWith' 'const'@.
insert :: forall k f v. GCompare k => k v -> f v -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f
insert k v (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.insert k v m)

-- | /O(log n)/. Insert with a function, combining new value and old value.
-- @'insertWith' f key value mp@
-- will insert the entry @key :=> value@ into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the entry @key :=> f new_value old_value@.
insertWith :: GCompare k => (f v -> f v -> f v) -> k v -> f v -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f
insertWith f k v (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.insertWith f k v m)

-- | Same as 'insertWith', but the combining function is applied strictly.
-- This is often the most desirable behavior.
insertWith' :: GCompare k => (f v -> f v -> f v) -> k v -> f v -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f
insertWith' f k v (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.insertWith' f k v m)

-- | /O(log n)/. Insert with a function, combining key, new value and old value.
-- @'insertWithKey' f key value mp@
-- will insert the entry @key :=> value@ into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the entry @key :=> f key new_value old_value@.
-- Note that the key passed to f is the same key passed to 'insertWithKey'.
insertWithKey :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f
insertWithKey f k v (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.insertWithKey f k v m)

-- | Same as 'insertWithKey', but the combining function is applied strictly.
insertWithKey' :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f
insertWithKey' f k v (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.insertWithKey' f k v m)


-- | /O(log n)/. Combines insert operation with old value retrieval.
-- The expression (@'insertLookupWithKey' f k x map@)
-- is a pair where the first element is equal to (@'lookup' k map@)
-- and the second element equal to (@'insertWithKey' f k x map@).
insertLookupWithKey :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> MonoidalNonEmptyDMap k f
                    -> (Maybe (f v), MonoidalNonEmptyDMap k f)
insertLookupWithKey f k v (MonoidalNonEmptyDMap m) =
  case NonEmptyDMap.insertLookupWithKey f k v m of
    (x, y) -> (x, MonoidalNonEmptyDMap y)

-- | /O(log n)/. A strict version of 'insertLookupWithKey'.
insertLookupWithKey' :: forall k f v. GCompare k => (k v -> f v -> f v -> f v) -> k v -> f v -> MonoidalNonEmptyDMap k f
                     -> (Maybe (f v), MonoidalNonEmptyDMap k f)
insertLookupWithKey' f k v (MonoidalNonEmptyDMap m) =
  case NonEmptyDMap.insertLookupWithKey' f k v m of
    (x, y) -> (x, MonoidalNonEmptyDMap y)

{--------------------------------------------------------------------
  Deletion
  [delete] is the inlined version of [deleteWith (\k x -> Nothing)]
--------------------------------------------------------------------}

-- | /O(log n)/. Delete a key and its value from the map. When the key is not
-- a member of the map, the original map is returned.
delete :: forall k f v. GCompare k => k v -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
delete k (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.delete k m)

-- | /O(log n)/. Update a value at a specific key with the result of the provided function.
-- When the key is not
-- a member of the map, the original map is returned.
adjust :: GCompare k => (f v -> f v) -> k v -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f
adjust f k (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.adjust f k m)

-- | Works the same as 'adjust' except the new value is return in some 'Applicative' @f@.
adjustF
  :: forall k f v g
  .  (GCompare  k, Applicative f)
  => k v
  -> (g v -> f (g v))
  -> MonoidalNonEmptyDMap k g -> f (MonoidalNonEmptyDMap k g)
adjustF k f = fmap MonoidalNonEmptyDMap . NonEmptyDMap.adjustF k f . unMonoidalNonEmptyDMap

-- | /O(log n)/. Adjust a value at a specific key. When the key is not
-- a member of the map, the original map is returned.
adjustWithKey :: GCompare k => (k v -> f v -> f v) -> k v -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f
adjustWithKey f k (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.adjustWithKey f k m)

-- | /O(log n)/. A strict version of 'adjustWithKey'.
adjustWithKey' :: GCompare k => (k v -> f v -> f v) -> k v -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f
adjustWithKey' f k (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.adjustWithKey' f k m)

-- | /O(log n)/. The expression (@'update' f k map@) updates the value @x@
-- at @k@ (if it is in the map). If (@f x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @k@ is bound to the new value @y@.
update :: GCompare k => (f v -> Maybe (f v)) -> k v -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
update f k (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.update f k m)

-- | /O(log n)/. The expression (@'updateWithKey' f k map@) updates the
-- value @x@ at @k@ (if it is in the map). If (@f k x@) is 'Nothing',
-- the element is deleted. If it is (@'Just' y@), the key @k@ is bound
-- to the new value @y@.
updateWithKey :: forall k f v. GCompare k => (k v -> f v -> Maybe (f v)) -> k v -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
updateWithKey f k (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.updateWithKey f k m)

-- | /O(log n)/. Lookup and update. See also 'updateWithKey'.
-- The function returns changed value, if it is updated.
-- Returns the original key value if the map entry is deleted.
updateLookupWithKey :: forall k f v. GCompare k => (k v -> f v -> Maybe (f v)) -> k v -> MonoidalNonEmptyDMap k f -> (Maybe (f v), Maybe (MonoidalNonEmptyDMap k f))
updateLookupWithKey f k (MonoidalNonEmptyDMap m) =
  case NonEmptyDMap.updateLookupWithKey f k m of
    (x, y) -> (x, fmap MonoidalNonEmptyDMap y)

-- | /O(log n)/. The expression (@'alter' f k map@) alters the value @x@ at @k@, or absence thereof.
-- 'alter' can be used to insert, delete, or update a value in a 'Map'.
-- In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter :: forall k f v. GCompare k => (Maybe (f v) -> Maybe (f v)) -> k v -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
alter f k (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.alter f k m)

-- | Works the same as 'alter' except the new value is return in some 'Functor' @f@.
-- In short : @(\v' -> alter (const v') k dm) <$> f (lookup k dm)@
alterF :: forall k f v g. (GCompare  k, Functor f) => k v -> (Maybe (g v) -> f (Maybe (g v))) -> MonoidalNonEmptyDMap k g -> f (Maybe (MonoidalNonEmptyDMap k g))
alterF k f = (fmap . fmap) MonoidalNonEmptyDMap
  . NonEmptyDMap.alterF k f
  . unMonoidalNonEmptyDMap

{--------------------------------------------------------------------
  Indexing
--------------------------------------------------------------------}

-- | /O(log n)/. Return the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map. Calls 'error' when
-- the key is not a 'member' of the map.
findIndex :: GCompare k => k v -> MonoidalNonEmptyDMap k f -> Int
findIndex k (MonoidalNonEmptyDMap m)
  = case NonEmptyDMap.lookupIndex k m of
      Nothing  -> error "MonoidalNonEmptyDMap.findIndex: element is not in the map"
      Just idx -> idx

-- | /O(log n)/. Lookup the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map.
lookupIndex :: forall k f v. GCompare k => k v -> MonoidalNonEmptyDMap k f -> Maybe Int
lookupIndex k (MonoidalNonEmptyDMap m) = NonEmptyDMap.lookupIndex k m

-- | /O(log n)/. Retrieve an element by /index/. Calls 'error' when an
-- invalid index is used.
elemAt :: Int -> MonoidalNonEmptyDMap k f -> DSum k f
elemAt i (MonoidalNonEmptyDMap m) = NonEmptyDMap.elemAt i m

-- | /O(log n)/. Update the element at /index/. Does nothing when an
-- invalid index is used.
updateAt :: (forall v. k v -> f v -> Maybe (f v)) -> Int -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
updateAt f i (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.updateAt f i m)

-- | /O(log n)/. Delete the element at /index/.
-- Defined as (@'deleteAt' i map = 'updateAt' (\k x -> 'Nothing') i map@).
deleteAt :: Int -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
deleteAt i (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.deleteAt i m)

{--------------------------------------------------------------------
  Minimal, Maximal
--------------------------------------------------------------------}

-- | /O(log n)/. The minimal key of the map. Calls 'error' is the map is empty.
findMin :: MonoidalNonEmptyDMap k f -> DSum k f
findMin (MonoidalNonEmptyDMap m) = NonEmptyDMap.lookupMin m

lookupMin :: MonoidalNonEmptyDMap k f -> DSum k f
lookupMin (MonoidalNonEmptyDMap m) = NonEmptyDMap.lookupMin m

-- | /O(log n)/. The maximal key of the map. Calls 'error' is the map is empty.
findMax :: MonoidalNonEmptyDMap k f -> DSum k f
findMax m = lookupMax m

lookupMax :: MonoidalNonEmptyDMap k f -> DSum k f
lookupMax (MonoidalNonEmptyDMap m) = NonEmptyDMap.lookupMax m

-- | /O(log n)/. Delete the minimal key. Returns an empty map if the map is empty.
deleteMin :: MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
deleteMin (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.deleteMin m)

-- | /O(log n)/. Delete the maximal key. Returns an empty map if the map is empty.
deleteMax :: MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
deleteMax (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.deleteMax m)

-- | /O(log n)/. Update the value at the minimal key.
updateMinWithKey :: (forall v. k v -> f v -> Maybe (f v)) -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
updateMinWithKey f (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.updateMinWithKey f m)

-- | /O(log n)/. Update the value at the maximal key.
updateMaxWithKey :: (forall v. k v -> f v -> Maybe (f v)) -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
updateMaxWithKey f (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.updateMaxWithKey f m)

{--------------------------------------------------------------------
  Union.
--------------------------------------------------------------------}

-- | The union of a list of maps, with a combining operation:
--   (@'unionsWithKey' f == 'Prelude.foldl' ('unionWithKey' f) 'empty'@).
unionsWithKey :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> NonEmpty(MonoidalNonEmptyDMap k f) -> MonoidalNonEmptyDMap k f
unionsWithKey f ms = MonoidalNonEmptyDMap (NonEmptyDMap.unionsWithKey f (coerce ms))

{--------------------------------------------------------------------
  Union with a combining function
--------------------------------------------------------------------}

-- | /O(n+m)/.
-- Union with a combining function.
unionWithKey :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f
unionWithKey f (MonoidalNonEmptyDMap m) (MonoidalNonEmptyDMap n) = MonoidalNonEmptyDMap (NonEmptyDMap.unionWithKey f m n)

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}

-- | /O(m * log (n\/m + 1)), m <= n/. Difference of two maps.
-- Return elements of the first map not existing in the second map.
difference :: GCompare k => MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k g -> Maybe (MonoidalNonEmptyDMap k f)
difference (MonoidalNonEmptyDMap m) (MonoidalNonEmptyDMap n) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.difference m n)

-- | /O(n+m)/. Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the key and both values.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWithKey :: GCompare k => (forall v. k v -> f v -> g v -> Maybe (f v)) -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k g -> Maybe (MonoidalNonEmptyDMap k f)
differenceWithKey f (MonoidalNonEmptyDMap m) (MonoidalNonEmptyDMap n) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.differenceWithKey f m n)

{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

-- | /O(m * log (n\/m + 1), m <= n/. Intersection with a combining function.
intersectionWithKey :: GCompare k => (forall v. k v -> f v -> g v -> h v) -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k g -> Maybe (MonoidalNonEmptyDMap k h)
intersectionWithKey f (MonoidalNonEmptyDMap m) (MonoidalNonEmptyDMap n) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.intersectionWithKey f m n)

{--------------------------------------------------------------------
  Submap
--------------------------------------------------------------------}
-- | /O(n+m)/.
-- This function is defined as (@'isSubmapOf' = 'isSubmapOfBy' 'eqTagged')@).
--
isSubmapOf
  :: forall k f
  .  (GCompare k, Has' Eq k f)
  => MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f -> Bool
isSubmapOf (MonoidalNonEmptyDMap m) (MonoidalNonEmptyDMap n) = NonEmptyDMap.isSubmapOf m n

{- | /O(n+m)/.
 The expression (@'isSubmapOfBy' f t1 t2@) returns 'True' if
 all keys in @t1@ are in tree @t2@, and when @f@ returns 'True' when
 applied to their respective keys and values.
-}
isSubmapOfBy :: GCompare k => (forall v. k v -> k v -> f v -> g v -> Bool) -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k g -> Bool
isSubmapOfBy f (MonoidalNonEmptyDMap m) (MonoidalNonEmptyDMap n) = NonEmptyDMap.isSubmapOfBy f m n

-- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
-- Defined as (@'isProperSubmapOf' = 'isProperSubmapOfBy' 'eqTagged'@).
isProperSubmapOf
  :: forall k f
  .  (GCompare k, Has' Eq k f)
  => MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k f -> Bool
isProperSubmapOf (MonoidalNonEmptyDMap m) (MonoidalNonEmptyDMap n) = NonEmptyDMap.isProperSubmapOf m n

{- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
 The expression (@'isProperSubmapOfBy' f m1 m2@) returns 'True' when
 @m1@ and @m2@ are not equal,
 all keys in @m1@ are in @m2@, and when @f@ returns 'True' when
 applied to their respective keys and values.
-}
isProperSubmapOfBy :: GCompare k => (forall v. k v -> k v -> f v -> g v -> Bool) -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k g -> Bool
isProperSubmapOfBy f (MonoidalNonEmptyDMap m) (MonoidalNonEmptyDMap n) = NonEmptyDMap.isProperSubmapOfBy f m n

{--------------------------------------------------------------------
  Filter and partition
--------------------------------------------------------------------}

-- | /O(n)/. Filter all keys\/values that satisfy the predicate.
filterWithKey :: GCompare k => (forall v. k v -> f v -> Bool) -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k f)
filterWithKey p (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.filterWithKey p m)

-- | /O(n)/. Partition the map according to a predicate. The first
-- map contains all elements that satisfy the predicate, the second all
-- elements that fail the predicate. See also 'split'.
partitionWithKey :: GCompare k => (forall v. k v -> f v -> Bool) -> MonoidalNonEmptyDMap k f -> (Maybe (MonoidalNonEmptyDMap k f), Maybe (MonoidalNonEmptyDMap k f))
partitionWithKey p (MonoidalNonEmptyDMap m) =
  case NonEmptyDMap.partitionWithKey p m of
    (x, y) -> (fmap MonoidalNonEmptyDMap x, fmap MonoidalNonEmptyDMap y)

-- | /O(n)/. Map keys\/values and collect the 'Just' results.
mapMaybeWithKey :: GCompare k => (forall v. k v -> f v -> Maybe (g v)) -> MonoidalNonEmptyDMap k f -> Maybe (MonoidalNonEmptyDMap k g)
mapMaybeWithKey f (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.mapMaybeWithKey f m)

-- | /O(n)/. Map keys\/values and separate the 'Left' and 'Right' results.
mapEitherWithKey :: GCompare k =>
  (forall v. k v -> f v -> Either (g v) (h v)) -> MonoidalNonEmptyDMap k f -> (Maybe (MonoidalNonEmptyDMap k g), Maybe (MonoidalNonEmptyDMap k h))
mapEitherWithKey f (MonoidalNonEmptyDMap m) =
  case NonEmptyDMap.mapEitherWithKey f m of
    (x, y) -> (fmap MonoidalNonEmptyDMap x, fmap MonoidalNonEmptyDMap y)

{--------------------------------------------------------------------
  Mapping
--------------------------------------------------------------------}

-- | /O(n)/. Map a function over all values in the map.
map :: (forall v. f v -> g v) -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k g
map f (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.map f m)

-- | /O(n)/. Map a function over all values in the map.
mapWithKey :: (forall v. k v -> f v -> g v) -> MonoidalNonEmptyDMap k f -> MonoidalNonEmptyDMap k g
mapWithKey f (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.mapWithKey f m)

-- | /O(n)/.
-- @'traverseWithKey' f m == 'fromList' <$> 'traverse' (\(k, v) -> (,) k <$> f k v) ('toList' m)@
-- That is, behaves exactly like a regular 'traverse' except that the traversing
-- function also has access to the key associated with a value.
traverseWithKey :: Applicative t => (forall v. k v -> f v -> t (g v)) -> MonoidalNonEmptyDMap k f -> t (MonoidalNonEmptyDMap k g)
traverseWithKey f (MonoidalNonEmptyDMap m) = fmap MonoidalNonEmptyDMap (NonEmptyDMap.traverseWithKey f m)

-- | /O(n)/. The function 'mapAccumLWithKey' threads an accumulating
-- argument throught the map in ascending order of keys.
mapAccumLWithKey :: (forall v. a -> k v -> f v -> (a, g v)) -> a -> MonoidalNonEmptyDMap k f -> (a, MonoidalNonEmptyDMap k g)
mapAccumLWithKey f x (MonoidalNonEmptyDMap m) =
  case NonEmptyDMap.mapAccumLWithKey f x m of
    (y, m') -> (y, MonoidalNonEmptyDMap m')

-- | /O(n)/. The function 'mapAccumRWithKey' threads an accumulating
-- argument through the map in descending order of keys.
mapAccumRWithKey :: (forall v. a -> k v -> f v -> (a, g v)) -> a -> MonoidalNonEmptyDMap k f -> (a, MonoidalNonEmptyDMap k g)
mapAccumRWithKey f x (MonoidalNonEmptyDMap m) =
  case NonEmptyDMap.mapAccumRWithKey f x m of
    (y, m') -> (y, MonoidalNonEmptyDMap m')

-- | /O(n*log n)/.
-- @'mapKeysWith' c f s@ is the map obtained by applying @f@ to each key of @s@.
--
-- The size of the result may be smaller if @f@ maps two or more distinct
-- keys to the same new key.  In this case the associated values will be
-- combined using @c@.
mapKeysWith :: GCompare k2 => (forall v. k2 v -> f v -> f v -> f v) -> (forall v. k1 v -> k2 v) -> MonoidalNonEmptyDMap k1 f -> MonoidalNonEmptyDMap k2 f
mapKeysWith c f (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.mapKeysWith c f m)

-- | /O(n)/.
-- @'mapKeysMonotonic' f s == 'mapKeys' f s@, but works only when @f@
-- is strictly monotonic.
-- That is, for any values @x@ and @y@, if @x@ < @y@ then @f x@ < @f y@.
-- /The precondition is not checked./
-- Semi-formally, we have:
--
-- > and [x < y ==> f x < f y | x <- ls, y <- ls]
-- >                     ==> mapKeysMonotonic f s == mapKeys f s
-- >     where ls = keys s
--
-- This means that @f@ maps distinct original keys to distinct resulting keys.
-- This function has better performance than 'mapKeys'.
mapKeysMonotonic :: (forall v. k1 v -> k2 v) -> MonoidalNonEmptyDMap k1 f -> MonoidalNonEmptyDMap k2 f
mapKeysMonotonic f (MonoidalNonEmptyDMap m) = MonoidalNonEmptyDMap (NonEmptyDMap.mapKeysMonotonic f m)

{--------------------------------------------------------------------
  Folds
--------------------------------------------------------------------}

-- | /O(n)/. Post-order fold.  The function will be applied from the lowest
-- value to the highest.
foldrWithKey :: (forall v. k v -> f v -> b -> b) -> b -> MonoidalNonEmptyDMap k f -> b
foldrWithKey f x (MonoidalNonEmptyDMap m) = NonEmptyDMap.foldrWithKey f x m

-- | /O(n)/. Pre-order fold.  The function will be applied from the highest
-- value to the lowest.
foldlWithKey :: (forall v. b -> k v -> f v -> b) -> b -> MonoidalNonEmptyDMap k f -> b
foldlWithKey f x (MonoidalNonEmptyDMap m) = NonEmptyDMap.foldlWithKey f x m

{--------------------------------------------------------------------
  List variations
--------------------------------------------------------------------}

-- | /O(n)/. Return all keys of the map in ascending order.
--
-- > keys (fromList [(5,"a"), (3,"b")]) == [3,5]
-- > keys empty == []

keys  :: MonoidalNonEmptyDMap k f -> NonEmpty (Some k)
keys (MonoidalNonEmptyDMap m) = NonEmptyDMap.keys m

-- | /O(n)/. Return all key\/value pairs in the map in ascending key order.
assocs :: MonoidalNonEmptyDMap k f -> NonEmpty (DSum k f)
assocs (MonoidalNonEmptyDMap m) = NonEmptyDMap.assocs m

{--------------------------------------------------------------------
  Lists
  use [foldlStrict] to reduce demand on the control-stack
--------------------------------------------------------------------}

-- | /O(n*log n)/. Build a map from a list of key\/value pairs with a combining function. See also 'fromAscListWithKey'.
fromListWithKey :: GCompare k => (forall v. k v -> f v -> f v -> f v) -> NonEmpty (DSum k f) -> MonoidalNonEmptyDMap k f
fromListWithKey f xs = MonoidalNonEmptyDMap (NonEmptyDMap.fromListWithKey f xs)

-- | /O(n)/. Convert to a list of key\/value pairs.
toList :: MonoidalNonEmptyDMap k f -> NonEmpty (DSum k f)
toList (MonoidalNonEmptyDMap m) = NonEmptyDMap.toList m

-- | /O(n*log n)/. Build a map from a list of key\/value pairs. See also 'fromAscList'.
-- If the list contains more than one value for the same key, the last value
-- for the key is retained.
fromList :: GCompare k => NonEmpty (DSum k f) -> MonoidalNonEmptyDMap k f
fromList = MonoidalNonEmptyDMap . NonEmptyDMap.fromList

-- | /O(n)/. Convert to an ascending list.
toAscList :: MonoidalNonEmptyDMap k f -> NonEmpty (DSum k f)
toAscList (MonoidalNonEmptyDMap m) = NonEmptyDMap.toAscList m

-- | /O(n)/. Build a map from an ascending list in linear time.
-- /The precondition (input list is ascending) is not checked./
fromAscList :: GEq k => NonEmpty (DSum k f) -> MonoidalNonEmptyDMap k f
fromAscList = MonoidalNonEmptyDMap . NonEmptyDMap.fromAscList

-- | /O(n)/. Build a map from an ascending list of distinct elements in linear time.
-- /The precondition is not checked./
fromDistinctAscList :: NonEmpty (DSum k f) -> MonoidalNonEmptyDMap k f
fromDistinctAscList = MonoidalNonEmptyDMap . NonEmptyDMap.fromDistinctAscList

-- | /O(n)/. Convert to a descending list.
toDescList :: MonoidalNonEmptyDMap k f -> NonEmpty (DSum k f)
toDescList (MonoidalNonEmptyDMap m) = NonEmptyDMap.toDescList m

{--------------------------------------------------------------------
  Building trees from ascending/descending lists can be done in linear time.

  Note that if [xs] is ascending that:
    fromAscList xs       == fromList xs
    fromAscListWith f xs == fromListWith f xs
--------------------------------------------------------------------}

-- | /O(n)/. Build a map from an ascending list in linear time with a
-- combining function for equal keys.
-- /The precondition (input list is ascending) is not checked./
fromAscListWithKey :: GEq k => (forall v. k v -> f v -> f v -> f v) -> NonEmpty (DSum k f) -> MonoidalNonEmptyDMap k f
fromAscListWithKey f xs = MonoidalNonEmptyDMap (NonEmptyDMap.fromAscListWithKey f xs)

{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}

-- | /O(log n)/. The expression (@'split' k map@) is a pair @(map1,map2)@ where
-- the keys in @map1@ are smaller than @k@ and the keys in @map2@ larger than @k@.
-- Any key equal to @k@ is found in neither @map1@ nor @map2@.
split :: forall k f v. GCompare k => k v -> MonoidalNonEmptyDMap k f -> (Maybe (MonoidalNonEmptyDMap k f), Maybe (MonoidalNonEmptyDMap k f))
split k (MonoidalNonEmptyDMap m) =
  case NonEmptyDMap.split k m of
    (x, y) -> (fmap MonoidalNonEmptyDMap x, fmap MonoidalNonEmptyDMap y)
{-# INLINABLE split #-}

-- | /O(log n)/. The expression (@'splitLookup' k map@) splits a map just
-- like 'split' but also returns @'lookup' k map@.
splitLookup :: forall k f v. GCompare k => k v -> MonoidalNonEmptyDMap k f -> (Maybe (MonoidalNonEmptyDMap k f), Maybe (f v), Maybe (MonoidalNonEmptyDMap k f))
splitLookup k (MonoidalNonEmptyDMap m) =
  case NonEmptyDMap.splitLookup k m of
    (x, v, y) -> (fmap MonoidalNonEmptyDMap x, v, fmap MonoidalNonEmptyDMap y)

-- | /O(n)/. Show the tree that implements the map. The tree is shown
-- in a compressed, hanging format. See 'showTreeWith'.
showTree :: (GShow k, Has' Show k f) => MonoidalNonEmptyDMap k f -> String
showTree (MonoidalNonEmptyDMap m) = NonEmptyDMap.showTree m

{- | /O(n)/. The expression (@'showTreeWith' showelem hang wide map@) shows
 the tree that implements the map. Elements are shown using the @showElem@ function. If @hang@ is
 'True', a /hanging/ tree is shown otherwise a rotated tree is shown. If
 @wide@ is 'True', an extra wide version is shown.
-}
showTreeWith :: (forall v. k v -> f v -> String) -> Bool -> Bool -> MonoidalNonEmptyDMap k f -> String
showTreeWith showElem hang wide (MonoidalNonEmptyDMap m) = NonEmptyDMap.showTreeWith showElem hang wide m

{--------------------------------------------------------------------
  Assertions
--------------------------------------------------------------------}

-- | /O(n)/. Test if the internal map structure is valid.
valid :: GCompare k => MonoidalNonEmptyDMap k f -> Bool
valid (MonoidalNonEmptyDMap m) = NonEmptyDMap.valid m
