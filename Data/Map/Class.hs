-- | Class of key-value maps
--
-- See 'StaticMap' and 'Map'.
module Data.Map.Class where

import Control.Applicative hiding (Alternative (..))
import Control.Arrow
import Data.Either.Both
import Data.Filtrable
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.IntMap (IntMap)
import qualified Data.IntMap as Int
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Data.Monoid (Dual (..), Last (..))
import Util ((∘), (∘∘), compose2, bind2)
import Util.Private (Endo (..))

-- | Class of key-value maps
--
-- Laws:
--
-- * @'adjustA' 'pure' _ = 'pure'@
--
-- * @'adjustA' 'Const' k '<=<' 'traverseWithKey' f = 'fmap' 'Const' '.' f k '<=<' 'getConst' '.' 'adjustA' 'Const' k@
class Traversable map => StaticMap map where
    type Key map
    -- | Modify the value of the key in the map. If the key is absent, the map is returned unmodified.
    adjustA :: Applicative p => (a -> p a) -> Key map -> map a -> p (map a)
    -- | Traverse a function over each value in the map.
    traverseWithKey :: (Applicative p) => (Key map -> a -> p b) -> map a -> p (map b)

-- | Class of key-value maps with variable structure
class (Filtrable map, StaticMap map) => Map map where
    -- | The empty map
    empty :: map a
    -- | Modify the value of the key in the map, or insert the key and its value into the map, or delete the key and its value from the map, functorially.
    --
    -- @fmap ('!?' k) . 'alterF' f k = f . ('!?' k)@
    --
    -- This is the most general operation on a given key in the map.
    alterF :: Functor f => (Maybe a -> f (Maybe a)) -> Key map -> map a -> f (map a)
    -- | Combine two maps with the given function, which is called once for each key present in either map, inclusive.
    mergeA :: Applicative p => (Key map -> Either' a b -> p (Maybe c)) -> map a -> map b -> p (map c)
    -- | Traverse a function over each value in the map, gathering the 'Just' values and forgetting the 'Nothing'.
    mapMaybeWithKeyA :: Applicative p => (Key map -> a -> p (Maybe b)) -> map a -> p (map b)
    -- | Traverse a function over each value in the map, gathering the 'Left' and 'Right' values separately.
    mapEitherWithKeyA :: Applicative p => (Key map -> a -> p (Either b c)) -> map a -> p (map b, map c)
    mapEitherWithKeyA f = liftA2 (,) <$> mapMaybeWithKeyA (fmap (Just `either` pure Nothing) ∘∘ f)
                                     <*> mapMaybeWithKeyA (fmap (pure Nothing `either` Just) ∘∘ f)

-- | Default implementation of `adjustA` in terms of `Map` methods
defaultAdjustA :: (Map map, Applicative p) => (a -> p a) -> Key map -> map a -> p (map a)
defaultAdjustA f = alterF (traverse f)

-- | Default implementation of `traverseWithKey` in terms of `Map` methods
defaultTraverseWithKey :: (Map map, Applicative p) => (Key map -> a -> p b) -> map a -> p (map b)
defaultTraverseWithKey f = mapMaybeWithKeyA (fmap Just ∘∘ f)

instance StaticMap Maybe where
    type Key Maybe = ()
    adjustA f () = traverse f
    traverseWithKey f = traverse (f ())

instance StaticMap IntMap where
    type Key IntMap = Int
    adjustA = defaultAdjustA
    traverseWithKey = defaultTraverseWithKey

instance Ord key => StaticMap (M.Map key) where
    type Key (M.Map key) = key
    adjustA = defaultAdjustA
    traverseWithKey = defaultTraverseWithKey

instance (StaticMap m, StaticMap n) => StaticMap (Compose m n) where
    type Key (Compose m n) = (Key m, Key n)
    adjustA f (i, j) = fmap Compose . adjustA (adjustA f j) i . getCompose
    traverseWithKey f = fmap Compose ∘ traverseWithKey (\ i -> traverseWithKey (\ j -> f (i, j))) ∘ getCompose

instance (StaticMap m, StaticMap n) => StaticMap (Product m n) where
    type Key (Product m n) = Either (Key m) (Key n)
    adjustA f k (Pair a b) = case k of
        Left  i -> flip Pair b <$> adjustA f i a
        Right j -> id   Pair a <$> adjustA f j b
    traverseWithKey f (Pair a b) =
        Pair <$> traverseWithKey (f ∘ Left) a <*> traverseWithKey (f ∘ Right) b

instance Map Maybe where
    empty = Nothing
    alterF = pure
    mergeA f = mapMaybeWithKeyA f ∘∘ fromMaybes
    mapMaybeWithKeyA f = mapMaybeA (f ())

instance Map IntMap where
    empty = Int.empty
    alterF = Int.alterF
    mergeA f = mapMaybeWithKeyA f ∘∘
               Int.mergeWithKey (pure $ Just ∘∘ Both) (fmap JustLeft) (fmap JustRight)
    mapMaybeWithKeyA f = fmap catMaybes . Int.traverseWithKey f
    mapEitherWithKeyA f = fmap partitionEithers . Int.traverseWithKey f

instance Ord key => Map (M.Map key) where
    empty = M.empty
    alterF = M.alterF
    mergeA f = M.mergeA (M.traverseMaybeMissing $ \ k a -> f k (JustLeft a))
                        (M.traverseMaybeMissing $ \ k b -> f k (JustRight b))
                        (M.zipWithMaybeAMatched $ \ k a b -> f k (Both a b))
    mapMaybeWithKeyA f = fmap catMaybes . M.traverseWithKey f
    mapEitherWithKeyA f = fmap partitionEithers . M.traverseWithKey f

instance (Map m, Map n) => Map (Compose m n) where
    empty = Compose empty
    alterF f (i, j) = fmap Compose . alterF (maybe (fmap (singleton j) <$> f Nothing) (fmap Just . alterF f j)) i . getCompose
    mergeA f =
        fmap Compose ∘∘
        compose2 (mergeA $ \ i ->
                  fmap Just ∘ either' (mapMaybeWithKeyA $ \ j -> f (i, j) ∘ JustLeft)
                                      (mapMaybeWithKeyA $ \ j -> f (i, j) ∘ JustRight)
                                      (mergeA $ \ j -> f (i, j))) getCompose getCompose
    mapMaybeWithKeyA f = fmap Compose . mapMaybeWithKeyA (\ i -> fmap Just . mapMaybeWithKeyA (\ j -> f (i, j))) . getCompose

instance (Map m, Map n) => Map (Product m n) where
    empty = Pair empty empty
    alterF f k (Pair a b) = case k of
        Left  i -> flip Pair b <$> alterF f i a
        Right j -> id   Pair a <$> alterF f j b
    mergeA f (Pair a₀ b₀) (Pair a₁ b₁) = Pair <$> mergeA (f . Left) a₀ a₁ <*> mergeA (f . Right) b₀ b₁
    mapMaybeWithKeyA f (Pair a b) = Pair <$> mapMaybeWithKeyA (f . Left) a <*> mapMaybeWithKeyA (f . Right) b

-- | Look up the key in the map.
infix 9 !?
(!?) :: StaticMap map => map a -> Key map -> Maybe a
(!?) = flip $ getLast ∘∘ fst ∘∘ adjustA ((,) <$> Last . Just <*> id)

-- | Insert a key and new value into the map, the new value clobbering the old if the key is already present.
-- @'insert' = 'insertWith' 'pure'@
insert :: Map map => Key map -> a -> map a -> map a
insert = insertWith pure

-- | Insert a key and new value into the map, combining the old and new values with the given function if the key is already present.
insertWith :: Map map => (a -> a -> a) -> Key map -> a -> map a -> map a
insertWith f = flip $ \ a -> alter (Just . maybe a (f a))

-- | Insert a key and new value into the map, looking up the old value if the key is already present.
insertLookup :: Map map => Key map -> a -> map a -> (Maybe a, map a)
insertLookup = insertLookupWith pure

-- | Insert a key and new value into the map, looking up the old value and combining the old and new values with the given function if the key is already present.
insertLookupWith :: Map map => (a -> a -> a) -> Key map -> a -> map a -> (Maybe a, map a)
insertLookupWith f = flip $ \ a -> alterLookup (Just . maybe a (f a))

-- | Delete a key and its value from the map. If the key is absent, the map is returned unmodified.
delete :: Map map => Key map -> map a -> map a
delete = alter (pure Nothing)

-- | Modify the value of the key in the map. If the key is absent, the map is returned unmodified.
adjust :: StaticMap map => (a -> a) -> Key map -> map a -> map a
adjust f = runIdentity ∘∘ adjustA (pure . f)

-- | Modify the value of the key in the map, or delete the key and its value from the map, if the given function returns 'Just' or 'Nothing', in turn. If the key is absent, the map is returned unmodified.
update :: Map map => (a -> Maybe a) -> Key map -> map a -> map a
update f = alter (>>= f)

-- | Modify the value of the key in the map, or delete the key and its value from the map, if the given function returns 'Just' or 'Nothing', in turn, looking up the old value if the key is already present. If the key is absent, the map is returned unmodified.
updateLookup :: Map map => (a -> Maybe a) -> Key map -> map a -> (Maybe a, map a)
updateLookup f = alterLookup (>>= f)

-- | Modify the value of the key in the map, or insert the key and its value into the map, or delete the key and its value from the map.
alter :: Map map => (Maybe a -> Maybe a) -> Key map -> map a -> map a
alter f = runIdentity ∘∘ alterF (Identity . f)

-- | Modify the value of the key in the map, or insert the key and its value into the map, or delete the key and its value from the map, looking up the old value if the key is already present.
alterLookup :: Map map => (Maybe a -> Maybe a) -> Key map -> map a -> (Maybe a, map a)
alterLookup f = alterF ((,) <*> f)

-- | Modify the value of the key in the map, or insert the key and its value into the map, or delete the key and its value from the map, looking up the old value if the key is already present, functorially.
--
-- This is no more general than `alterF`, but is defined for convenience.
alterLookupF :: (Map map, Functor f) => (Maybe a -> f (Maybe a)) -> Key map -> map a -> f (Maybe a, map a)
alterLookupF f = getCompose ∘∘ alterF (Compose ∘ liftA2 fmap (,) f)

-- | Map a function over each value in the map.
mapWithKey :: StaticMap map => (Key map -> a -> b) -> map a -> map b
mapWithKey f = runIdentity . traverseWithKey (Identity ∘∘ f)

-- | Map a function over each value in the map, gathering the 'Just' values and forgetting the 'Nothing'.
mapMaybeWithKey :: Map map => (Key map -> a -> Maybe b) -> map a -> map b
mapMaybeWithKey f = runIdentity . mapMaybeWithKeyA (pure ∘∘ f)

-- | Map a function over each value in the map, gathering the 'Left' and 'Right' separately.
mapEitherWithKey :: Map map => (Key map -> a -> Either b c) -> map a -> (map b, map c)
mapEitherWithKey f = runIdentity . mapEitherWithKeyA (pure ∘∘ f)

foldMapWithKeyA :: (StaticMap map, Applicative p, Monoid b) => (Key map -> a -> p b) -> map a -> p b
foldMapWithKeyA f = fmap getConst . getCompose . traverseWithKey (Compose ∘∘ fmap Const ∘∘ f)

foldrWithKeyM :: (StaticMap map, Monad m) => (Key map -> a -> b -> m b) -> b -> map a -> m b
foldrWithKeyM f = flip $ runKleisli . appEndo . foldMapWithKey (Endo ∘∘ Kleisli ∘∘ f)

foldlWithKeyM :: (StaticMap map, Monad m) => (b -> Key map -> a -> m b) -> b -> map a -> m b
foldlWithKeyM f = flip $ runKleisli . appEndo . getDual . foldMapWithKey (Dual ∘∘ Endo ∘∘ Kleisli ∘∘ \ k a b -> f b k a)

foldMapWithKey :: (StaticMap map, Monoid b) => (Key map -> a -> b) -> map a -> b
foldMapWithKey f = runIdentity . foldMapWithKeyA (pure ∘∘ f)

foldrWithKey :: StaticMap map => (Key map -> a -> b -> b) -> b -> map a -> b
foldrWithKey f = flip $ appEndo . foldMapWithKey (Endo ∘∘ f)

foldlWithKey :: StaticMap map => (b -> Key map -> a -> b) -> b -> map a -> b
foldlWithKey f = flip $ appEndo . getDual . foldMapWithKey (Dual ∘∘ Endo ∘∘ \ k a b -> f b k a)

fromList :: Map map => [(Key map, a)] -> map a
fromList = fromListWith pure

fromListWith :: Map map => (a -> a -> a) -> [(Key map, a)] -> map a
fromListWith = fromListWithKey . pure

fromListWithKey :: Map map => (Key map -> a -> a -> a) -> [(Key map, a)] -> map a
fromListWithKey f = Foldable.foldl' (flip . uncurry $ insertWith =<< f) empty

fromListWithM :: (Map map, Monad m) => (a -> a -> m a) -> [(Key map, a)] -> m (map a)
fromListWithM = fromListWithKeyM . pure

fromListWithKeyM :: (Map map, Monad m) => (Key map -> a -> a -> m a) -> [(Key map, a)] -> m (map a)
fromListWithKeyM f = sequenceA . fromListWithKey (bind2 . f) . (fmap . fmap) pure

-- | Modify the value of the key in the map, looking up the old value if the key is already present. If the key is absent, the map is returned unmodified.
adjustLookupA :: (StaticMap map, Applicative p) => (a -> p a) -> Key map -> map a -> p (Maybe a, map a)
adjustLookupA f = sequenceA ∘∘ (getLast *** id <<< getCompose) ∘∘ adjustA (\ a -> Compose (pure a, f a))

-- | Map with a single element
singleton :: Map map => Key map -> a -> map a
singleton k a = fromList [(k, a)]

-- | Union of two maps, combining values of the same key with the given function
unionWith :: Map map => (Key map -> a -> a -> a) -> map a -> map a -> map a
unionWith f = runIdentity ∘∘ unionWithA (\ k -> pure ∘∘ f k)

-- | Intersection of two maps, combining values of the same key with the given function
intersectionWith :: Map map => (Key map -> a -> b -> c) -> map a -> map b -> map c
intersectionWith f = runIdentity ∘∘ intersectionWithA (\ k -> pure ∘∘ f k)

-- | Combine two maps with the given function, which is called once for each key present in either map, inclusive.
merge :: Map map => (Key map -> Either' a b -> Maybe c) -> map a -> map b -> map c
merge f = runIdentity ∘∘ mergeA (Identity ∘∘ f)

-- | Union of two maps, combining values of the same key with the given function
unionWithA :: (Map map, Applicative p) => (Key map -> a -> a -> p a) -> map a -> map a -> p (map a)
unionWithA f = mergeA (\ k -> \ case JustLeft a -> pure (Just a); JustRight a -> pure (Just a); Both a b -> Just <$> f k a b)

-- | Intersection of two maps, combining values of the same key with the given function
intersectionWithA :: (Map map, Applicative p) => (Key map -> a -> b -> p c) -> map a -> map b -> p (map c)
intersectionWithA f = mergeA (\ k -> \ case Both a b -> Just <$> f k a b; _ -> pure Nothing)

-- | Difference of two maps, which contains exactly the keys present in the first map but absent in the second
difference :: Map map => map a -> map b -> map a
difference = merge $ pure $ either' Just (pure Nothing) $ \ _ _ -> Nothing

-- | Symmetric difference of two maps, which contains exactly the keys present in the either map but absent in the other
symmetricDifference :: Map map => map a -> map a -> map a
symmetricDifference = merge $ pure $ either' Just Just $ \ _ _ -> Nothing

-- | Map a function over each key in the map.
mapKeys :: (StaticMap m, Map n) => (Key m -> Key n) -> m a -> n a
mapKeys f = foldrWithKey (insert . f) empty

-- | Map a function over each key in the map, combining values of keys which collide with the given function.
mapKeysWith :: (StaticMap m, Map n) => (a -> a -> a) -> (Key m -> Key n) -> m a -> n a
mapKeysWith combine f = foldrWithKey (insertWith combine . f) empty

-- | Traverse a function over each key in the map.
traverseKeys :: (StaticMap m, Map n, Applicative p) => (Key m -> p (Key n)) -> m a -> p (n a)
traverseKeys f = fmap (flip appEndo empty) . foldMapWithKeyA (\ i a -> (\ j -> Endo $ insert j a) <$> f i)

-- | Traverse a function over each key in the map, combining values of keys which collide with the given function.
traverseKeysWith :: (StaticMap m, Map n, Applicative p) => (a -> a -> a) -> (Key m -> p (Key n)) -> m a -> p (n a)
traverseKeysWith combine f = fmap (flip appEndo empty) . foldMapWithKeyA (\ i a -> (\ j -> Endo $ insertWith combine j a) <$> f i)

-- | Map a function over each key in the map, gathering the 'Just' values and forgetting the 'Nothing'.
mapKeysMaybe :: (StaticMap m, Map n) => (Key m -> Maybe (Key n)) -> m a -> n a
mapKeysMaybe f = runIdentity . traverseKeysMaybe (Identity . f)

-- | Map a function over each key in the map, gathering the 'Just' values and forgetting the 'Nothing', combining values of keys which collide with the given function.
mapKeysMaybeWith :: (StaticMap m, Map n) => (a -> a -> a) -> (Key m -> Maybe (Key n)) -> m a -> n a
mapKeysMaybeWith combine f = runIdentity . traverseKeysMaybeWith combine (Identity . f)

-- | Traverse a function over each key in the map, gathering the 'Just' values and forgetting the 'Nothing'.
traverseKeysMaybe :: (StaticMap m, Map n, Applicative p) => (Key m -> p (Maybe (Key n))) -> m a -> p (n a)
traverseKeysMaybe f = fmap (flip appEndo empty) . foldMapWithKeyA (\ i a -> foldMap (\ j -> Endo $ insert j a) <$> f i)

-- | Traverse a function over each key in the map, gathering the 'Just' values and forgetting the 'Nothing', combining values of keys which collide with the given function.
traverseKeysMaybeWith :: (StaticMap m, Map n, Applicative p) => (a -> a -> a) -> (Key m -> p (Maybe (Key n))) -> m a -> p (n a)
traverseKeysMaybeWith combine f = fmap (flip appEndo empty) . foldMapWithKeyA (\ i a -> foldMap (\ j -> Endo $ insertWith combine j a) <$> f i)

-- | Keys of the map
--
-- @'keys' as '!?' k = k '<$' (as '!?' k)@
keys :: StaticMap map => map a -> map (Key map)
keys = mapWithKey pure

-- | Wrapper of a 'Map' whose semigroup operation is the union, combining values elementwise, and ergo whose monoidal unit is empty
newtype Union map a = Union { unUnion :: map a }
  deriving (Functor, Foldable, Traversable)
  deriving (Eq, Ord, Read, Show) via map a
  deriving (Eq1, Ord1, Read1, Show1) via map

instance Filtrable map => Filtrable (Union map) where
    mapMaybe f = Union . mapMaybe f . unUnion

instance StaticMap map => StaticMap (Union map) where
    type Key (Union map) = Key map
    adjustA f k = fmap Union . adjustA f k . unUnion
    traverseWithKey f = fmap Union . traverseWithKey f . unUnion

instance Map map => Map (Union map) where
    empty = Union empty
    alterF f k = fmap Union . alterF f k . unUnion
    mergeA f = fmap Union ∘∘ compose2 (mergeA f) unUnion unUnion
    mapMaybeWithKeyA f = fmap Union . mapMaybeWithKeyA f . unUnion

instance (Map map, Semigroup a) => Semigroup (Union map a) where
    (<>) = Union ∘∘ unionWith (pure (<>)) `on` unUnion

instance (Map map, Semigroup a) => Monoid (Union map a) where
    mempty = Union empty

-- | Wrapper of a 'Map' whose semigroup operation is the intersection, combining values elementwise
newtype Intersection map a = Intersection { unIntersection :: map a }
  deriving (Functor, Foldable, Traversable)
  deriving (Eq, Ord, Read, Show) via map a
  deriving (Eq1, Ord1, Read1, Show1) via map

instance Filtrable map => Filtrable (Intersection map) where
    mapMaybe f = Intersection . mapMaybe f . unIntersection

instance StaticMap map => StaticMap (Intersection map) where
    type Key (Intersection map) = Key map
    adjustA f k = fmap Intersection . adjustA f k . unIntersection
    traverseWithKey f = fmap Intersection . traverseWithKey f . unIntersection

instance Map map => Map (Intersection map) where
    empty = Intersection empty
    alterF f k = fmap Intersection . alterF f k . unIntersection
    mergeA f = fmap Intersection ∘∘ compose2 (mergeA f) unIntersection unIntersection
    mapMaybeWithKeyA f = fmap Intersection . mapMaybeWithKeyA f . unIntersection

instance (Map map, Semigroup a) => Semigroup (Intersection map a) where
    (<>) = Intersection ∘∘ intersectionWith (pure (<>)) `on` unIntersection

-- | Wrapper of a 'Map' whose semigroup operation is the symmetric difference, and ergo whose monoidal unit is empty
newtype SymmetricDifference map a = SymmetricDifference { unSymmetricDifference :: map a }
  deriving (Functor, Foldable, Traversable)
  deriving (Eq, Ord, Read, Show) via map a
  deriving (Eq1, Ord1, Read1, Show1) via map

instance Filtrable map => Filtrable (SymmetricDifference map) where
    mapMaybe f = SymmetricDifference . mapMaybe f . unSymmetricDifference

instance StaticMap map => StaticMap (SymmetricDifference map) where
    type Key (SymmetricDifference map) = Key map
    adjustA f k = fmap SymmetricDifference . adjustA f k . unSymmetricDifference
    traverseWithKey f = fmap SymmetricDifference . traverseWithKey f . unSymmetricDifference

instance Map map => Map (SymmetricDifference map) where
    empty = SymmetricDifference empty
    alterF f k = fmap SymmetricDifference . alterF f k . unSymmetricDifference
    mergeA f = fmap SymmetricDifference ∘∘ compose2 (mergeA f) unSymmetricDifference unSymmetricDifference
    mapMaybeWithKeyA f = fmap SymmetricDifference . mapMaybeWithKeyA f . unSymmetricDifference

instance Map map => Semigroup (SymmetricDifference map a) where
    (<>) = SymmetricDifference ∘∘ symmetricDifference `on` unSymmetricDifference

instance Map map => Monoid (SymmetricDifference map a) where
    mempty = SymmetricDifference empty
