module Data.Map.Class where

import Control.Applicative hiding (Alternative (..))
import Control.Arrow
import Data.Either.Both
import Data.Filtrable
import qualified Data.Foldable as Foldable
import Data.Functor.Compose
import Data.Functor.Identity
import Data.IntMap (IntMap)
import qualified Data.IntMap as Int
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Data.Monoid (Dual (..), Last (..))
import Util ((∘∘))
import Util.Private (Endo (..))

class Traversable map => StaticMap map where
    type Key map
    adjustA :: Applicative p => (a -> p a) -> Key map -> map a -> p (map a)
    traverseWithKey :: (Applicative p) => (Key map -> a -> p b) -> map a -> p (map b)

class (Filtrable map, StaticMap map) => Map map where
    empty :: map a
    alterF :: Functor f => (Maybe a -> f (Maybe a)) -> Key map -> map a -> f (map a)
    mergeA :: Applicative p => (Key map -> Either' a b -> p (Maybe c)) -> map a -> map b -> p (map c)
    mapMaybeWithKeyA :: Applicative p => (Key map -> a -> p (Maybe b)) -> map a -> p (map b)
    mapEitherWithKeyA :: Applicative p => (Key map -> a -> p (Either b c)) -> map a -> p (map b, map c)
    mapEitherWithKeyA f = liftA2 (,) <$> mapMaybeWithKeyA (fmap (Just `either` pure Nothing) ∘∘ f)
                                     <*> mapMaybeWithKeyA (fmap (pure Nothing `either` Just) ∘∘ f)

defaultAdjustA :: (Map map, Applicative p) => (a -> p a) -> Key map -> map a -> p (map a)
defaultAdjustA f = alterF (traverse f)

defaultTraverseWithKey :: (Map map, Applicative p) => (Key map -> a -> p b) -> map a -> p (map b)
defaultTraverseWithKey f = mapMaybeWithKeyA (fmap Just ∘∘ f)

instance Filtrable IntMap where
    mapMaybe = Int.mapMaybe

instance Filtrable (M.Map key) where
    mapMaybe = M.mapMaybe

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

infix 9 !?
(!?) :: StaticMap map => map a -> Key map -> Maybe a
(!?) = flip $ getLast ∘∘ fst ∘∘ adjustA ((,) <$> Last . Just <*> id)

insert :: Map map => Key map -> a -> map a -> map a
insert = insertWith pure

insertWith :: Map map => (a -> a -> a) -> Key map -> a -> map a -> map a
insertWith f = flip $ \ a -> alter (Just . maybe a (f a))

insertLookup :: Map map => Key map -> a -> map a -> (Maybe a, map a)
insertLookup = insertLookupWith pure

insertLookupWith :: Map map => (a -> a -> a) -> Key map -> a -> map a -> (Maybe a, map a)
insertLookupWith f = flip $ \ a -> alterLookup (Just . maybe a (f a))

delete :: Map map => Key map -> map a -> map a
delete = alter (pure Nothing)

adjust :: StaticMap map => (a -> a) -> Key map -> map a -> map a
adjust f = runIdentity ∘∘ adjustA (pure . f)

update :: Map map => (a -> Maybe a) -> Key map -> map a -> map a
update f = alter (>>= f)

updateLookup :: Map map => (a -> Maybe a) -> Key map -> map a -> (Maybe a, map a)
updateLookup f = alterLookup (>>= f)

alter :: Map map => (Maybe a -> Maybe a) -> Key map -> map a -> map a
alter f = runIdentity ∘∘ alterF (Identity . f)

alterLookup :: Map map => (Maybe a -> Maybe a) -> Key map -> map a -> (Maybe a, map a)
alterLookup f = alterF ((,) <*> f)

mapWithKey :: StaticMap map => (Key map -> a -> b) -> map a -> map b
mapWithKey f = runIdentity . traverseWithKey (Identity ∘∘ f)

mapMaybeWithKey :: Map map => (Key map -> a -> Maybe b) -> map a -> map b
mapMaybeWithKey f = runIdentity . mapMaybeWithKeyA (pure ∘∘ f)

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

adjustLookupA :: (StaticMap map, Applicative p) => (a -> p a) -> Key map -> map a -> p (Maybe a, map a)
adjustLookupA f = sequenceA ∘∘ (getLast *** id <<< getCompose) ∘∘ adjustA (\ a -> Compose (pure a, f a))

singleton :: Map map => Key map -> a -> map a
singleton k a = fromList [(k, a)]

unionWith :: Map map => (Key map -> a -> a -> a) -> map a -> map a -> map a
unionWith f = runIdentity ∘∘ unionWithA (\ k -> pure ∘∘ f k)

intersectionWith :: Map map => (Key map -> a -> b -> c) -> map a -> map b -> map c
intersectionWith f = runIdentity ∘∘ intersectionWithA (\ k -> pure ∘∘ f k)

merge :: Map map => (Key map -> Either' a b -> Maybe c) -> map a -> map b -> map c
merge f = runIdentity ∘∘ mergeA (Identity ∘∘ f)

unionWithA :: (Map map, Applicative p) => (Key map -> a -> a -> p a) -> map a -> map a -> p (map a)
unionWithA f = mergeA (\ k -> \ case JustLeft a -> pure (Just a); JustRight a -> pure (Just a); Both a b -> Just <$> f k a b)

intersectionWithA :: (Map map, Applicative p) => (Key map -> a -> b -> p c) -> map a -> map b -> p (map c)
intersectionWithA f = mergeA (\ k -> \ case Both a b -> Just <$> f k a b; _ -> pure Nothing)

mapKeys :: (StaticMap m, Map n) => (Key m -> Key n) -> m a -> n a
mapKeys f = foldrWithKey (insert . f) empty

traverseKeys :: (StaticMap m, Map n, Applicative p) => (Key m -> p (Key n)) -> m a -> p (n a)
traverseKeys f = fmap (flip appEndo empty) . foldMapWithKeyA (\ i a -> (\ j -> Endo $ insert j a) <$> f i)

keys :: StaticMap map => map a -> map (Key map)
keys = mapWithKey pure
