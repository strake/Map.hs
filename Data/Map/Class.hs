module Data.Map.Class where

import Control.Applicative
import Control.Arrow
import Data.Either.Both
import Data.Filtrable
import Data.Functor.Compose
import Data.Functor.Identity
import Data.IntMap (IntMap)
import qualified Data.IntMap as Int
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Data.Monoid (Last (..))
import Util ((∘∘))

class Traversable map => StaticMap map where
    type Key map
    adjustA :: Applicative p => (a -> p a) -> Key map -> map a -> p (map a)

class (Filtrable map, StaticMap map) => Map map where
    alterF :: Functor f => (Maybe a -> f (Maybe a)) -> Key map -> map a -> f (map a)
    mergeA :: Applicative p => (Key map -> Either' a b -> p (Maybe c)) -> map a -> map b -> p (map c)
    mapMaybeWithKeyA :: Applicative p => (Key map -> a -> p (Maybe b)) -> map a -> p (map b)
    mapEitherWithKeyA :: Applicative p => (Key map -> a -> p (Either b c)) -> map a -> p (map b, map c)
    mapEitherWithKeyA f = liftA2 (,) <$> mapMaybeWithKeyA (fmap (Just `either` pure Nothing) ∘∘ f)
                                     <*> mapMaybeWithKeyA (fmap (pure Nothing `either` Just) ∘∘ f)

defaultAdjustA :: (Map map, Applicative p) => (a -> p a) -> Key map -> map a -> p (map a)
defaultAdjustA f = alterF (traverse f)

instance Filtrable IntMap where
    mapMaybe = Int.mapMaybe

instance Filtrable (M.Map key) where
    mapMaybe = M.mapMaybe

instance StaticMap IntMap where
    type Key IntMap = Int
    adjustA = defaultAdjustA

instance Ord key => StaticMap (M.Map key) where
    type Key (M.Map key) = key
    adjustA = defaultAdjustA

instance Map IntMap where
    alterF = Int.alterF
    mergeA f = mapMaybeWithKeyA f ∘∘
               Int.mergeWithKey (pure $ Just ∘∘ Both) (fmap JustLeft) (fmap JustRight)
    mapMaybeWithKeyA f = fmap catMaybes . Int.traverseWithKey f
    mapEitherWithKeyA f = fmap partitionEithers . Int.traverseWithKey f

instance Ord key => Map (M.Map key) where
    alterF = M.alterF
    mergeA f = M.mergeA (M.traverseMaybeMissing $ \ k a -> f k (JustLeft a))
                        (M.traverseMaybeMissing $ \ k b -> f k (JustRight b))
                        (M.zipWithMaybeAMatched $ \ k a b -> f k (Both a b))
    mapMaybeWithKeyA f = fmap catMaybes . M.traverseWithKey f
    mapEitherWithKeyA f = fmap partitionEithers . M.traverseWithKey f

infix 9 !?
(!?) :: StaticMap map => map a -> Key map -> Maybe a
as !? k = getLast . fst $ adjustA ((,) <$> Last . Just <*> id) k as

mapMaybeWithKey :: Map map => (Key map -> a -> Maybe b) -> map a -> map b
mapMaybeWithKey f = runIdentity . mapMaybeWithKeyA (pure ∘∘ f)

mapEitherWithKey :: Map map => (Key map -> a -> Either b c) -> map a -> (map b, map c)
mapEitherWithKey f = runIdentity . mapEitherWithKeyA (pure ∘∘ f)

adjustLookupA :: (StaticMap map, Applicative p) => (a -> p a) -> Key map -> map a -> p (Maybe a, map a)
adjustLookupA f = sequenceA ∘∘ (getLast *** id <<< getCompose) ∘∘ adjustA (\ a -> Compose (pure a, f a))
