module Data.Map.Class where

import Control.Applicative
import Data.Either.Both
import Data.Filtrable
import Data.IntMap (IntMap)
import qualified Data.IntMap as Int
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Util ((∘∘))

class (Filtrable map, Traversable map) => Map map where
    type Key map
    alterF :: Functor f => (Maybe a -> f (Maybe a)) -> Key map -> map a -> f (map a)
    mergeA :: Applicative p => (Key map -> Either' a b -> p (Maybe c)) -> map a -> map b -> p (map c)
    mapMaybeWithKeyA :: Applicative p => (Key map -> a -> p (Maybe b)) -> map a -> p (map b)
    mapEitherWithKeyA :: Applicative p => (Key map -> a -> p (Either b c)) -> map a -> p (map b, map c)
    mapEitherWithKeyA f = liftA2 (,) <$> mapMaybeWithKeyA (fmap (Just `either` pure Nothing) ∘∘ f)
                                     <*> mapMaybeWithKeyA (fmap (pure Nothing `either` Just) ∘∘ f)

instance Filtrable IntMap where
    mapMaybe = Int.mapMaybe

instance Filtrable (M.Map key) where
    mapMaybe = M.mapMaybe

instance Map IntMap where
    type Key IntMap = Int
    alterF = Int.alterF
    mergeA f = mapMaybeWithKeyA f ∘∘
               Int.mergeWithKey (pure $ Just ∘∘ Both) (fmap JustLeft) (fmap JustRight)
    mapMaybeWithKeyA f = fmap catMaybes . Int.traverseWithKey f
    mapEitherWithKeyA f = fmap partitionEithers . Int.traverseWithKey f

instance Ord key => Map (M.Map key) where
    type Key (M.Map key) = key
    alterF = M.alterF
    mergeA f = M.mergeA (M.traverseMaybeMissing $ \ k a -> f k (JustLeft a))
                        (M.traverseMaybeMissing $ \ k b -> f k (JustRight b))
                        (M.zipWithMaybeAMatched $ \ k a b -> f k (Both a b))
    mapMaybeWithKeyA f = fmap catMaybes . M.traverseWithKey f
    mapEitherWithKeyA f = fmap partitionEithers . M.traverseWithKey f
