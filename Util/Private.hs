module Util.Private where

import Prelude hiding ((.), id)
import Control.Category

newtype Endo s a = Endo { appEndo :: s a a }
instance Category s => Semigroup (Endo s a) where Endo f <> Endo g = Endo (f . g)
instance Category s => Monoid (Endo s a) where mempty = Endo id
