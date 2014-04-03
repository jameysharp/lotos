module LOTOS.Util (
    Counter(), counter, counts
) where

import qualified Data.Map as Map
import Data.Monoid

newtype Counter k = Counter { counts :: Map.Map k Int }

instance Ord k => Monoid (Counter k) where
    mempty = Counter mempty
    mappend (Counter l) (Counter r) = Counter $ Map.unionWith (+) l r

counter :: k -> Counter k
counter k = Counter $ Map.singleton k 1
