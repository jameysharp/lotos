module LOTOS.Util (
    fromMaybeT,
    Counter(), counter, counts,
    MemoT, runMemoT, memoM
) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid

fromMaybeT :: Monad m => a -> MaybeT m a -> m a
fromMaybeT def = liftM (fromMaybe def) . runMaybeT

newtype Counter k = Counter { counts :: Map.Map k Int }

instance Ord k => Monoid (Counter k) where
    mempty = Counter mempty
    mappend (Counter l) (Counter r) = Counter $ Map.unionWith (+) l r

counter :: k -> Counter k
counter k = Counter $ Map.singleton k 1

type MemoT m a b = StateT (Map.Map a b) m

runMemoT :: Monad m => MemoT m a b c -> m (c, Map.Map a b)
runMemoT m = runStateT m Map.empty

memoM :: (MonadFix m, Ord a) => (a -> MemoT m a b b) -> a -> MemoT m a b b
memoM f k = do
    seen <- get
    let compute = mfix $ \ x -> do
        put $ Map.insert k x seen
        f k
    maybe compute return $ Map.lookup k seen
