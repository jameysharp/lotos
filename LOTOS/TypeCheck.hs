module LOTOS.TypeCheck (inferFunctionality, Functionality) where

import LOTOS.AST

import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import Data.List
import qualified Data.Map as Map
import Unbound.LocallyNameless

-- TODO: Since we aren't tracking types yet we can only count how many values are in an exit branch
data Functionality = NoExit | MayExit Int
    deriving Eq

instance Show Functionality where
    show NoExit = "noexit"
    show (MayExit 0) = "exit"
    show (MayExit n) = "exit(" ++ intercalate ", " [ 't' : show k | k <- [1..n] ] ++ ")"

type TypeError = String
type FunctionalityMap = Map.Map (Name Process) Functionality

inferFunctionality :: Process -> Either TypeError FunctionalityMap
inferFunctionality p = fixpoint initial
    where
    (transfer, initial) = runFreshM $ runWriterT $ inferFunctionality' p
    fixpoint last = do
        next <- runReaderT transfer last
        if next == last then return last else fixpoint next

inferFunctionality' :: Process -> WriterT FunctionalityMap FreshM (ReaderT FunctionalityMap (Either TypeError) FunctionalityMap)
inferFunctionality' (Process procname (Embed binding)) = do
    (_, binding') <- unbind binding
    (recProcs, b) <- unbind binding'
    tell $ Map.singleton procname NoExit
    f <- lift $ inferBehaviorFunctionality b
    maps <- mapM inferFunctionality' $ unrec recProcs
    return $ do
        f' <- f
        maps' <- sequence maps
        return $ Map.insert procname f' $ Map.unions maps'

makeTypeError :: String -> ReaderT a (Either TypeError) b
makeTypeError msg = lift $ Left msg

inferBehaviorFunctionality :: Behavior -> FreshM (ReaderT FunctionalityMap (Either TypeError) Functionality)
inferBehaviorFunctionality Stop = return $ return NoExit
inferBehaviorFunctionality (Action _ binding) = do
    (_, b) <- unbind binding
    inferBehaviorFunctionality b
inferBehaviorFunctionality (Choice b1 b2) = inferChoiceFunctionality b1 b2
inferBehaviorFunctionality (Parallel _ b1 b2) = inferInterleavingFunctionality b1 b2
inferBehaviorFunctionality (Interleaving b1 b2) = inferInterleavingFunctionality b1 b2
inferBehaviorFunctionality (Synchronization b1 b2) = inferInterleavingFunctionality b1 b2
inferBehaviorFunctionality (Hide binding) = do
    (_, b) <- unbind binding
    inferBehaviorFunctionality b
inferBehaviorFunctionality (Instantiate procname _ _) = return $ do
    others <- ask
    case Map.lookup procname others of
        Nothing -> makeTypeError $ "can't instantiate undefined process '" ++ show procname ++ "'"
        Just f -> return f
inferBehaviorFunctionality (Exit vs) = return $ return $ MayExit $ length vs
inferBehaviorFunctionality (Sequence b1 binding) = do
    (names, b2) <- unbind binding
    f1 <- inferBehaviorFunctionality b1
    f2 <- inferBehaviorFunctionality b2
    return $ do
        f1' <- f1
        case f1' of
            NoExit -> return NoExit
            MayExit n | n == length names -> f2
            _ -> makeTypeError $ "can't sequence " ++ show f1' ++ " into " ++ show names
inferBehaviorFunctionality (Preempt b1 b2) = inferChoiceFunctionality b1 b2

inferChoiceFunctionality :: Behavior -> Behavior -> FreshM (ReaderT FunctionalityMap (Either TypeError) Functionality)
inferChoiceFunctionality b1 b2 = do
    f1 <- inferBehaviorFunctionality b1
    f2 <- inferBehaviorFunctionality b2
    return $ do
        f1' <- f1
        f2' <- f2
        case (f1', f2') of
            (NoExit, _) -> return f2'
            (_, NoExit) -> return f1'
            (MayExit n, MayExit m) | n == m -> return $ MayExit n
            _ -> makeTypeError $ "can't unify choice of " ++ show f1' ++ " or " ++ show f2'

inferInterleavingFunctionality :: Behavior -> Behavior -> FreshM (ReaderT FunctionalityMap (Either TypeError) Functionality)
inferInterleavingFunctionality b1 b2 = do
    f1 <- inferBehaviorFunctionality b1
    f2 <- inferBehaviorFunctionality b2
    return $ do
        f1' <- f1
        f2' <- f2
        case (f1', f2') of
            (NoExit, _) -> return NoExit
            (_, NoExit) -> return NoExit
            (MayExit n, MayExit m) | n == m -> return $ MayExit n
            _ -> makeTypeError $ "can't unify interleaving of " ++ show f1' ++ " with " ++ show f2'
