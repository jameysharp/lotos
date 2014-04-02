module LOTOS.Specialize (liftProcesses, specializeGates) where

import LOTOS.AST

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import qualified Data.Map as Map
import qualified Data.Set as Set
import Generics.RepLib
import Unbound.LocallyNameless

-- "Lambda-lifting" for processes. This is conceptually related to the
-- supercombinator compilation strategy, as described in chapter 13 of "The
-- Implementation of Functional Programming Languages" (Simon Peyton Jones,
-- 1987). Use this if you're compiling to a language that doesn't
-- support nested functions. If you don't want to deal with first-order
-- gates either, use specializeGates instead.
liftProcesses :: Process -> Process
liftProcesses = runFreshM . liftProcesses'

liftProcesses' :: Process -> FreshM Process
liftProcesses' (Process procname (Embed binding)) = do
    (formals, binding') <- unbind binding
    (recProcs, b) <- unbind binding'
    -- First, lift grandchildren.
    procs <- mapM liftProcesses' $ unrec recProcs
    -- Then, lift children.
    (updated, procs') <- runWriterT $ mfix $ \ updated -> liftM Set.fromList $ mapM (liftChildren formals updated) procs
    -- Finally, update self.
    return $ Process procname $ Embed $ bind formals $ bind (rec procs') $ extendInstantiate formals updated b

liftChildren :: ([Gate], [Variable]) -> Set.Set (Name Process) -> Process -> WriterT [Process] FreshM (Name Process)
liftChildren newFormals@(newGates, newParams) updated (Process procname (Embed binding)) = do
    ((gates, params), binding') <- unbind binding
    (recProcs, b) <- unbind binding'
    procs <- mapM (extendProcess newFormals updated) $ unrec recProcs
    let self = Process procname $ Embed $ bind (newGates ++ gates, newParams ++ params) $ bind (rec []) $ extendInstantiate newFormals updated b
    writer (procname, self : procs)

extendProcess :: Fresh m => ([Gate], [Variable]) -> Set.Set (Name Process) -> Process -> m Process
extendProcess newFormals@(newGates, newParams) updated (Process procname (Embed binding)) = do
    ((gates, params), binding') <- unbind binding
    (recProcs, b) <- unbind binding'
    return $ Process procname $ Embed $ bind (newGates ++ gates, newParams ++ params) $ bind recProcs $ extendInstantiate newFormals updated b

extendInstantiate :: ([Gate], [Variable]) -> Set.Set (Name Process) -> Behavior -> Behavior
extendInstantiate (newGates, newParams) updated = everywhere (mkT f)
    where
    f (Instantiate procname gates params) | procname `Set.member` updated = Instantiate procname (newGates ++ gates) (map Variable newParams ++ params)
    f b = b

-- In addition to "lambda-lifting" the process, specializeGates ensures
-- that none of the nested processes are parameterized over gates. If a
-- process is instantiated with two or more distinct lists of gates,
-- then this transformation will make the program bigger. If you're
-- willing to deal with first-order gates, use liftProcesses instead.
specializeGates :: Process -> Process
specializeGates p = runFreshM $ do
    Process procname (Embed binding) <- liftProcesses' p
    (formals, binding') <- unbind binding
    (recProcs, b) <- unbind binding'
    let scope = Map.fromList [ (name, p) | p@(Process name _) <- unrec recProcs ]
    (b', procs') <- flip runReaderT scope $ flip runStateT Map.empty $ specializeInstantiationGates b
    return $ Process procname $ Embed $ bind formals $ bind (rec $ Map.elems procs') b'

type SpecializeM a = StateT (Map.Map (Name Process, [Gate]) Process) (ReaderT (Map.Map (Name Process) Process) FreshM) a

specializeInstantiationGates :: Behavior -> SpecializeM Behavior
specializeInstantiationGates (Instantiate procname gates actuals) = do
    Process procname' _ <- memoM specializeGatesWith (procname, gates)
    return $ Instantiate procname' [] actuals
specializeInstantiationGates b = descendBehavior specializeInstantiationGates b

memoM :: (MonadFix m, Ord a) => (a -> StateT (Map.Map a b) m b) -> a -> StateT (Map.Map a b) m b
memoM f k = do
    seen <- get
    let compute = mfix $ \ x -> do
        put $ Map.insert k x seen
        f k
    maybe compute return $ Map.lookup k seen

specializeGatesWith :: (Name Process, [Gate]) -> SpecializeM Process
specializeGatesWith (procname, gates) = do
    scope <- lift ask
    let Just process@(Process _ (Embed binding)) = Map.lookup procname scope
    if null gates then return process else do
    ((formalGates, formalParams), binding') <- unbind binding
    (_, b) <- unbind binding' -- liftProcesses ensured we have no nested processes
    procname' <- fresh $ procname
    let Just assign = mkPerm (map AnyName formalGates) (map AnyName gates)
    b' <- specializeInstantiationGates $ swaps assign b
    return $ Process procname' $ Embed $ bind ([], formalParams) $ bind (rec []) b'
