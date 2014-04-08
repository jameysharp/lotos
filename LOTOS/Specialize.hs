{-# LANGUAGE PatternGuards #-}
module LOTOS.Specialize (liftProcesses, specializeGates) where

import LOTOS.AST
import LOTOS.AST.Util
import LOTOS.Util
import LOTOS.Simplify

import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Writer
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Set as Set
import Unbound.LocallyNameless

-- "Lambda-lifting" for processes. This is conceptually related to the
-- supercombinator compilation strategy, as described in chapter 13 of "The
-- Implementation of Functional Programming Languages" (Simon Peyton Jones,
-- 1987). Use this if you're compiling to a language that doesn't
-- support nested functions. If you don't want to deal with first-order
-- gates either, use specializeGates instead.
liftProcesses :: Process -> Process
liftProcesses = runFreshM . liftProcessesM

liftProcessesM :: Process -> FreshM Process
liftProcessesM p = do
    (p', descendents) <- runWriterT $ liftProcesses' Map.empty p
    flip transformProcess p' $ \ formals [] b -> return (formals, descendents, b)

type Scope = ([Gate], [Variable])

liftProcesses' :: Map.Map (Name Process) Scope -> Process -> WriterT [Process] FreshM Process
liftProcesses' updated p@(Process name _) = flip transformProcess p $ \ formals procs b -> do
    let formals' = Map.findWithDefault mempty name updated `mappend` formals
    let updated' = Map.fromList [ (name, formals') | Process name _ <- procs ] `Map.union` updated
    procs' <- mapM (liftProcesses' updated') procs
    b' <- lift $ extendInstantiate updated' b
    writer ((formals', [], b'), procs')

extendInstantiate :: Map.Map (Name Process) Scope -> Behavior -> FreshM Behavior
extendInstantiate updated (Instantiate procname gates params)
    | Just (newGates, newParams) <- Map.lookup procname updated
    = return $ Instantiate procname (newGates ++ gates) (map Variable newParams ++ params)
extendInstantiate updated b = descendBehavior (extendInstantiate updated) b

-- In addition to "lambda-lifting" the process, specializeGates ensures
-- that none of the nested processes are parameterized over gates. If a
-- process is instantiated with two or more distinct lists of gates,
-- then this transformation will make the program bigger. If you're
-- willing to deal with first-order gates, use liftProcesses instead.
specializeGates :: Process -> Process
specializeGates p = runFreshM $ liftProcessesM p >>= transformProcess f
    where
    f formals procs b = do
        let scope = Map.fromList [ (name, p) | p@(Process name _) <- procs ]
        (b', procs') <- flip runReaderT scope $ runMemoT $ specializeInstantiationGates Set.empty b
        return (formals, Map.elems procs', b')

type SpecializeM a = MemoT (ReaderT (Map.Map (Name Process) Process) FreshM) (Name Process, [Gate], Set.Set Gate) Process a

specializeInstantiationGates :: Set.Set Gate -> Behavior -> SpecializeM Behavior
specializeInstantiationGates hidden (Instantiate procname gates actuals) = do
    Process procname' _ <- memoM specializeGatesWith (procname, gates, hidden)
    return $ Instantiate procname' [] actuals
specializeInstantiationGates hidden (Hide binding) = do
    (gs, b) <- unbind binding
    b' <- specializeInstantiationGates (hidden `Set.union` Set.fromList gs) b
    hideB gs b'
specializeInstantiationGates hidden b = descendBehavior (specializeInstantiationGates hidden) b

specializeGatesWith :: (Name Process, [Gate], Set.Set Gate) -> SpecializeM Process
specializeGatesWith (procname, gates, hidden) = do
    scope <- lift ask
    let Just process = Map.lookup procname scope
    if null gates then return process else do
    -- NOTE: liftProcesses ensured we have no nested processes
    Process _ body <- flip transformProcess process $ \ (formalGates, formalParams) [] b -> do
        let Just assign = mkPerm (map AnyName formalGates) (map AnyName gates)
        b' <- specializeInstantiationGates hidden $ swaps assign b
        simplified <- hideB (Set.toList hidden) b'
        return (([], formalParams), [], simplified)
    procname' <- fresh $ procname
    return $ Process procname' body
