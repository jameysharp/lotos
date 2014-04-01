module LOTOS.Specialize (liftProcesses) where

import LOTOS.AST

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.Writer
import qualified Data.Set as Set
import Generics.RepLib
import Unbound.LocallyNameless

-- "Lambda-lifting" for processes. This is conceptually related to the
-- supercombinator compilation strategy, as described in chapter 13 of "The
-- Implementation of Functional Programming Languages" (Simon Peyton Jones,
-- 1987).
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
