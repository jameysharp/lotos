module LOTOS.AST.Util where

import LOTOS.AST

import Control.Applicative
import Unbound.LocallyNameless

-- descendBehavior is like gmapM but collects behaviors immediately below bindings too.
descendBehavior :: (Fresh m, Applicative m) => (Behavior -> m Behavior) -> Behavior -> m Behavior
descendBehavior f (Action g binding) = do
    (vs, b) <- unbind binding
    Action g <$> (bind vs <$> f b)
descendBehavior f (Sequence b1 binding) = do
    (names, b2) <- unbind binding
    Sequence <$> f b1 <*> (bind names <$> f b2)
descendBehavior f (Hide binding) = do
    (gs, b) <- unbind binding
    Hide <$> (bind gs <$> f b)
descendBehavior f b = gmapM (mkM f) b

transformProcess :: Fresh m => (([Gate], [Variable]) -> [Process] -> Behavior -> m (([Gate], [Variable]), [Process], Behavior)) -> Process -> m Process
transformProcess f (Process procname (Embed binding)) = do
    (formals, binding') <- unbind binding
    (recProcs, b) <- unbind binding'
    (formals', procs', b') <- f formals (unrec recProcs) b
    return $ Process procname $ Embed $ bind formals' $ bind (rec procs') b'
