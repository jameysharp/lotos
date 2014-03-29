module LOTOS where

import LOTOS.AST
import LOTOS.Controllable
import LOTOS.Parser
import LOTOS.Simplify

import Control.Monad
import Data.Maybe
import Unbound.LocallyNameless hiding (flatten)

isTerminalBehavior :: Behavior -> Bool
isTerminalBehavior (Exit _) = True
isTerminalBehavior Stop = True
isTerminalBehavior _ = False

parallelB :: [Gate] -> Behavior -> Behavior -> Behavior
parallelB sync b1 b2 = maybe Stop flatten $ runFreshMT $ parallel' (Parallel sync) (`elem` sync) b1 b2

synchronizationB :: Behavior -> Behavior -> Behavior
synchronizationB b1 b2 = maybe Stop flatten $ runFreshMT $ parallel' Synchronization (const True) b1 b2

parallel' :: (Behavior -> Behavior -> Behavior) -> (Gate -> Bool) -> Behavior -> Behavior -> FreshMT Maybe (Behavior, Behavior, [Variable], Behavior)
parallel' base sync (Action g1 binding) b2
    | not (sync g1) = do
        (v1, b1) <- unbind binding
        (l, r, names, b) <- parallel' base sync b1 b2
        return (Action g1 $ bind v1 l, r, names, b)
    | isTerminalBehavior b2 = mzero -- gate in sync can't match
parallel' base sync b1 (Action g2 binding)
    | not (sync g2) = do
        (v2, b2) <- unbind binding
        (l, r, names, b) <- parallel' base sync b1 b2
        return (l, Action g2 $ bind v2 r, names, b)
    | isTerminalBehavior b1 = mzero -- gate in sync can't match
parallel' base sync (Action g1 binding1) (Action g2 binding2)
    | g1 == g2 = do
        (v1, b1) <- unbind binding1
        (v2, b2) <- unbind binding2
        guard $ length v1 == length v2 -- sync gates must have same attribute types
        let freshNames = getFreshNames v1 v2
        let push decls = substs [(old, Variable new) | (VariableDeclaration old, new) <- zip decls freshNames ]
        rest <- parallel' base sync (push v1 b1) (push v2 b2)
        let l = Exit $ map exitExpression v1
        let r = Exit $ map exitExpression v2
        return (l, r, freshNames, Action g1 $ bind (map (ValueDeclaration . Embed . Variable) freshNames) $ flatten rest)
    | otherwise = mzero
parallel' base sync (Choice b1 b2) pb = do
    b1' <- liftM flatten (parallel' base sync pb b1) `mplus` return Stop
    b2' <- liftM flatten (parallel' base sync pb b2) `mplus` return Stop
    case filter (not . isStop) [b1', b2'] of
        [] -> mzero
        (b:bs) -> return (Exit [], Exit [], [], foldr Choice b bs)
parallel' base sync b1 b2@(Choice _ _) = parallel' base sync b2 b1
parallel' base _ a b = return (Exit [], Exit [], [], base a b)

isStop :: Behavior -> Bool
isStop Stop = True
isStop _ = False

exitExpression :: GateValue -> ExitExpression
exitExpression (ValueDeclaration (Embed expr)) = ExitExpression expr
exitExpression (VariableDeclaration _) = ExitAny

getFreshNames :: [GateValue] -> [GateValue] -> [Variable]
getFreshNames [] [] = []
getFreshNames (VariableDeclaration name : v1) (_ : v2) = name : getFreshNames v1 v2
getFreshNames (_ : v1) (VariableDeclaration name : v2) = name : getFreshNames v1 v2
getFreshNames (ValueDeclaration (Embed (Variable name)) : v1) (_ : v2) = name : getFreshNames v1 v2
getFreshNames v1 v2 = error $ "getFreshNames: " ++ show v1 ++ " " ++ show v2

flatten :: (Behavior, Behavior, [Variable], Behavior) -> Behavior
flatten (l, r, names, b) = Sequence (Interleaving l r) $ bind names b

sample :: Behavior
sample = simplify $ uncontrolled [s2n "os.req", s2n "dev.irq"] $ Hide class_gates $ parallelB class_gates os_spec dev_spec

class_gates = [s2n "class.send", s2n "class.ok", s2n "class.err"]
Right os_spec = parseBehavior "" "os.req ?msg; class.send !msg; (class.ok; os.complete; exit [] class.err ?err; os.failed !err; exit)"
Right dev_spec = parseBehavior "" "dev.enqueue ?packet; class.send !packet; dev.irq ?status; (class.ok; exit [] class.err !status; exit)"
