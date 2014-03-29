module LOTOS where

import LOTOS.AST
import LOTOS.Controllable
import LOTOS.Parser
import LOTOS.Simplify

import Control.Monad
import Data.Maybe

isTerminalBehavior :: Behavior -> Bool
isTerminalBehavior (Exit _) = True
isTerminalBehavior Stop = True
isTerminalBehavior _ = False

parallelB :: [Gate] -> Behavior -> Behavior -> Behavior
parallelB sync b1 b2 = maybe Stop flatten $ parallel' (Parallel sync) (`elem` sync) b1 b2

synchronizationB :: Behavior -> Behavior -> Behavior
synchronizationB b1 b2 = maybe Stop flatten $ parallel' Synchronization (const True) b1 b2

parallel' :: (Behavior -> Behavior -> Behavior) -> (Gate -> Bool) -> Behavior -> Behavior -> Maybe (Behavior, Behavior, [Variable], Behavior)
parallel' base sync (Action g1 v1 b1) b2
    | not (sync g1) = do
        (l, r, names, b) <- parallel' base sync b1 b2
        return (Action g1 v1 l, r, names, b)
    | isTerminalBehavior b2 = mzero -- gate in sync can't match
parallel' base sync b1 (Action g2 v2 b2)
    | not (sync g2) = do
        (l, r, names, b) <- parallel' base sync b1 b2
        return (l, Action g2 v2 r, names, b)
    | isTerminalBehavior b1 = mzero -- gate in sync can't match
parallel' base sync (Action g1 v1 b1) (Action g2 v2 b2)
    | g1 == g2 = do
        guard $ length v1 == length v2 -- sync gates must have same attribute types
        let freshNames = getFreshNames v1 v2
        let push decls = rename [(old, Variable new) | (VariableDeclaration old, new) <- zip decls freshNames, old /= new ]
        rest <- parallel' base sync (push v1 b1) (push v2 b2)
        let l = Exit $ map exitExpression v1
        let r = Exit $ map exitExpression v2
        return (l, r, freshNames, Action g1 (map (ValueDeclaration . Variable) freshNames) $ flatten rest)
    | otherwise = mzero
parallel' base sync (Choice b1 b2) pb =
    case map flatten $ mapMaybe (parallel' base sync pb) [b1, b2] of
    [] -> Nothing
    (b:bs) -> Just (Exit [], Exit [], [], foldr Choice b bs)
parallel' base sync b1 b2@(Choice _ _) = parallel' base sync b2 b1
parallel' base _ a b = return (Exit [], Exit [], [], base a b)

exitExpression :: GateValue -> ExitExpression
exitExpression (ValueDeclaration expr) = ExitExpression expr
exitExpression (VariableDeclaration _) = ExitAny

getFreshNames :: [GateValue] -> [GateValue] -> [Variable]
getFreshNames [] [] = []
getFreshNames (VariableDeclaration name : v1) (_ : v2) = name : getFreshNames v1 v2
getFreshNames (_ : v1) (VariableDeclaration name : v2) = name : getFreshNames v1 v2
getFreshNames (ValueDeclaration (Variable name) : v1) (_ : v2) = name : getFreshNames v1 v2
getFreshNames v1 v2 = error $ "getFreshNames: " ++ show v1 ++ " " ++ show v2

flatten :: (Behavior, Behavior, [Variable], Behavior) -> Behavior
flatten (l, r, names, b) = Sequence names (Interleaving l r) b

sample :: Behavior
sample = simplify $ uncontrolled ["os.req", "dev.irq"] $ Hide class_gates $ parallelB class_gates os_spec dev_spec
    where
    class_gates = ["class.send", "class.ok", "class.err"]

Right os_spec = parseBehavior "" "os.req ?msg; class.send !msg; (class.ok; os.complete; exit [] class.err ?err; os.failed !err; exit)"
Right dev_spec = parseBehavior "" "dev.enqueue ?packet; class.send !packet; dev.irq ?status; (class.ok; exit [] class.err !status; exit)"
