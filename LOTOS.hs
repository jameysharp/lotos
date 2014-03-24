{-# LANGUAGE DeriveDataTypeable #-}
module LOTOS where

import Control.Monad
import Data.Data
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Generics.Str
import Data.Generics.Uniplate.Data
import Data.Typeable

type Gate = String

type Name = String

newtype Expression = Variable Name
    deriving (Eq, Data, Typeable)

instance Show Expression where
    show (Variable name) = name

data ExitExpression = ExitExpression Expression | ExitAny
    deriving (Eq, Data, Typeable)

instance Show ExitExpression where
    show ExitAny = "any"
    show (ExitExpression expr) = show expr

data GateValue = ValueDeclaration Expression | VariableDeclaration Name
    deriving (Data, Typeable)

instance Show GateValue where
    show (ValueDeclaration expr) = '!' : show expr
    show (VariableDeclaration name) = '?' : name

data Behavior
    = Stop
    | Action Gate [GateValue] Behavior
    | Choice Behavior Behavior
    | Parallel [Gate] Behavior Behavior
    | Interleaving Behavior Behavior
    | Synchronization Behavior Behavior
    | Hide [Gate] Behavior
    | Process Name [Gate]
    | Exit [ExitExpression]
    | Sequence Behavior [Name] Behavior
    | Preempt Behavior Behavior
    deriving (Data, Typeable)

instance Show Behavior where
    show Stop = "stop"
    show (Action g vs b) = unwords (g : map show vs) ++ "; " ++ show b
    show (Choice b1 b2) = "(" ++ show b1 ++ ") [] (" ++ show b2 ++ ")"
    show (Parallel gs b1 b2) = "(" ++ show b1 ++ ") |" ++ show gs ++ "| (" ++ show b2 ++ ")"
    show (Interleaving b1 b2) = "(" ++ show b1 ++ ") ||| (" ++ show b2 ++ ")"
    show (Synchronization b1 b2) = "(" ++ show b1 ++ ") || (" ++ show b2 ++ ")"
    show (Hide gs b) = unwords ("hide" : gs ++ ["in", show b])
    show (Process name []) = name
    show (Process name gs) = name ++ " " ++ show gs
    show (Exit []) = "exit"
    show (Exit gs) = "exit(" ++ unwords (map show gs) ++ ")"
    show (Sequence b1 accept b2) = "(" ++ show b1 ++ ") >> " ++
        case accept of
        [] -> "(" ++ show b2 ++ ")"
        _ -> unwords ("accept" : accept ++ ["in", "(" ++ show b2 ++ ")"])
    show (Preempt b1 b2) = "(" ++ show b1 ++ ") |> (" ++ show b2 ++ ")"

isTerminalBehavior :: Behavior -> Bool
isTerminalBehavior (Exit _) = True
isTerminalBehavior Stop = True
isTerminalBehavior _ = False

rename :: [(Name, Expression)] -> Behavior -> Behavior
rename [] b = b
rename binding b = transformBi replace b
    where
    replace old@(Variable name) = fromMaybe old $ lookup name binding

hideB :: [Gate] -> Behavior -> Behavior
hideB gates (Action g vs b)
    | g `elem` gates = hideB gates b
    | otherwise = Action g vs $ hideB gates b
hideB gates (Choice b1 b2) = Choice (hideB gates b1) (hideB gates b2)
hideB gates b@(Parallel sync b1 b2)
    | not $ any (`elem` gates) sync = Parallel sync (hideB gates b1) (hideB gates b2)
hideB gates (Interleaving b1 b2) = Interleaving (hideB gates b1) (hideB gates b2)
hideB gates (Hide gates' b) = hideB (gates `union` gates') b
hideB gates b@(Process name gates') | not $ any (`elem` gates) gates' = b
hideB _ Stop = Stop
hideB _ (Exit exprs) = Exit exprs
hideB gates (Sequence b1 names b2) = Sequence (hideB gates b1) names (hideB gates b2)
hideB gates (Preempt b1 b2) = Preempt (hideB gates b1) (hideB gates b2)
hideB gates b = Hide gates b

sequenceB :: Behavior -> [Name] -> Behavior -> Behavior
sequenceB (Action g vs b1) names b2 = Action g vs (sequenceB b1 names b2)
sequenceB Stop _ _ = Stop
sequenceB (Exit vs) names b | null [() | ExitAny <- vs] = rename [(old, new) | (ExitExpression new, old) <- zip vs names, Variable old /= new ] b
sequenceB a [] (Exit []) = a
sequenceB a names b = Sequence a names b

interleavingB :: Behavior -> Behavior -> Behavior
interleavingB (Exit v1) (Exit v2) | length v1 == length v2 && all isJust merged = Exit $ map fromJust merged
    where
    merged = zipWith exitMerge v1 v2
    exitMerge ExitAny b = Just b
    exitMerge a ExitAny = Just a
    exitMerge _ _ = Nothing
interleavingB (Exit []) b = b
interleavingB a (Exit []) = a
interleavingB a b = Interleaving a b

parallelB :: [Gate] -> Behavior -> Behavior -> Behavior
parallelB sync b1 b2 = maybe Stop flatten $ parallel' (`elem` sync) b1 b2

synchronizationB :: Behavior -> Behavior -> Behavior
synchronizationB b1 b2 = maybe Stop flatten $ parallel' (const True) b1 b2

parallel' :: (Gate -> Bool) -> Behavior -> Behavior -> Maybe (Behavior, Behavior, [Name], Behavior)
parallel' sync (Action g1 v1 b1) b2
    | not (sync g1) = do
        (l, r, names, b) <- parallel' sync b1 b2
        return (Action g1 v1 l, r, names, b)
    | isTerminalBehavior b2 = Nothing -- gate in sync can't match
parallel' sync b1 (Action g2 v2 b2)
    | not (sync g2) = do
        (l, r, names, b) <- parallel' sync b1 b2
        return (l, Action g2 v2 r, names, b)
    | isTerminalBehavior b1 = Nothing -- gate in sync can't match
parallel' sync (Action g1 v1 b1) (Action g2 v2 b2)
    | g1 == g2 = do
        guard $ length v1 == length v2 -- sync gates must have same attribute types
        let freshNames = getFreshNames v1 v2
        let push decls = rename [(old, Variable new) | (VariableDeclaration old, new) <- zip decls freshNames, old /= new ]
        rest <- parallel' sync (push v1 b1) (push v2 b2)
        let l = Exit $ map exitExpression v1
        let r = Exit $ map exitExpression v2
        return (l, r, freshNames, Action g1 (map (ValueDeclaration . Variable) freshNames) $ flatten rest)
    | otherwise = Nothing
parallel' sync (Choice b1 b2) pb =
    case map flatten $ mapMaybe (parallel' sync pb) [b1, b2] of
    [] -> Nothing
    (b:bs) -> Just (Exit [], Exit [], [], foldr Choice b bs)
parallel' sync b1 b2@(Choice _ _) = parallel' sync b2 b1
parallel' sync (Exit []) (Exit []) = Just (Exit [], Exit [], [], Exit [])
parallel' _ a b = error $ "what to do with parallel' (" ++ show a ++ ") (" ++ show b ++ ")?"

exitExpression :: GateValue -> ExitExpression
exitExpression (ValueDeclaration expr) = ExitExpression expr
exitExpression (VariableDeclaration _) = ExitAny

getFreshNames :: [GateValue] -> [GateValue] -> [Name]
getFreshNames [] [] = []
getFreshNames (VariableDeclaration name : v1) (_ : v2) = name : getFreshNames v1 v2
getFreshNames (_ : v1) (VariableDeclaration name : v2) = name : getFreshNames v1 v2
getFreshNames (ValueDeclaration (Variable name) : v1) (_ : v2) = name : getFreshNames v1 v2
getFreshNames v1 v2 = error $ "getFreshNames: " ++ show v1 ++ " " ++ show v2

flatten :: (Behavior, Behavior, [Name], Behavior) -> Behavior
flatten (l, r, names, b) = sequenceB (interleavingB l r) names b

uncontrolled :: [Gate] -> Behavior -> Behavior
uncontrolled gates (Interleaving b1 b2)
    | b1 `isActionOn` gates || not (b2 `isActionOn` gates), Just b <- extractInterleavedAction b1 b2 = uncontrolled gates b
    | Just b <- extractInterleavedAction b2 b1 = uncontrolled gates b
uncontrolled gates b = descend (uncontrolled gates) b

isActionOn :: Behavior -> [Gate] -> Bool
isActionOn (Action g _ _) gates | g `elem` gates = True
isActionOn _ _ = False

extractInterleavedAction :: Behavior -> Behavior -> Maybe Behavior
extractInterleavedAction b1 b2 = do
    Action g v b1' <- return b1
    common <- commonExit $ map (exitOf [name | VariableDeclaration name <- v]) $ exits b1'
    b2' <- if all (ExitAny ==) common then return b2 else do
        (b2', free) <- para (unify common) b2
        guard $ Map.null free
        return b2'
    return $ Action g v $ interleavingB b1' b2'
    where
    unify common (Exit exprs) [] = Just (unboundExit, exitBinding) where
        unboundExit = Exit [ case l of ExitAny -> r; _ -> ExitAny | (l, r) <- zip common exprs ]
        exitBinding = Map.fromList [ (var, expr) | (ExitExpression expr, ExitExpression (Variable var)) <- zip common exprs ]
    unify common (Action g vs b) [Just (b', binding)] = Just (unboundAction, actionBinding) where
        unboundAction = Action g (map updatingDecl vs) b'
        updatingDecl (VariableDeclaration var) | Just expr <- Map.lookup var binding = ValueDeclaration expr
        updatingDecl d = d
        actionBinding = foldr Map.delete binding [ name | VariableDeclaration name <- vs ]
    unify common b cs = do
        (bs, bindings) <- liftM unzip $ sequence cs
        guard $ same bindings
        let (old, fromStr) = uniplate b
        let (_, fromList) = strStructure old
        return (fromStr $ fromList bs, head bindings)

exits :: Behavior -> [[ExitExpression]]
exits b = [exprs | Exit exprs <- universe b] -- FIXME: exclude Exits from Sequence LHS

exitOf :: [Name] -> [ExitExpression] -> [ExitExpression]
exitOf names = map restrict
    where
    restrict exit@(ExitExpression expr) | any (`elem` names) [var | Variable var <- universe expr] = exit
    restrict _ = ExitAny

same :: Eq a => [a] -> Bool
same (x:xs) = all (x ==) xs

commonExit :: [[ExitExpression]] -> Maybe [ExitExpression]
commonExit exprs = if all same $ transpose exprs then Just (head exprs) else Nothing

sample :: Behavior
sample = uncontrolled ["os.req", "dev.irq"] $ hideB class_gates $ parallelB class_gates os_spec dev_spec
    where
    class_gates = ["class.send", "class.ok", "class.err"]
    os_spec = (Action "os.req" [VariableDeclaration "msg"] (Action "class.send" [ValueDeclaration $ Variable "msg"] (Choice (Action "class.ok" [] (Action "os.complete" [] $ Exit [])) (Action "class.err" [VariableDeclaration "err"] (Action "os.failed" [ValueDeclaration $ Variable "err"] $ Exit [])))))
    dev_spec = (Action "dev.enqueue" [VariableDeclaration "packet"] (Action "class.send" [ValueDeclaration $ Variable "packet"] (Action "dev.irq" [VariableDeclaration "status"] (Choice (Action "class.ok" [] $ Exit []) (Action "class.err" [ValueDeclaration $ Variable "status"] $ Exit [])))))
