{-# LANGUAGE DeriveDataTypeable #-}
module LOTOS where

import Control.Arrow
import Control.Monad
import Data.Data
import Data.Function
import Data.Generics.Str
import Data.Generics.Uniplate.Data
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
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
-- FIXME: handle name shadowing
rename binding b = transformBi replace b
    where
    replace old@(Variable name) = fromMaybe old $ lookup name binding

simplify :: Behavior -> Behavior
simplify = transform f
    where
    -- Note: If any rule introduces a constructor that appears in some rule's pattern, be sure to apply `f` recursively.
    f (Choice Stop b) = b
    f (Choice a Stop) = a

    f (Sequence (Action g vs b1) names b2) = Action g vs $ f $ Sequence b1 names b2
    f (Sequence Stop _ _) = Stop
    f (Sequence (Exit vs) names b) | not (any (ExitAny ==) vs) = rename [(old, new) | (ExitExpression new, old) <- zip vs names, Variable old /= new ] b
    f (Sequence b names (Exit vs)) = replaceExit b
        where
        replaceExit (Exit vs') =
            let rebind (ExitExpression (Variable var)) | Just expr <- lookup var (zip names vs') = expr
                -- XXX: Once Expression adds operators, check that we aren't using ExitAny as an operand
                rebind e = e
            in Exit $ map rebind vs
        -- Don't replace Exits on the LHS of a nested Sequence.
        replaceExit (Sequence a names b) = Sequence a names $ replaceExit b
        replaceExit b = descend replaceExit b

    -- Avoid infinite loop when simplifying the result of impossibleGates.
    f p@(Parallel _ (Process{}) Stop) = p
    f p@(Parallel _ Stop (Process{})) = p

    -- Distribute Parallel across Interleaving when possible.
    f (Parallel sync b1 b2) = emitInterleavings $ parallels ++ empty
        where
        hasSyncGates b = partition (Set.null . snd) [ (branch, Set.fromList sync `gatesFreeIn` branch) | branch <- interleavingBranches b ]
        (lempty, l) = hasSyncGates b1
        (rempty, r) = hasSyncGates b2
        empty = map fst $ lempty ++ rempty
        partitions = disjointPartitions $ nub $ map snd $ l ++ r
        parallels = [ (emitParallel `on` filterInPartition p) l r | p <- partitions ]
        emitInterleavings = foldr1 (\ b1' b2' -> f $ Interleaving b1' b2')
        filterInPartition p = filter ((`elem` p) . snd)
        emitParallel l r = case (l, r) of
            ([], _) -> r'
            (_, []) -> l'
            _ -> Parallel (lsync `union` rsync) l' r'
            where
            simpleGates g b = if null g then b else simplify $ impossibleGates g b
            lsync = Set.toList $ Set.unions $ map snd l
            l' = simpleGates (lsync \\ rsync) $ emitInterleavings $ map fst l
            rsync = Set.toList $ Set.unions $ map snd r
            r' = simpleGates (rsync \\ lsync) $ emitInterleavings $ map fst r

    f (Synchronization (Exit v1) (Exit v2)) | Just merged <- unifyExits v1 v2 = Exit merged

    f (Interleaving Stop b) = alwaysStop b
    f (Interleaving a Stop) = alwaysStop a

    f (Interleaving (Exit v1) (Exit v2)) | Just merged <- unifyExits v1 v2 = Exit merged
    f (Interleaving (Exit v) b) | all (ExitAny ==) v = b
    f (Interleaving a (Exit v)) | all (ExitAny ==) v = a

    f (Hide gs b) = case Set.toList $ Set.fromList gs `gatesFreeIn` b of
        [] -> b
        gs' -> Hide gs' b

    f (Preempt Stop b) = b

    f b = b

impossibleGates :: [Gate] -> Behavior -> Behavior
impossibleGates [] b = b
impossibleGates gates (Action g _ _) | g `elem` gates = Stop
impossibleGates gates (Hide gates' b) = impossibleGates (gates \\ gates') b
impossibleGates gates p@(Process name gates') | not (null (gates `intersect` gates')) = Parallel (gates `intersect` gates') p Stop
impossibleGates gates b = descend (impossibleGates gates) b

interleavingBranches :: Behavior -> [Behavior]
interleavingBranches (Interleaving b1 b2) = interleavingBranches b1 ++ interleavingBranches b2
interleavingBranches b = [b]

disjointPartitions :: Ord a => [Set.Set a] -> [[Set.Set a]]
disjointPartitions [] = []
disjointPartitions (x : xs) = let (disj, conj) = go x xs in (x : conj) : disjointPartitions disj
    where
    go disjointWith xs = case partition (Set.null . Set.intersection disjointWith) xs of
        (disj@(_:_), conj@(_:_)) -> second (conj ++) $ go (Set.unions conj) disj
        ret -> ret

alwaysStop :: Behavior -> Behavior
alwaysStop (Exit _) = Stop
alwaysStop b@(Process{}) = Sequence b [] Stop
alwaysStop b = descend alwaysStop b

unifyExits :: [ExitExpression] -> [ExitExpression] -> Maybe [ExitExpression]
unifyExits v1 v2 = sequence $ zipWith exitMerge v1 v2
    where
    exitMerge ExitAny b = Just b
    exitMerge a ExitAny = Just a
    exitMerge _ _ = Nothing

gatesFreeIn :: Set.Set Gate -> Behavior -> Set.Set Gate
gatesFreeIn gates _ | Set.null gates = Set.empty
gatesFreeIn gates (Action g _ b) = (if g `Set.member` gates then Set.insert g else id) $ gatesFreeIn (g `Set.delete` gates) b
gatesFreeIn gates (Parallel gs b1 b2) = gatesFreeIn' ((uncurry Set.difference &&& uncurry Set.intersection) (gates, Set.fromList gs)) [b1, b2]
gatesFreeIn gates (Hide gs b) = gatesFreeIn (gates `Set.difference` Set.fromList gs) b
gatesFreeIn gates (Process _ gs) = Set.fromList gs `Set.intersection` gates
gatesFreeIn gates b = gatesFreeIn' (gates, Set.empty) $ children b

gatesFreeIn' :: (Set.Set Gate, Set.Set Gate) -> [Behavior] -> Set.Set Gate
gatesFreeIn' start = snd . foldr (\ b (want, found) -> (Set.difference want &&& Set.union found) $ gatesFreeIn want b) start

removeHiddenActions :: Behavior -> Behavior
removeHiddenActions = removeAction []
    where
    removeAction gates (Action g _ b) | g `elem` gates = removeAction gates b
    removeAction gates (Hide gates' b) = Hide gates' $ removeAction (gates `union` gates') b
    removeAction gates b = descend (removeAction gates) b

parallelB :: [Gate] -> Behavior -> Behavior -> Behavior
parallelB sync b1 b2 = maybe Stop flatten $ parallel' (Parallel sync) (`elem` sync) b1 b2

synchronizationB :: Behavior -> Behavior -> Behavior
synchronizationB b1 b2 = maybe Stop flatten $ parallel' Synchronization (const True) b1 b2

parallel' :: (Behavior -> Behavior -> Behavior) -> (Gate -> Bool) -> Behavior -> Behavior -> Maybe (Behavior, Behavior, [Name], Behavior)
parallel' base sync (Action g1 v1 b1) b2
    | not (sync g1) = do
        (l, r, names, b) <- parallel' base sync b1 b2
        return (Action g1 v1 l, r, names, b)
    | isTerminalBehavior b2 = Nothing -- gate in sync can't match
parallel' base sync b1 (Action g2 v2 b2)
    | not (sync g2) = do
        (l, r, names, b) <- parallel' base sync b1 b2
        return (l, Action g2 v2 r, names, b)
    | isTerminalBehavior b1 = Nothing -- gate in sync can't match
parallel' base sync (Action g1 v1 b1) (Action g2 v2 b2)
    | g1 == g2 = do
        guard $ length v1 == length v2 -- sync gates must have same attribute types
        let freshNames = getFreshNames v1 v2
        let push decls = rename [(old, Variable new) | (VariableDeclaration old, new) <- zip decls freshNames, old /= new ]
        rest <- parallel' base sync (push v1 b1) (push v2 b2)
        let l = Exit $ map exitExpression v1
        let r = Exit $ map exitExpression v2
        return (l, r, freshNames, Action g1 (map (ValueDeclaration . Variable) freshNames) $ flatten rest)
    | otherwise = Nothing
parallel' base sync (Choice b1 b2) pb =
    case map flatten $ mapMaybe (parallel' base sync pb) [b1, b2] of
    [] -> Nothing
    (b:bs) -> Just (Exit [], Exit [], [], foldr Choice b bs)
parallel' base sync b1 b2@(Choice _ _) = parallel' base sync b2 b1
parallel' base _ a b = Just $ (Exit [], Exit [], [], base a b)

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
flatten (l, r, names, b) = Sequence (Interleaving l r) names b

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
    return $ Action g v $ Interleaving b1' b2'
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
sample = simplify $ removeHiddenActions $ uncontrolled ["os.req", "dev.irq"] $ Hide class_gates $ parallelB class_gates os_spec dev_spec
    where
    class_gates = ["class.send", "class.ok", "class.err"]
    os_spec = (Action "os.req" [VariableDeclaration "msg"] (Action "class.send" [ValueDeclaration $ Variable "msg"] (Choice (Action "class.ok" [] (Action "os.complete" [] $ Exit [])) (Action "class.err" [VariableDeclaration "err"] (Action "os.failed" [ValueDeclaration $ Variable "err"] $ Exit [])))))
    dev_spec = (Action "dev.enqueue" [VariableDeclaration "packet"] (Action "class.send" [ValueDeclaration $ Variable "packet"] (Action "dev.irq" [VariableDeclaration "status"] (Choice (Action "class.ok" [] $ Exit []) (Action "class.err" [ValueDeclaration $ Variable "status"] $ Exit [])))))
