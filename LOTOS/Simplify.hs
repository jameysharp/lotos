{-# LANGUAGE PatternGuards #-}
module LOTOS.Simplify (simplify) where

import LOTOS.AST

import Control.Applicative
import Control.Arrow
import Control.Monad
import Data.Function
import Data.List
import qualified Data.Set as Set
import Generics.RepLib
import Unbound.LocallyNameless hiding (union)

simplify :: Behavior -> Behavior
simplify = runFreshM . simplify'

simplify' :: Behavior -> FreshM Behavior
simplify' b = simplifyOnce =<< descendBehavior simplify' b

-- Note: If any rule introduces a constructor that appears in some rule's pattern, be sure to apply `simplifyOnce` recursively.
simplifyOnce :: Behavior -> FreshM Behavior
simplifyOnce (Choice b1 b2) = choiceB b1 b2
simplifyOnce (Sequence b1 binding) = uncurry (sequenceB b1) =<< unbind binding
simplifyOnce (Parallel sync b1 b2) = parallelB sync b1 b2
simplifyOnce (Synchronization b1 b2) = synchronizationB b1 b2
simplifyOnce (Interleaving b1 b2) = interleavingB b1 b2
simplifyOnce (Hide binding) = uncurry hideB =<< unbind binding
simplifyOnce (Preempt b1 b2) = preemptB b1 b2
simplifyOnce b = return b

choiceB :: Behavior -> Behavior -> FreshM Behavior
choiceB Stop b = return b
choiceB a Stop = return a
choiceB a b = return $ Choice a b

sequenceB :: Behavior -> [Variable] -> Behavior -> FreshM Behavior
sequenceB (Action g binding) names b2 = do
    (vs, b1) <- unbind binding
    Action g <$> (bind vs <$> sequenceB b1 names b2)
sequenceB Stop _ _ = return Stop
sequenceB (Exit vs) names b | not (any (ExitAny ==) vs) = return $ substs [(old, new) | (ExitExpression new, old) <- zip vs names ] b
sequenceB b1 names (Exit vs) = replaceExit b1
    where
    replaceExit (Exit vs') =
        let rebind (ExitExpression (Variable var)) | Just expr <- lookup var (zip names vs') = expr
            -- XXX: Once Expression adds operators, check that we aren't using ExitAny as an operand
            rebind e = e
        in return $ Exit $ map rebind vs
    -- Don't replace Exits on the LHS of a nested Sequence.
    replaceExit (Sequence a binding) = do
        (names', b) <- unbind binding
        Sequence a <$> (bind names' <$> replaceExit b)
    -- FIXME: handle Process
    replaceExit b = descendBehavior replaceExit b
sequenceB b1 names b2 = return $ Sequence b1 $ bind names b2

parallelB :: [Gate] -> Behavior -> Behavior -> FreshM Behavior
-- Distribute Parallel across Interleaving when possible.
parallelB sync b1 b2 = do
    parallels <- sequence [ (emitParallel `on` filterInPartition p) l r | p <- partitions ]
    emitInterleavings $ parallels ++ empty
    where
    hasSyncGates b = partition (Set.null . snd) [ (branch, Set.fromList sync `gatesFreeIn` branch) | branch <- interleavingBranches b ]
    (lempty, l) = hasSyncGates b1
    (rempty, r) = hasSyncGates b2
    empty = map fst $ lempty ++ rempty
    partitions = disjointPartitions $ nub $ map snd $ l ++ r
    emitInterleavings (x:xs) = foldM (\ b1' b2' -> interleavingB b1' b2') x xs
    filterInPartition p = filter ((`elem` p) . snd)
    emitParallel l r = case (l, r) of
        ([], _) -> r'
        (_, []) -> l'
        _ -> Parallel (lsync `union` rsync) <$> l' <*> r'
        where
        simpleGates g branches = emitInterleavings branches >>= impossibleGates g
        lsync = Set.toList $ Set.unions $ map snd l
        l' = simpleGates (lsync \\ rsync) $ map fst l
        rsync = Set.toList $ Set.unions $ map snd r
        r' = simpleGates (rsync \\ lsync) $ map fst r

synchronizationB :: Behavior -> Behavior -> FreshM Behavior
synchronizationB (Exit v1) (Exit v2) | Just merged <- unifyExits v1 v2 = return $ Exit merged
synchronizationB b1 b2 = return $ Synchronization b1 b2

interleavingB :: Behavior -> Behavior -> FreshM Behavior
interleavingB Stop b = insertBeforeExit (const Stop) [] b
interleavingB a Stop = insertBeforeExit (const Stop) [] a
-- XXX: Not clearly correct if subtree contains a Process or name shadowing.
interleavingB (Exit vs) b | Just merged <- everywhereM (mkM $ unifyExits vs) b = return merged
interleavingB a (Exit vs) | Just merged <- everywhereM (mkM $ unifyExits vs) a = return merged
interleavingB b1 b2 = return $ Interleaving b1 b2

hideB :: [Gate] -> Behavior -> FreshM Behavior
hideB [] b = return b
hideB gs b@(Action g binding) | g `elem` gs = do
    (vs, b') <- unbind binding
    if Set.null (bindersAny vs `Set.intersection` fvAny b')
        then hideB gs b'
        else hideB' gs b
-- Don't hide any gate we're still trying to synchronize on.
hideB gs b@(Synchronization{}) = hideB' gs b
hideB gs b@(Parallel sync b1 b2) = case partition (`elem` sync) gs of
    (inSync, []) -> hideB' inSync b
    (inSync, notInSync) -> do
        b1' <- hideB notInSync b1
        b2' <- hideB notInSync b2
        b' <- parallelB sync b1' b2'
        hideB inSync b'
hideB gs (Hide binding) = do
    (gs', b) <- unbind binding
    hideB (gs `union` gs') b
hideB gs b@(Process{}) = hideB' gs b
hideB gs b = simplifyOnce =<< descendBehavior (hideB gs) b

hideB' :: [Gate] -> Behavior -> FreshM Behavior
hideB' gs b = return $ case Set.toList $ Set.fromList gs `gatesFreeIn` b of
    [] -> b
    gs' -> Hide $ bind gs' b

preemptB :: Behavior -> Behavior -> FreshM Behavior
preemptB Stop b = return b
preemptB b1 b2 = return $ Preempt b1 b2

impossibleGates :: [Gate] -> Behavior -> FreshM Behavior
impossibleGates [] b = return b
impossibleGates gates (Action g _) | g `elem` gates = return Stop
impossibleGates gates (Hide binding) = do
    (gates', b) <- unbind binding
    hideB gates' =<< impossibleGates (gates \\ gates') b
impossibleGates gates p@(Process _ gates') | not (null (gates `intersect` gates')) = return $ Parallel (gates `intersect` gates') p Stop
impossibleGates gates b = simplifyOnce =<< descendBehavior (impossibleGates gates) b

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

insertBeforeExit :: ([ExitExpression] -> Behavior) -> [Variable] -> Behavior -> FreshM Behavior
insertBeforeExit f _ (Exit vs) = return $ f vs
insertBeforeExit f results b@(Process{}) = return $ Sequence b $ bind results $ f $ map (ExitExpression . Variable) results
insertBeforeExit f results (Sequence lhs binding) = do
    (names, rhs) <- unbind binding
    Sequence lhs <$> (bind names <$> insertBeforeExit f results rhs)
insertBeforeExit f results b = descendBehavior (insertBeforeExit f results) b

unifyExits :: [ExitExpression] -> [ExitExpression] -> Maybe [ExitExpression]
unifyExits v1 v2 = sequence $ zipWith exitMerge v1 v2
    where
    exitMerge ExitAny b = Just b
    exitMerge a ExitAny = Just a
    exitMerge _ _ = Nothing

gatesFreeIn :: Set.Set Gate -> Behavior -> Set.Set Gate
gatesFreeIn gates b = gates `Set.intersection` fv b
