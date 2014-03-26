{-# LANGUAGE PatternGuards #-}
module LOTOS.Simplify (simplify) where

import LOTOS.AST

import Control.Arrow
import Data.Function
import Data.Generics.Uniplate.Data
import Data.List
import Data.Maybe
import qualified Data.Set as Set

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

    f (Interleaving Stop b) = insertBeforeExit (const Stop) [] b
    f (Interleaving a Stop) = insertBeforeExit (const Stop) [] a

    -- XXX: Not clearly correct if subtree contains a Process or name shadowing.
    f (Interleaving (Exit vs) b) | Just merged <- transformBiM (unifyExits vs) b = merged
    f (Interleaving a (Exit vs)) | Just merged <- transformBiM (unifyExits vs) a = merged

    f (Hide [] b) = b
    f (Hide gs (Action g vs b)) | g `elem` gs = f $ Hide gs b
    f (Hide gs b@(Synchronization{})) = hideB (Set.toList $ Set.fromList gs `gatesFreeIn` b) b
    f (Hide gs b@(Parallel sync _ _)) = hideB (sync `intersect` gs) $ case gs \\ sync of
        [] -> b
        gs' -> f $ descend (f . Hide gs') b
    f (Hide gs (Hide gs' b)) = f $ Hide (gs `union` gs') b
    f (Hide gs b@(Process _ gs')) = hideB (gs `intersect` gs') b
    f (Hide gs b) = descend (f . Hide gs) b

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

insertBeforeExit :: ([ExitExpression] -> Behavior) -> [Name] -> Behavior -> Behavior
insertBeforeExit f _ (Exit vs) = f vs
insertBeforeExit f results b@(Process{}) = Sequence b results $ f $ map (ExitExpression . Variable) results
insertBeforeExit f results (Sequence lhs names rhs) = Sequence lhs names $ insertBeforeExit f results rhs
insertBeforeExit f results b = descend (insertBeforeExit f results) b

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

hideB :: [Gate] -> Behavior -> Behavior
hideB [] b = b
hideB gates b = Hide gates b
