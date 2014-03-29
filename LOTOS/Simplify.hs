{-# LANGUAGE PatternGuards #-}
module LOTOS.Simplify (simplify) where

import LOTOS.AST

import Control.Applicative
import Control.Arrow
import Control.Monad
import Data.Function
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Generics.RepLib
import Unbound.LocallyNameless hiding (union)
import Unbound.LocallyNameless.Ops

simplify :: Behavior -> Behavior
simplify = runFreshM . (everywhereM $ mkM f)
    where
    -- Note: If any rule introduces a constructor that appears in some rule's pattern, be sure to apply `f` recursively.
    f (Choice Stop b) = return b
    f (Choice a Stop) = return a

    f (Sequence (Action g binding1) binding2) = do
        (vs, b1) <- unbind binding1
        Action g <$> (bind vs <$> f (Sequence b1 binding2))
    f (Sequence Stop _) = return Stop
    f (Sequence (Exit vs) binding) | not (any (ExitAny ==) vs) = do
        (names, b) <- unbind binding
        return $ substs [(old, new) | (ExitExpression new, old) <- zip vs names ] b
    -- this must be the last Sequence rule as we can't pattern-match through bindings
    f b@(Sequence b1 binding) = do
        (names, b2) <- unbind binding
        case b2 of
            Exit vs -> replaceExit names vs b1
            _ -> return b
        where
        replaceExit names vs (Exit vs') =
            let rebind (ExitExpression (Variable var)) | Just expr <- lookup var (zip names vs') = expr
                -- XXX: Once Expression adds operators, check that we aren't using ExitAny as an operand
                rebind e = e
            in return $ Exit $ map rebind vs
        -- Don't replace Exits on the LHS of a nested Sequence.
        replaceExit names vs (Sequence a binding) = do
            (names', b) <- unbind binding
            Sequence a <$> (bind names' <$> replaceExit names vs b)
        -- FIXME: handle Process
        replaceExit names vs b = descendBehavior (replaceExit names vs) b

    -- Avoid infinite loop when simplifying the result of impossibleGates.
    f p@(Parallel _ (Process{}) Stop) = return p
    f p@(Parallel _ Stop (Process{})) = return p

    -- Distribute Parallel across Interleaving when possible.
    f (Parallel sync b1 b2) = do
        parallels <- sequence [ (emitParallel `on` filterInPartition p) l r | p <- partitions ]
        emitInterleavings $ parallels ++ empty
        where
        hasSyncGates b = partition (Set.null . snd) [ (branch, Set.fromList sync `gatesFreeIn` branch) | branch <- interleavingBranches b ]
        (lempty, l) = hasSyncGates b1
        (rempty, r) = hasSyncGates b2
        empty = map fst $ lempty ++ rempty
        partitions = disjointPartitions $ nub $ map snd $ l ++ r
        emitInterleavings (x:xs) = foldM (\ b1' b2' -> f $ Interleaving b1' b2') x xs
        filterInPartition p = filter ((`elem` p) . snd)
        emitParallel l r = case (l, r) of
            ([], _) -> r'
            (_, []) -> l'
            _ -> Parallel (lsync `union` rsync) <$> l' <*> r'
            where
            simpleGates g branches = do
                b <- emitInterleavings branches
                if null g then return b else do
                b' <- impossibleGates g b
                everywhereM (mkM f) b'
            lsync = Set.toList $ Set.unions $ map snd l
            l' = simpleGates (lsync \\ rsync) $ map fst l
            rsync = Set.toList $ Set.unions $ map snd r
            r' = simpleGates (rsync \\ lsync) $ map fst r

    f (Synchronization (Exit v1) (Exit v2)) | Just merged <- unifyExits v1 v2 = return $ Exit merged

    f (Interleaving Stop b) = insertBeforeExit (const Stop) [] b
    f (Interleaving a Stop) = insertBeforeExit (const Stop) [] a

    -- XXX: Not clearly correct if subtree contains a Process or name shadowing.
    f (Interleaving (Exit vs) b) | Just merged <- everywhereM (mkM $ unifyExits vs) b = return merged
    f (Interleaving a (Exit vs)) | Just merged <- everywhereM (mkM $ unifyExits vs) a = return merged

    f (Hide [] b) = return b
    f b@(Hide gs (Action g binding)) | g `elem` gs = do
        (vs, b') <- unbind binding
        if Set.null (bindersAny vs `Set.intersection` fvAny b')
            then f $ Hide gs b'
            else return b
    f (Hide gs b@(Synchronization{})) = return $ hideB (Set.toList $ Set.fromList gs `gatesFreeIn` b) b
    f (Hide gs b@(Parallel sync _ _)) = do
        -- Don't hide any gate we're still trying to synchronize on.
        b' <- case gs \\ sync of
            [] -> return b
            gs' -> descendBehavior (f . Hide gs') b >>= f
        return $ hideB (sync `intersect` gs) b'
    f (Hide gs (Hide gs' b)) = f $ Hide (gs `union` gs') b
    f (Hide gs b@(Process _ gs')) = return $ hideB (gs `intersect` gs') b
    f (Hide gs b) = descendBehavior (f . Hide gs) b >>= f

    f (Preempt Stop b) = return b

    f b = return b

impossibleGates :: (Fresh m, Applicative m) => [Gate] -> Behavior -> m Behavior
impossibleGates [] b = return b
impossibleGates gates (Action g _) | g `elem` gates = return Stop
impossibleGates gates (Hide gates' b) = impossibleGates (gates \\ gates') b
impossibleGates gates p@(Process name gates') | not (null (gates `intersect` gates')) = return $ Parallel (gates `intersect` gates') p Stop
impossibleGates gates b = descendBehavior (impossibleGates gates) b

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
gatesFreeIn gates _ | Set.null gates = Set.empty
gatesFreeIn gates (Action g binding) = let (_, b) = unsafeUnbind binding in (if g `Set.member` gates then Set.insert g else id) $ gatesFreeIn (g `Set.delete` gates) b
gatesFreeIn gates (Parallel gs b1 b2) = gatesFreeIn' ((uncurry Set.difference &&& uncurry Set.intersection) (gates, Set.fromList gs)) [b1, b2]
gatesFreeIn gates (Hide gs b) = gatesFreeIn (gates `Set.difference` Set.fromList gs) b
gatesFreeIn gates (Process _ gs) = Set.fromList gs `Set.intersection` gates
gatesFreeIn gates b = gatesFreeIn' (gates, Set.empty) $ subtreesBehavior b

gatesFreeIn' :: (Set.Set Gate, Set.Set Gate) -> [Behavior] -> Set.Set Gate
gatesFreeIn' start = snd . foldr (\ b (want, found) -> (Set.difference want &&& Set.union found) $ gatesFreeIn want b) start

hideB :: [Gate] -> Behavior -> Behavior
hideB [] b = b
hideB gates b = Hide gates b
