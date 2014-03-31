{-# LANGUAGE PatternGuards #-}
module LOTOS.Simplify (
    simplify,
    simplifyOnce,
    choiceB, sequenceB, parallelB, synchronizationB, interleavingB, hideB, preemptB
) where

import LOTOS.AST

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Writer
import Data.Function
import Data.List
import qualified Data.Map as Map
import Data.Maybe
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
    -- FIXME: handle Instantiate
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
    emitInterleavings [] = error "LOTOS.Simplify internal error: emitInterleavings called with empty list"
    emitInterleavings (x:xs) = foldM (\ b1' b2' -> interleavingB b1' b2') x xs
    filterInPartition p = filter ((`elem` p) . snd)
    emitParallel l r = case (l, r) of
        ([], _) -> simplify_r
        (_, []) -> simplify_l
        _ -> do
            l' <- simplify_l
            r' <- simplify_r
            liftM (fromMaybe $ Parallel sync' l' r') $ runMaybeT $ do
                (leadl, namesl, choicesl) <- breakGates sync' l'
                (leadr, namesr, choicesr) <- breakGates sync' r'
                choices <- lift $ sequence $ Map.elems $ Map.intersectionWithKey (unifyAction sync') choicesl choicesr
                (after, toMerge) <- case choices of
                    [] -> return (Stop, [])
                    [x] -> return x
                    xs | all (null . snd) xs -> do
                        after <- lift $ foldM choiceB (fst $ head xs) (map fst $ tail xs)
                        return (after, [])
                    _ -> mzero -- FIXME: merge multiple feasible choices
                lift $ do
                    let (mergel, merger) = unzip toMerge
                    let namesl' = namesl \\ mergel
                    let namesr' = namesr \\ merger
                    let exitAnys = map (const ExitAny)
                    let extractMerges names merges f = Exit . uncurry (++) . (map snd *** f . map snd) . partition ((`elem` merges) . fst) . zip names
                    leadl' <- insertBeforeExit (extractMerges namesl mergel (++ exitAnys namesr')) namesl leadl
                    leadr' <- insertBeforeExit (extractMerges namesr merger (exitAnys namesl' ++)) namesr leadr
                    lead <- interleavingB leadl' leadr'
                    sequenceB lead (mergel ++ namesl' ++ namesr') after
        where
        simpleGates g branches = emitInterleavings branches >>= impossibleGates g
        sync' = lsync `union` rsync
        lsync = Set.toList $ Set.unions $ map snd l
        simplify_l = simpleGates (lsync \\ rsync) $ map fst l
        rsync = Set.toList $ Set.unions $ map snd r
        simplify_r = simpleGates (rsync \\ lsync) $ map fst r

breakGates :: [Gate] -> Behavior -> MaybeT FreshM (Behavior, [Variable], Map.Map Gate (Bind [GateValue] Behavior))
breakGates gs (Action g binding) | g `notElem` gs = do
    (vs, b) <- unbind binding
    (next, names, rest) <- breakGates gs b
    let names' = Set.toList $ binders vs `Set.intersection` fv (Map.elems rest)
    next' <- lift $ insertBeforeExit (\ vs' -> Exit $ map (ExitExpression . Variable) names' ++ vs') names next
    return (Action g $ bind vs next', names' ++ names, rest)
breakGates gs b = do
    choices <- breakGates' gs b
    return (Exit [], [], choices)

breakGates' :: [Gate] -> Behavior -> MaybeT FreshM (Map.Map Gate (Bind [GateValue] Behavior))
breakGates' gs (Action g binding) | g `elem` gs = return $ Map.singleton g binding
breakGates' gs (Choice b1 b2) = do
    choices1 <- breakGates' gs b1
    choices2 <- breakGates' gs b2
    -- TODO: deal with non-deterministic choice branches?
    guard $ Set.null $ Map.keysSet choices1 `Set.intersection` Map.keysSet choices2
    return $ Map.union choices1 choices2
breakGates' _ _ = mzero

unifyAction :: [Gate] -> Gate -> Bind [GateValue] Behavior -> Bind [GateValue] Behavior -> FreshM (Behavior, [(Variable, Variable)])
unifyAction sync g bindingl bindingr = do
    (vsl, bl) <- unbind bindingl
    (vsr, br) <- unbind bindingr
    let (unified, toMerge) = runWriter $ zipWithM unifyGateValue vsl vsr
    let (vsnames, vs) = unzip unified
    let push decls = substs [(old, Variable new) | (VariableDeclaration old, new) <- zip decls vsnames ]
    after <- parallelB sync (push vsl bl) (push vsr br)
    return (Action g $ bind vs after, toMerge)

unifyGateValue :: GateValue -> GateValue -> Writer [(Variable, Variable)] (Variable, GateValue)
-- NOTE: In this first case, name1 and name2 were free in this action, so it's OK for them to escape their binding.
unifyGateValue v@(ValueDeclaration (Embed (Variable name1))) (ValueDeclaration (Embed (Variable name2))) = writer ((name1, v), [(name1, name2)])
unifyGateValue v@(ValueDeclaration (Embed (Variable name))) (VariableDeclaration _) = return (name, v)
unifyGateValue (VariableDeclaration _) v@(ValueDeclaration (Embed (Variable name))) = return (name, v)
unifyGateValue v@(VariableDeclaration name) (VariableDeclaration _) = return (name, v)

synchronizationB :: Behavior -> Behavior -> FreshM Behavior
synchronizationB (Exit v1) (Exit v2) | Just merged <- unifyExits v1 v2 = return $ Exit merged
synchronizationB b1 b2 = return $ Synchronization b1 b2

interleavingB :: Behavior -> Behavior -> FreshM Behavior
interleavingB Stop b = insertBeforeExit (const Stop) [] b
interleavingB a Stop = insertBeforeExit (const Stop) [] a
-- XXX: Not clearly correct if subtree contains process instantiation.
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
hideB gs b@(Instantiate{}) = hideB' gs b
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
impossibleGates gates p@(Instantiate _ gates') | not (null (gates `intersect` gates')) = return $ Parallel (gates `intersect` gates') p Stop
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
insertBeforeExit f results b@(Instantiate{}) = return $ Sequence b $ bind results $ f $ map (ExitExpression . Variable) results
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
