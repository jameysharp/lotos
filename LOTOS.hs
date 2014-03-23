module LOTOS where

import Data.Maybe

type Gate = String

data Behavior
    = Stop
    | Action Gate Behavior
    | Choice Behavior Behavior
    | Parallel [Gate] Behavior Behavior
    | Interleaving Behavior Behavior
    | Synchronization Behavior Behavior
    | Hide [Gate] Behavior
    | Process [Gate]
    | Exit
    | Sequence Behavior Behavior
    | Preempt Behavior Behavior
    deriving (Show, Eq)

interleavingB :: Behavior -> Behavior -> Behavior
interleavingB Exit b = b
interleavingB Stop b = Stop
interleavingB a Exit = a
interleavingB a Stop = Stop
interleavingB a b = Interleaving a b

sequenceB :: Behavior -> Behavior -> Behavior
sequenceB (Action g b1) b2 = Action g (sequenceB b1 b2)
sequenceB Stop b = Stop
sequenceB Exit b = b
sequenceB a Exit = a
sequenceB a b = Sequence a b

parallelB :: [Gate] -> Behavior -> Behavior -> Behavior
parallelB sync b1 b2 = maybe Stop flatten $ parallel' (`elem` sync) b1 b2

synchronizationB :: Behavior -> Behavior -> Behavior
synchronizationB b1 b2 = maybe Stop flatten $ parallel' (const True) b1 b2

parallel' :: (Gate -> Bool) -> Behavior -> Behavior -> Maybe ([Gate], [Gate], Behavior)
parallel' sync (Action g1 b1) b2
    | not (sync g1) = do
        (l, r, b) <- parallel' sync b1 b2
        return (g1 : l, r, b)
    | b2 == Exit || b2 == Stop = Nothing -- gate in sync can't match
parallel' sync b1 (Action g2 b2)
    | not (sync g2) = do
        (l, r, b) <- parallel' sync b1 b2
        return (l, g2 : r, b)
    | b1 == Exit || b1 == Stop = Nothing -- gate in sync can't match
parallel' sync (Action g1 b1) (Action g2 b2)
    | g1 == g2 = do
        rest <- parallel' sync b1 b2
        return ([], [], Action g1 $ flatten rest)
    | otherwise = Nothing
parallel' sync (Choice b1 b2) pb =
    case map flatten $ mapMaybe (parallel' sync pb) [b1, b2] of
    [] -> Nothing
    (b:bs) -> Just ([], [], foldr Choice b bs)
parallel' sync b1 b2@(Choice _ _) = parallel' sync b2 b1
parallel' sync Exit Exit = Just $ ([], [], Exit)
parallel' _ a b = error $ "what to do with parallel' (" ++ show a ++ ") (" ++ show b ++ ")?"

flatten :: ([Gate], [Gate], Behavior) -> Behavior
flatten (l, r, b) = sequenceB (interleavingB (foldr Action Exit l) (foldr Action Exit r)) b
