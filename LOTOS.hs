module LOTOS where

import Data.List
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

hideB :: [Gate] -> Behavior -> Behavior
hideB gates (Action g b)
    | g `elem` gates = hideB gates b
    | otherwise = Action g $ hideB gates b
hideB gates (Choice b1 b2) = Choice (hideB gates b1) (hideB gates b2)
hideB gates b@(Parallel sync b1 b2)
    | not $ any (`elem` gates) sync = Parallel sync (hideB gates b1) (hideB gates b2)
hideB gates (Interleaving b1 b2) = Interleaving (hideB gates b1) (hideB gates b2)
hideB gates (Hide gates' b) = hideB (gates `union` gates') b
hideB gates b@(Process gates') | not $ any (`elem` gates) gates' = b
hideB _ Stop = Stop
hideB _ Exit = Exit
hideB gates (Sequence b1 b2) = Sequence (hideB gates b1) (hideB gates b2)
hideB gates (Preempt b1 b2) = Preempt (hideB gates b1) (hideB gates b2)
hideB gates b = Hide gates b

sequenceB :: Behavior -> Behavior -> Behavior
sequenceB (Action g b1) b2 = Action g (sequenceB b1 b2)
sequenceB Stop b = Stop
sequenceB Exit b = b
sequenceB a Exit = a
sequenceB a b = Sequence a b

interleavingB :: Behavior -> Behavior -> Behavior
interleavingB Exit b = b
interleavingB a Exit = a
interleavingB a b = Interleaving a b

parallelB :: [Gate] -> Behavior -> Behavior -> Behavior
parallelB sync b1 b2 = maybe Stop flatten $ parallel' (`elem` sync) b1 b2

synchronizationB :: Behavior -> Behavior -> Behavior
synchronizationB b1 b2 = maybe Stop flatten $ parallel' (const True) b1 b2

parallel' :: (Gate -> Bool) -> Behavior -> Behavior -> Maybe (Behavior, Behavior, Behavior)
parallel' sync (Action g1 b1) b2
    | not (sync g1) = do
        (l, r, b) <- parallel' sync b1 b2
        return (Action g1 l, r, b)
    | b2 == Exit || b2 == Stop = Nothing -- gate in sync can't match
parallel' sync b1 (Action g2 b2)
    | not (sync g2) = do
        (l, r, b) <- parallel' sync b1 b2
        return (l, Action g2 r, b)
    | b1 == Exit || b1 == Stop = Nothing -- gate in sync can't match
parallel' sync (Action g1 b1) (Action g2 b2)
    | g1 == g2 = do
        rest <- parallel' sync b1 b2
        return (Exit, Exit, Action g1 $ flatten rest)
    | otherwise = Nothing
parallel' sync (Choice b1 b2) pb =
    case map flatten $ mapMaybe (parallel' sync pb) [b1, b2] of
    [] -> Nothing
    (b:bs) -> Just (Exit, Exit, foldr Choice b bs)
parallel' sync b1 b2@(Choice _ _) = parallel' sync b2 b1
parallel' sync Exit Exit = Just (Exit, Exit, Exit)
parallel' _ a b = error $ "what to do with parallel' (" ++ show a ++ ") (" ++ show b ++ ")?"

flatten :: (Behavior, Behavior, Behavior) -> Behavior
flatten (l, r, b) = sequenceB (interleavingB l r) b

sample :: Behavior
sample = hideB class_gates $ parallelB class_gates os_spec dev_spec
    where
    class_gates = ["class.send", "class.ok", "class.err"]
    os_spec = (Action "os.req" (Action "class.send" (Choice (Action "class.ok" (Action "os.complete" Exit)) (Action "class.err" (Action "os.failed" Exit)))))
    dev_spec = (Action "dev.enqueue" (Action "class.send" (Action "dev.irq" (Choice (Action "class.ok" Exit) (Action "class.err" Exit)))))
