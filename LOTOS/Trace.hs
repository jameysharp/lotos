module LOTOS.Trace (Trace(..), traceBehavior) where

import LOTOS.AST

import Data.Function
import qualified Data.Map as Map

data Trace = TraceExit | Trace (Map.Map Gate Trace)
    deriving Show

traceBehavior :: Behavior -> Trace
traceBehavior Stop = Trace Map.empty
traceBehavior (Action g _ b) = Trace $ Map.singleton g $ traceBehavior b
traceBehavior (Choice b1 b2) = (joinChoiceTrace `on` traceBehavior) b1 b2
traceBehavior (Parallel sync b1 b2) = (synchronizeTrace (`elem` sync) `on` traceBehavior) b1 b2
traceBehavior (Interleaving b1 b2) = (synchronizeTrace (const False) `on` traceBehavior) b1 b2
traceBehavior (Synchronization b1 b2) = (synchronizeTrace (const True) `on` traceBehavior) b1 b2
traceBehavior (Hide _ b) = traceBehavior b
traceBehavior (Process{}) = Trace Map.empty -- FIXME: ought to recurse on the named Process
traceBehavior (Exit _) = TraceExit
traceBehavior (Sequence b1 _ b2) = replaceTraceExit (traceBehavior b2) $ traceBehavior b1
traceBehavior (Preempt b1 b2) = preempt $ traceBehavior b1
    where
    preempt t = joinChoiceTrace (mapTrace preempt t) $ traceBehavior b2

mapTrace :: (Trace -> Trace) -> Trace -> Trace
mapTrace _ TraceExit = TraceExit
mapTrace f (Trace t) = Trace $ Map.map f t

-- FIXME: joining TraceExit with Trace should remember that Exit was an option
joinChoiceTrace :: Trace -> Trace -> Trace
joinChoiceTrace (Trace t1) (Trace t2) = Trace $ Map.unionWith joinChoiceTrace t1 t2
joinChoiceTrace TraceExit t = t
joinChoiceTrace t TraceExit = t

replaceTraceExit :: Trace -> Trace -> Trace
replaceTraceExit t' TraceExit = t'
replaceTraceExit t' t = mapTrace (replaceTraceExit t') t

synchronizeTrace :: (Gate -> Bool) -> Trace -> Trace -> Trace
synchronizeTrace sync t1 t2 = chooseSync `joinChoiceTrace` insertAsync async1 t2 `joinChoiceTrace` insertAsync async2 t1
    where
    (sync1, async1) = partitionSync sync t1
    (sync2, async2) = partitionSync sync t2
    chooseSync = Trace $ Map.intersectionWith (synchronizeTrace sync) sync1 sync2
    insertAsync from to = Trace $ Map.map (synchronizeTrace sync to) from

-- FIXME: TraceExit should go in the async partition
partitionSync :: (Gate -> Bool) -> Trace -> (Map.Map Gate Trace, Map.Map Gate Trace)
partitionSync _ TraceExit = (Map.empty, Map.empty)
partitionSync sync (Trace t) = Map.partitionWithKey (\k _-> sync k) t
