{-# LANGUAGE DeriveDataTypeable #-}
module LOTOS.AST where

import Data.Data
import Data.Generics.Uniplate.Data
import Data.Maybe
import Data.Typeable

type Gate = String

type Variable = String

newtype Expression = Variable Variable
    deriving (Eq, Data, Typeable)

instance Show Expression where
    show (Variable name) = name

data ExitExpression = ExitExpression Expression | ExitAny
    deriving (Eq, Data, Typeable)

instance Show ExitExpression where
    show ExitAny = "any"
    show (ExitExpression expr) = show expr

data GateValue = ValueDeclaration Expression | VariableDeclaration Variable
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
    | Process String [Gate]
    | Exit [ExitExpression]
    | Sequence [Variable] Behavior Behavior
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
    show (Sequence accept b1 b2) = "(" ++ show b1 ++ ") >> " ++
        case accept of
        [] -> "(" ++ show b2 ++ ")"
        _ -> unwords ("accept" : accept ++ ["in", "(" ++ show b2 ++ ")"])
    show (Preempt b1 b2) = "(" ++ show b1 ++ ") |> (" ++ show b2 ++ ")"

rename :: [(Variable, Expression)] -> Behavior -> Behavior
rename [] b = b
-- FIXME: handle name shadowing
rename binding b = transformBi replace b
    where
    replace old@(Variable name) = fromMaybe old $ lookup name binding
