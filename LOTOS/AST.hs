{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module LOTOS.AST where

import Data.List
import Data.Maybe
import Generics.RepLib

type Gate = String

type Variable = String

newtype Expression = Variable Variable
    deriving Eq

$(derive [''Expression])

instance Show Expression where
    show (Variable name) = name

data ExitExpression = ExitExpression Expression | ExitAny
    deriving Eq

$(derive [''ExitExpression])

instance Show ExitExpression where
    show ExitAny = "any"
    show (ExitExpression expr) = show expr

data GateValue = ValueDeclaration Expression | VariableDeclaration Variable

$(derive [''GateValue])

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

$(derive [''Behavior])

instance Show Behavior where
    show Stop = "stop"
    show (Action g vs b) = unwords (g : map show vs) ++ "; " ++ show b
    show (Choice b1 b2) = "(" ++ show b1 ++ ") [] (" ++ show b2 ++ ")"
    show (Parallel gs b1 b2) = "(" ++ show b1 ++ ") |[" ++ intercalate ", " gs ++ "]| (" ++ show b2 ++ ")"
    show (Interleaving b1 b2) = "(" ++ show b1 ++ ") ||| (" ++ show b2 ++ ")"
    show (Synchronization b1 b2) = "(" ++ show b1 ++ ") || (" ++ show b2 ++ ")"
    show (Hide gs b) = unwords ("hide" : [intercalate ", " gs, "in", "(" ++ show b ++ ")"])
    show (Process name []) = name
    show (Process name gs) = name ++ " " ++ "[" ++ intercalate ", " gs ++ "]"
    show (Exit []) = "exit"
    show (Exit gs) = "exit(" ++ intercalate ", " (map show gs) ++ ")"
    show (Sequence accept b1 b2) = "(" ++ show b1 ++ ") >> " ++
        case accept of
        [] -> "(" ++ show b2 ++ ")"
        _ -> unwords ("accept" : [intercalate ", " accept, "in", "(" ++ show b2 ++ ")"])
    show (Preempt b1 b2) = "(" ++ show b1 ++ ") [> (" ++ show b2 ++ ")"

rename :: [(Variable, Expression)] -> Behavior -> Behavior
rename [] b = b
-- FIXME: handle name shadowing
rename binding b = everywhere (mkT replace) b
    where
    replace old@(Variable name) = fromMaybe old $ lookup name binding
