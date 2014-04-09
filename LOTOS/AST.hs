{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module LOTOS.AST where

import Data.List
import Generics.RepLib
import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops

type Variable = Name Expression

data Expression
    = Variable Variable
    | IntLiteral Int
    deriving Eq

$(derive [''Expression])
instance Alpha Expression

instance Subst Expression Expression where
    isvar (Variable name) = Just $ SubstName name
    isvar _ = Nothing

instance Show Expression where
    show (Variable name) = show name
    show (IntLiteral val) = show val

data ExitExpression = ExitExpression Expression | ExitAny
    deriving Eq

$(derive [''ExitExpression])
instance Alpha ExitExpression
instance Subst Expression ExitExpression

instance Show ExitExpression where
    show ExitAny = "any"
    show (ExitExpression expr) = show expr

data GateValue = ValueDeclaration (Embed Expression) | VariableDeclaration Variable

$(derive [''GateValue])
instance Alpha GateValue
instance Subst Expression GateValue

instance Show GateValue where
    show (ValueDeclaration (Embed expr)) = '!' : show expr
    show (VariableDeclaration name) = '?' : show name

type Gate = Name GateInstance

data GateInstance -- gates have no real representation
$(derive [''GateInstance])

data Behavior
    = Stop
    | Action Gate (Bind [GateValue] Behavior)
    | Choice Behavior Behavior
    | Parallel [Gate] Behavior Behavior
    | Interleaving Behavior Behavior
    | Synchronization Behavior Behavior
    | Hide (Bind [Gate] Behavior)
    | Instantiate (Name Process) [Gate] [Expression]
    | Exit [ExitExpression]
    | Sequence Behavior (Bind [Variable] Behavior)
    | Preempt Behavior Behavior

instance Alpha Behavior
instance Subst Expression Behavior

instance Show Behavior where
    show Stop = "stop"
    show (Action g binding) = let (vs, b) = unsafeUnbind binding in unwords (show g : map show vs) ++ "; " ++ show b
    show (Choice b1 b2) = "(" ++ show b1 ++ ") [] (" ++ show b2 ++ ")"
    show (Parallel gs b1 b2) = "(" ++ show b1 ++ ") |[" ++ intercalate ", " (map show gs) ++ "]| (" ++ show b2 ++ ")"
    show (Interleaving b1 b2) = "(" ++ show b1 ++ ") ||| (" ++ show b2 ++ ")"
    show (Synchronization b1 b2) = "(" ++ show b1 ++ ") || (" ++ show b2 ++ ")"
    show (Hide binding) = let (gs, b) = unsafeUnbind binding in unwords ("hide" : [intercalate ", " (map show gs), "in", "(" ++ show b ++ ")"])
    show (Instantiate name gates params) =
        let gateStr = if null gates then "" else " " ++ "[" ++ intercalate ", " (map show gates) ++ "]"
            paramStr = if null params then "" else " " ++ "(" ++ intercalate ", " (map show params) ++ ")"
        in show name ++ gateStr ++ paramStr
    show (Exit []) = "exit"
    show (Exit gs) = "exit(" ++ intercalate ", " (map show gs) ++ ")"
    show (Sequence b1 binding) = let (accept, b2) = unsafeUnbind binding in "(" ++ show b1 ++ ") >> " ++
        case accept of
        [] -> "(" ++ show b2 ++ ")"
        _ -> unwords ("accept" : [intercalate ", " $ map show accept, "in", "(" ++ show b2 ++ ")"])
    show (Preempt b1 b2) = "(" ++ show b1 ++ ") [> (" ++ show b2 ++ ")"

data Process = Process (Name Process) (Embed (Bind ([Gate], [Variable]) (Bind (Rec [Process]) Behavior)))

$(derive [''Behavior, ''Process])
instance Alpha Process
instance Subst Expression Process

instance Show Process where
    show (Process procname (Embed binding)) =
        let ((gates, params), binding') = unsafeUnbind binding
            (recProcs, b) = unsafeUnbind binding'
            procs = unrec recProcs
            gateStr = if null gates then "" else " [" ++ intercalate ", " (map show gates) ++ "]"
            paramStr = if null params then "" else " (" ++ intercalate ", " (map show params) ++ ")"
            procStr = if null procs then "" else unwords $ " where" : map show procs
        in "process " ++ show procname ++ gateStr ++ paramStr ++ " := " ++ show b ++ procStr ++ " endproc"
