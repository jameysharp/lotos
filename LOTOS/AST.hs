{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module LOTOS.AST where

import Control.Applicative
import Data.List
import Data.Maybe
import Generics.RepLib
import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops

type Gate = String

type Variable = Name Expression

newtype Expression = Variable Variable
    deriving Eq

$(derive [''Expression])
instance Alpha Expression
instance Subst Expression Expression

instance Show Expression where
    show (Variable name) = name2String name

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
    show (VariableDeclaration name) = '?' : name2String name

data Behavior
    = Stop
    | Action Gate (Bind [GateValue] Behavior)
    | Choice Behavior Behavior
    | Parallel [Gate] Behavior Behavior
    | Interleaving Behavior Behavior
    | Synchronization Behavior Behavior
    | Hide [Gate] Behavior
    | Process String [Gate]
    | Exit [ExitExpression]
    | Sequence Behavior (Bind [Variable] Behavior)
    | Preempt Behavior Behavior

$(derive [''Behavior])
instance Alpha Behavior
instance Subst Expression Behavior

instance Show Behavior where
    show Stop = "stop"
    show (Action g binding) = let (vs, b) = unsafeUnbind binding in unwords (g : map show vs) ++ "; " ++ show b
    show (Choice b1 b2) = "(" ++ show b1 ++ ") [] (" ++ show b2 ++ ")"
    show (Parallel gs b1 b2) = "(" ++ show b1 ++ ") |[" ++ intercalate ", " gs ++ "]| (" ++ show b2 ++ ")"
    show (Interleaving b1 b2) = "(" ++ show b1 ++ ") ||| (" ++ show b2 ++ ")"
    show (Synchronization b1 b2) = "(" ++ show b1 ++ ") || (" ++ show b2 ++ ")"
    show (Hide gs b) = unwords ("hide" : [intercalate ", " gs, "in", "(" ++ show b ++ ")"])
    show (Process name []) = name
    show (Process name gs) = name ++ " " ++ "[" ++ intercalate ", " gs ++ "]"
    show (Exit []) = "exit"
    show (Exit gs) = "exit(" ++ intercalate ", " (map show gs) ++ ")"
    show (Sequence b1 binding) = let (accept, b2) = unsafeUnbind binding in "(" ++ show b1 ++ ") >> " ++
        case accept of
        [] -> "(" ++ show b2 ++ ")"
        _ -> unwords ("accept" : [intercalate ", " $ map name2String accept, "in", "(" ++ show b2 ++ ")"])
    show (Preempt b1 b2) = "(" ++ show b1 ++ ") [> (" ++ show b2 ++ ")"

-- descendBehavior is like gmapM but collects behaviors immediately below bindings too.
descendBehavior :: (Fresh m, Applicative m) => (Behavior -> m Behavior) -> Behavior -> m Behavior
descendBehavior f (Action g binding) = do
    (vs, b) <- unbind binding
    Action g <$> (bind vs <$> f b)
descendBehavior f (Sequence b1 binding) = do
    (names, b2) <- unbind binding
    Sequence <$> f b1 <*> (bind names <$> f b2)
descendBehavior f b = gmapM (mkM f) b

-- subtreesBehavior is like subtrees but collects behaviors immediately below bindings too.
-- XXX: probably ought to unbind safely but I'm only using this in contexts that ignore variable names.
subtreesBehavior :: Behavior -> [Behavior]
subtreesBehavior (Action g binding) = let (_, b) = unsafeUnbind binding in [b]
subtreesBehavior (Sequence b1 binding) = let (_, b2) = unsafeUnbind binding in [b1, b2]
subtreesBehavior b = subtrees b
