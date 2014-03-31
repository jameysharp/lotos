{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module LOTOS.AST where

import Control.Applicative
import Data.List
import Generics.RepLib
import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops

type Variable = Name Expression

newtype Expression = Variable Variable
    deriving Eq

$(derive [''Expression])
instance Alpha Expression

instance Subst Expression Expression where
    isvar (Variable name) = Just $ SubstName name

instance Show Expression where
    show (Variable name) = show name

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
    | Instantiate String [Gate]
    | Exit [ExitExpression]
    | Sequence Behavior (Bind [Variable] Behavior)
    | Preempt Behavior Behavior

$(derive [''Behavior])
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
    show (Instantiate name []) = name
    show (Instantiate name gs) = name ++ " " ++ "[" ++ intercalate ", " (map show gs) ++ "]"
    show (Exit []) = "exit"
    show (Exit gs) = "exit(" ++ intercalate ", " (map show gs) ++ ")"
    show (Sequence b1 binding) = let (accept, b2) = unsafeUnbind binding in "(" ++ show b1 ++ ") >> " ++
        case accept of
        [] -> "(" ++ show b2 ++ ")"
        _ -> unwords ("accept" : [intercalate ", " $ map show accept, "in", "(" ++ show b2 ++ ")"])
    show (Preempt b1 b2) = "(" ++ show b1 ++ ") [> (" ++ show b2 ++ ")"

-- descendBehavior is like gmapM but collects behaviors immediately below bindings too.
descendBehavior :: (Fresh m, Applicative m) => (Behavior -> m Behavior) -> Behavior -> m Behavior
descendBehavior f (Action g binding) = do
    (vs, b) <- unbind binding
    Action g <$> (bind vs <$> f b)
descendBehavior f (Sequence b1 binding) = do
    (names, b2) <- unbind binding
    Sequence <$> f b1 <*> (bind names <$> f b2)
descendBehavior f (Hide binding) = do
    (gs, b) <- unbind binding
    Hide <$> (bind gs <$> f b)
descendBehavior f b = gmapM (mkM f) b
