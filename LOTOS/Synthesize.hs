{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module LOTOS.Synthesize where

import LOTOS.AST
import LOTOS.Controllable

import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer
import Data.List
import Generics.RepLib
import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops

newtype Procedure = Procedure (Bind [Variable] Statement)

instance Show Procedure where
    show (Procedure binding) = let (formals, body) = unsafeUnbind binding in "(" ++ unwords (map show formals) ++ ") { " ++ show body ++ "}"

data Statement
    = Call Gate (Bind [GateValue] Statement)
    | Wait Gate (Bind [GateValue] ([Expression], Name Procedure))
    | Continue [Expression] (Name Procedure)
    | IfThenElse Statement Statement
    | Unordered Statement Statement
    | Return

instance Show Statement where
    show (Call g binding) =
        let (vs, b) = unsafeUnbind binding
            inparams = [ expr | ValueDeclaration (Embed expr) <- vs ]
            outparams = [ var | VariableDeclaration var <- vs ]
            assignment = if null outparams then "" else "var " ++ intercalate ", " (map show outparams) ++ " = "
        in assignment ++ show g ++ "(" ++ intercalate ", " (map show inparams) ++ "); " ++ show b
    show (Wait g binding) =
        let (vs, (closed, procname)) = unsafeUnbind binding
            inparams = [ expr | ValueDeclaration (Embed expr) <- vs ]
            outparams = [ var | VariableDeclaration var <- vs ]
            continuation = if closed == map Variable outparams
                then show procname
                else "function(" ++ intercalate ", " (map show outparams) ++ ") { " ++ show procname ++ "(" ++ intercalate ", " (map show closed) ++ "); }"
        in show g ++ "(" ++ intercalate ", " (map show inparams ++ [continuation]) ++ "); "
    show (Continue actuals procname) = show procname ++ "(" ++ intercalate ", " (map show actuals) ++ "); "
    show (IfThenElse s1 s2) = "if(???) { " ++ show s1 ++ "} else { " ++ show s2 ++ "} "
    show (Unordered s1 s2) = show s1 ++ show s2
    show Return = ""

$(derive [''Statement, ''Procedure])
instance Alpha Statement
instance Alpha Procedure

newtype Program = Program (Statement, [(Name Procedure, Procedure)])

instance Show Program where
    show (Program (initial, procs)) = unlines $ [ "function " ++ show procname ++ show body | (procname, body) <- procs ] ++ [show initial]

codegen :: [Gate] -> Behavior -> Program
codegen blocking b = Program $ runWriter $ runFreshMT $ codegen' (const Return) blocking $ uncontrolled blocking b

codegen' :: ([Expression] -> Statement) -> [Gate] -> Behavior -> FreshMT (Writer [(Name Procedure, Procedure)]) Statement
codegen' _ _ Stop = return Return
codegen' onExit blocking (Action g binding) = do
    (vs, b) <- unbind binding
    next <- codegen' onExit blocking b
    if g `elem` blocking
        then do
            let vars = fv b
            procname <- fresh $ s2n "ready"
            lift $ tell [(procname, Procedure $ bind vars next)]
            return $ Wait g $ bind vs (map Variable vars, procname)
        else return $ Call g $ bind vs next
codegen' onExit blocking (Choice b1 b2) = IfThenElse <$> codegen' onExit blocking b1 <*> codegen' onExit blocking b2
codegen' onExit blocking (Interleaving b1 b2) = do
    procname <- fresh $ s2n "rendezvous"
    lift $ tell [(procname, Procedure $ bind [] $ onExit [])] -- FIXME: wait for procname to be called twice and merge the exits
    let onExit' exprs = Continue exprs procname
    Unordered <$> codegen' onExit' blocking b1 <*> codegen' onExit' blocking b2
-- FIXME: handle codegen for Instantiate behaviors
codegen' onExit _ (Exit vs) | all (/= ExitAny) vs = return $ onExit [ expr | ExitExpression expr <- vs ]
codegen' onExit blocking (Sequence b1 binding) = do
    (names, b2) <- unbind binding
    s2 <- codegen' onExit blocking b2
    procname <- fresh $ s2n "sequence"
    lift $ tell [(procname, Procedure $ bind names s2)]
    codegen' (\ exprs -> Continue exprs procname) blocking b1
-- FIXME: handle codegen for Preempt behaviors
codegen' _ _ b = error $ "LOTOS.Synthesize.codegen: can't synthesize " ++ show b ++ ", did you call simplify first?"
