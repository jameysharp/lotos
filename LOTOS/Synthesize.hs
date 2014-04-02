{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module LOTOS.Synthesize where

import LOTOS.AST
import LOTOS.Controllable
import LOTOS.Specialize

import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer
import Data.List
import Generics.RepLib
import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops

data Procedure = Procedure (Name Procedure) (Bind [Variable] Statement)

instance Show Procedure where
    show (Procedure name binding) = let (formals, body) = unsafeUnbind binding in "function " ++ show name ++ "(" ++ unwords (map show formals) ++ ") { " ++ show body ++ "}"

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

newtype Program = Program [Procedure]

instance Show Program where
    show (Program procs) = unlines $ map show procs

codegen :: [Gate] -> Process -> Program
codegen blocking = Program . execWriter . runFreshMT . codegenProcess blocking . specializeGates

codegenProcess :: [Gate] -> Process -> FreshMT (Writer [Procedure]) ()
codegenProcess blocking (Process procname (Embed binding)) = do
    ((_, params), binding') <- unbind binding
    (recProcs, b) <- unbind binding'
    mapM_ (codegenProcess blocking) $ unrec recProcs
    stmt <- codegenBehavior (name2String procname) (const Return) blocking $ uncontrolled blocking b
    lift $ tell [Procedure (translate procname) $ bind params stmt]

codegenBehavior :: String -> ([Expression] -> Statement) -> [Gate] -> Behavior -> FreshMT (Writer [Procedure]) Statement
codegenBehavior _ _ _ Stop = return Return
codegenBehavior base onExit blocking (Action g binding) = do
    (vs, b) <- unbind binding
    next <- codegenBehavior base onExit blocking b
    if g `elem` blocking
        then do
            let vars = fv b
            procname <- fresh $ s2n $ base ++ "_cont"
            lift $ tell [Procedure procname $ bind vars next]
            return $ Wait g $ bind vs (map Variable vars, procname)
        else return $ Call g $ bind vs next
codegenBehavior base onExit blocking (Choice b1 b2) = IfThenElse <$> codegenBehavior base onExit blocking b1 <*> codegenBehavior base onExit blocking b2
codegenBehavior base onExit blocking (Interleaving b1 b2) = do
    procname <- fresh $ s2n $ base ++ "_join"
    lift $ tell [Procedure procname $ bind [] $ onExit []] -- FIXME: wait for procname to be called twice and merge the exits
    let onExit' exprs = Continue exprs procname
    Unordered <$> codegenBehavior base onExit' blocking b1 <*> codegenBehavior base onExit' blocking b2
-- FIXME: implement onExit in Instantiate
codegenBehavior _ _ _ (Instantiate procname [] params) = return $ Call (translate procname) $ bind (map (ValueDeclaration . Embed) params) Return
codegenBehavior _ onExit _ (Exit vs) | all (/= ExitAny) vs = return $ onExit [ expr | ExitExpression expr <- vs ]
codegenBehavior base onExit blocking (Sequence b1 binding) = do
    (names, b2) <- unbind binding
    s2 <- codegenBehavior base onExit blocking b2
    procname <- fresh $ s2n $ base ++ "_seq"
    lift $ tell [Procedure procname $ bind names s2]
    codegenBehavior base (\ exprs -> Continue exprs procname) blocking b1
-- FIXME: handle codegen for Preempt behaviors
codegenBehavior _ _ _ b = error $ "LOTOS.Synthesize.codegen: can't synthesize " ++ show b ++ ", did you call simplify first?"
