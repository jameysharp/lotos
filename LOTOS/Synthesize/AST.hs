{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module LOTOS.Synthesize.AST where

import LOTOS.AST

import Data.List
import Generics.RepLib
import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops

data Procedure = Procedure (Name Procedure) (Bind [Variable] Statement)

instance Show Procedure where
    show (Procedure name binding) = let (formals, body) = unsafeUnbind binding in "function " ++ show name ++ "(" ++ intercalate ", " (map show formals) ++ ") { " ++ show body ++ "}"

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
