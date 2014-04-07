module Main (main) where

import LOTOS.AST
import LOTOS.Parser
import LOTOS.Simplify
import LOTOS.Synthesize
import LOTOS.TypeCheck

import Control.Monad
import Data.List
import qualified Data.Map as Map
import System.Environment
import Unbound.LocallyNameless hiding (union)
import Unbound.LocallyNameless.Ops

main :: IO ()
main = do
    args <- getArgs
    let (files, uncontrolled_gates) = case break ("--" ==) args of
            (files, []) -> (files, [])
            (uncontrolled_gates, _ : files) -> (files, uncontrolled_gates)

    when (null files) $ do
        progname <- getProgName
        fail $ "usage: " ++ progname ++ " [gates... --] filename.lotos..."

    specs <- forM files $ \ filename -> do
        contents <- readFile filename
        case parseProcess filename contents of
            Left err -> fail $ show err
            Right p -> return p

    let (bs, gatelist, paramlist) = unzip3
            [ (Instantiate name gates $ map Variable params, gates, params)
            | Process name (Embed binding) <- specs
            -- Use unsafeUnbind so we can cheat by having formal gate params mean the same thing in different ASTs.
            , let ((gates, params), _) = unsafeUnbind binding ]
    let formalGates = foldr1 union gatelist
    let b = Hide $ bind formalGates $ foldr1 (Parallel formalGates) bs
    let merged = Process (s2n "merged") $ Embed $ bind ([], foldr1 union paramlist) $ bind (rec specs) b

    putStrLn "Merged specification:"
    print merged
    putStrLn ""

    let showProcessFunctionality (proc, func) = show proc ++ " : " ++ show func

    putStrLn "Inferred process functionality:"
    case inferFunctionality merged of
        Left err -> fail err
        Right fs -> mapM_ (putStrLn . showProcessFunctionality) $ Map.toList fs
    putStrLn ""

    let simplified = simplifyProcess merged

    putStrLn "After simplification:"
    print simplified
    putStrLn ""

    putStrLn "Simplified process functionality:"
    case inferFunctionality simplified of
        Left err -> fail $ "simplification broke functionality inference: " ++ err
        Right fs -> mapM_ (putStrLn . showProcessFunctionality) $ Map.toList fs
    putStrLn ""

    putStrLn "Imperative equivalent:"
    print $ codegen (map s2n uncontrolled_gates) simplified
