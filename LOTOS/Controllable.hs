{-# LANGUAGE PatternGuards #-}
module LOTOS.Controllable (uncontrolled) where

import LOTOS.AST

import Control.Monad
import Data.Generics.Str
import Data.Generics.Uniplate.Data
import Data.List
import qualified Data.Map as Map

uncontrolled :: [Gate] -> Behavior -> Behavior
uncontrolled gates (Interleaving b1 b2)
    | b1 `isActionOn` gates || not (b2 `isActionOn` gates), Just b <- extractInterleavedAction b1 b2 = uncontrolled gates b
    | Just b <- extractInterleavedAction b2 b1 = uncontrolled gates b
uncontrolled gates b = descend (uncontrolled gates) b

isActionOn :: Behavior -> [Gate] -> Bool
isActionOn (Action g _ _) gates | g `elem` gates = True
isActionOn _ _ = False

extractInterleavedAction :: Behavior -> Behavior -> Maybe Behavior
extractInterleavedAction b1 b2 = do
    Action g v b1' <- return b1
    common <- commonExit $ map (exitOf [name | VariableDeclaration name <- v]) $ exits b1'
    b2' <- if all (ExitAny ==) common then return b2 else do
        (b2', free) <- para (unify common) b2
        guard $ Map.null free
        return b2'
    return $ Action g v $ Interleaving b1' b2'
    where
    unify common (Exit exprs) [] = Just (unboundExit, exitBinding) where
        unboundExit = Exit [ case l of ExitAny -> r; _ -> ExitAny | (l, r) <- zip common exprs ]
        exitBinding = Map.fromList [ (var, expr) | (ExitExpression expr, ExitExpression (Variable var)) <- zip common exprs ]
    unify common (Action g vs b) [Just (b', binding)] = Just (unboundAction, actionBinding) where
        unboundAction = Action g (map updatingDecl vs) b'
        updatingDecl (VariableDeclaration var) | Just expr <- Map.lookup var binding = ValueDeclaration expr
        updatingDecl d = d
        actionBinding = foldr Map.delete binding [ name | VariableDeclaration name <- vs ]
    unify common b cs = do
        (bs, bindings) <- liftM unzip $ sequence cs
        guard $ same bindings
        let (old, fromStr) = uniplate b
        let (_, fromList) = strStructure old
        return (fromStr $ fromList bs, head bindings)

exits :: Behavior -> [[ExitExpression]]
exits b = [exprs | Exit exprs <- universe b] -- FIXME: exclude Exits from Sequence LHS

exitOf :: [Name] -> [ExitExpression] -> [ExitExpression]
exitOf names = map restrict
    where
    restrict exit@(ExitExpression expr) | any (`elem` names) [var | Variable var <- universe expr] = exit
    restrict _ = ExitAny

same :: Eq a => [a] -> Bool
same (x:xs) = all (x ==) xs

commonExit :: [[ExitExpression]] -> Maybe [ExitExpression]
commonExit exprs = if all same $ transpose exprs then Just (head exprs) else Nothing
