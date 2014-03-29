{-# LANGUAGE PatternGuards #-}
module LOTOS.Controllable (uncontrolled) where

import LOTOS.AST

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer
import Data.List
import qualified Data.Map as Map
import Data.Monoid
import Generics.RepLib

uncontrolled :: [Gate] -> Behavior -> Behavior
uncontrolled gates (Interleaving b1 b2)
    | b1 `isActionOn` gates || not (b2 `isActionOn` gates), Just b <- extractInterleavedAction b1 b2 = uncontrolled gates b
    | Just b <- extractInterleavedAction b2 b1 = uncontrolled gates b
uncontrolled gates b = gmapT (mkT $ uncontrolled gates) b

isActionOn :: Behavior -> [Gate] -> Bool
isActionOn (Action g _ _) gates | g `elem` gates = True
isActionOn _ _ = False

extractInterleavedAction :: Behavior -> Behavior -> Maybe Behavior
extractInterleavedAction b1 b2 = do
    Action g v b1' <- return b1
    common <- commonExit $ map (exitOf [name | VariableDeclaration name <- v]) $ exits b1'
    b2' <- if all (ExitAny ==) common then return b2 else do
        (b2', free) <- runWriterT $ unify common b2
        guard $ all Map.null free
        return b2'
    return $ Action g v $ Interleaving b1' b2'
    where
    unify :: [ExitExpression] -> Behavior -> WriterT [Map.Map Variable Expression] Maybe Behavior
    unify common (Exit exprs) = writer (unboundExit, [exitBinding]) where
        unboundExit = Exit [ case l of ExitAny -> r; _ -> ExitAny | (l, r) <- zip common exprs ]
        exitBinding = Map.fromList [ (var, expr) | (ExitExpression expr, ExitExpression (Variable var)) <- zip common exprs ]
    unify common (Action g vs b) = do
        (b', bindings) <- lift $ runWriterT $ unify common b
        vs' <- case bindings of
            [] -> return vs
            [binding] -> do
                let updatingDecl (VariableDeclaration var)
                        | Just expr <- Map.lookup var binding = writer (ValueDeclaration expr, [var])
                    updatingDecl d = return d
                let (vs', shadowed) = runWriter $ mapM updatingDecl vs
                writer (vs', [foldr Map.delete binding shadowed])
        return $ Action g vs' b'
    unify common b = do
        (b', bindings) <- lift $ runWriterT $ gmapM (mkM $ unify common) b
        guard $ null bindings || same bindings
        writer (b', take 1 bindings)

exits :: Behavior -> [[ExitExpression]]
exits b = [exprs | Exit exprs <- listify (const True) b] -- FIXME: exclude Exits from Sequence LHS

exitOf :: [Variable] -> [ExitExpression] -> [ExitExpression]
exitOf names = map restrict
    where
    restrict exit@(ExitExpression expr) | any (`elem` names) [var | Variable var <- listify (const True) expr] = exit
    restrict _ = ExitAny

same :: Eq a => [a] -> Bool
same (x:xs) = all (x ==) xs

commonExit :: [[ExitExpression]] -> Maybe [ExitExpression]
commonExit exprs = if all same $ transpose exprs then Just (head exprs) else Nothing
