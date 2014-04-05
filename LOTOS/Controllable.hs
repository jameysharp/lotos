{-# LANGUAGE PatternGuards #-}
module LOTOS.Controllable (uncontrolled) where

import LOTOS.AST
import LOTOS.AST.Util
import LOTOS.Simplify

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Writer
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import Generics.RepLib
import Unbound.LocallyNameless

uncontrolled :: [Gate] -> Behavior -> Behavior
uncontrolled gates b = fromMaybe b $ runFreshM $ runMaybeT $ uncontrolled' gates b

uncontrolled' :: [Gate] -> Behavior -> MaybeT FreshM Behavior
uncontrolled' gates b = MaybeT $ do
    b' <- runMaybeT $ case b of
        -- If the right side starts with an uncontrolled gate, use that first.
        Interleaving b2 (Action g binding) | g `elem` gates -> extractInterleavedAction g binding b2
        Interleaving (Action g binding) b2 -> extractInterleavedAction g binding b2
        Interleaving b2 (Action g binding) -> extractInterleavedAction g binding b2
        _ -> mzero
    b'' <- runMaybeT $ (lift . simplifyOnce) =<< descendBehavior (uncontrolled' gates) (fromMaybe b b')
    return $ b'' `mplus` b'

extractInterleavedAction :: Gate -> Bind [GateValue] Behavior -> Behavior -> MaybeT FreshM Behavior
extractInterleavedAction g binding b2 = do
    (v, b1') <- unbind binding
    common <- commonExit $ map (exitOf [name | VariableDeclaration name <- v]) $ exits b1'
    -- Only extract if it might unify with b2's exits.
    if all (ExitAny ==) common then mzero else do
    (b2', free) <- runWriterT $ unify common b2
    guard $ all Map.null free
    next <- lift $ interleavingB b1' b2'
    return $ Action g $ bind v next

unify :: [ExitExpression] -> Behavior -> WriterT [Map.Map Variable Expression] (MaybeT FreshM) Behavior
unify common (Exit exprs) = writer (unboundExit, [exitBinding]) where
    unboundExit = Exit [ case l of ExitAny -> r; _ -> ExitAny | (l, r) <- zip common exprs ]
    exitBinding = Map.fromList [ (var, expr) | (ExitExpression expr, ExitExpression (Variable var)) <- zip common exprs ]
unify common (Action g binding) = do
    (vs, b) <- unbind binding
    (b', bindings) <- lift $ runWriterT $ unify common b
    vs' <- case bindings of
        [] -> return vs
        [binding] -> do
            let updatingDecl (VariableDeclaration var)
                    | Just expr <- Map.lookup var binding = writer (ValueDeclaration $ Embed expr, [var])
                updatingDecl d = return d
            let (vs', shadowed) = runWriter $ mapM updatingDecl vs
            writer (vs', [foldr Map.delete binding shadowed])
        _ -> error "LOTOS.Controllable internal error: too many bindings from Action"
    return $ Action g $ bind vs' b'
unify common b = do
    (b', bindings) <- lift $ runWriterT $ descendBehavior (unify common) b
    guard $ same bindings
    writer (b', take 1 bindings)

exits :: Behavior -> [[ExitExpression]]
exits b = [exprs | Exit exprs <- listify (const True) b] -- FIXME: exclude Exits from Sequence LHS

exitOf :: [Variable] -> [ExitExpression] -> [ExitExpression]
exitOf names = map restrict
    where
    restrict exit@(ExitExpression expr) | any (`elem` names) [var | Variable var <- listify (const True) expr] = exit
    restrict _ = ExitAny

same :: Eq a => [a] -> Bool
same [] = True
same (x:xs) = all (x ==) xs

commonExit :: (Monad m, MonadPlus m) => [[ExitExpression]] -> m [ExitExpression]
commonExit exprs = do
    guard $ all same $ transpose exprs
    return $ head exprs
