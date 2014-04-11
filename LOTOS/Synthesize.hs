module LOTOS.Synthesize (codegen) where

import LOTOS.AST
import LOTOS.Controllable
import LOTOS.Specialize

import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer
import Data.List
import qualified Data.Set as Set
import Language.C hiding (Name)
import Unbound.LocallyNameless

codegen :: [Gate] -> Process -> CTranslUnit
codegen blocking = flip CTranslUnit undefNode . execWriter . runFreshMT . codegenProcess blocking . specializeGates

codegenProcess :: [Gate] -> Process -> FreshMT (Writer [CExtDecl]) ()
codegenProcess blocking (Process procname (Embed binding)) = do
    ((_, params), binding') <- unbind binding
    (recProcs, b) <- unbind binding'
    mapM_ (codegenProcess blocking) $ unrec recProcs
    stmt <- codegenBehavior (name2String procname) (const cReturn) blocking $ uncontrolled blocking b
    lift $ tell [cProcedure (translate procname) params stmt]

codegenBehavior :: String -> ([Expression] -> CStat) -> [Gate] -> Behavior -> FreshMT (Writer [CExtDecl]) CStat
codegenBehavior _ _ _ Stop = return cReturn
codegenBehavior base onExit blocking (Action g binding) = do
    (vs, b) <- unbind binding
    next <- codegenBehavior base onExit blocking b
    if g `elem` blocking
        then do
            let inparams = [ codegenExpression expr | ValueDeclaration (Embed expr) <- vs ]
            let outparams = [ var | VariableDeclaration var <- vs ]
            let vars = Set.toList $ fv b
            let closureparams = vars \\ outparams
            -- FIXME: generate a closure structure and allocate/free as needed.
            let closure = case closureparams of [var] -> var; _ -> s2n "closure"
            procname <- fresh $ s2n $ base ++ "_cont"
            lift $ tell [cProcedure procname (outparams ++ [closure]) next]
            return $ cCall g $ inparams ++ [cVar procname, if null closureparams then codegenExpression (IntLiteral 0) else cVar closure]
        else do
            let outdecls = [ cDecl (CVoidType undefNode) [CPtrDeclr [] undefNode] var | VariableDeclaration var <- vs ]
            let paramexpr (ValueDeclaration (Embed expr)) = codegenExpression expr
                paramexpr (VariableDeclaration var) = CUnary CAdrOp (cVar var) undefNode
            return $ cBlock $ map CBlockDecl outdecls ++ [CBlockStmt $ cCall g $ map paramexpr vs, CBlockStmt next]
codegenBehavior base onExit blocking (Choice b1 b2) = do
    s1 <- codegenBehavior base onExit blocking b1
    s2 <- codegenBehavior base onExit blocking b2
    -- FIXME: generate correct If condition expressions
    return $ CIf (codegenExpression $ IntLiteral $ -1) s1 (Just s2) undefNode
codegenBehavior base onExit blocking (Interleaving b1 b2) = do
    procname <- fresh $ s2n $ base ++ "_join"
    lift $ tell [cProcedure procname [] $ onExit []] -- FIXME: wait for procname to be called twice and merge the exits
    let onExit' exprs = cCall procname $ map codegenExpression exprs
    s1 <- codegenBehavior base onExit' blocking b1
    s2 <- codegenBehavior base onExit' blocking b2
    return $ cBlock [CBlockStmt s1, CBlockStmt s2]
-- FIXME: implement onExit in Instantiate
codegenBehavior _ _ _ (Instantiate procname [] params) = return $ cCall procname $ map codegenExpression params
codegenBehavior _ onExit _ (Exit vs) | all (/= ExitAny) vs = return $ onExit [ expr | ExitExpression expr <- vs ]
codegenBehavior base onExit blocking (Sequence b1 binding) = do
    (names, b2) <- unbind binding
    s2 <- codegenBehavior base onExit blocking b2
    procname <- fresh $ s2n $ base ++ "_seq"
    lift $ tell [cProcedure procname names s2]
    codegenBehavior base (\ exprs -> cCall procname $ map codegenExpression exprs) blocking b1
-- FIXME: handle codegen for Preempt behaviors
codegenBehavior _ _ _ b = error $ "LOTOS.Synthesize.codegen: can't synthesize " ++ show b ++ ", did you call simplify first?"

cBlock :: [CBlockItem] -> CStat
cBlock stmts = CCompound [] (concat [ case stmt of CBlockStmt (CCompound _ stmts' _) -> stmts'; _ -> [stmt] | stmt <- stmts ]) undefNode

cReturn :: CStat
cReturn = CReturn Nothing undefNode

cVar :: Name a -> CExpr
cVar nm = CVar (internalIdent $ show nm) undefNode

cCall :: Name a -> [CExpr] -> CStat
cCall nm actuals = CExpr (Just $ CCall (cVar nm) actuals undefNode) undefNode

cDecl :: CTypeSpec -> [CDerivedDeclr] -> Name a -> CDecl
cDecl ty derived nm = CDecl [CTypeSpec ty] [(Just $ CDeclr (Just $ internalIdent $ show nm) derived Nothing [] undefNode, Nothing, Nothing)] undefNode

cProcedure :: Variable -> [Variable] -> CStat -> CExtDecl
cProcedure nm formals body = CFDefExt $ CFunDef static_void declr [] (cBlock [CBlockStmt body]) undefNode
    where
    static_void = [CStorageSpec $ CStatic undefNode, CTypeSpec $ CVoidType undefNode]
    formalDecls = [ cDecl (CVoidType undefNode) [CPtrDeclr [] undefNode] formal | formal <- formals ]
    declr = CDeclr (Just $ internalIdent $ show nm) [CFunDeclr (Right (formalDecls, False)) [] undefNode] Nothing [] undefNode

codegenExpression :: Expression -> CExpr
codegenExpression (Variable name) = cVar name
codegenExpression (IntLiteral n) = CConst $ CIntConst (cInteger $ fromIntegral n) undefNode
