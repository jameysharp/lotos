{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module LOTOS.AST where

import Data.List
import Generics.RepLib
import Unbound.LocallyNameless hiding (empty)
import Unbound.LocallyNameless.Ops
import Text.PrettyPrint

type Variable = Name Expression

data Expression
    = Variable Variable
    | IntLiteral Int
    deriving Eq

$(derive [''Expression])
instance Alpha Expression

instance Subst Expression Expression where
    isvar (Variable name) = Just $ SubstName name
    isvar _ = Nothing

instance Show Expression where
    show (Variable name) = show name
    show (IntLiteral val) = show val

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
    | Instantiate (Name Process) [Gate] [Expression]
    | Exit [ExitExpression]
    | Sequence Behavior (Bind [Variable] Behavior)
    | Preempt Behavior Behavior

instance Alpha Behavior
instance Subst Expression Behavior

data Process = Process (Name Process) (Embed (Bind ([Gate], [Variable]) (Bind (Rec [Process]) Behavior)))

$(derive [''Behavior, ''Process])
instance Alpha Process
instance Subst Expression Process

prettyBehavior :: Behavior -> Doc
prettyBehavior Stop = text "stop"
prettyBehavior b@(Action{}) = sep $ go b
    where
    go (Action g binding) = let (vs, b) = unsafeUnbind binding in (hsep (text (show g) : map (text . show) vs) <> semi) : go b
    go b = [prettyBehavior b]
prettyBehavior (Choice b1 b2) = parens $ nest 4 $ sep $ intersperse (text "[]") $ map prettyBehavior $ go $ Choice b1 b2
    where
    go (Choice b1 b2) = go b1 ++ go b2
    go b = [b]
prettyBehavior (Parallel gs b1 b2) = parens $ nest 4 $ sep [prettyBehavior b1, op, prettyBehavior b2]
    where op = text "|[" <> sep (punctuate (text ",") (map (text . show) gs)) <> text "]|"
prettyBehavior (Interleaving b1 b2) = parens $ nest 4 $ sep [prettyBehavior b1, text "|||", prettyBehavior b2]
prettyBehavior (Synchronization b1 b2) = parens $ nest 4 $ sep [prettyBehavior b1, text "||", prettyBehavior b2]
prettyBehavior (Hide binding) = hang op 4 $ prettyBehavior b
    where
    (gs, b) = unsafeUnbind binding
    op = text "hide" <+> sep (punctuate (text ",") (map (text . show) gs)) <+> text "in"
prettyBehavior (Instantiate name gates params) = text (show name) <+> gatesDoc <+> paramsDoc
    where
    gatesDoc = if null gates then empty else brackets (sep $ punctuate (text ",") (map (text . show) gates))
    paramsDoc = if null params then empty else parens (sep $ punctuate (text ",") (map (text . show) params))
prettyBehavior (Exit vs) = text "exit" <> if null vs then empty else parens (sep $ punctuate (text ",") (map (text . show) vs))
prettyBehavior (Sequence b1 binding) = let (names, b2) = unsafeUnbind binding in parens $ nest 4 $ sep [prettyBehavior b1, text ">>" <+> op names, prettyBehavior b2]
    where
    op [] = empty
    op names = text "accept" <+> sep (punctuate (text ",") (map (text . show) names)) <+> text "in"
prettyBehavior (Preempt b1 b2) = parens $ nest 4 $ sep [prettyBehavior b1, text "[>", prettyBehavior b2]

instance Show Behavior where
    show = show . prettyBehavior

prettyProcess :: Process -> Doc
prettyProcess (Process procname (Embed binding)) =
    let ((gates, params), binding') = unsafeUnbind binding
        (recProcs, b) = unsafeUnbind binding'
        procs = unrec recProcs
        gatesDoc = if null gates then empty else brackets $ sep $ punctuate (text ",") (map (text . show) gates)
        paramsDoc = if null params then empty else parens $ sep $ punctuate (text ",") (map (text . show) params)
        procDocs = if null procs then [] else text "where" : map (nest 4 . prettyProcess) procs
    in sep $ [text "process" <+> text (show procname) <+> gatesDoc <+> paramsDoc <+> text ":=", nest 4 $ prettyBehavior b] ++ procDocs ++ [text "endproc"]

instance Show Process where
    show = show . prettyProcess
