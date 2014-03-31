{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
module LOTOS.Parser (parseBehavior, parseProcess) where

import LOTOS.AST

import Control.Applicative
import Control.Monad
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Unbound.LocallyNameless hiding (Infix)

lexer :: Stream s m Char => T.GenTokenParser s u m
lexer = T.makeTokenParser $ T.LanguageDef {
    T.commentStart = "(*",
    T.commentEnd = "*)",
    T.commentLine = "",
    T.nestedComments = False,
    T.identStart = letter <|> char '_',
    T.identLetter = alphaNum <|> oneOf "_.",
    T.opStart = mzero,
    T.opLetter = mzero,
    T.reservedNames = ["any", "stop", "hide", "accept", "in", "exit", "where", "process", "endproc"],
    T.reservedOpNames = [],
    T.caseSensitive = True
}

opname :: Stream s m Char => String -> ParsecT s u m String
opname = T.lexeme lexer . try . string

variableName :: Stream s m Char => ParsecT s u m Variable
variableName = s2n <$> T.identifier lexer <?> "variable name"

gateName :: Stream s m Char => ParsecT s u m Gate
gateName = s2n <$> T.identifier lexer <?> "gate name"

processName :: Stream s m Char => ParsecT s u m (Name Process)
processName = s2n <$> T.identifier lexer <?> "process name"

expression :: Stream s m Char => ParsecT s u m Expression
expression =
    Variable <$> variableName
    <|> T.parens lexer expression

gateValue :: Stream s m Char => ParsecT s u m GateValue
gateValue =
    ValueDeclaration <$ char '!' <*> (Embed <$> expression)
    <|>
    VariableDeclaration <$ char '?' <*> variableName
    <?> "gate parameter"

behavior :: Stream s m Char => ParsecT s u m Behavior
behavior =
    Hide <$> (bind <$> between (reserved "hide") (reserved "in") (commaSep1 gateName) <*> behavior)
    <|> buildExpressionParser behaviorOperators term
    where
    behaviorOperators = [
            [binop "[]" Choice AssocLeft],
            [Infix parallelOp AssocLeft, binop "|||" Interleaving AssocLeft, binop "||" Synchronization AssocLeft],
            [binop "[>" Preempt AssocRight], -- XXX: associativity matters for preempt; check spec
            [Infix sequenceOp AssocRight] -- XXX: associativity matters for sequence; check spec
        ]

    T.TokenParser { .. } = lexer
    binop tok op assoc = Infix (op <$ opname tok) assoc

    parallelOp = Parallel <$> between (opname "|[") (opname "]|") (commaSep gateName)

    sequenceOp = do
        _ <- opname ">>"
        names <- option [] (between (reserved "accept") (reserved "in") (commaSep1 variableName))
        return $ \ b1 b2 -> Sequence b1 (bind names b2)

    term =
        parens behavior
        <|> Stop <$ reserved "stop"
        <|> Exit <$ reserved "exit" <*> option [] (parens $ commaSep1 exitExpression)
        -- can't lexically distinguish gateName from processName; try both
        <|> do
            (gate, vs) <- try ((,) <$> gateName <*> many gateValue <* semi)
            b <- term
            return $ Action gate $ bind vs b
        -- need a `try` here to disambiguate between a bracketed gate-list and a following Choice/Preempt operator
        <|> Instantiate <$> processName <*> option [] (try $ brackets $ commaSep1 gateName)

    exitExpression = ExitAny <$ reserved "any" <|> ExitExpression <$> expression

process :: Stream s m Char => ParsecT s u m Process
process = do
    reserved "process"
    procname <- processName
    gates <- option [] (brackets $ commaSep1 gateName)
    params <- option [] (parens $ commaSep1 variableName)
    _ <- opname ":="
    b <- behavior
    procs <- option [] (reserved "where" >> many1 process)
    reserved "endproc"
    return $ Process procname $ Embed $ bind (gates, params) $ bind (rec procs) b
    where
    T.TokenParser { .. } = lexer

parseBehavior :: SourceName -> String -> Either ParseError Behavior
parseBehavior = parse (T.whiteSpace lexer *> behavior <* eof)

parseProcess :: SourceName -> String -> Either ParseError Process
parseProcess = parse (T.whiteSpace lexer *> process <* eof)
