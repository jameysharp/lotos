{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
module LOTOS.Parser (parseBehavior) where

import LOTOS.AST

import Control.Applicative
import Control.Monad
import Text.Parsec hiding ((<|>), many)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T

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
    T.reservedNames = ["any", "stop", "hide", "accept", "in", "exit"],
    T.reservedOpNames = [],
    T.caseSensitive = True
}

variableName :: Stream s m Char => ParsecT s u m Variable
variableName = T.identifier lexer <?> "variable name"

gateName :: Stream s m Char => ParsecT s u m Gate
gateName = T.identifier lexer <?> "gate name"

processName :: Stream s m Char => ParsecT s u m String
processName = T.identifier lexer <?> "process name"

expression :: Stream s m Char => ParsecT s u m Expression
expression =
    Variable <$> variableName
    <|> T.parens lexer expression

gateValue :: Stream s m Char => ParsecT s u m GateValue
gateValue =
    ValueDeclaration <$ char '!' <*> expression
    <|>
    VariableDeclaration <$ char '?' <*> variableName
    <?> "gate parameter"

behavior :: Stream s m Char => ParsecT s u m Behavior
behavior =
    Hide <$> between (reserved "hide") (reserved "in") (commaSep1 gateName) <*> behavior
    <|> buildExpressionParser behaviorOperators term
    where
    behaviorOperators = [
            [binop "[]" Choice AssocLeft],
            [Infix parallelOp AssocLeft, binop "|||" Interleaving AssocLeft, binop "||" Synchronization AssocLeft],
            [binop "[>" Preempt AssocRight], -- XXX: associativity matters for preempt; check spec
            [Infix sequenceOp AssocRight] -- XXX: associativity matters for sequence; check spec
        ]

    T.TokenParser { .. } = lexer
    opname = lexeme . try . string
    binop tok op assoc = Infix (op <$ opname tok) assoc

    parallelOp = Parallel <$> between (opname "|[") (opname "]|") (commaSep gateName)

    sequenceOp = Sequence <$ opname ">>" <*> option [] (between (reserved "accept") (reserved "in") (commaSep1 variableName))

    term =
        parens behavior
        <|> Stop <$ reserved "stop"
        <|> Exit <$ reserved "exit" <*> option [] (parens $ commaSep1 exitExpression)
        -- can't lexically distinguish gateName from processName; try both
        <|> try (Action <$> gateName <*> many gateValue <* semi) <*> term
        -- need a `try` here to disambiguate between a bracketed gate-list and a following Choice/Preempt operator
        <|> Process <$> processName <*> option [] (try $ brackets $ commaSep1 gateName)

    exitExpression = ExitAny <$ reserved "any" <|> ExitExpression <$> expression

parseBehavior :: SourceName -> String -> Either ParseError Behavior
parseBehavior = parse (T.whiteSpace lexer *> behavior <* eof)
