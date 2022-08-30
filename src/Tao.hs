module Tao where

import Core
import Parser

newtype Error
  = SyntaxError ParserError
  deriving (Eq, Show)

fromText :: String -> Either Error Term
fromText src = case parse src term of
  Left err -> Left (SyntaxError err)
  Right term -> Right term

variableName :: Parser Variable
variableName = do
  -- TODO: support `-` and other characters, maybe URL-like names
  c <- lowercase
  cs <- zeroOrMore (oneOf [alphanumeric, char '_'])
  succeed (c : cs)

constructorName :: Parser Constructor
constructorName = do
  -- TODO: support `-` and other characters, maybe URL-like names, or keep types CamelCase?
  c <- uppercase
  cs <- zeroOrMore (oneOf [alphanumeric, char '_'])
  succeed (c : cs)

typeName :: Parser String
typeName = constructorName

operator :: Parser String
operator = do
  let ops = ["==", "+", "-", "*"]
  _ <- token (char '(')
  op <- token (oneOf (map text ops))
  _ <- token (char ')')
  succeed op

comment :: Parser String
comment = do
  _ <- text "--"
  _ <- zeroOrOne space
  until' (== '\n') anyChar

pattern :: Parser Pattern
pattern = do
  p <-
    oneOf
      [ fmap (const PAny) (token (char '_')),
        fmap (PAs PAny) variableName,
        fmap PInt (token integer),
        do
          ctr <- token constructorName
          ps <- zeroOrMore pattern
          succeed (PCtr ctr ps),
        do
          _ <- token (char '(')
          p <- token pattern
          _ <- token (char ')')
          succeed p
      ]
  oneOf
    [ do _ <- token (char '@'); x <- token variableName; succeed (PAs p x),
      succeed p
    ]

-- def :: Parser (Pattern, Expr)
-- def = do
--   p <- token pattern
--   _ <- token (char '=')
--   expr <- token expression
--   _ <- token (char ';')
--   succeed (p, expr)

definition :: Parser (Variable, Expr)
definition = do
  _ <- token (char '@')
  name <- token variableName
  _ <- token (char '=')
  expr <- token expression
  _ <- token (char ';')
  -- TODO: support newlines and indentation aware parsing
  -- expr <- expression
  -- _ <- zeroOrMore (oneOf [char ' ', char '\t'])
  -- _ <- oneOf [char '\n', char ';']
  succeed (name, expr)

case' :: Char -> Parser Case
case' delimiter = do
  _ <- token (char delimiter)
  ps <- oneOrMore (token pattern)
  _ <- token (text "->")
  expr <- expression
  succeed (ps, expr)

expression :: Parser Expr
expression = do
  let cases :: Parser [Case]
      cases = do
        c <- token (case' '\\')
        cs <- zeroOrMore (token (case' '|'))
        succeed (c : cs)

  withOperators
    [ atom (const err) (char '_'),
      atom var variableName,
      atom int integer,
      atom (const . Call) operator,
      atom (match "") cases,
      prefix with (oneOrMore definition),
      prefix (const id) comment,
      inbetween (const id) (char '(') (char ')')
    ]
    [ infixL 1 (const eq) (text "=="),
      infixL 2 (const add) (char '+'),
      infixL 2 (const sub) (char '-'),
      infixL 3 (const mul) (char '*'),
      infixL 4 (\_ a b -> app a [b]) (succeed ())
    ]

typeAlternative :: Parser (Constructor, Int)
typeAlternative = do
  name <- token constructorName
  arity <- token integer
  succeed (name, arity)

typeDefinition :: Parser (Context -> Context)
typeDefinition = do
  name <- token typeName
  let args = [] -- TODO
  alts <- oneOrMore (token typeAlternative)
  succeed (defineType name args alts)

context :: Parser Context
context = do
  defs <- zeroOrMore typeDefinition
  succeed (foldr id empty defs)

term :: Parser Term
term = do
  ctx <- context
  expr <- expression
  succeed (expr ctx)
