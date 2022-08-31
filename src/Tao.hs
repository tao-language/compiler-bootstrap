module Tao where

import Core
import Parser

newtype Error
  = SyntaxError ParserError
  deriving (Eq, Show)

parse :: String -> Either Error Term
parse src = do
  let typeAlternative :: Parser (Constructor, Int)
      typeAlternative = do
        name <- token constructorName
        arity <- token integer
        succeed (name, arity)

  let typeDefinition :: Parser (Context -> Context)
      typeDefinition = do
        name <- token typeName
        let args = [] -- TODO
        alts <- oneOrMore (token typeAlternative)
        succeed (defineType name args alts)

  let context :: Parser Context
      context = do
        defs <- zeroOrMore typeDefinition
        succeed (foldr id empty defs)

  let term :: Parser Term
      term = do
        ctx <- context
        expr <- expression ""
        succeed (expr ctx)

  case Parser.parse src term of
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
        fmap bind variableName,
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

blankLine :: Parser ()
blankLine = do
  _ <- zeroOrMore space
  _ <- char '\n'
  succeed ()

indentation :: String -> Parser ()
indentation indent = do
  _ <- zeroOrMore blankLine
  oneOf
    [ do _ <- text indent; succeed (),
      do _ <- zeroOrMore space; endOfFile
    ]

continuation :: String -> Parser String
continuation indent = do
  let continue :: Parser String
      continue = do
        _ <- endOfLine
        _ <- indentation indent
        suffix <- oneOrMore space
        succeed (indent ++ suffix)

  oneOf [continue, succeed indent]

lineBreak :: String -> Parser ()
lineBreak indent =
  oneOf
    [ do _ <- token (char ';'); succeed (),
      do _ <- endOfLine; indentation indent
    ]

definition :: String -> Parser (Pattern, Expr)
definition indent = do
  p <- token pattern
  _ <- token (char '=')
  indent <- continuation indent
  expr <- expression indent
  _ <- lineBreak indent
  succeed (p, expr)

case' :: String -> Char -> Parser Case
case' indent delimiter = do
  _ <- token (char delimiter)
  ps <- oneOrMore (token pattern)
  _ <- token (text "->")
  indent <- continuation indent
  expr <- expression indent
  succeed (ps, expr)

expression :: String -> Parser Expr
expression indent = do
  let definitions :: Parser [(Pattern, Expr)]
      definitions = do
        def <- definition indent
        defs <- zeroOrMore (definition indent)
        succeed (def : defs)

  -- let cases :: Parser [Case]
  --     cases = do
  --       c <- token (case' '\\')
  --       cs <- zeroOrMore (token (case' '|'))
  --       succeed (c : cs)

  withOperators
    [ prefix let' definitions,
      atom var variableName,
      atom int integer,
      atom (const . Call) operator,
      atom (match "") (exactly 1 (case' indent '\\')),
      -- atom (match "") cases,
      prefix (const id) comment,
      inbetween (const id) (char '(') (char ')'),
      atom (const err) (text "#error")
    ]
    [ infixL 1 (const eq) (text "=="),
      infixL 2 (const add) (char '+'),
      infixL 2 (const sub) (char '-'),
      infixL 3 (const mul) (char '*'),
      infixL 4 (\_ a b -> app a [b]) (succeed ())
    ]
