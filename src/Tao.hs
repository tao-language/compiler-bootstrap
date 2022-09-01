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

comment :: String -> Parser String
comment indent = do
  _ <- text "--"
  _ <- zeroOrOne space
  text <- until' (== '\n') anyChar
  -- text <- zeroOrMore (charIf (/= '\n') "")
  _ <- endOfLine
  _ <- indentation indent
  succeed text

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

lineBreak :: Char -> String -> Parser ()
lineBreak delimiter indent =
  oneOf
    [ do _ <- token (char delimiter); succeed (),
      do _ <- endOfLine; indentation indent
    ]

definition :: String -> Parser (Pattern, Expr)
definition indent = do
  p <- token pattern
  _ <- token (char '=')
  indent <- continuation indent
  expr <- expression indent
  _ <- lineBreak ';' indent
  succeed (p, expr)

case' :: String -> Parser Case
case' indent = do
  ps <- oneOrMore (token pattern)
  _ <- token (text "->")
  indent' <- continuation indent
  expr <- expression indent'
  _ <- lineBreak '|' indent
  succeed (ps, expr)

expression :: String -> Parser Expr
expression indent = do
  let definitions :: Parser [(Pattern, Expr)]
      definitions = do
        def <- definition indent
        defs <- zeroOrMore (definition indent)
        succeed (def : defs)

  let cases :: Parser [Case]
      cases = do
        c <- case' indent
        cs <- zeroOrMore (case' indent)
        succeed (c : cs)

  -- TODO: make prefix and infix operators into functions instead of lists
  -- TODO: make operators support indentations
  -- TODO: make parentheses support indentations
  withOperators
    [ atom (const err) (text "#error"),
      prefix let' definitions,
      atom (match "") cases,
      atom var (token variableName),
      atom int (token integer),
      atom (const . Call) (token operator),
      prefix (const id) (comment indent),
      inbetween (const id) (token (char '(')) (token (char ')'))
    ]
    [ infixL 1 (const eq) (token (text "==")),
      infixL 2 (const add) (token (char '+')),
      infixL 2 (const sub) (token (char '-')),
      infixL 3 (const mul) (token (char '*')),
      infixL 4 (\_ a b -> app a [b]) (succeed ())
    ]
