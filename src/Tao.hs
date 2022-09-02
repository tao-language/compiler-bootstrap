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

comment :: Parser String
comment = do
  -- TODO: support multi-line comments
  _ <- text "--"
  _ <- maybe' space
  until' (== '\n') anyChar

emptyLine :: Parser String
emptyLine = do
  _ <- zeroOrMore space
  comment' <- oneOf [comment, succeed ""]
  _ <- char '\n'
  succeed comment'

newLine :: String -> Parser [String]
newLine indent = do
  _ <- char '\n'
  comments <- zeroOrMore emptyLine
  _ <- text indent
  succeed comments

continueLine :: String -> Parser String
continueLine indent =
  do
    _ <- newLine indent
    extra <- oneOrMore space
    succeed (indent ++ extra)
    |> orElse (succeed indent)

token :: Parser a -> Parser a
token parser = do
  x <- parser
  _ <- zeroOrMore space
  succeed x

delimiter :: String -> Parser a -> Parser [String]
delimiter indent parser =
  oneOf
    [ do _ <- token parser; succeed [],
      newLine indent
    ]

expression :: String -> Parser Expr
expression indent = do
  let define :: Parser Expr
      define = do
        defs <- definitions indent
        _ <- delimiter indent (char ';')
        expr <- expression indent
        succeed (let' defs expr)

  -- TODO: make prefix and infix operators into functions instead of lists
  -- TODO: make operators support newLines
  -- TODO: make parentheses support newLines
  withOperators
    [ atom (const err) (text "#error"), -- TODO: keyword
      atom (match "") (cases indent),
      atom id define,
      atom var (token variableName),
      atom int (token integer),
      atom (const . Call) (token (operator indent)),
      inbetween (const id) (token (char '(')) (token (char ')'))
    ]
    [ infixL 1 (const eq) (token (text "==")),
      infixL 2 (const add) (token (char '+')),
      infixL 2 (const sub) (token (char '-')),
      infixL 3 (const mul) (token (char '*')),
      infixL 4 (\_ a b -> app a [b]) (succeed ())
    ]

operator :: String -> Parser String
operator indent = do
  let ops = ["==", "+", "-", "*"]
  _ <- token (char '(')
  _ <- continueLine indent
  op <- token (oneOf (map text ops))
  _ <- maybe' (newLine indent)
  _ <- token (char ')')
  succeed op

pattern :: Parser Pattern
pattern = do
  p <-
    oneOf
      [ fmap (const PAny) (token (char '_')),
        fmap bind (token variableName),
        fmap PInt (token integer),
        do
          ctr <- token constructorName
          succeed (PCtr ctr []),
        do
          let ctrWithArgs = do
                ctr <- token constructorName
                ps <- zeroOrMore pattern
                succeed (PCtr ctr ps)
          _ <- token (char '(')
          p <- oneOf [ctrWithArgs, pattern]
          _ <- token (char ')')
          succeed p
      ]
  oneOf
    [ do _ <- token (char '@'); x <- token variableName; succeed (PAs p x),
      succeed p
    ]

defineRules :: String -> Parser (Variable, Expr)
defineRules indent = do
  let rule :: Parser ([Pattern], Expr)
      rule = do
        ps <- zeroOrMore (do _ <- continueLine indent; pattern)
        indent <- continueLine indent
        _ <- token (char '=')
        indent <- continueLine indent
        expr <- expression indent
        succeed (ps, expr)
  name <- token variableName
  case' <- rule
  cases <- zeroOrMore (do _ <- newLine indent; _ <- token (text name); rule)
  succeed (name, match "" (case' : cases))

unpackPattern :: String -> Parser [(Variable, Expr)]
unpackPattern indent = do
  p <- pattern
  indent <- continueLine indent
  _ <- token (char '=')
  indent <- continueLine indent
  expr <- expression indent
  succeed (unpack (p, expr))

definitions :: String -> Parser [(Variable, Expr)]
definitions indent = do
  let definition = oneOf [exactly 1 (defineRules indent), unpackPattern indent]
  def <- definition
  defs <- zeroOrMore (do _ <- delimiter indent (char ';'); definition)
  succeed (concat (def : defs))

case' :: String -> Parser Case
case' indent = do
  ps <- oneOrMore pattern
  indent <- continueLine indent
  _ <- token (text "->")
  indent <- continueLine indent
  expr <- expression indent
  succeed (ps, expr)

cases :: String -> Parser [Case]
cases indent = do
  c <- case' indent
  cs <- zeroOrMore (do _ <- delimiter indent (char '|'); case' indent)
  succeed (c : cs)
