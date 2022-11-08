module TaoLang where

import Control.Monad (void)
import Parser
import Tao

readExpr :: String -> IO Expr
readExpr x = case parseExpr x of
  Right exprs -> return exprs
  Left err -> fail ("❌ " ++ show err)

readDefinitions :: String -> IO Env
readDefinitions filename = do
  src <- readFile filename
  case parseEnv src of
    Right env -> return env
    Left err -> fail ("❌ " ++ show err)

-- readModule :: String -> IO [(String, Expr)]

parseExpr :: String -> Either ParserError Expr
parseExpr src = parse src (expression "")

parseEnv :: String -> Either ParserError [(String, Expr)]
parseEnv src = parse src (fmap concat (zeroOrMore (definition "")))

lowerName :: Parser String
lowerName = do
  -- TODO: support `-` and other characters, maybe URL-like names
  c <- lowercase
  cs <- zeroOrMore (oneOf [alphanumeric, char '_'])
  succeed (c : cs)

upperName :: Parser String
upperName = do
  -- TODO: support `-` and other characters, maybe URL-like names, or keep types CamelCase?
  c <- uppercase
  cs <- zeroOrMore (oneOf [alphanumeric, char '_'])
  succeed (c : cs)

keyword :: String -> Parser String
keyword txt = do
  token (text txt) |> notFollowedBy (oneOf [void letter, void number])

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

spaces :: String -> Parser String
spaces indent =
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
    [ newLine indent,
      do _ <- token parser; succeed []
    ]

operator :: String -> Parser Expr
operator indent = do
  let ops =
        [ fmap (const Eq) (text "=="),
          fmap (const Add) (text "+"),
          fmap (const Sub) (text "-"),
          fmap (const Mul) (text "*")
        ]
  _ <- token (char '(')
  _ <- spaces indent
  op <- token (oneOf ops)
  _ <- maybe' (newLine indent)
  _ <- token (char ')')
  succeed op

pattern :: Parser Pattern
pattern = do
  oneOf
    [ fmap (const PAny) (token (char '_')),
      do
        x <- token lowerName
        p <- oneOf [do _ <- token (char '@'); pattern, succeed PAny]
        succeed (PAs p x),
      fmap (PEq . Int) (token integer),
      do
        ctr <- token upperName
        succeed (PCtr ctr []),
      do
        let ctrWithArgs = do
              ctr <- token upperName
              ps <- zeroOrMore pattern
              succeed (PCtr ctr ps)
        _ <- token (char '(')
        p <- oneOf [ctrWithArgs, pattern]
        _ <- token (char ')')
        succeed p
    ]

case' :: String -> Parser Case
case' indent = do
  ps <- oneOrMore pattern
  indent <- spaces indent
  _ <- token (text "->")
  indent <- spaces indent
  expr <- expression indent
  succeed (ps, expr)

match :: String -> Parser Expr
match indent = do
  _ <- token (char '\\')
  c <- case' indent
  cs <- zeroOrMore (do _ <- delimiter indent (char '|'); case' indent)
  succeed (Match (c : cs))

rule :: String -> Parser ([Pattern], Expr)
rule indent = do
  ps <- zeroOrMore (do _ <- spaces indent; pattern)
  indent <- spaces indent
  _ <- token (char '=')
  indent <- spaces indent
  expr <- expression indent
  succeed (ps, expr)

rules :: String -> String -> Parser Expr
rules indent name = do
  case' <- rule indent
  case case' of
    ([], value) -> succeed value
    case' -> do
      cases <- zeroOrMore (do _ <- newLine indent; _ <- token (text name); rule indent)
      succeed (Match (case' : cases))

define :: String -> Parser (String, Expr)
define indent = do
  name <- token lowerName
  oneOf
    [ do
        _ <- token (char ':')
        indent <- spaces indent
        type' <- expression indent
        indent <- spaces indent
        _ <- token (char '=')
        indent <- spaces indent
        value <- expression indent
        succeed (name, Ann value type'),
      do
        _ <- token (char ':')
        indent <- spaces indent
        type' <- expression indent
        _ <- newLine indent
        _ <- token (text name)
        value <- rules indent name
        succeed (name, Ann value type'),
      do
        value <- rules indent name
        succeed (name, value)
    ]

unpack' :: String -> Parser [(String, Expr)]
unpack' indent = do
  p <- pattern
  indent <- spaces indent
  _ <- token (char '=')
  indent <- spaces indent
  expr <- expression indent
  succeed (unpack (p, expr))

definition :: String -> Parser [(String, Expr)]
definition indent = do
  defs <- oneOf [exactly 1 (define indent), unpack' indent]
  _ <- delimiter indent (char ';')
  succeed defs

let' :: String -> Parser Expr
let' indent = do
  defs <- oneOrMore (definition indent)
  expr <- expression indent
  succeed (Let (concat defs) expr)

builtin :: Parser Expr
builtin = do
  let alternative :: Parser Alt
      alternative = do
        name <- token upperName
        xs <- zeroOrMore (token lowerName)
        succeed (name, xs)

  _ <- char '@'
  oneOf
    [ fmap (const IntT) (keyword "Int"),
      fmap (const (Bool True)) (keyword "True"),
      fmap (const (Bool False)) (keyword "False"),
      do
        name <- token upperName
        alts <- collection (token (char '{')) (token (char '}')) (token (char '|')) alternative
        succeed (TypeDef name alts),
      do
        name <- token lowerName
        typ <- expression ""
        succeed (Call name typ)
    ]

expression :: String -> Parser Expr
expression indent = do
  -- TODO: make prefix and infix operators into functions instead of lists
  -- TODO: make operators support newLines
  -- TODO: make parentheses support newLines
  withOperators
    [ atom id builtin,
      atom id (match indent),
      atom id (let' indent),
      atom Var (token lowerName),
      atom Int (token integer),
      atom id (token (operator indent)),
      inbetween (const id) (token (char '(')) (token (char ')'))
    ]
    [ infixR 1 (const Fun) (token (text "->")),
      infixL 2 (const eq) (token (text "==")),
      infixL 3 (const add) (token (char '+')),
      infixL 3 (const sub) (token (char '-')),
      infixL 4 (const mul) (token (char '*')),
      infixL 5 (const App) (succeed ())
    ]
