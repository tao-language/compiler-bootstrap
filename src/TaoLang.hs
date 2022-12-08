module TaoLang where

import Control.Monad (void)
import Data.List (sort)
import Parser
import System.Directory
import System.FilePath ((</>))
import Tao

loadExpr :: String -> IO Expr
loadExpr text = case parseExpr text of
  Right expr -> return expr
  Left err -> fail ("❌ " ++ show err)

loadDef :: String -> IO Env
loadDef text = case parseDef text of
  Right env -> return env
  Left err -> fail ("❌ " ++ show err)

loadEnv :: String -> IO Env
loadEnv text = case parseEnv text of
  Right env -> return env
  Left err -> fail ("❌ " ++ show err)

loadBlock :: String -> IO Expr
loadBlock text = case parseBlock text of
  Right expr -> return expr
  Left err -> fail ("❌ " ++ show err)

loadFile :: FilePath -> FilePath -> IO Env
loadFile moduleName fileName = do
  src <- readFile (moduleName </> fileName)
  case parseEnv src of
    Right env -> return env
    Left err -> fail ("❌ " ++ show err)

loadModule :: FilePath -> IO Env
loadModule moduleName = do
  files <- listDirectory moduleName
  fileDefs <- mapM (loadFile moduleName) (sort files)
  return (concat fileDefs)

-- TODO: make sure there are no unparsed inputs
parseExpr :: String -> Either ParserError Expr
parseExpr src = parse src (expression "")

-- TODO: make sure there are no unparsed inputs
parseDef :: String -> Either ParserError Env
parseDef src = parse src (definition "")

-- TODO: make sure there are no unparsed inputs
parseEnv :: String -> Either ParserError Env
parseEnv src = parse src (fmap concat (zeroOrMore (definition "")))

-- TODO: make sure there are no unparsed inputs
parseBlock :: String -> Either ParserError Expr
parseBlock src = parse src (block "")

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

maybeNewLine :: String -> Parser String
maybeNewLine indent =
  oneOf
    [ do
        _ <- newLine indent
        extra <- oneOrMore space
        succeed (indent ++ extra),
      succeed indent
    ]

token :: Parser a -> Parser a
token parser = do
  x <- parser
  _ <- zeroOrMore space
  succeed x

operator :: Parser Operator
operator = do
  let ops =
        [ fmap (const Eq) (text "=="),
          fmap (const Add) (text "+"),
          fmap (const Sub) (text "-"),
          fmap (const Mul) (text "*")
        ]
  _ <- token (char '(')
  op <- token (oneOf ops)
  _ <- token (char ')')
  succeed op

annotatedExpr :: String -> Parser Expr
annotatedExpr indent = do
  _ <- token (char '(')
  expr <- expression indent
  _ <- token (char ':')
  type' <- expression indent
  _ <- token (char ')')
  succeed (Ann expr type')

tuple :: String -> Parser Expr
tuple indent = do
  _ <- token (char '(')
  items <-
    oneOf
      [ do
          x <- expression indent
          xs <- oneOrMore (do _ <- token (char ','); expression indent)
          _ <- maybe' (token (char ','))
          succeed (x : xs),
        do
          x <- expression indent
          _ <- token (char ',')
          succeed [x],
        succeed []
      ]
  _ <- token (char ')')
  succeed (Tup items)

record :: String -> Parser Expr
record indent = do
  let item = do
        name <- token lowerName
        _ <- token (char '=')
        value <- expression indent
        succeed (name, value)
  _ <- token (char '(')
  field <- item
  fields <- zeroOrMore (do _ <- token (char ','); item)
  _ <- maybe' (token (char ','))
  _ <- token (char ')')
  succeed (Rec (field : fields))

pattern :: String -> Parser Pattern
pattern indent = do
  p <-
    oneOf
      [ -- Pattern wildcard: _
        fmap (const PAny) (token (char '_')),
        -- Integer equality pattern
        fmap (PEq . Int) (token integer),
        do
          -- Variable equality pattern
          x <- lowerName
          _ <- token (char '\'')
          succeed (PEq (Var x)),
        do
          -- Named pattern: x@_
          x <- token lowerName
          _ <- token (char '@')
          p <- pattern indent
          succeed (PAs p x),
        -- Variable pattern: x
        fmap PVar (token lowerName),
        do
          -- Constructor 0-arity: Nil
          ctr <- token upperName
          succeed (PCtr ctr []),
        do
          -- Constructor n-arity: Cons x xs
          _ <- token (char '(')
          ctr <- token upperName
          ps <- zeroOrMore (pattern indent)
          _ <- token (char ')')
          succeed (PCtr ctr ps),
        do
          -- Tuple empty / unit pattern: ()
          _ <- token (char '(')
          _ <- token (char ')')
          succeed (PTup []),
        do
          -- Tuple pattern: (x, y)
          _ <- token (char '(')
          p <- pattern indent
          ps <- oneOrMore (do _ <- token (char ','); pattern indent)
          _ <- maybe' (token (char ','))
          _ <- token (char ')')
          succeed (PTup (p : ps)),
        do
          -- Tuple singleton pattern: (x,)
          _ <- token (char '(')
          p <- pattern indent
          _ <- token (char ',')
          _ <- token (char ')')
          succeed (PTup [p]),
        do
          -- Record pattern: (.x, y = _)
          let item =
                oneOf
                  [ do
                      _ <- token (char '.')
                      x <- token lowerName
                      succeed (x, PVar x),
                    do
                      x <- token lowerName
                      _ <- token (char '=')
                      p <- pattern indent
                      succeed (x, p)
                  ]
          _ <- token (char '(')
          field <- item
          fields <- zeroOrMore (do _ <- token (char ','); item)
          _ <- maybe' (token (char ','))
          _ <- token (char ')')
          succeed (PRec (field : fields)),
        do
          _ <- token (char '(')
          p <- pattern indent
          _ <- token (char ':')
          t <- pattern indent
          _ <- token (char ')')
          succeed (PAnn p t),
        do
          -- Expression equality pattern
          _ <- token (char '(')
          expr <- expression indent
          _ <- token (char ')')
          succeed (PEq expr)
      ]
  oneOf
    [ do
        _ <- token (char '|')
        cond <- expression indent
        succeed (PIf p cond),
      succeed p
    ]

case' :: String -> Parser Case
case' indent = do
  ps <- oneOrMore (pattern indent)
  _ <- token (text "->")
  indent <- maybeNewLine indent
  expr <- block indent
  succeed (ps, expr)

match :: String -> Parser Expr
match indent = do
  _ <- token (char '\\')
  c <- case' indent
  cs <- zeroOrMore (do _ <- maybe' (newLine indent); _ <- token (char '|'); case' indent)
  succeed (Match (c : cs))

rule :: String -> Parser ([Pattern], Expr)
rule indent = do
  ps <- zeroOrMore (pattern indent)
  _ <- token (char '=')
  indent <- maybeNewLine indent
  expr <- block indent
  succeed (ps, expr)

rules :: String -> String -> Parser Expr
rules indent name = do
  case' <- rule indent
  case case' of
    ([], value) -> succeed value
    case' -> do
      cases <- zeroOrMore (do _ <- newLine indent; _ <- token (text name); rule indent)
      succeed (Match (case' : cases))

define :: String -> Parser [(String, Expr)]
define indent = do
  oneOf
    [ do
        -- Typed one-line definition
        name <- token lowerName
        _ <- token (char ':')
        type' <- expression indent
        _ <- token (char '=')
        _ <- maybeNewLine indent
        value <- block indent
        succeed [(name, Ann value type')],
      do
        -- Typed definition
        name <- token lowerName
        _ <- token (char ':')
        type' <- expression indent
        _ <- newLine indent
        _ <- token (text name)
        value <- rules indent name
        succeed [(name, Ann value type')],
      do
        -- Untyped definition
        name <- token lowerName
        value <- rules indent name
        succeed [(name, value)],
      do
        -- Pattern unpacking
        p <- pattern indent
        _ <- token (char '=')
        indent <- maybeNewLine indent
        value <- block indent
        succeed (unpack (p, value))
    ]

definition :: String -> Parser [(String, Expr)]
definition indent = do
  defs <- define indent
  _ <- oneOf [void (newLine indent), void (token (char ';')), endOfFile]
  succeed defs

builtin :: Parser Expr
builtin = do
  _ <- char '@'
  oneOf
    [ fmap (const IntT) (keyword "Int"),
      do
        name <- token lowerName
        typ <- expression ""
        succeed (Op (Call name typ))
    ]

expression :: String -> Parser Expr
expression indent = do
  -- TODO: make prefix and infix operators into functions instead of lists
  -- TODO: make operators support newLines
  -- TODO: make parentheses support newLines
  withOperators
    [ atom Int (token integer),
      atom id builtin,
      atom id (match indent),
      atom Op operator,
      atom id (annotatedExpr indent),
      atom id (tuple indent),
      atom id (record indent),
      atom Var (token lowerName),
      inbetween (const id) (token (char '(')) (token (char ')'))
    ]
    [ infixR 1 (const FunT) (token (text "->")),
      infixL 2 (const eq) (token (text "==")),
      infixL 3 (const add) (token (char '+')),
      infixL 3 (const sub) (token (char '-')),
      infixL 4 (const mul) (token (char '*')),
      infixL 5 (const App) (succeed ())
    ]

block :: String -> Parser Expr
block indent = do
  defs <- zeroOrMore (definition indent)
  expr <- expression indent
  case concat defs of
    [] -> succeed expr
    defs -> succeed (Let defs expr)
