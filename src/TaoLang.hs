module TaoLang where

import Control.Monad (void)
import Data.List (sort)
import Flow ((|>))
import Parser
import System.Directory
import System.FilePath ((</>))
import Tao

data Error
  = SyntaxError !ParserError
  | TypeError !TypeError
  deriving (Eq, Show)

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

parse :: String -> Parser a -> Either Error a
parse src parser = case Parser.parse src parser of
  Right x -> Right x
  Left err -> Left (SyntaxError err)

-- TODO: make sure there are no unparsed inputs
parseExpr :: String -> Either Error Expr
parseExpr src = TaoLang.parse src (expression "")

-- TODO: make sure there are no unparsed inputs
parseDef :: String -> Either Error Env
parseDef src = TaoLang.parse src (definition "")

-- TODO: make sure there are no unparsed inputs
parseEnv :: String -> Either Error Env
parseEnv src = TaoLang.parse src (fmap concat (zeroOrMore (definition "")))

-- TODO: make sure there are no unparsed inputs
parseBlock :: String -> Either Error Expr
parseBlock src = TaoLang.parse src (block "")

eval :: Env -> Expr -> Either Error (Expr, Expr)
eval env expr = case Tao.eval env expr of
  Right (result, type') -> Right (result, type')
  Left err -> Left (TypeError err)

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
  _ <- char ')'
  succeed op

annotatedExpr :: String -> Parser Expr
annotatedExpr indent = do
  _ <- token (char '(')
  expr <- token (expression indent)
  _ <- token (char ':')
  type' <- token (expression indent)
  _ <- char ')'
  succeed (Ann expr type')

tuple :: String -> Parser [Expr]
tuple indent = do
  _ <- token (char '(')
  items <-
    oneOf
      [ do
          x <- token (expression indent)
          xs <- oneOrMore (do _ <- token (char ','); token (expression indent))
          _ <- maybe' (token (char ','))
          succeed (x : xs),
        do
          x <- token (expression indent)
          _ <- token (char ',')
          succeed [x],
        succeed []
      ]
  _ <- char ')'
  succeed items

record :: String -> Parser [(String, Expr)]
record indent = do
  let item = do
        name <- token lowerName
        _ <- token (char '=')
        value <- expression indent
        succeed (name, value)
  _ <- token (char '(')
  field <- item
  fields <- zeroOrMore (do _ <- token (char ','); token item)
  _ <- maybe' (token (char ','))
  _ <- char ')'
  succeed (field : fields)

pattern :: String -> Parser Pattern
pattern indent = do
  p <-
    oneOf
      [ -- Pattern wildcard: _
        fmap (const PAny) (char '_'),
        -- Integer equality pattern
        fmap (PEq . Int) integer,
        do
          -- Variable equality pattern
          x <- lowerName
          _ <- char '\''
          succeed (PEq (Var x)),
        do
          -- Named pattern: x@_
          x <- token lowerName
          _ <- token (char '@')
          p <- token (pattern indent)
          succeed (PAs p x),
        -- Variable pattern: x
        fmap PVar lowerName,
        do
          -- Constructor 0-arity: Nil
          ctr <- upperName
          succeed (PCtr ctr []),
        do
          -- Constructor n-arity: Cons x xs
          _ <- token (char '(')
          ctr <- token upperName
          ps <- zeroOrMore (token (pattern indent))
          _ <- char ')'
          succeed (PCtr ctr ps),
        do
          -- Tuple empty / unit pattern: ()
          _ <- token (char '(')
          _ <- char ')'
          succeed (PTup []),
        do
          -- Tuple pattern: (x, y)
          _ <- token (char '(')
          p <- token (pattern indent)
          ps <- oneOrMore (do _ <- token (char ','); token (pattern indent))
          _ <- maybe' (token (char ','))
          _ <- char ')'
          succeed (PTup (p : ps)),
        do
          -- Tuple singleton pattern: (x,)
          _ <- token (char '(')
          p <- token (pattern indent)
          _ <- token (char ',')
          _ <- char ')'
          succeed (PTup [p]),
        do
          -- Record pattern: (.x, y = _)
          let item =
                oneOf
                  [ do
                      _ <- token (char '.')
                      x <- lowerName
                      succeed (x, PVar x),
                    do
                      x <- token lowerName
                      _ <- token (char '=')
                      p <- pattern indent
                      succeed (x, p)
                  ]
          _ <- token (char '(')
          field <- item
          fields <- zeroOrMore (do _ <- token (char ','); token item)
          _ <- maybe' (token (char ','))
          _ <- char ')'
          succeed (PRec (field : fields)),
        do
          _ <- token (char '(')
          p <- token (pattern indent)
          _ <- token (char ':')
          t <- token (pattern indent)
          _ <- char ')'
          succeed (PAnn p t),
        do
          -- Expression equality pattern
          _ <- token (char '(')
          expr <- token (expression indent)
          _ <- char ')'
          succeed (PEq expr)
      ]
  _ <- zeroOrMore space
  oneOf
    [ do
        _ <- token (char '|')
        cond <- expression indent
        succeed (PIf p cond),
      succeed p
    ]

case' :: String -> Parser Case
case' indent = do
  ps <- oneOrMore (token (pattern indent))
  _ <- token (text "->")
  indent <- maybeNewLine indent
  expr <- block indent
  succeed (ps, expr)

match :: String -> Parser Expr
match indent = do
  _ <- token (char '\\')
  c <- case' indent
  cs <- zeroOrMore (do _ <- zeroOrMore space; _ <- maybe' (newLine indent); _ <- token (char '|'); case' indent)
  succeed (Match (c : cs))

rule :: String -> Parser ([Pattern], Expr)
rule indent = do
  ps <- zeroOrMore (token (pattern indent))
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
        type' <- token (expression indent)
        _ <- token (char '=')
        _ <- maybeNewLine indent
        value <- block indent
        succeed [(name, Ann value type')],
      do
        -- Typed definition
        name <- token lowerName
        _ <- token (char ':')
        type' <- token (expression indent)
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
        p <- token (pattern indent)
        _ <- token (char '=')
        indent <- maybeNewLine indent
        value <- block indent
        succeed (unpack (p, value))
    ]

definition :: String -> Parser [(String, Expr)]
definition indent = do
  defs <- token (define indent)
  _ <- oneOf [void (newLine indent), void (token (char ';')), endOfFile]
  succeed defs

builtin :: Parser Expr
builtin = do
  _ <- char '@'
  name <- token lowerName
  typ <- expression ""
  succeed (Op (Call name typ))

parentheses :: String -> Parser Expr
parentheses indent = do
  _ <- token (char '(')
  expr <- token (expression indent)
  _ <- char ')'
  succeed expr

expression :: String -> Parser Expr
expression indent = do
  let keyword :: a -> String -> Parser a
      keyword x txt = do
        _ <- text txt |> notFollowedBy (oneOf [void letter, void number])
        succeed x

  let op parser = do
        _ <- zeroOrMore space
        x <- parser
        _ <- zeroOrMore space
        succeed x

  let unaryTerms =
        [ keyword Err "!error",
          keyword TypT "Type",
          keyword boolT "Bool",
          keyword true "True",
          keyword false "False",
          keyword IntT "Int",
          fmap Int integer,
          fmap Op operator,
          fmap Tup (tuple indent),
          fmap Rec (record indent),
          annotatedExpr indent,
          match indent,
          fmap Var lowerName,
          builtin,
          parentheses indent
        ]

  let unary :: Parser Expr
      unary = do
        a <- oneOf unaryTerms
        oneOf
          [ do
              _ <- char '.'
              x <- lowerName
              succeed (Get a x),
            succeed a
          ]

  -- TODO: make operators support newLines
  -- TODO: make parentheses support newLines
  withOperators
    unary
    [ infixR 1 (const FunT) (op (text "->")),
      infixL 2 (const eq) (op (text "==")),
      infixL 3 (const add) (op (char '+')),
      infixL 3 (const sub) (op (char '-')),
      infixL 4 (const mul) (op (char '*')),
      infixL 5 (const App) (oneOrMore space)
    ]

block :: String -> Parser Expr
block indent = do
  defs <- zeroOrMore (definition indent)
  expr <- expression indent
  case concat defs of
    [] -> succeed expr
    defs -> succeed (Let defs expr)
