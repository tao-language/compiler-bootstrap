module TaoLang
  ( Tao.Expr (..),
    Tao.Operator (..),
    Tao.Pattern (..),
    Tao.add,
    Tao.app,
    Tao.eq,
    Tao.forT,
    Tao.funT,
    Tao.lam,
    Tao.let',
    Tao.mul,
    Tao.prelude,
    Tao.sub,
    TaoLang.eval,
    block,
    builtin,
    case',
    comment,
    define,
    emptyLine,
    expression,
    identifier,
    loadBlock,
    loadDef,
    loadEnv,
    loadExpr,
    loadFile,
    loadModule,
    match,
    maybeNewLine,
    newLine,
    operator,
    parseBlock,
    parseDef,
    parseEnv,
    parseExpr,
    pattern',
    record,
    rule,
    rules,
    tuple,
  )
where

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

loadBlock :: String -> IO (Env, Expr)
loadBlock text = case parseBlock text of
  Right (env, expr) -> return (env, expr)
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
  defs <- mapM (loadFile moduleName) (sort files)
  return (concat defs)

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
parseBlock :: String -> Either Error (Env, Expr)
parseBlock src = TaoLang.parse src (block "")

eval :: Env -> Expr -> Either Error (Expr, Expr)
eval env expr = case Tao.eval env expr of
  Right (result, type') -> Right (result, type')
  Left err -> Left (TypeError err)

identifier :: Parser Char -> Parser String
identifier firstChar = do
  -- TODO: support `-` and other characters, maybe URL-like names
  c <- firstChar
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

field :: Parser delim -> String -> Parser (String, Expr)
field delimiter indent = do
  name <- token (identifier lowercase)
  _ <- token delimiter
  value <- expression indent
  succeed (name, value)

record :: Parser delim -> String -> Parser [(String, Expr)]
record delimiter indent = do
  _ <- token (char '(')
  field' <- field delimiter indent
  fields <- zeroOrMore (do _ <- token (char ','); token (field delimiter indent))
  _ <- maybe' (token (char ','))
  _ <- char ')'
  succeed (field' : fields)

recordSet :: String -> Parser Expr
recordSet indent = do
  _ <- token (char '(')
  expr <- token (expression indent)
  _ <- token (char '|')
  field' <- field (char '=') indent
  fields <- zeroOrMore (do _ <- token (char ','); token (field (char '=') indent))
  _ <- maybe' (token (char ','))
  _ <- char ')'
  succeed (Set expr (field' : fields))

pattern' :: String -> Parser Pattern
pattern' indent = do
  p <-
    oneOf
      [ -- Pattern wildcard: _
        fmap (const PAny) (char '_'),
        -- Integer equality pattern
        fmap (PEq . Int) integer,
        do
          -- Variable equality pattern
          x <- identifier lowercase
          _ <- char '\''
          succeed (PEq (Var x)),
        do
          -- Named pattern: x@_
          x <- token (identifier lowercase)
          _ <- token (char '@')
          p <- token (pattern' indent)
          succeed (PAs p x),
        -- Variable pattern: x
        fmap PVar (identifier lowercase),
        do
          -- Constructor 0-arity: Nil
          ctr <- identifier uppercase
          succeed (PCtr ctr []),
        do
          -- Constructor n-arity: Cons x xs
          _ <- token (char '(')
          ctr <- token (identifier uppercase)
          ps <- zeroOrMore (token (pattern' indent))
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
          p <- token (pattern' indent)
          ps <- oneOrMore (do _ <- token (char ','); token (pattern' indent))
          _ <- maybe' (token (char ','))
          _ <- char ')'
          succeed (PTup (p : ps)),
        do
          -- Tuple singleton pattern: (x,)
          _ <- token (char '(')
          p <- token (pattern' indent)
          _ <- token (char ',')
          _ <- char ')'
          succeed (PTup [p]),
        do
          -- Record pattern: (.x, y = _)
          let item =
                oneOf
                  [ do
                      _ <- token (char '.')
                      x <- identifier lowercase
                      succeed (x, PVar x),
                    do
                      x <- token (identifier lowercase)
                      _ <- token (char '=')
                      p <- pattern' indent
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
          p <- token (pattern' indent)
          _ <- token (char ':')
          t <- token (pattern' indent)
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
  ps <- oneOrMore (token (pattern' indent))
  _ <- token (text "->")
  indent <- maybeNewLine indent
  (env, expr) <- block indent
  succeed (ps, let' env expr)

match :: String -> Parser Expr
match indent = do
  _ <- token (char '\\')
  c <- case' indent
  cs <- zeroOrMore (do _ <- zeroOrMore space; _ <- maybe' (newLine indent); _ <- token (char '|'); case' indent)
  succeed (Match (c : cs))

rule :: String -> Parser ([Pattern], Expr)
rule indent = do
  ps <- zeroOrMore (token (pattern' indent))
  _ <- token (char '=')
  indent <- maybeNewLine indent
  (env, expr) <- block indent
  succeed (ps, let' env expr)

rules :: String -> String -> Parser Expr
rules indent name = do
  case' <- rule indent
  case case' of
    ([], value) -> succeed value
    case' -> do
      cases <- zeroOrMore (do _ <- newLine indent; _ <- token (text name); rule indent)
      succeed (Match (case' : cases))

ctrDef :: Expr -> String -> Parser (String, ([String], Expr))
ctrDef type' indent = do
  cname <- token (identifier uppercase)
  xs <- zeroOrMore (token (identifier lowercase))
  oneOf
    [ do
        _ <- token (char ':')
        type' <- expression indent
        succeed (cname, (xs, type')),
      do
        let xsT = newNames (xs ++ freeVars type') (map (++ "T") xs)
        succeed (cname, (xs, forT xsT (funT (map Var xsT) type')))
    ]

define :: String -> Parser [(String, Expr)]
define indent = do
  oneOf
    [ do
        -- Typed one-line definition
        name <- token (identifier lowercase)
        _ <- token (char ':')
        type' <- token (expression indent)
        _ <- token (char '=')
        _ <- maybeNewLine indent
        (env, value) <- block indent
        succeed [(name, Ann (let' env value) type')],
      do
        -- Typed definition
        name <- token (identifier lowercase)
        _ <- token (char ':')
        type' <- token (expression indent)
        _ <- newLine indent
        _ <- token (text name)
        value <- rules indent name
        succeed [(name, Ann value type')],
      do
        -- Untyped definition
        name <- token (identifier lowercase)
        value <- rules indent name
        succeed [(name, value)],
      do
        -- Tagged union type definition
        tname <- token (identifier uppercase)
        vars <- zeroOrMore (token (identifier lowercase))
        let type' = app (Var tname) (map Var vars)
        _ <- token (char '=')
        def <- ctrDef type' indent
        defs <- zeroOrMore (do _ <- zeroOrMore space; _ <- token (char '|'); ctrDef type' indent)
        let defs' = def : defs
        let ctr (cname, _) = (cname, Ctr tname cname)
        succeed ((tname, lam vars (SumT defs')) : map ctr defs'),
      do
        -- Pattern unpacking
        p <- token (pattern' indent)
        _ <- token (char '=')
        indent <- maybeNewLine indent
        (env, value) <- block indent
        succeed (unpack (p, let' env value))
    ]

definition :: String -> Parser [(String, Expr)]
definition indent = do
  defs <- token (define indent)
  _ <- oneOf [void (newLine indent), void (token (char ';')), endOfFile]
  succeed defs

builtin :: Parser Expr
builtin = do
  _ <- char '@'
  name <- token (identifier letter)
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
          keyword IntT "Int",
          fmap Int integer,
          fmap Op operator,
          recordSet indent,
          fmap Tup (tuple indent),
          fmap RecT (record (char ':') indent),
          fmap Rec (record (char '=') indent),
          annotatedExpr indent,
          match indent,
          fmap Var (identifier letter),
          builtin,
          parentheses indent
        ]

  let unary :: Parser Expr
      unary = do
        a <- oneOf unaryTerms
        oneOf
          [ do
              _ <- char '.'
              x <- identifier lowercase
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

block :: String -> Parser (Env, Expr)
block indent = do
  defs <- zeroOrMore (definition indent)
  expr <- expression indent
  succeed (concat defs, expr)
