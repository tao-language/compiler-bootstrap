module TaoLang where

import Control.Monad (void)
import Parser
import System.Directory
import System.FilePath ((</>))
import Tao

loadExpr :: String -> IO Expr
loadExpr text = case parseExpr text of
  Right exprs -> return exprs
  Left err -> fail ("❌ " ++ show err)

loadDef :: String -> IO Env
loadDef text = case parseDef text of
  Right def -> return def
  Left err -> fail ("❌ " ++ show err)

loadEnv :: String -> IO Env
loadEnv text = case parseEnv text of
  Right env -> return env
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
  fileDefs <- mapM (loadFile moduleName) files
  return (concat fileDefs)

-- TODO: make sure there are no unparsed inputs
parseExpr :: String -> Either ParserError Expr
parseExpr src = parse src (expression "")

-- TODO: make sure there are no unparsed inputs
parseDef :: String -> Either ParserError [(String, Expr)]
parseDef src = parse src (definition "")

-- TODO: make sure there are no unparsed inputs
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

annotatedExpr :: String -> Parser Expr
annotatedExpr indent = do
  _ <- token (char '(')
  _ <- spaces indent
  expr <- expression indent
  _ <- token (char ':')
  type' <- expression indent
  _ <- maybe' (newLine indent)
  _ <- token (char ')')
  succeed (Ann expr type')

pattern :: Parser Pattern
pattern = do
  oneOf
    [ fmap (const PAny) (token (char '_')),
      do
        x <- token lowerName
        oneOf
          [ do _ <- token (char '@'); p <- pattern; succeed (PAs p x),
            succeed (PVar x)
          ],
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
  cs <- zeroOrMore (do _ <- maybe' (newLine indent); _ <- token (char '|'); case' indent)
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

define :: String -> Parser [(String, Expr)]
define indent = do
  oneOf
    [ do
        -- Typed definition
        name <- token lowerName
        _ <- token (char ':')
        indent <- spaces indent
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
        p <- pattern
        indent <- spaces indent
        _ <- token (char '=')
        indent <- spaces indent
        expr <- expression indent
        succeed (unpack (p, expr))
    ]

definition :: String -> Parser [(String, Expr)]
definition indent = do
  defs <- define indent
  _ <- oneOf [void (newLine indent), void (token (char ';')), endOfFile]
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
    [ atom Int (token integer),
      atom id builtin,
      atom id (match indent),
      atom id (let' indent),
      atom id (token (operator indent)),
      atom id (token (annotatedExpr indent)),
      atom Var (token lowerName),
      inbetween (const id) (token (char '(')) (token (char ')'))
    ]
    [ infixR 1 (const Fun) (token (text "->")),
      infixL 2 (const eq) (token (text "==")),
      infixL 3 (const add) (token (char '+')),
      infixL 3 (const sub) (token (char '-')),
      infixL 4 (const mul) (token (char '*')),
      infixL 5 (const App) (succeed ())
    ]
