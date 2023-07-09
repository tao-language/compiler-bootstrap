module TaoLang where

import Control.Monad (void)
import Data.List (intercalate)
import Flow ((|>))
import Parser
import System.Directory
import System.FilePath ((</>))
import Tao

{-- TODO:
* Type definitions:
    Bool = True | False
    Vec n a =
      | Nil : Vec 0 a
      | Cons a (Vec n a): Vec (n + 1) a

* Syntax sugar (https://en.wikibooks.org/wiki/Haskell/Syntactic_sugar)
  - Do notation
  - Where definitions
  - Case and Match
  - Infix operators (x `op` y)
  - Partial operators (+ x) (y -)
  - IfElse
  - Char
  - Maybe
  - Tuple
  - Record
  - List
  - String
  - Set
  - Dict
  - Vector
  - Matrix
  - Tensor
  - List sequence [1..n] [1..] [1, 3..]
  - List comprehension
  - Unnamed Union types
  - Unnamed Record types

* Documentation
  - Markdown description
  - Arguments
  - Return
  - Examples (tested)
  - Only documented functions/types are public
--}

data Error
  = SyntaxError !ParserError
  | CompileError !Tao.CompileError
  deriving (Eq, Show)

-- loadExpr :: String -> IO Expr
-- loadExpr text = case parseExpr text of
--   Right expr -> return expr
--   Left err -> fail ("❌ " ++ show err)

-- loadDefinitions :: String -> IO [Definition]
-- loadDefinitions text = case parseDefinitions text of
--   Right defs -> return defs
--   Left err -> fail ("❌ " ++ show err)

-- loadBlock :: String -> IO ([Definition], Expr)
-- loadBlock text = case parseBlock text of
--   Right (env, expr) -> return (env, expr)
--   Left err -> fail ("❌ " ++ show err)

-- loadFile :: FilePath -> FilePath -> IO Env
-- loadFile moduleName fileName = do
--   src <- readFile (moduleName </> fileName)
--   case TaoLang.parse (zeroOrMore definition) src of
--     Right defs -> return (concatMap unpack defs)
--     Left err -> fail ("❌ " ++ show err)

-- loadModule :: FilePath -> IO Env
-- loadModule moduleName = do
--   files <- listDirectory moduleName
--   envs <- mapM (loadFile moduleName) (sort files)
--   return (concat envs)

parse :: Parser a -> String -> Either Error a
parse parser src = case Parser.parse parser src of
  Right x -> Right x
  Left err -> Left (SyntaxError err)

parseSome :: Parser a -> String -> Either Error (a, State)
parseSome parser src = case Parser.parseSome parser src of
  Right (x, state) -> Right (x, state)
  Left err -> Left (SyntaxError err)

-- -- TODO: make sure there are no unparsed inputs
-- parseExpr :: String -> Either Error Expr
-- parseExpr src = TaoLang.parse src (expression 0 "")

-- -- TODO: make sure there are no unparsed inputs
-- parseDefinitions :: String -> Either Error [Definition]
-- parseDefinitions src = TaoLang.parse src (zeroOrMore (definition ""))

-- -- TODO: make sure there are no unparsed inputs
-- parseBlock :: String -> Either Error ([Definition], Expr)
-- parseBlock src = TaoLang.parse src (block "")

-- eval :: Env -> Expr -> Either Error (Expr, Type)
-- eval env expr = case infer env expr of
--   Right (type', _) -> Right (reduce env expr, type')
--   Left err -> Left (TypeError err)

-- Parsers
keyword :: a -> String -> Parser a
keyword x txt = do
  let wordBreak =
        [ void letter,
          void number,
          void $ char '_',
          void $ char '\''
        ]
  _ <- token (text txt |> notFollowedBy (oneOf wordBreak))
  succeed x

identifier :: Parser Char -> Parser String
identifier firstChar = do
  -- TODO: support `-` and other characters, maybe URL-like names
  maybeUnderscore <- maybe' (char '_')
  c1 <- firstChar
  cs <- zeroOrMore (oneOf [alphanumeric, char '_'])
  let x = case maybeUnderscore of
        Just c0 -> c0 : c1 : cs
        Nothing -> c1 : cs
  keyword x ""

emptyLine :: Parser String
emptyLine = do
  let close = oneOf [char '\n', char ';']
  line <- subparser close (zeroOrMore space)
  _ <- close
  succeed line

newLine :: Parser ()
newLine = do
  _ <- token $ oneOf [void (char ';'), endOfLine]
  _ <- zeroOrMore emptyLine
  succeed ()

commentSingleLine :: Parser String
commentSingleLine = do
  let open = do _ <- text "--"; maybe' space
  let close = newLine
  _ <- open
  txt <- subparser close (zeroOrMore anyChar)
  _ <- close
  succeed txt

commentMultiLine :: Parser String
commentMultiLine = do
  let open = do _ <- text "{--"; maybe' space
  let close = do _ <- maybe' space; _ <- text "--}"; maybe' newLine
  _ <- open
  txt <- subparser close (zeroOrMore anyChar)
  _ <- close
  succeed txt

comments :: Parser String
comments = do
  texts <- zeroOrMore (oneOf [commentSingleLine, commentMultiLine])
  succeed (intercalate "\n" texts)

token :: Parser a -> Parser a
token parser = do
  x <- parser
  _ <- zeroOrMore space
  succeed x

-- Patterns
patternToken :: Parser Pattern
patternToken = do
  oneOf
    [ keyword AnyP "_",
      IntP <$> token integer,
      VarP <$> identifier lowercase,
      (`CtrP` []) <$> identifier uppercase,
      do
        _ <- token $ char '('
        p <- pattern'
        _ <- token $ char ')'
        succeed p
    ]

pattern' :: Parser Pattern
pattern' =
  oneOf
    [ do
        ctr <- identifier uppercase
        ps <- oneOrMore patternToken
        succeed (CtrP ctr ps),
      patternToken
    ]

-- Expressions
expressionToken :: Parser Expr
expressionToken =
  oneOf
    [ token $ Int <$> integer,
      token $ Num <$> number,
      Var <$> identifier letter,
      do
        _ <- token $ char '('
        a <- expression 0
        _ <- token $ char ')'
        succeed a
    ]

expression :: Int -> Parser Expr
expression prec = do
  let forall :: Parser [String]
      forall = do
        _ <- keyword () "@forall"
        xs <- oneOrMore $ identifier lowercase
        _ <- token $ char '.'
        succeed xs

  let branch :: Int -> Parser Branch
      branch prec = do
        ps <- oneOrMore patternToken
        _ <- token $ char '='
        b <- expression prec
        succeed (Br ps b)

  let match' :: Parser Expr
      match' = do
        _ <- token $ char '\\'
        br <- branch 0
        brs <- zeroOrMore (do _ <- token $ char '|'; branch 0)
        succeed (match (br : brs))

  withOperators
    [ constant match',
      prefixOp 0 Let (oneOrMore definition),
      prefixOp 1 for forall,
      constant expressionToken
    ]
    [ infixL 1 (Op2 Eq) (token $ text "=="),
      infixR 2 Fun (token $text "->"),
      infixL 3 (Op2 Lt) (token $ text "<"),
      infixL 4 (Op2 Add) (token $ text "+"),
      infixL 4 (Op2 Sub) (token $ text "-"),
      infixL 5 (Op2 Mul) (token $ text "*"),
      infixL 6 App (succeed ())
    ]
    prec

-- Definitions
typeAnnotation :: Parser (String, Type)
typeAnnotation = do
  x <- identifier lowercase
  _ <- token $ char ':'
  t <- expression 0
  succeed (x, t)

typedVariableDefinition :: Parser Definition
typedVariableDefinition = do
  (x, t) <- typeAnnotation
  _ <- token $ char '='
  a <- expression 0
  _ <- newLine
  succeed (Typed x t a)

rulesDefinition :: Parser Definition
rulesDefinition = do
  let branch :: Parser Branch
      branch = do
        ps <- zeroOrMore pattern'
        _ <- token $ char '='
        a <- expression 0
        _ <- newLine
        succeed (Br ps a)

  maybeType <- maybe' typeAnnotation
  case maybeType of
    Just (x, t) -> do
      _ <- newLine
      _ <- keyword () x
      b <- branch
      bs <- zeroOrMore (do _ <- keyword () x; branch)
      succeed (Typed x t (match (b : bs)))
    Nothing -> do
      x <- identifier lowercase
      b <- branch
      bs <- zeroOrMore (do _ <- keyword () x; branch)
      succeed (Untyped x (match (b : bs)))

unpackDefinition :: Parser Definition
unpackDefinition = do
  types <- zeroOrMore (do ann <- typeAnnotation; _ <- newLine; succeed ann)
  p <- pattern'
  _ <- token $ char '='
  a <- expression 0
  _ <- newLine
  succeed (Unpack p types a)

definition :: Parser Definition
definition =
  oneOf
    [ typedVariableDefinition,
      rulesDefinition,
      unpackDefinition
    ]

unionTypeDefinition :: Parser ContextDefinition
unionTypeDefinition = do
  let argument :: Parser (String, Type)
      argument =
        oneOf
          [ do
              _ <- token $ char '('
              arg <- typeAnnotation
              _ <- token $ char ')'
              succeed arg,
            do
              x <- identifier lowercase
              succeed (x, Var nameType)
          ]

  let alternative :: Type -> Parser (String, Type)
      alternative defaultType = do
        name <- identifier uppercase
        args <- zeroOrMore expressionToken
        oneOf
          [ do
              _ <- token $ char ':'
              t <- expression 1
              succeed (name, fun args t),
            succeed (name, fun args defaultType)
          ]

  _ <- keyword () "type"
  name <- identifier uppercase
  args <- zeroOrMore argument
  _ <- token $ char '='
  let defaultType = app (Var name) (map (Var . fst) args)
  oneOf
    [ do
        alt <- alternative defaultType
        alts <- zeroOrMore (do _ <- token $ char '|'; alternative defaultType)
        succeed (UnionType name args (alt : alts)),
      do
        _ <- keyword () "_"
        succeed (UnionType name args [])
    ]

contextDefinition :: Parser ContextDefinition
contextDefinition =
  oneOf
    [ unionTypeDefinition,
      do
        def <- definition
        succeed (Value def)
    ]
