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
    type Bool = True | False
    type Vec n a
        = Nil : Vec 0 a
        | Cons a (Vec n a): Vec (n + 1) a
* Parse until end of file on parseExpr, parseDefs, etc
    - Maybe get rid of `parse*` or `load*` (?)
* AST type
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

loadFile :: FilePath -> FilePath -> IO Env
loadFile moduleName fileName = do
  src <- readFile (moduleName </> fileName)
  case TaoLang.parse (zeroOrMore define) src of
    Right defs -> return (concatMap unpack defs)
    Left err -> fail ("❌ " ++ show err)

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
    [ keyword Knd "Type",
      keyword IntT "Int",
      keyword IntT "Num",
      token $ Int <$> integer,
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
      prefixOp 0 Let (oneOrMore define),
      prefixOp 1 for forall,
      prefix 1 TypeOf (keyword () "@typeof"),
      constant expressionToken
    ]
    [ infixL 1 (Op2 "==") (token $ text "=="),
      infixR 2 Fun (token $text "->"),
      infixL 3 (Op2 "<") (token $ text "<"),
      infixL 4 (Op2 "+") (token $ text "+"),
      infixL 4 (Op2 "-") (token $ text "-"),
      infixL 5 (Op2 "*") (token $ text "*"),
      infixL 6 App (succeed ())
    ]
    prec

-- Definitions
defineRules :: [(String, Type)] -> Parser Definition
defineRules types = do
  x <- identifier lowercase
  let branch :: Parser Branch
      branch = do
        ps <- zeroOrMore pattern'
        _ <- token $ char '='
        a <- expression 0
        _ <- newLine
        succeed (Br ps a)
  b <- branch
  bs <- zeroOrMore (do _ <- keyword () x; branch)
  succeed (Def types (VarP x) (match (b : bs)))

definePattern :: [(String, Type)] -> Parser Definition
definePattern types = do
  p <- pattern'
  _ <- token $ char '='
  a <- expression 0
  _ <- newLine
  succeed (Def types p a)

defineType :: Parser Definition
defineType = do
  let typeArg :: Parser (String, Type)
      typeArg =
        oneOf
          [ do
              _ <- token $ char '('
              x <- identifier lowercase
              _ <- token $ char ':'
              t <- expression 0
              _ <- token $ char ')'
              succeed (x, t),
            do
              x <- identifier lowercase
              succeed (x, Knd)
          ]

  let alternativeArg :: Parser (String, Type)
      alternativeArg =
        oneOf
          [ do
              _ <- token $ char '('
              x <- identifier lowercase
              _ <- token $ char ':'
              t <- expression 0
              _ <- token $ char ')'
              succeed (x, t),
            do
              t <- expressionToken
              succeed ("", t)
          ]

  let alternative :: Type -> Parser (String, ([(String, Type)], Type))
      alternative defaultType = do
        ctr <- identifier uppercase
        args <- zeroOrMore alternativeArg
        t <- oneOf [do _ <- token $ char ':'; expression 0, succeed defaultType]
        succeed (ctr, (args, t))

  name <- identifier uppercase
  args <- zeroOrMore typeArg
  let defaultType = app (Var name) (Var . fst <$> args)
  _ <- token $ char '='
  alt <- alternative defaultType
  alts <- zeroOrMore (do _ <- token $ char '|'; alternative defaultType)
  _ <- newLine
  succeed (DefT name args (alt : alts))

define :: Parser Definition
define = do
  let typeDef :: Parser delim -> Parser (String, Type)
      typeDef delimiter = do
        x <- identifier lowercase
        _ <- token $ char ':'
        t <- expression 0
        _ <- delimiter
        succeed (x, t)

  oneOf
    [ defineType,
      do
        (x, t) <- typeDef (token $ char '=')
        a <- expression 0
        _ <- newLine
        succeed (Def [(x, t)] (VarP x) a),
      do
        types <- zeroOrMore (typeDef newLine)
        def <- oneOf [defineRules types, definePattern types]
        succeed def
    ]
