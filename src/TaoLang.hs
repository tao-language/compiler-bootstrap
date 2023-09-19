module TaoLang where

import Control.Monad (void)
import Data.List (intercalate)
import Flow ((|>))
import Parser (Parser)
import qualified Parser as P
import System.Directory
import System.FilePath ((</>))
import Tao

{-- TODO:
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
  - List sequence [1..n] [1..] [1, 3..] ['a'..'z']
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

loadFile :: FilePath -> FilePath -> IO Env
loadFile moduleName fileName = do
  src <- readFile (moduleName </> fileName)
  case TaoLang.parse (P.zeroOrMore definition) src of
    Right ctx -> return ctx
    Left err -> fail ("❌ " ++ show err)

-- -- loadModule :: FilePath -> IO Env
-- -- loadModule moduleName = do
-- --   files <- listDirectory moduleName
-- --   envs <- mapM (loadFile moduleName) (sort files)
-- --   return (concat envs)

parse :: Parser a -> String -> Either CompileError a
parse parser src = case P.parse parser src of
  Right x -> Right x
  Left err -> Left (SyntaxError err)

parseSome :: Parser a -> String -> Either CompileError (a, P.State)
parseSome parser src = case P.parseSome parser src of
  Right (x, state) -> Right (x, state)
  Left err -> Left (SyntaxError err)

-- Parsers
token :: Parser a -> Parser a
token parser = do
  x <- parser
  _ <- P.zeroOrMore P.space
  P.succeed x

emptyLine :: Parser String
emptyLine = do
  let close = P.oneOf [P.char '\n', P.char ';']
  line <- P.subparser close (P.zeroOrMore P.space)
  _ <- close
  P.succeed line

newLine :: Parser ()
newLine = do
  _ <- token $ P.oneOf [void (P.char ';'), P.endOfLine]
  _ <- P.zeroOrMore emptyLine
  P.succeed ()

keyword :: a -> String -> Parser a
keyword x txt = do
  let wordBreak =
        [ void P.letter,
          void P.number,
          void $ P.char '_',
          void $ P.char '\''
        ]
  _ <- token (P.text txt |> P.notFollowedBy (P.oneOf wordBreak))
  P.succeed x

identifier :: Parser Char -> Parser String
identifier firstChar = do
  -- TODO: support `-` and other characters, maybe URL-like names
  maybeUnderscore <- P.maybe' (P.char '_')
  c1 <- firstChar
  cs <- P.zeroOrMore (P.oneOf [P.alphanumeric, P.char '_'])
  let x = case maybeUnderscore of
        Just c0 -> c0 : c1 : cs
        Nothing -> c1 : cs
  keyword x ""

commentSingleLine :: Parser String
commentSingleLine = do
  let open = do _ <- P.text "--"; P.maybe' P.space
  let close = newLine
  _ <- open
  txt <- P.subparser close (P.zeroOrMore P.anyChar)
  _ <- close
  P.succeed txt

commentMultiLine :: Parser String
commentMultiLine = do
  let open = do _ <- P.text "{--"; P.maybe' P.space
  let close = do _ <- P.maybe' P.space; _ <- P.text "--}"; P.maybe' newLine
  _ <- open
  txt <- P.subparser close (P.zeroOrMore P.anyChar)
  _ <- close
  P.succeed txt

comments :: Parser String
comments = do
  texts <- P.zeroOrMore (P.oneOf [commentSingleLine, commentMultiLine])
  P.succeed (intercalate "\n" texts)

-- Patterns
patternToken :: Parser Pattern
patternToken = do
  P.oneOf
    [ keyword PAny "_",
      PInt <$> token P.integer,
      PVar <$> identifier P.lowercase,
      PTag <$> identifier P.uppercase,
      do
        _ <- token $ P.char '('
        p <- pattern' 0
        _ <- token $ P.char ')'
        P.succeed p
    ]

pattern' :: Int -> Parser Pattern
pattern' prec = do
  P.withOperators
    [P.constant patternToken]
    [P.infixL 6 PApp (P.succeed ())]
    prec

-- Expressions
expressionToken :: Parser Expr
expressionToken =
  P.oneOf
    [ token $ Int <$> P.integer,
      token $ Num <$> P.number,
      Var <$> identifier P.letter,
      do
        _ <- token $ P.char '('
        a <- expression 0
        _ <- token $ P.char ')'
        P.succeed a
    ]

expression :: Int -> Parser Expr
expression prec = do
  let branch :: Int -> Parser ([Pattern], Expr)
      branch prec = do
        ps <- P.oneOrMore patternToken
        _ <- token $ P.char '='
        b <- expression prec
        P.succeed (ps, b)

  let match' :: Parser Expr
      match' = do
        _ <- token $ P.char '\\'
        br <- branch 0
        brs <- P.zeroOrMore (do _ <- token $ P.char '|'; branch 0)
        P.succeed (match (br : brs))

  P.withOperators
    [ P.constant match',
      P.prefixOp 0 Let (P.oneOrMore definition),
      P.constant expressionToken
    ]
    [ P.infixL 1 Eq (token $ P.text "=="),
      P.infixR 2 (App . App Fun) (token $ P.text "->"),
      P.infixL 3 Lt (token $ P.text "<"),
      P.infixL 4 Add (token $ P.text "+"),
      P.infixL 4 Sub (token $ P.text "-"),
      P.infixL 5 Mul (token $ P.text "*"),
      P.infixL 6 Pow (token $ P.text "^"),
      P.infixL 7 App (P.succeed ())
    ]
    prec

-- Definitions
definition :: Parser (Pattern, Expr)
definition =
  P.oneOf
    [ -- unionTypeDefinition,
      -- typedVariableDefinition,
      rulesDefinition
      -- , unpackDefinition
    ]

typeAnnotation :: Parser (String, Type)
typeAnnotation = do
  x <- identifier P.lowercase
  _ <- token $ P.char ':'
  xs <- P.oneOf [P.succeed []]
  t <- expression 0
  P.succeed (x, For xs t)

-- typedVariableDefinition :: Parser Definition
-- typedVariableDefinition = do
--   (x, t) <- typeAnnotation
--   _ <- token $ char '='
--   a <- expression 0
--   _ <- newLine
--   succeed (Typed x t a)

rulesDefinition :: Parser (Pattern, Expr)
rulesDefinition = do
  let branch :: Parser ([Pattern], Expr)
      branch = do
        ps <- P.zeroOrMore patternToken
        _ <- token $ P.char '='
        a <- expression 0
        _ <- newLine
        P.succeed (ps, a)

  maybeType <- P.maybe' typeAnnotation
  case maybeType of
    Just (x, ty) -> do
      _ <- newLine
      _ <- keyword () x
      b <- branch
      bs <- P.zeroOrMore (do _ <- keyword () x; branch)
      P.succeed (PVar x, Ann (match (b : bs)) ty)
    Nothing -> do
      x <- identifier P.lowercase
      b <- branch
      bs <- P.zeroOrMore (do _ <- keyword () x; branch)
      P.succeed (PVar x, match (b : bs))

-- unpackDefinition :: Parser Definition
-- unpackDefinition = do
--   types <- zeroOrMore (do ann <- typeAnnotation; _ <- newLine; succeed ann)
--   p <- pattern'
--   _ <- token $ char '='
--   a <- expression 0
--   _ <- newLine
--   succeed (Unpack p types a)

-- definition :: Parser Definition
-- definition =
--   oneOf
--     [ typedVariableDefinition,
--       rulesDefinition,
--       unpackDefinition
--     ]

-- unionTypeDefinition :: Parser ContextDefinition
-- unionTypeDefinition = do
--   let argument :: Parser (String, Type)
--       argument =
--         oneOf
--           [ do
--               _ <- token $ char '('
--               arg <- typeAnnotation
--               _ <- token $ char ')'
--               succeed arg,
--             do
--               x <- identifier lowercase
--               succeed (x, Var nameType)
--           ]

--   let alternative :: Type -> Parser (String, Type)
--       alternative defaultType = do
--         name <- identifier uppercase
--         args <- zeroOrMore expressionToken
--         oneOf
--           [ do
--               _ <- token $ char ':'
--               t <- expression 1
--               succeed (name, fun args t),
--             succeed (name, fun args defaultType)
--           ]

--   _ <- keyword () "type"
--   name <- identifier uppercase
--   args <- zeroOrMore argument
--   _ <- token $ char '='
--   let defaultType = app (Var name) (map (Var . fst) args)
--   oneOf
--     [ do
--         alt <- alternative defaultType
--         alts <- zeroOrMore (do _ <- token $ char '|'; alternative defaultType)
--         succeed (UnionType name args (alt : alts)),
--       do
--         _ <- keyword () "_"
--         succeed (UnionType name args [])
--     ]
