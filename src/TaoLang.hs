{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module TaoLang where

import Control.Monad (void)
import Data.Char (isSpace)
import Data.List (dropWhileEnd, intercalate)
import Debug.Trace
import Error
import Flow ((|>))
import Parser (Parser, Position (..), Span (..))
import qualified Parser as P
import System.Exit
import Tao

{-- TODO:
\* Token sugar (https://en.wikibooks.org/wiki/Haskell/Syntactic_sugar)
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

\* Documentation
  - Markdown description
  - Arguments
  - Return
  - Examples (tested)
  - Only documented functions/types are public
--}

loadFile :: String -> IO (Token SourceFile)
loadFile filename = do
  -- src <- readFile filename
  -- case P.parse name (P.zeroOrMore definition) src of
  --   Right (ctx, P.State {P.source = ""}) -> return ctx
  --   Right (ctx, state) -> do
  --     let (P.Parser p) = definition
  --     case p state of
  --       Right (ctx, state) -> error "unknown error"
  --       Left state -> System.Exit.die (show state)
  --   Left state -> System.Exit.die (show state)
  error "TODO: loadFile"

-- TODO: loadModule :: String -> IO (Token Module)

parseExpression :: String -> Either Error (Token Expression)
parseExpression src = error "TODO: parseExpression"

parseDefinition :: String -> Either Error (Token Definition)
parseDefinition src = error "TODO: parseDefinition"

parseFile :: String -> Either Error (Token SourceFile)
parseFile src = error "TODO: parseFile"

-- Concrete Syntax Tree tokens
token :: Parser a -> Parser (Token a)
token parser = do
  comments <- P.zeroOrMore comment
  docs <- P.oneOf [docString, P.succeed DocString {public = False, description = ""}]
  s1 <- P.getState
  x <- parser
  s2 <- P.getState
  _ <- P.zeroOrMore P.space
  trailingComment <- P.oneOf [comment, P.succeed ""]
  P.succeed
    Token
      { span = Span {name = s1.name, start = s1.pos, end = s2.pos},
        docs = docs,
        comments = comments,
        commentsTrailing = trailingComment,
        value = x
      }

comment :: Parser String
comment = do
  _ <- P.char '#'
  _ <- P.zeroOrMore P.space
  txt <- P.textUntil lineBreak
  P.succeed (dropWhileEnd isSpace txt)

docString :: Parser DocString
docString = do
  let delimiter = P.text "---"
  _ <- delimiter
  _ <- P.zeroOrMore P.space
  public <-
    P.oneOf
      [ False <$ P.word "private",
        True <$ P.word "public",
        P.succeed True
      ]
  _ <- P.zeroOrMore P.space
  docs <- P.textUntil (lineDelimiter delimiter)
  P.succeed DocString {public = public, description = dropWhileEnd isSpace $ dropWhile isSpace docs}

lineBreak :: Parser ()
lineBreak = do
  _ <- P.endOfLine
  _ <- P.zeroOrMore P.whitespace
  P.succeed ()

lineDelimiter :: Parser delim -> Parser ()
lineDelimiter delimiter = do
  _ <- lineBreak
  _ <- delimiter
  _ <- P.zeroOrMore P.space
  _ <- lineBreak
  P.succeed ()

variableName :: Parser String
variableName = error "TODO"

tagName :: Parser String
tagName = error "TODO"

-- Patterns
patternAtom :: Parser (Token Pattern)
patternAtom = do
  let atoms =
        [ PAny <$ P.word "_",
          PInt <$> P.integer
          -- PVar <$> identifier P.lowercase,
          -- PTag <$> identifier P.uppercase,
          -- do
          --   _ <- token $ P.char '('
          --   p <- pattern'
          --   _ <- token $ P.char ')'
          --   P.succeed p
        ]
  token (P.oneOf atoms)

-- pattern' :: Parser (Token Pattern)
-- pattern' = patternAtom -- TODO

-- -- Expressions
-- expressionAtom :: Parser Expression
-- expressionAtom =
--   P.oneOf
--     [ token $ Int <$> P.integer,
--       token $ Num <$> P.number,
--       Var <$> identifier P.lowercase,
--       Tag <$> identifier P.uppercase,
--       do
--         _ <- token $ P.char '('
--         a <- expression 0
--         _ <- token $ P.char ')'
--         P.succeed a
--     ]

-- expression :: Int -> Parser Expression
-- expression prec = do
--   let matchBranch :: Int -> Parser ([Pattern], Expression)
--       matchBranch prec = do
--         _ <- token $ P.char '|'
--         p <- patternAtom
--         (ps, b) <- branch prec
--         P.succeed (p : ps, b)

--   let match :: Int -> Parser Expression
--       match prec = do
--         _ <- token $ P.char '\\'
--         br <- branch prec
--         brs <- P.zeroOrMore (matchBranch prec)
--         P.succeed (Match (br : brs))

--   P.withOperators
--     [ P.constant (match 2),
--       P.prefixOp 0 Let (P.oneOrMore definition),
--       P.constant expressionAtom
--     ]
--     [ P.infixR 1 Or (token $ P.text "|"),
--       P.infixR 1 If (token $ P.text "?"),
--       P.infixR 2 (\a b -> Ann a (For [] b)) (token $ P.text ":"),
--       P.infixL 3 Eq (token $ P.text "=="),
--       P.infixL 4 Lt (token $ P.text "<"),
--       P.infixR 5 Fun (token $ P.text "->"),
--       P.infixL 6 Add (token $ P.text "+"),
--       P.infixL 6 Sub (token $ P.text "-"),
--       P.infixL 7 Mul (token $ P.text "*"),
--       P.infixL 8 App (P.succeed ()),
--       P.infixL 10 Pow (token $ P.text "^")
--     ]
--     prec

-- Definitions
definition :: Parser Definition
definition =
  P.oneOf
    -- untypedDef
    -- typedVarDef,
    -- typedDef,
    -- unpackDef
    []

-- untypedDef :: Parser Definition
-- untypedDef = do
--   x <- identifier P.lowercase
--   a <- branches 0 x
--   P.succeed
--     ( Def
--         { docs = Nothing,
--           type' = Nothing,
--           name = x,
--           value = a
--         }
--     )

-- typedDef :: Parser Error Definition
-- typedDef = do
--   (x, ty) <- typeAnnotation
--   _ <- newLine
--   _ <- keyword () x
--   a <- branches 0 x
--   P.succeed
--     ( Def
--         { docs = Nothing,
--           type' = Just ty,
--           name = x,
--           value = a
--         }
--     )

-- typedVarDef :: Parser Error Definition
-- typedVarDef = do
--   (x, ty) <- typeAnnotation
--   _ <- token $ P.char '='
--   a <- expression 0
--   _ <- newLine
--   P.succeed
--     ( Def
--         { docs = Nothing,
--           type' = Just ty,
--           name = x,
--           value = a
--         }
--     )

-- unpackDef :: Parser Error Definition
-- unpackDef = do
--   types <- P.zeroOrMore (do ann <- typeAnnotation; _ <- newLine; P.succeed ann)
--   p <- pattern'
--   _ <- token $ P.char '='
--   a <- expression 0
--   _ <- newLine
--   P.succeed
--     ( Unpack
--         { docs = Nothing,
--           types = types,
--           pattern = p,
--           value = a
--         }
--     )

-- typeAnnotation :: Parser Error (String, Type)
-- typeAnnotation = do
--   x <- identifier P.lowercase
--   _ <- token $ P.char ':'
--   xs <-
--     P.oneOf
--       [ do
--           _ <- token $ P.char '@'
--           x <- identifier P.lowercase
--           xs <- P.zeroOrMore (identifier P.lowercase)
--           _ <- token $ P.char '.'
--           P.succeed (x : xs),
--         P.succeed []
--       ]
--   t <- expression 0
--   P.succeed (x, For xs t)

-- branches :: Int -> String -> Parser Expression
-- branches prec x = do
--   br <- branch prec
--   _ <- newLine
--   brs <- P.zeroOrMore (rule prec x)
--   P.succeed (Match (br : brs))

-- branch :: Int -> Parser ([Pattern], Expression)
-- branch prec = do
--   ps <- P.zeroOrMore patternAtom
--   _ <- token $ P.char '='
--   b <- expression prec
--   P.succeed (ps, b)

-- rule :: Int -> String -> Parser ([Pattern], Expression)
-- rule prec x = do
--   _ <- keyword x
--   br <- branch prec
--   _ <- newLine
--   P.succeed br

-- Utils
-- newLine :: Parser ()
-- newLine = do
--   _ <- token $ P.oneOrMore $ P.oneOf [void (P.char ';'), void P.space, P.endOfLine]
--   P.succeed ()

-- keyword :: String -> Parser String
-- keyword txt = do
--   let wordBreak =
--         [ void P.letter,
--           void P.number,
--           void $ P.char '_',
--           void $ P.char '\''
--         ]
--   token (P.text txt |> P.notFollowedBy (P.oneOf wordBreak))

-- identifier :: Parser Char -> Parser String
-- identifier firstChar = do
--   -- TODO: support `-` and other characters, maybe URL-like names
--   maybeUnderscore <- P.maybe' (P.char '_')
--   c1 <- firstChar
--   cs <- P.zeroOrMore (P.oneOf [P.alphanumeric, P.char '_'])
--   let x = case maybeUnderscore of
--         Just c0 -> c0 : c1 : cs
--         Nothing -> c1 : cs
--   keyword x

-- token :: Parser a -> Parser a
-- token parser = do
--   x <- parser
--   _ <- P.zeroOrMore P.space
--   P.succeed x

-- emptyLine :: Parser Error String
-- emptyLine = do
--   let close = P.oneOf [P.char '\n', P.char ';']
--   line <- P.subparser close (P.zeroOrMore P.space)
--   _ <- close
--   P.succeed line

-- commentSingleLine :: Parser Error String
-- commentSingleLine = do
--   let open = do _ <- P.text "--"; P.maybe' P.space
--   let close = newLine
--   _ <- open
--   txt <- P.subparser close (P.zeroOrMore P.anyChar)
--   _ <- close
--   P.succeed txt

-- commentMultiLine :: Parser Error String
-- commentMultiLine = do
--   let open = do _ <- P.text "{--"; P.maybe' P.space
--   let close = do _ <- P.maybe' P.space; _ <- P.text "--}"; P.maybe' newLine
--   _ <- open
--   txt <- P.subparser close (P.zeroOrMore P.anyChar)
--   _ <- close
--   P.succeed txt

-- comments :: Parser Error String
-- comments = do
--   texts <- P.zeroOrMore (P.oneOf [commentSingleLine, commentMultiLine])
--   P.succeed (intercalate "\n" texts)
