{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module TaoLang where

import Control.Monad (void)
import Data.Char (isSpace, isUpper)
import Data.List (dropWhileEnd, intercalate)
import Debug.Trace
import Error
import Flow ((|>))
import Parser (Parser)
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

-- Utilities
startsWithUpper :: String -> Bool
startsWithUpper (c : _) | isUpper c = True
startsWithUpper _ = False

identifier :: Parser String
identifier = do
  c <- P.letter
  cs <- P.zeroOrMore (P.oneOf validChars)
  P.succeed (c : cs)
  where
    validChars =
      [ P.letter,
        P.digit,
        P.char '_',
        P.char '-' |> P.notFollowedBy (P.char '>')
      ]

lineBreak :: Parser ()
lineBreak = do
  _ <- P.endOfLine
  _ <- P.whitespaces
  P.succeed ()

inbetween :: String -> String -> Parser a -> Parser a
inbetween open close parser = do
  _ <- P.text open
  _ <- P.whitespaces
  x <- parser
  _ <- P.whitespaces
  _ <- P.text close
  P.succeed x

collection :: String -> String -> String -> Parser a -> Parser [a]
collection open delim close parser =
  inbetween open close (delimited delim parser)

delimited :: String -> Parser a -> Parser [a]
delimited delim parser =
  P.oneOf
    [ do
        x <- parser
        xs <- P.zeroOrMore (do _ <- operator delim; parser)
        _ <- P.maybe' (operator delim)
        P.succeed (x : xs),
      P.succeed []
    ]

operator :: String -> Parser ()
operator name = do
  _ <- P.whitespaces
  _ <- P.text name
  _ <- P.whitespaces
  P.succeed ()

-- Concrete Syntax Tree tokens
token :: Parser a -> Parser (Token a)
token parser = do
  comments <- P.zeroOrMore comment
  docs <- P.oneOf [docString, P.succeed DocString {public = False, description = ""}]
  s1 <- P.getState
  x <- parser
  s2 <- P.getState
  _ <- P.spaces
  trailingComment <- P.oneOf [comment, P.succeed ""]
  P.succeed
    Token
      { start = (s1.row, s1.col),
        end = (s2.row, s2.col),
        docs = docs,
        comments = comments,
        commentsTrailing = trailingComment,
        value = x
      }

comment :: Parser String
comment = do
  _ <- P.char '#'
  _ <- P.spaces
  txt <- P.textUntil lineBreak
  P.succeed (dropWhileEnd isSpace txt)

docString :: Parser DocString
docString = do
  let delimiter = P.text "---"
  _ <- delimiter
  _ <- P.spaces
  public <-
    P.oneOf
      [ False <$ P.word "private",
        True <$ P.word "public",
        P.succeed True
      ]
  _ <- P.spaces
  docs <- P.textUntil (lineDelimiter delimiter)
  P.succeed DocString {public = public, description = dropWhileEnd isSpace $ dropWhile isSpace docs}
  where
    lineDelimiter :: Parser delim -> Parser ()
    lineDelimiter delimiter = do
      _ <- lineBreak
      _ <- delimiter
      _ <- P.spaces
      _ <- lineBreak
      P.succeed ()

-- Patterns
patternAtom :: Parser Pattern
patternAtom = do
  let field :: Parser (Name, Pattern)
      field = do
        x <- token identifier
        p <-
          P.oneOf
            [ do _ <- operator ":"; pattern',
              P.succeed (fmap (const (VarP x.value)) x)
            ]
        P.succeed (x, p)
  let atoms :: [Parser PatternAtom]
      atoms =
        [ AnyP <$ P.word "_",
          do
            name <- identifier
            case name of
              "Type" -> P.succeed KndP
              "Int" -> P.succeed IntTP
              "Num" -> P.succeed NumTP
              _ | startsWithUpper name -> P.succeed (TagP name)
              _ -> P.succeed (VarP name),
          IntP <$> P.integer,
          RecP <$> collection "{" ":" "}" field
        ]
  P.oneOf
    [ token (P.oneOf atoms),
      do
        p <- inbetween "(" ")" pattern'
        _ <- P.spaces
        P.succeed p
    ]

pattern' :: Parser Pattern
pattern' =
  P.withOperators
    [P.atom patternAtom]
    [ P.infixR 1 (tok FunP) (operator "->"),
      P.infixL 2 (tok AppP) P.whitespaces
    ]
    0
  where
    tok :: (Pattern -> Pattern -> PatternAtom) -> Pattern -> Pattern -> Pattern
    tok f p q = p {value = f p q, end = q.end}

-- Expressions
expressionAtom :: Parser Expression
expressionAtom = do
  let atoms =
        [ do
            name <- identifier
            case name of
              "Type" -> P.succeed Knd
              "Int" -> P.succeed IntT
              "Num" -> P.succeed NumT
              _ | startsWithUpper name -> P.succeed (Tag name)
              _ -> P.succeed (Var name),
          Int <$> P.integer,
          Num <$> P.number
        ]
  token (P.oneOf atoms)

-- expression :: Parser Expression
-- expression

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
--     [ P.atom (match 2),
--       P.prefixOp 0 Let (P.oneOrMore definition),
--       P.atom expressionAtom
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
--   _ <- P.spaces
--   P.succeed x

-- emptyLine :: Parser Error String
-- emptyLine = do
--   let close = P.oneOf [P.char '\n', P.char ';']
--   line <- P.subparser close (P.spaces)
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
