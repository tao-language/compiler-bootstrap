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

loadFile :: String -> IO SourceFile
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

-- parseExpression :: String -> Either Error (Token Expression)
-- parseExpression src = error "TODO: parseExpression"

-- parseDefinition :: String -> Either Error (Token Definition)
-- parseDefinition src = error "TODO: parseDefinition"

-- parseFile :: String -> Either Error (Token SourceFile)
-- parseFile src = error "TODO: parseFile"

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

inbetween :: String -> String -> Parser a -> Parser (Token', a, Token')
inbetween open close parser = do
  open <- token (void $ P.text open)
  _ <- P.whitespaces
  x <- parser
  _ <- P.whitespaces
  close <- token (void $ P.text close)
  P.succeed (open, x, close)

collection :: String -> String -> String -> Parser a -> Parser (Token', [a], Token')
collection open delim close parser = do
  inbetween open close (P.oneOf [delimited delim parser, P.succeed []])

delimited :: String -> Parser a -> Parser [a]
delimited delim parser = do
  let delim' = operator (P.text delim)
  x <- parser
  xs <- P.zeroOrMore (do _ <- delim'; parser)
  _ <- P.maybe' delim'
  P.succeed (x : xs)

operator :: Parser op -> Parser Token'
operator op = do
  _ <- P.whitespaces
  tok <- token op
  _ <- P.whitespaces
  P.succeed (void tok)

-- Concrete Syntax Tree tokens
token :: Parser a -> Parser (Token a)
token parser = do
  comments <- P.zeroOrMore comment
  state <- P.getState
  x <- parser
  _ <- P.spaces
  trailingComments <- P.zeroOrOne comment
  P.succeed
    Token
      { value = x,
        row = state.row,
        col = state.col,
        comments = comments,
        trailingComments = trailingComments
      }

comment :: Parser String
comment = do
  _ <- P.char '#'
  _ <- P.spaces
  txt <- P.textUntil lineBreak
  P.succeed (dropWhileEnd isSpace txt)

-- docs <- P.oneOf [docString, P.succeed DocString {public = False, description = ""}]
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
pattern' :: Parser appDelim -> Parser Pattern
pattern' delim = do
  let op = operator . P.text
  P.withOperators
    [P.atom patternAtom]
    [ P.infixROp 1 FunP (op "->"),
      P.infixLOp 2 AppP (token $ void delim)
    ]
    0

patternAtom :: Parser Pattern
patternAtom =
  P.oneOf
    [ AnyP <$> operator (P.text "_"),
      patternName,
      IntP <$> token P.integer,
      patternRecord,
      patternTuple
    ]

patternName :: Parser Pattern
patternName = do
  name <- token identifier
  case name.value of
    "Type" -> P.succeed (KndP $ void name)
    "Int" -> P.succeed (IntTP $ void name)
    "Num" -> P.succeed (NumTP $ void name)
    x | startsWithUpper x -> P.succeed (TagP name)
    _ -> P.succeed (VarP name)

patternRecordField :: Parser (Token String, Pattern)
patternRecordField = do
  name <- token identifier
  P.oneOf
    [ do
        _ <- operator (P.text ":")
        p <- pattern' P.whitespaces
        P.succeed (name, p),
      P.succeed (name, VarP name)
    ]

patternRecord :: Parser Pattern
patternRecord = do
  (open, fields, close) <- collection "{" "," "}" patternRecordField
  P.succeed (RecordP open fields close)

patternTuple :: Parser Pattern
patternTuple = do
  let item = pattern' P.whitespaces
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        (open, item, close) <- inbetween "(" ")" (do p <- item; _ <- P.char ','; P.succeed p)
        P.succeed (TupleP open [item] close),
      do
        (open, items, close) <- collection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [item] -> P.succeed item
          -- General case tuples: () (x, y, ...)
          _ -> P.succeed (TupleP open items close)
    ]

-- Expressions
expression :: Parser appDelim -> Parser Expression
expression delim = do
  let op = operator . P.text
  let lambdaPatterns = do
        _ <- P.char '\\'
        ps <- P.oneOrMore (do _ <- P.whitespaces; patternAtom)
        _ <- op "="
        P.succeed ps
  P.withOperators
    [ P.atom expressionAtom,
      P.prefixOp 2 Lambda lambdaPatterns
      -- TODO: block
    ]
    -- [ P.infixR 1 (merge Or) (operator "|"),
    --   P.suffixOp 2 ann typeAnnotation,
    --   P.infixR 3 (merge Eq) (operator "=="),
    --   P.infixR 4 (merge Lt) (operator "<"),
    --   P.infixR 5 (merge Fun) (operator "->"),
    --   P.infixR 6 (merge Add) (operator "+"),
    --   P.infixR 6 (merge Sub) (operator "-"),
    --   P.infixR 7 (merge Mul) (operator "*"),
    --   P.infixR 8 (merge App) (P.succeed ()),
    --   P.infixR 9 (merge Pow) (operator "^")
    [ P.infixROp 1 Fun (op "->"),
      P.infixLOp 2 App (token $ void delim)
    ]
    0

expressionAtom :: Parser Expression
expressionAtom =
  P.oneOf
    [ expressionName,
      Int <$> token P.integer,
      Num <$> token P.number,
      expressionTuple,
      expressionRecord
    ]

expressionName :: Parser Expression
expressionName = do
  name <- token identifier
  case name.value of
    "Type" -> P.succeed (Knd $ void name)
    "Int" -> P.succeed (IntT $ void name)
    "Num" -> P.succeed (NumT $ void name)
    x | startsWithUpper x -> P.succeed (Tag name)
    _ -> P.succeed (Var name)

expressionTuple :: Parser Expression
expressionTuple = do
  let item = expression P.whitespaces
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        (open, item, close) <- inbetween "(" ")" (do p <- item; _ <- P.char ','; P.succeed p)
        P.succeed (Tuple open [item] close),
      do
        (open, items, close) <- collection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [item] -> P.succeed item
          -- General case tuples: () (x, y, ...)
          _ -> P.succeed (Tuple open items close)
    ]

expressionRecordField :: Parser (Token String, Expression)
expressionRecordField = do
  name <- token identifier
  _ <- operator (P.text ":")
  value <- expression P.whitespaces
  P.succeed (name, value)

expressionRecord :: Parser Expression
expressionRecord = do
  (open, fields, close) <- collection "{" "," "}" expressionRecordField
  P.succeed (Record open fields close)

expressionBlock :: Parser Expression
expressionBlock =
  -- TODO: zero or more definition --> Let
  expression (P.succeed ())

-- expressionAtom :: Parser Expression
-- expressionAtom = do
--   let atoms =
--         [ do
--             name <- identifier
--             case name of
--               "Type" -> P.succeed Knd
--               "Int" -> P.succeed IntT
--               "Num" -> P.succeed NumT
--               _ | startsWithUpper name -> P.succeed (Tag name)
--               _ -> P.succeed (Var name),
--           Int <$> P.integer,
--           Num <$> P.number
--         ]
--   P.oneOf
--     [ token (P.oneOf atoms),
--       do
--         a <- inbetween "(" ")" expression
--         _ <- P.spaces
--         P.succeed a
--     ]

-- expression :: Parser Expression
-- expression = do
--   P.withOperators
--     [ P.atom expressionAtom
--     -- , P.prefixOp 2 lamOp lamPatterns
--     ]
--     [ P.infixR 1 (merge Or) (operator "|"),
--       P.suffixOp 2 ann typeAnnotation,
--       P.infixR 3 (merge Eq) (operator "=="),
--       P.infixR 4 (merge Lt) (operator "<"),
--       P.infixR 5 (merge Fun) (operator "->"),
--       P.infixR 6 (merge Add) (operator "+"),
--       P.infixR 6 (merge Sub) (operator "-"),
--       P.infixR 7 (merge Mul) (operator "*"),
--       P.infixR 8 (merge App) (P.succeed ()),
--       P.infixR 9 (merge Pow) (operator "^")
--     ]
--     0

-- where
--   lamOp :: [Pattern] -> Expression -> Expression
--   lamOp [] b = b
--   lamOp (p : ps) b = Lam (p : ps) b <$ b {start = p.start}

--   lamPatterns :: Parser [Pattern]
--   lamPatterns = do
--     _ <- operator "\\"
--     ps <- P.oneOrMore patternAtom
--     _ <- operator "="
--     P.succeed ps

-- typeAnnotation :: Parser Type
-- typeAnnotation = do
--   _ <- operator ":"
--   xs <-
--     P.oneOf
--       [ do
--           _ <- operator "@"
--           xs <- P.oneOrMore (token identifier)
--           _ <- operator "."
--           P.succeed xs,
--         P.succeed []
--       ]
--   t <- expression
--   P.succeed (For xs t)

-- lambda :: Parser Expression
-- lambda =
--   -- \
--   -- pattern
--   -- branch
--   error "TODO: lambda"

-- branch :: Parser ([Pattern], Expression)
-- branch =
--   -- zeroOrMore pattern
--   -- =
--   -- block
--   error "TODO: branch"

-- -- Definitions
-- definition :: Parser Definition
-- definition = P.oneOf [rulesDef, unpackDef]

-- rulesDef :: Parser Definition
-- rulesDef =
--   -- x
--   -- maybe typeAnnotation
--   error "TODO: rulesDef"

-- unpackDef :: Parser Definition
-- unpackDef = error "TODO: unpackDef"

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
