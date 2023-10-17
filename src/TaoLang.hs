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

docString :: Parser String -> Parser DocString
docString delimiter = do
  delim <- delimiter
  _ <- P.spaces
  public <-
    P.oneOf
      [ False <$ P.word "private",
        True <$ P.word "public",
        P.succeed True
      ]
  _ <- P.spaces
  docs <- P.textUntil (closeDelimiter delim)
  P.succeed DocString {public = public, description = dropWhileEnd isSpace $ dropWhile isSpace docs}
  where
    closeDelimiter :: String -> Parser ()
    closeDelimiter delim = do
      _ <- lineBreak
      _ <- P.text delim
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
    [ P.infixROp 1 Or (op "|"),
      P.suffixOp 2 Ann (typeAnnotation delim),
      P.infixROp 3 Eq (op "=="),
      P.infixROp 4 Lt (op "<"),
      P.infixROp 5 Fun (op "->"),
      P.infixROp 6 Add (op "+"),
      P.infixROp 6 Sub (op "-"),
      P.infixROp 7 Mul (op "*"),
      P.infixLOp 8 App (token $ void delim),
      P.infixROp 9 Pow (op "^")
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

-- expressionBlock :: Parser Expression
-- expressionBlock =
--   -- TODO: zero or more definition --> Let
--   expression (P.succeed ())

typeAnnotation :: Parser appDelim -> Parser Type
typeAnnotation delim = do
  _ <- operator (P.text ":")
  xs <-
    P.oneOf
      [ do
          _ <- operator (P.text "@")
          xs <- P.oneOrMore (token identifier)
          _ <- operator (P.text ".")
          P.succeed xs,
        P.succeed []
      ]
  t <- expression delim
  P.succeed (For xs t)

-- Definitions
definition :: Parser Definition
definition = P.oneOf [letDef] -- , unpackDef, typeDef, test]

letDef :: Parser Definition
letDef = do
  let branch :: Parser ([Pattern], Expression)
      branch = do
        ps <- P.zeroOrMore patternAtom
        _ <- operator (P.char '=')
        b <- expression (P.succeed ())
        _ <- lineBreak
        P.succeed (ps, b)
  let ruleEntry :: String -> Parser ([Pattern], Expression)
      ruleEntry name = do
        _ <- P.word name
        _ <- P.whitespaces
        branch
  docs <- P.maybe' (docString (P.atLeast 3 $ P.char '-'))
  name <- token identifier
  (type', rules) <-
    P.oneOf
      [ do
          -- x : Int = 42
          type' <- typeAnnotation (P.succeed ())
          rule <- branch
          P.succeed (Just type', [rule]),
        do
          -- f : Int -> Int
          -- f x = 42
          type' <- typeAnnotation (P.succeed ())
          _ <- lineBreak
          rules <- P.oneOrMore (ruleEntry name.value)
          P.succeed (Just type', rules),
        do
          -- f x = 42
          rule <- branch
          rules <- P.zeroOrMore (ruleEntry name.value)
          P.succeed (Nothing, rule : rules)
      ]
  P.succeed LetDef {docs = docs, name = name, type' = type', rules = rules}

unpackDef :: Parser Definition
-- (x, y) = z
unpackDef = error "TODO: unpackDef"

typeDef :: Parser Definition
-- type Bool = True | False
typeDef = error "TODO: typeDef"

test :: Parser Definition
-- > 1 + 1
-- 2
test = error "TODO: test"

-- Module
sourceFile :: Parser SourceFile
sourceFile = do
  docs <- P.maybe' (docString (P.atLeast 3 $ P.char '='))
  imports <- P.zeroOrMore (token import')
  definitions <- P.zeroOrMore definition
  P.succeed
    SourceFile
      { docs = docs,
        imports = imports,
        definitions = definitions
      }

import' :: Parser Import
import' = do
  _ <- P.word "import"
  _ <- P.spaces
  dirName <- token (concat <$> P.zeroOrMore (P.concat [identifier, P.text "/"]))
  modName <- token identifier
  name <-
    P.oneOf
      [ do
          _ <- P.word "as"
          _ <- P.spaces
          name <- token identifier
          P.succeed name,
        P.succeed modName
      ]
  _ <- P.spaces
  exposing <-
    P.oneOf
      [ fmap (\(_, xs, _) -> xs) (collection "(" "," ")" (token identifier)),
        P.succeed []
      ]
  _ <- lineBreak
  P.succeed
    Import
      { path = fmap (++ modName.value) dirName,
        name = name,
        exposing = exposing
      }
