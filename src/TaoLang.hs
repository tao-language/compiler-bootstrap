{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module TaoLang where

import Control.Monad (void)
import Data.Char (isSpace, isUpper)
import Data.List (dropWhileEnd, intercalate)
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
  src <- readFile filename
  case P.parse sourceFile src of
    Right (file, _) -> return file
    Left state -> System.Exit.die $ "error: " ++ show state.remaining

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

identifier :: Parser Error String
identifier = do
  let validChars =
        [ P.letter,
          P.digit,
          P.char '_',
          P.char '-' |> P.notFollowedBy (P.char '>')
        ]
  c <- P.letter
  cs <- P.zeroOrMore (P.oneOf validChars)
  P.ok (c : cs)

lineBreak :: Parser Error ()
lineBreak = do
  _ <- P.endOfLine
  _ <- P.whitespaces
  P.ok ()

inbetween :: String -> String -> Parser Error a -> Parser Error (Token', a, Token')
inbetween open close parser = do
  open <- token (P.text open)
  _ <- P.whitespaces
  x <- parser
  _ <- P.whitespaces
  close <- token (P.text close)
  P.ok (void open, x, void close)

collection :: String -> String -> String -> Parser Error a -> Parser Error (Token', [a], Token')
collection open delim close parser = do
  inbetween open close (P.oneOf [delimited delim parser, P.ok []])

delimited :: String -> Parser Error a -> Parser Error [a]
delimited delim parser = do
  x <- parser
  xs <- P.zeroOrMore (P.paddedL (op delim) parser)
  _ <- P.maybe' (op delim)
  P.ok (x : xs)

-- Concrete Syntax Tree tokens
token :: Parser Error a -> Parser Error (Token a)
token parser = do
  comments <- P.zeroOrMore comment
  state1 <- P.getState
  x <- parser
  state2 <- P.getState
  _ <- P.spaces
  trailingComments <- P.zeroOrOne comment
  P.ok
    Token
      { value = x,
        row = state1.row,
        col = state1.col,
        len = state2.index - state1.index,
        comments = comments,
        trailingComments = trailingComments
      }

comment :: Parser Error String
comment = do
  _ <- P.char '#'
  _ <- P.spaces
  txt <- P.skipTo lineBreak
  P.ok (dropWhileEnd isSpace txt)

docString :: Parser Error String -> Parser Error DocString
docString delimiter = do
  delim <- delimiter
  _ <- P.spaces
  public <-
    P.oneOf
      [ False <$ P.word "private",
        True <$ P.word "public",
        P.ok True
      ]
  _ <- P.spaces
  docs <- P.skipTo (closeDelimiter delim)
  P.ok DocString {public = public, description = dropWhileEnd isSpace $ dropWhile isSpace docs}
  where
    closeDelimiter :: String -> Parser Error ()
    closeDelimiter delim = do
      _ <- lineBreak
      _ <- P.text delim
      _ <- P.spaces
      _ <- lineBreak
      P.ok ()

op :: String -> Parser Error Token'
op txt = do
  _ <- P.whitespaces
  tok <- token (P.text txt)
  _ <- P.whitespaces
  P.ok (void tok)

-- Patterns
pattern' :: Parser Error appDelim -> Parser Error Pattern
pattern' delim = do
  let ops =
        [ P.infixR 1 FunP (op "->"),
          P.infixL 2 AppP (token $ void delim)
        ]
  P.operators 0 ops patternAtom

patternAtom :: Parser Error Pattern
patternAtom =
  P.oneOf
    [ AnyP <$> op "_",
      patternName,
      IntP <$> token P.integer,
      patternRecord,
      patternTuple
    ]

patternName :: Parser Error Pattern
patternName = do
  name <- token identifier
  case name.value of
    "Type" -> P.ok (KndP $ void name)
    "Int" -> P.ok (IntTP $ void name)
    "Num" -> P.ok (NumTP $ void name)
    x | startsWithUpper x -> P.ok (TagP name)
    _ -> P.ok (VarP name)

patternRecordField :: Parser Error (Token String, Pattern)
patternRecordField = do
  name <- token identifier
  P.oneOf
    [ do
        _ <- op ":"
        p <- pattern' P.whitespaces
        P.ok (name, p),
      P.ok (name, VarP name)
    ]

patternRecord :: Parser Error Pattern
patternRecord = do
  (open, fields, close) <- collection "{" "," "}" patternRecordField
  P.ok (RecordP open fields close)

patternTuple :: Parser Error Pattern
patternTuple = do
  let item = pattern' P.whitespaces
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        (open, item, close) <- inbetween "(" ")" (P.paddedR (op ",") item)
        P.ok (TupleP open [item] close),
      do
        (open, items, close) <- collection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [item] -> P.ok item
          -- General case tuples: () (x, y, ...)
          _ -> P.ok (TupleP open items close)
    ]

-- Expressions
expression :: Parser Error appDelim -> Parser Error Expression
expression delim = do
  let lambdaPatterns = do
        _ <- P.char '\\'
        ps <- P.oneOrMore (P.paddedL P.whitespaces patternAtom)
        _ <- op "="
        P.ok ps
  let ops =
        [ P.infixR 1 Or (op "|"),
          P.prefix 2 Lambda lambdaPatterns,
          P.suffix 2 (flip Ann) (typeAnnotation delim),
          P.infixR 3 Eq (op "=="),
          P.infixR 4 Lt (op "<"),
          P.infixR 5 Fun (op "->"),
          P.infixR 6 Add (op "+"),
          P.infixR 6 Sub (op "-"),
          P.infixR 7 Mul (op "*"),
          P.infixL 8 App (token $ void delim),
          P.infixR 9 Pow (op "^")
        ]

  P.operators 0 ops expressionAtom

expressionAtom :: Parser Error Expression
expressionAtom =
  P.oneOf
    [ expressionName,
      Int <$> token P.integer,
      Num <$> token P.number,
      expressionTuple,
      expressionRecord
    ]

expressionName :: Parser Error Expression
expressionName = do
  name <- token identifier
  case name.value of
    "Type" -> P.ok (Knd $ void name)
    "Int" -> P.ok (IntT $ void name)
    "Num" -> P.ok (NumT $ void name)
    x | startsWithUpper x -> P.ok (Tag name)
    _ -> P.ok (Var name)

expressionTuple :: Parser Error Expression
expressionTuple = do
  let item = expression P.whitespaces
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        (open, item, close) <- inbetween "(" ")" (do p <- item; _ <- P.char ','; P.ok p)
        P.ok (Tuple open [item] close),
      do
        (open, items, close) <- collection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [item] -> P.ok item
          -- General case tuples: () (x, y, ...)
          _ -> P.ok (Tuple open items close)
    ]

expressionRecordField :: Parser Error (Token String, Expression)
expressionRecordField = do
  name <- token identifier
  _ <- op ":"
  value <- expression P.whitespaces
  P.ok (name, value)

expressionRecord :: Parser Error Expression
expressionRecord = do
  (open, fields, close) <- collection "{" "," "}" expressionRecordField
  P.ok (Record open fields close)

-- expressionBlock :: Parser Expression
-- expressionBlock =
--   -- TODO: zero or more definition --> Let
--   expression (P.ok ())

typeAnnotation :: Parser Error appDelim -> Parser Error Type
typeAnnotation delim = do
  _ <- op ":"
  xs <-
    P.oneOf
      [ do
          _ <- op "@"
          xs <- P.oneOrMore (token identifier)
          _ <- op "."
          P.ok xs,
        P.ok []
      ]
  t <- expression delim
  P.ok (For xs t)

-- Definitions
definition :: Parser Error Definition
definition = P.oneOf [letDef] -- , unpackDef, typeDef, test]

letDef :: Parser Error Definition
letDef = do
  let branch :: Parser Error ([Pattern], Expression)
      branch = do
        ps <- P.zeroOrMore patternAtom
        _ <- op "="
        b <- expression (P.ok ())
        _ <- lineBreak
        P.ok (ps, b)
  let ruleEntry :: String -> Parser Error ([Pattern], Expression)
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
          type' <- typeAnnotation (P.ok ())
          rule <- branch
          P.ok (Just type', [rule]),
        do
          -- f : Int -> Int
          -- f x = 42
          type' <- typeAnnotation (P.ok ())
          _ <- lineBreak
          rules <- P.oneOrMore (ruleEntry name.value)
          P.ok (Just type', rules),
        do
          -- f x = 42
          rule <- branch
          rules <- P.zeroOrMore (ruleEntry name.value)
          P.ok (Nothing, rule : rules)
      ]
  P.ok LetDef {docs = docs, name = name, type' = type', rules = rules}

unpackDef :: Parser Error Definition
-- (x, y) = z
unpackDef = error "TODO: unpackDef"

typeDef :: Parser Error Definition
-- type Bool = True | False
typeDef = error "TODO: typeDef"

test :: Parser Error Definition
-- > 1 + 1
-- 2
test = error "TODO: test"

-- Module
sourceFile :: Parser Error SourceFile
sourceFile = do
  docs <- P.maybe' (docString (P.atLeast 3 $ P.char '='))
  imports <- P.zeroOrMore import'
  definitions <- P.zeroOrMore definition
  _ <- P.whitespaces
  _ <- P.endOfFile
  P.ok
    SourceFile
      { docs = docs,
        imports = imports,
        definitions = definitions
      }

import' :: Parser Error Import
import' = do
  _ <- P.word "import"
  _ <- P.oneOrMore P.space
  dirName <- token (concat <$> P.zeroOrMore (P.concat [identifier, P.text "/"]))
  modName <- token identifier
  name <-
    P.oneOf
      [ do
          _ <- P.word "as"
          _ <- P.spaces
          name <- token identifier
          P.ok name,
        P.ok modName
      ]
  _ <- P.spaces
  exposing <-
    P.oneOf
      [ fmap (\(_, xs, _) -> xs) (collection "(" "," ")" (token identifier)),
        P.ok []
      ]
  _ <- lineBreak
  P.ok
    Import
      { path = (fmap (++ modName.value) dirName) {len = dirName.len + modName.len},
        name = name,
        exposing = exposing
      }
