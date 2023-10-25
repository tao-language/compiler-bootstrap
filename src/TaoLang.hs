{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module TaoLang where

import Control.Monad (void)
import Core (DocString (..), Metadata (..))
import Data.Char (isSpace, isUpper)
import Data.List (dropWhileEnd, intercalate)
import Flow ((|>))
import qualified Parser as P
import Tao

type TaoParser a = P.Parser ParserContext a

{-- TODO:
\* Token sugar (https://en.wikibooks.org/wiki/Haskell/Syntactic_sugar)
  - Do notation
  - Where statements
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

-- TODO: load all imports here (all IO operations)
loadModule :: String -> IO Module
loadModule filename = do
  src <- readFile filename
  case P.parse filename (module' filename) src of
    Right (mod, _) -> return mod
    Left P.State {name, row, col, context} -> do
      putStrLn $ intercalate ":" [name, show row, show col]
      print context
      error "Syntax error"

-- parseExpr :: String -> Either SyntaxError Expr
-- parseExpr src = error "TODO: parseExpr"

-- parseStatement :: String -> Either SyntaxError Statement
-- parseStatement src = error "TODO: parseStatement"

-- Utilities
startsWithUpper :: String -> Bool
startsWithUpper (c : _) | isUpper c = True
startsWithUpper _ = False

identifier :: TaoParser String
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

lineBreak :: TaoParser ()
lineBreak = do
  _ <- P.endOfLine
  _ <- P.whitespaces
  P.ok ()

inbetween :: String -> String -> TaoParser a -> TaoParser a
inbetween open close parser = do
  _ <- P.text open
  _ <- P.whitespaces
  x <- parser
  _ <- P.whitespaces
  _ <- P.text close
  P.ok x

collection :: String -> String -> String -> TaoParser a -> TaoParser [a]
collection open delim close parser = do
  inbetween open close (P.oneOf [delimited delim parser, P.ok []])

delimited :: String -> TaoParser a -> TaoParser [a]
delimited delim parser = do
  x <- parser
  xs <- P.zeroOrMore (P.paddedL (op delim) parser)
  _ <- P.maybe' (op delim)
  P.ok (x : xs)

-- Concrete Syntax Tree tokens
comment :: TaoParser String
comment = do
  _ <- P.char '#'
  _ <- P.spaces
  txt <- P.skipToAfter lineBreak
  P.ok (dropWhileEnd isSpace txt)

docString :: TaoParser String -> TaoParser DocString
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
  docs <- P.skipToAfter (closeDelimiter delim)
  P.ok DocString {public = public, description = dropWhileEnd isSpace $ dropWhile isSpace docs}
  where
    closeDelimiter :: String -> TaoParser ()
    closeDelimiter delim = do
      _ <- lineBreak
      _ <- P.text delim
      _ <- P.spaces
      _ <- lineBreak
      P.ok ()

metadata :: TaoParser a -> TaoParser ([Metadata], a)
metadata parser = do
  comments <- P.zeroOrMore comment
  meta <- case comments of
    [] -> P.ok []
    comments -> P.ok [Comments comments]
  state <- P.getState
  x <- parser
  _ <- P.spaces
  trailingComment <- P.maybe' comment
  meta <- case trailingComment of
    Nothing -> P.ok meta
    Just comment -> P.ok (TrailingComment comment : meta)
  P.ok (Location state.name state.row state.col : meta, x)

op :: String -> TaoParser [Metadata]
op txt = do
  _ <- P.whitespaces
  (meta, _) <- metadata (P.text txt)
  _ <- P.whitespaces
  P.ok meta

-- Patterns
pattern' :: TaoParser appDelim -> TaoParser Pattern
pattern' delim = do
  let meta f m p q = PMeta m (f p q)
  let ops =
        [ P.infixR 1 (meta PFun) (op "->"),
          P.infixL 2 (const PApp) (void delim)
        ]
  P.operators 0 ops patternAtom

patternAtom :: TaoParser Pattern
patternAtom = do
  (meta, p) <-
    (metadata . P.oneOf)
      [ PAny <$ op "_",
        patternName,
        PInt <$> P.integer,
        patternRecord,
        patternTuple
      ]
  P.ok (PMeta meta p)

patternName :: TaoParser Pattern
patternName = do
  name <- identifier
  case name of
    "Type" -> P.ok PKnd
    "Int" -> P.ok PIntT
    "Num" -> P.ok PNumT
    x | startsWithUpper x -> P.ok (PTag name)
    _ -> P.ok (PVar name)

patternRecordField :: TaoParser (String, Pattern)
patternRecordField = do
  (meta, name) <- metadata identifier
  P.oneOf
    [ do
        _ <- op ":"
        p <- pattern' P.whitespaces
        P.ok (name, p),
      P.ok (name, PMeta meta (PVar name))
    ]

patternRecord :: TaoParser Pattern
patternRecord = do
  fields <- collection "{" "," "}" patternRecordField
  P.ok (PRecord fields)

patternTuple :: TaoParser Pattern
patternTuple = do
  let item = pattern' P.whitespaces
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        item <- inbetween "(" ")" (P.paddedR (op ",") item)
        P.ok (PTuple [item]),
      do
        items <- collection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [PMeta _ item] -> P.ok item -- discard nested metadata (redundant)
          [item] -> P.ok item
          -- General case tuples: () (x, y, ...)
          _ -> P.ok (PTuple items)
    ]

-- Exprs
expression :: TaoParser appDelim -> TaoParser Expr
expression delim = do
  let meta f m a b = Meta m (f a b)
  let lamPatterns = do
        (meta, _) <- metadata (P.char '\\')
        ps <- P.oneOrMore (P.paddedL P.whitespaces patternAtom)
        _ <- op "="
        P.ok (meta, ps)
  let metaLam (m, ps) b = Meta m (lam ps b)
  let ops =
        [ P.infixR 1 (meta Or) (op "|"),
          P.prefix 2 metaLam lamPatterns,
          P.suffix 2 (flip Ann) (typeAnnotation delim),
          P.infixR 3 (meta Eq) (op "=="),
          P.infixR 4 (meta Lt) (op "<"),
          P.infixR 5 (meta Fun) (op "->"),
          P.infixR 6 (meta Add) (op "+"),
          P.infixR 6 (meta Sub) (op "-"),
          P.infixR 7 (meta Mul) (op "*"),
          P.infixL 8 (const App) (void delim),
          P.infixR 9 (meta Pow) (op "^")
        ]

  P.operators 0 ops expressionAtom

expressionAtom :: TaoParser Expr
expressionAtom = do
  (meta, a) <-
    (metadata . P.oneOf)
      [ expressionName,
        Int <$> P.integer,
        Num <$> P.number,
        expressionTuple,
        expressionRecord
      ]
  P.ok (Meta meta a)

expressionName :: TaoParser Expr
expressionName = do
  name <- identifier
  case name of
    "Type" -> P.ok Knd
    "Int" -> P.ok IntT
    "Num" -> P.ok NumT
    x | startsWithUpper x -> P.ok (Tag name)
    _ -> P.ok (Var name)

expressionTuple :: TaoParser Expr
expressionTuple = do
  let item = expression P.whitespaces
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        item <- inbetween "(" ")" (do p <- item; _ <- P.char ','; P.ok p)
        P.ok (Tuple [item]),
      do
        items <- collection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [Meta _ item] -> P.ok item -- discard nested metadata (redundant)
          [item] -> P.ok item
          -- General case tuples: () (x, y, ...)
          _ -> P.ok (Tuple items)
    ]

expressionRecordField :: TaoParser (String, Expr)
expressionRecordField = do
  name <- identifier
  _ <- op ":"
  value <- expression P.whitespaces
  P.ok (name, value)

expressionRecord :: TaoParser Expr
expressionRecord = do
  fields <- collection "{" "," "}" expressionRecordField
  P.ok (Record fields)

-- expressionBlock :: Parser Expr
-- expressionBlock =
--   -- TODO: zero or more statement --> Let
--   expression (P.ok ())

typeAnnotation :: TaoParser appDelim -> TaoParser Type
typeAnnotation delim = do
  _ <- op ":"
  xs <-
    P.oneOf
      [ do
          _ <- P.char '@'
          xs <- P.oneOrMore (P.paddedL P.whitespaces identifier)
          _ <- op "."
          P.ok xs,
        P.ok []
      ]
  t <- expression delim
  P.ok (For xs t)

-- Statements
statement :: TaoParser Statement
statement =
  (P.scope CStatement . P.oneOf)
    [letDef, unpackDef, typeDef, import', prompt]

letDef :: TaoParser Statement
letDef = do
  let branch :: TaoParser ([Pattern], Expr)
      branch = do
        ps <- P.zeroOrMore patternAtom
        _ <- op "="
        b <- expression (P.ok ())
        _ <- lineBreak
        P.ok (ps, b)
  let ruleDef :: String -> TaoParser ([Pattern], Expr)
      ruleDef name = do
        _ <- P.word name
        _ <- P.whitespaces
        branch
  docs <- P.maybe' (docString (P.atLeast 3 $ P.char '-'))
  (meta, name) <- metadata identifier
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
          rules <- P.oneOrMore (ruleDef name)
          P.ok (Just type', rules),
        do
          -- f x = 42
          rule <- branch
          rules <- P.zeroOrMore (ruleDef name)
          P.ok (Nothing, rule : rules)
      ]
  P.ok LetDef {docs = docs, name = name, type' = type', value = match rules, meta = meta}

unpackDef :: TaoParser Statement
-- (x, y) = z
unpackDef = P.fail' -- TODO

typeDef :: TaoParser Statement
-- type Bool = True | False
typeDef = P.fail' -- TODO

import' :: TaoParser Statement
import' = do
  (meta, _) <- metadata (P.word "import")
  dirName <- concat <$> P.zeroOrMore (P.concat [identifier, P.text "/"])
  modName <- identifier
  _ <- P.spaces
  name <-
    P.oneOf
      [ do
          _ <- P.word "as"
          _ <- P.spaces
          name <- identifier
          _ <- P.spaces
          P.ok name,
        P.ok modName
      ]
  exposing <-
    P.oneOf
      [ collection "(" "," ")" identifier,
        P.ok []
      ]
  _ <- lineBreak
  P.ok
    Import
      { path = dirName ++ modName,
        name = name,
        exposing = exposing,
        meta = meta
      }

prompt :: TaoParser Statement
-- > 1 + 1
-- 2
prompt = P.fail' -- TODO

-- Module
module' :: String -> TaoParser Module
module' name = do
  docs <- P.maybe' (docString (P.atLeast 3 $ P.char '='))
  body <- P.zeroOrMore statement
  _ <- P.whitespaces
  _ <- P.scope CEndOfFile P.endOfFile
  P.ok Module {name = name, docs = docs, body = body}
