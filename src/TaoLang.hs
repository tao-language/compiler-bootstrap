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

keywords :: [String]
keywords = ["type"]

-- TODO: load all imports here (all IO operations)
loadModule :: String -> IO Module
loadModule filename = do
  src <- readFile filename
  case P.parse filename (module' filename) src of
    Right (mod, _) -> return mod
    Left P.State {name, pos = (row, col), context} -> do
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
          P.paddedR (P.lookaheadNot $ P.char '>') (P.char '-')
        ]
  c <- P.letter
  cs <- P.zeroOrMore (P.oneOf validChars)
  _ <- P.spaces
  case c : cs of
    name | name `elem` keywords -> P.fail'
    name -> return name

lineBreak :: TaoParser ()
lineBreak = do
  _ <- P.endOfLine
  _ <- P.whitespaces
  return ()

inbetween :: String -> String -> TaoParser a -> TaoParser a
inbetween open close parser = do
  _ <- P.text open
  _ <- P.whitespaces
  x <- parser
  _ <- P.whitespaces
  _ <- P.text close
  return x

collection :: String -> String -> String -> TaoParser a -> TaoParser [a]
collection open delim close parser = do
  inbetween open close (P.oneOf [delimited delim parser, return []])

delimited :: String -> TaoParser a -> TaoParser [a]
delimited delim parser = do
  let delimiter = P.paddedR P.whitespaces (P.text delim)
  x <- parser
  xs <- P.zeroOrMore (P.paddedL delimiter parser)
  _ <- P.maybe' delimiter
  return (x : xs)

-- Concrete Syntax Tree
comment :: TaoParser ((Int, Int), String)
comment = do
  _ <- P.char '#'
  _ <- P.spaces
  state <- P.getState
  txt <- P.skipTo lineBreak
  return (state.pos, dropWhileEnd isSpace txt)

docString :: TaoParser String -> TaoParser DocString
docString delimiter = do
  delim <- delimiter
  P.commit CDocString
  _ <- P.spaces
  public <-
    P.oneOf
      [ False <$ P.word "private",
        True <$ P.word "public",
        return True
      ]
  _ <- P.spaces
  docs <- P.skipTo (closeDelimiter delim)
  return DocString {public = public, description = dropWhileEnd isSpace $ dropWhile isSpace docs}
  where
    closeDelimiter :: String -> TaoParser ()
    closeDelimiter delim = do
      _ <- lineBreak
      _ <- P.text delim
      _ <- P.spaces
      _ <- lineBreak
      return ()

location :: TaoParser a -> TaoParser (Metadata, a)
location parser = do
  state <- P.getState
  x <- parser
  _ <- P.spaces
  return (Location state.name state.pos, x)

op :: String -> TaoParser [Metadata]
op txt = do
  _ <- P.whitespaces
  (loc, _) <- location (P.text txt)
  _ <- P.whitespaces
  return [loc]

syntaxError :: [TaoParser until] -> TaoParser Metadata
syntaxError until = do
  state1 <- P.getState
  c <- P.anyChar
  cs <- P.skipTo (P.lookahead $ P.oneOf until)
  state2 <- P.getState
  return (SyntaxError state1.name state1.pos state2.pos (c : cs))

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
  (loc, p) <-
    (location . P.oneOf)
      [ PAny <$ P.word "_",
        patternName,
        PInt <$> P.integer,
        patternRecord,
        patternTuple
      ]
  return (PMeta [loc] p)

patternName :: TaoParser Pattern
patternName = do
  name <- identifier
  case name of
    "Type" -> return PKnd
    "Int" -> return PIntT
    "Num" -> return PNumT
    x | startsWithUpper x -> return (PTag name)
    _ -> return (PVar name)

patternTuple :: TaoParser Pattern
patternTuple = do
  let item =
        P.oneOf
          [ pattern' P.whitespaces,
            do
              err <- syntaxError [P.char ',', P.char ')']
              return (PMeta [err] PErr)
          ]
  _ <- P.char '('
  P.commit CParentheses
  _ <- P.whitespaces
  P.oneOf
    [ do
        -- Empty tuple: ()
        _ <- P.char ')'
        return (PTuple []),
      do
        x <- item
        P.oneOf
          [ do
              -- Parenthesized expression: (x)
              _ <- P.char ')'
              return x,
            do
              -- Tuple: (x,) (x, y) (x, y,)
              xs <- P.zeroOrMore $ do
                _ <- P.char ','
                _ <- P.whitespaces
                item
              _ <- P.maybe' (P.paddedR P.whitespaces $ P.char ',')
              _ <- P.char ')'
              return (PTuple (x : xs))
          ]
    ]

patternRecordField :: TaoParser (String, Pattern)
patternRecordField = do
  (loc, x) <- location identifier
  P.commit (CRecordField x)
  _ <- P.whitespaces
  P.oneOf
    [ do
        _ <- P.char ':'
        _ <- P.whitespaces
        p <- pattern' P.whitespaces
        return (x, p),
      return (x, PMeta [loc] (PVar x))
    ]

patternRecord :: TaoParser Pattern
patternRecord = do
  fields <- collection "{" "," "}" patternRecordField
  return (PRecord fields)

-- Exprs
expression :: TaoParser appDelim -> TaoParser Expr
expression delim = do
  let meta f m a b = Meta m (f a b)
  let lamPatterns = do
        (loc, _) <- location (P.char '\\')
        ps <- P.oneOrMore (P.paddedL P.whitespaces patternAtom)
        _ <- P.whitespaces
        _ <- P.char '='
        _ <- P.whitespaces
        return ([loc], ps)
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
  comments <- P.zeroOrMore comment
  expr <- P.operators 0 ops expressionAtom
  trailingComment <- P.maybe' comment
  case trailingComment of
    Just (pos, comment) -> return (Meta [Comments comments, TrailingComment pos comment] expr)
    Nothing -> return expr

expressionAtom :: TaoParser Expr
expressionAtom = do
  (loc, a) <-
    (location . P.oneOf)
      [ expressionName,
        Int <$> P.integer,
        Num <$> P.number,
        expressionTuple,
        expressionRecord
      ]
  return (Meta [loc] a)

expressionName :: TaoParser Expr
expressionName = do
  name <- identifier
  case name of
    "Type" -> return Knd
    "Int" -> return IntT
    "Num" -> return NumT
    x | startsWithUpper x -> return (Tag name)
    _ -> return (Var name)

expressionTuple :: TaoParser Expr
expressionTuple = do
  let item = expression P.whitespaces
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        item <- inbetween "(" ")" (do p <- item; _ <- P.char ','; return p)
        return (Tuple [item]),
      do
        items <- collection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [Meta _ item] -> return item -- discard nested metadata (redundant)
          [item] -> return item
          -- General case tuples: () (x, y, ...)
          _ -> return (Tuple items)
    ]

expressionRecordField :: TaoParser (String, Expr)
expressionRecordField = do
  name <- identifier
  P.commit (CRecordField name)
  _ <- P.whitespaces
  _ <- P.char ':'
  _ <- P.whitespaces
  value <- expression P.whitespaces
  return (name, value)

expressionRecord :: TaoParser Expr
expressionRecord = do
  fields <- collection "{" "," "}" expressionRecordField
  return (Record fields)

-- expressionBlock :: Parser Expr
-- expressionBlock =
--   -- TODO: zero or more statement --> Let
--   expression (return ())

typeAnnotation :: TaoParser appDelim -> TaoParser Type
typeAnnotation delim = do
  _ <- P.char ':'
  _ <- P.whitespaces
  xs <-
    P.oneOf
      [ do
          _ <- P.char '@'
          xs <- P.oneOrMore (P.paddedL P.whitespaces identifier)
          _ <- op "."
          return xs,
        return []
      ]
  t <- expression delim
  return (For xs t)

-- Statements
statement :: TaoParser Statement
statement =
  P.oneOf
    [ letDef,
      -- ,unpackDef
      typeDef
      -- ,import'
      -- ,prompt
    ]

letDef :: TaoParser Statement
letDef = do
  let branch :: TaoParser ([Pattern], Expr)
      branch = do
        ps <- P.zeroOrMore patternAtom
        _ <- P.char '='
        _ <- P.whitespaces
        b <- expression (return ())
        _ <- lineBreak
        return (ps, b)
  let ruleDef :: String -> TaoParser ([Pattern], Expr)
      ruleDef name = do
        _ <- P.word name
        _ <- P.whitespaces
        branch
  docs <- P.maybe' (docString (P.atLeast 3 $ P.char '-'))
  examples <- P.zeroOrMore example
  -- comments <- P.zeroOrMore comment
  (meta, name) <- location identifier
  (type', rules) <-
    P.oneOf
      [ do
          type' <- typeAnnotation (return ())
          P.commit (CLetDefTyped name)
          P.oneOf
            [ do
                -- x : Int = 42
                _ <- P.char '='
                P.commit (CLetDefTypedVar name)
                _ <- P.whitespaces
                value <- expression (return ())
                _ <- lineBreak
                return (Just type', [([], value)]),
              do
                -- f : Int -> Int
                _ <- lineBreak
                rules <- P.oneOrMore (ruleDef name)
                return (Just type', rules)
            ],
        do
          -- f x = 42
          rule <- branch
          P.commit (CLetDefUntyped name)
          rules <- P.zeroOrMore (ruleDef name)
          return (Nothing, rule : rules)
      ]
  return
    LetDef
      { docs = docs,
        examples = examples,
        name = name,
        type' = type',
        value = match rules,
        meta = [meta]
      }

example :: TaoParser (Expr, Expr)
example = do
  _ <- P.char '>'
  _ <- P.spaces
  prompt <- expression (return ())
  case prompt of
    _ | Just (prompt, (pos, comment)) <- getTrailingComment prompt -> do
      result <- P.parseFrom pos comment (expression $ return ())
      return (prompt, result)
    prompt -> do
      _ <- lineBreak
      result <- expression (return ())
      _ <- lineBreak
      return (prompt, result)

getTrailingComment :: Expr -> Maybe (Expr, ((Int, Int), String))
getTrailingComment (Meta [] a) = getTrailingComment a
getTrailingComment (Meta (TrailingComment pos comment : _) a) = Just (a, (pos, comment))
getTrailingComment (Meta (_ : meta) a) = getTrailingComment (Meta meta a)
getTrailingComment _ = Nothing

unpackDef :: TaoParser Statement
-- (x, y) = z
unpackDef = P.fail' -- TODO

typeDef :: TaoParser Statement
-- type Bool = True | False
typeDef = do
  docs <- P.maybe' (docString (P.atLeast 3 $ P.char '-'))
  examples <- P.zeroOrMore example
  _ <- P.word "type"
  P.commit CTypeDef
  _ <- P.whitespaces
  name <- identifier
  P.oneOf
    [ do
        _ <- P.char '='
        _ <- P.whitespaces
        _ <- lineBreak
        return
          TypeDef
            { docs = docs,
              examples = examples,
              name = name,
              args = [],
              alts = [],
              meta = []
            },
      do
        _ <- lineBreak
        return
          TypeDef
            { docs = docs,
              examples = examples,
              name = name,
              args = [],
              alts = [],
              meta = []
            }
    ]

prompt :: TaoParser Statement
-- > 1 + 1
prompt = P.fail' -- TODO

import' :: TaoParser Statement
import' = do
  (loc, _) <- location (P.word "import")
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
          return name,
        return modName
      ]
  exposing <-
    P.oneOf
      [ collection "(" "," ")" identifier,
        return []
      ]
  _ <- lineBreak
  return
    Import
      { path = dirName ++ modName,
        name = name,
        exposing = exposing,
        meta = [loc]
      }

-- Module
module' :: String -> TaoParser Module
module' name = do
  docs <- P.maybe' (docString (P.atLeast 3 $ P.char '='))
  P.oneOf
    [ do
        _ <- P.endOfFile
        return Module {name = name, docs = docs, body = []},
      do
        body <- P.oneOrMore statement
        _ <- P.whitespaces
        _ <- P.endOfFile
        return Module {name = name, docs = docs, body = body}
    ]
