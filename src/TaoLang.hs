{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module TaoLang where

import Control.Monad (void)
import Core (Error (..), Metadata (..))
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

lineBreak :: TaoParser String
lineBreak = do
  comment <- P.oneOf ["" <$ P.endOfLine, "" <$ P.char ';', fmap snd commentSingleLine]
  _ <- P.whitespaces
  return comment

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
comment :: TaoParser ([Metadata], String)
comment = P.oneOf [commentMultiLine, commentSingleLine]

commentSingleLine :: TaoParser ([Metadata], String)
commentSingleLine = do
  state <- P.getState
  _ <- P.char '#'
  P.commit CComment
  _ <- P.spaces
  line <- P.skipTo P.endOfLine
  return ([Location state.name state.pos], dropWhileEnd isSpace line)

commentMultiLine :: TaoParser ([Metadata], String)
commentMultiLine = do
  state <- P.getState
  delim <- P.chain [P.text "#--", P.zeroOrMore (P.char '-')]
  P.commit CCommentMultiLine
  _ <- P.spaces
  line <- P.skipTo lineBreak
  error "TODO: commentMultiLine"
  return ([Location state.name state.pos], dropWhileEnd isSpace line)

docString :: TaoParser String -> TaoParser ([Metadata], String)
docString delimiter = do
  -- comments <- P.zeroOrMore comment
  -- (loc, delim) <- location delimiter
  -- let meta = [loc]
  -- meta <- case comments of
  --   [] -> return meta
  --   comments -> return (meta ++ [Comments comments])
  -- P.commit CDocString
  -- _ <- P.spaces
  -- public <-
  --   P.oneOf
  --     [ False <$ P.word "private",
  --       True <$ P.word "public",
  --       return True
  --     ]
  -- _ <- P.spaces
  -- trailingComment1 <- P.maybe' comment
  -- meta <- case trailingComment1 of
  --   Nothing -> return meta
  --   Just (m, comment) -> return (meta ++ [TrailingComment m comment])
  -- docs <- P.zeroOrMore $ do
  --   P.lookaheadNot (do lineBreak; P.text delim)
  --   P.anyChar
  -- lineBreak
  -- _ <- P.text delim
  -- _ <- P.spaces
  -- trailingComment2 <- P.oneOf [Just <$> comment, Nothing <$ lineBreak]
  -- meta <- case trailingComment2 of
  --   Nothing -> return meta
  --   Just comment -> return (meta ++ [TrailingComment comment])
  -- return (meta, dropWhileEnd isSpace $ dropWhile isSpace docs)
  error "TODO: DocString"

location :: TaoParser a -> TaoParser (Metadata, a)
location parser = do
  state <- P.getState
  x <- parser
  _ <- P.spaces
  return (Location state.name state.pos, x)

op :: String -> TaoParser Metadata
op txt = do
  _ <- P.spaces
  (loc, _) <- location (P.text txt)
  _ <- P.spaces
  return loc

-- Expressions
expression :: TaoParser appDelim -> TaoParser Expr
expression delim = do
  let metaOp f m a b = Meta m (f a b)
  let typeAnnotation = do
        _ <- P.char ':'
        _ <- P.whitespaces
        type' delim
  let ops =
        [ P.infixR 1 (metaOp Or) (op "|"),
          -- P.prefix 2 metaLam lamPatterns,
          P.suffix 2 (flip Ann) typeAnnotation,
          P.infixR 3 (metaOp eq) (op "=="),
          P.infixR 4 (metaOp lt) (op "<"),
          P.infixR 4 (metaOp gt) (op ">"),
          P.infixR 5 (metaOp Fun) (op "->"),
          P.infixR 6 (metaOp add) (op "+"),
          P.infixR 6 (metaOp sub) (op "-"),
          P.infixR 7 (metaOp mul) (op "*"),
          P.infixL 8 (const App) (void delim),
          P.infixR 9 (metaOp pow) (op "^")
        ]
  P.operators 0 ops expressionAtom

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
  return (Meta loc a)

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

type' :: TaoParser appDelim -> TaoParser Type
type' delim = do
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
    [ fmap (\(ts, p, a) -> Def ts p a) definition,
      import',
      test,
      fmap (uncurry Comment) comment
    ]

definition :: TaoParser ([(String, Type)], Expr, Expr)
definition = do
  let annotation = do
        x <- identifier
        _ <- P.spaces
        _ <- P.char ':'
        _ <- P.spaces
        ty <- type' P.spaces
        _ <- lineBreak
        return (x, ty)
  types <- P.zeroOrMore annotation
  pattern' <- expression P.spaces
  _ <- P.whitespaces
  _ <- P.char '='
  P.commit CDefinition
  _ <- P.whitespaces
  value <- expression P.spaces
  _ <- lineBreak
  return (types, pattern', value)

import' :: TaoParser Statement
import' = do
  (loc, _) <- location (P.word "import")
  P.commit CImport
  dirName <- concat <$> P.zeroOrMore (P.concat [identifier, P.text "/"])
  modName <- identifier
  let name = dirName ++ modName
  _ <- P.spaces
  alias <-
    P.oneOf
      [ do
          _ <- P.word "as"
          _ <- P.spaces
          name <- identifier
          _ <- P.spaces
          return name,
        return name
      ]
  exposing <-
    P.oneOf
      [ collection "(" "," ")" identifier,
        return []
      ]
  _ <- lineBreak
  return (Import name alias exposing)

test :: TaoParser Statement
test = do
  _ <- P.char '>'
  _ <- P.oneOrMore P.space
  P.commit CTest
  expr <- expression P.spaces
  _ <- lineBreak
  result <-
    P.oneOf
      [ do
          result <- expression P.spaces
          _ <- lineBreak
          return result,
        case expr of
          Ann a _ -> return a
          _ -> return (Tag "True")
      ]
  return (Test expr result)

-- Module
module' :: TaoParser [Statement]
module' = do
  P.commit CModule
  stmts <- P.zeroOrMore statement
  _ <- P.whitespaces
  _ <- P.endOfFile
  return stmts

-- Package
package :: String -> Package -> IO Package
package filename pkg | filename `elem` map fst pkg.modules = return pkg
package filename pkg = do
  src <- readFile filename
  case P.parse filename module' src of
    Right (mod, _) -> return (pkg {modules = (filename, mod) : pkg.modules})
    Left P.State {name, pos = (row, col), context} -> do
      let loc = intercalate ":" [name, show row, show col]
      putStrLn loc
      print context
      error ("🛑 " ++ loc ++ ": syntax error")
