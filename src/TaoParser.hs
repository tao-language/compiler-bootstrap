{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TaoParser where

import Control.Monad (void)
import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import Data.Char (isSpace, isUpper)
import Data.Function ((&))
import Data.List (dropWhileEnd, intercalate)
import qualified Parser as P
import Tao

type Parser a = P.Parser ParserContext a

data ParserContext
  = CFile
  | CDefinition
  | CImport
  | CTest
  | CComment
  | CCommentMultiLine
  | CDocString
  | CRecordField String
  deriving (Eq, Show)

-- Utilities
startsWithUpper :: String -> Bool
startsWithUpper (c : _) | isUpper c = True
startsWithUpper _ = False

parseIdentifier :: Parser String
parseIdentifier = do
  let keywords = ["type"]
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

parseLineBreak :: Parser String
parseLineBreak = do
  parseComment <- P.oneOf ["" <$ P.endOfLine, "" <$ P.char ';', fmap snd parseCommentSingleLine]
  _ <- P.whitespaces
  return parseComment

parseInbetween :: String -> String -> Parser a -> Parser a
parseInbetween open close parser = do
  _ <- P.text open
  _ <- P.whitespaces
  x <- parser
  _ <- P.whitespaces
  _ <- P.text close
  return x

parseCollection :: String -> String -> String -> Parser a -> Parser [a]
parseCollection open delim close parser = do
  parseInbetween open close (P.oneOf [parseDelimited delim parser, return []])

parseDelimited :: String -> Parser a -> Parser [a]
parseDelimited delim parser = do
  let delimiter = P.paddedR P.whitespaces (P.text delim)
  x <- parser
  xs <- P.zeroOrMore (P.paddedL delimiter parser)
  _ <- P.maybe' delimiter
  return (x : xs)

-- Concrete Syntax Tree
parseComment :: Parser ([C.Metadata], String)
parseComment = P.oneOf [parseCommentMultiLine, parseCommentSingleLine]

parseCommentSingleLine :: Parser ([C.Metadata], String)
parseCommentSingleLine = do
  state <- P.getState
  _ <- P.char '#'
  P.commit CComment
  _ <- P.spaces
  line <- P.skipTo P.endOfLine
  return ([C.Location state.name state.pos], dropWhileEnd isSpace line)

parseCommentMultiLine :: Parser ([C.Metadata], String)
parseCommentMultiLine = do
  state <- P.getState
  delim <- P.chain [P.text "#--", P.zeroOrMore (P.char '-')]
  P.commit CCommentMultiLine
  _ <- P.spaces
  line <- P.skipTo parseLineBreak
  error "TODO: parseCommentMultiLine"
  return ([C.Location state.name state.pos], dropWhileEnd isSpace line)

parseDocString :: Parser String -> Parser ([C.Metadata], String)
parseDocString delimiter = do
  -- parseComments <- P.zeroOrMore parseComment
  -- (loc, delim) <- parseLocation delimiter
  -- let meta = [loc]
  -- meta <- case parseComments of
  --   [] -> return meta
  --   parseComments -> return (meta ++ [parseComments parseComments])
  -- P.commit CDocString
  -- _ <- P.spaces
  -- public <-
  --   P.oneOf
  --     [ False <$ P.word "private",
  --       True <$ P.word "public",
  --       return True
  --     ]
  -- _ <- P.spaces
  -- trailingparseComment1 <- P.maybe' parseComment
  -- meta <- case trailingparseComment1 of
  --   Nothing -> return meta
  --   Just (m, parseComment) -> return (meta ++ [TrailingparseComment m parseComment])
  -- docs <- P.zeroOrMore $ do
  --   P.lookaheadNot (do parseLineBreak; P.text delim)
  --   P.anyChar
  -- parseLineBreak
  -- _ <- P.text delim
  -- _ <- P.spaces
  -- trailingparseComment2 <- P.oneOf [Just <$> parseComment, Nothing <$ parseLineBreak]
  -- meta <- case trailingparseComment2 of
  --   Nothing -> return meta
  --   Just parseComment -> return (meta ++ [TrailingparseComment parseComment])
  -- return (meta, dropWhileEnd isSpace $ dropWhile isSpace docs)
  error "TODO: DocString"

parseLocation :: Parser a -> Parser (C.Metadata, a)
parseLocation parser = do
  state <- P.getState
  x <- parser
  _ <- P.spaces
  return (C.Location state.name state.pos, x)

parseOp :: String -> Parser C.Metadata
parseOp txt = do
  _ <- P.spaces
  (loc, _) <- parseLocation (P.text txt)
  _ <- P.spaces
  return loc

parseExpr :: Parser appDelim -> Parser Expr
parseExpr delim = do
  let metaOp f m a b = Meta m (f a b)
  let ops =
        [ P.infixR 1 (metaOp Or) (parseOp "|"),
          P.infixR 2 (metaOp Ann) (parseOp ":"),
          P.infixR 3 (metaOp eq) (parseOp "=="),
          P.infixR 4 (metaOp lt) (parseOp "<"),
          P.infixR 4 (metaOp gt) (parseOp ">"),
          P.infixR 5 (metaOp Fun) (parseOp "->"),
          P.infixR 6 (metaOp add) (parseOp "+"),
          P.infixR 6 (metaOp sub) (parseOp "-"),
          P.infixR 7 (metaOp mul) (parseOp "*"),
          P.infixL 8 (const App) (void delim),
          P.infixR 9 (metaOp pow) (parseOp "^")
        ]
  P.operators 0 ops parseExprAtom

parseExprAtom :: Parser Expr
parseExprAtom = do
  (loc, a) <-
    (parseLocation . P.oneOf)
      [ parseName,
        Int <$> P.integer,
        Num <$> P.number,
        parseTuple,
        parseRecord
      ]
  return (Meta loc a)

parseName :: Parser Expr
parseName = do
  name <- parseIdentifier
  case name of
    x | startsWithUpper x -> do
      args <- P.zeroOrMore parseExprAtom
      return (Tag name args)
    _ -> return (Var name)

parseTuple :: Parser Expr
parseTuple = do
  let item = parseExpr P.whitespaces
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        item <- parseInbetween "(" ")" (do p <- item; _ <- P.char ','; return p)
        return (Tuple [item]),
      do
        items <- parseCollection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [Meta _ item] -> return item -- discard nested metadata (redundant)
          [item] -> return item
          -- General case tuples: () (x, y, ...)
          _ -> return (Tuple items)
    ]

parseRecordField :: Parser (String, Expr)
parseRecordField = do
  name <- parseIdentifier
  P.commit (CRecordField name)
  _ <- P.whitespaces
  _ <- P.char ':'
  _ <- P.whitespaces
  value <- parseExpr P.whitespaces
  return (name, value)

parseRecord :: Parser Expr
parseRecord = do
  fields <- parseCollection "{" "," "}" parseRecordField
  return (Record fields)

-- Statements
parseStmt :: Parser Stmt
parseStmt =
  P.oneOf
    [ fmap (uncurry Def) parseDefinition,
      fmap (uncurry TypeAnn) parseTypeAnnotation,
      parseImport,
      parseTest,
      fmap (uncurry Comment) parseComment
    ]

parseDefinition :: Parser (Expr, Expr)
parseDefinition = do
  pattern' <- parseExpr P.spaces
  _ <- P.whitespaces
  _ <- P.char '='
  P.commit CDefinition
  _ <- P.whitespaces
  value <- parseExpr P.spaces
  _ <- parseLineBreak
  return (pattern', value)

parseTypeAnnotation :: Parser (String, Expr)
parseTypeAnnotation = do
  x <- parseIdentifier
  _ <- P.spaces
  _ <- P.char ':'
  _ <- P.spaces
  ty <- parseExpr P.spaces
  _ <- parseLineBreak
  return (x, ty)

parseImport :: Parser Stmt
parseImport = do
  (loc, _) <- parseLocation (P.word "import")
  P.commit CImport
  dirName <- concat <$> P.zeroOrMore (P.concat [parseIdentifier, P.text "/"])
  modName <- parseIdentifier
  let name = dirName ++ modName
  _ <- P.spaces
  alias <-
    P.oneOf
      [ do
          _ <- P.word "as"
          _ <- P.spaces
          name <- parseIdentifier
          _ <- P.spaces
          return name,
        return name
      ]
  exposing <-
    P.oneOf
      [ parseCollection "(" "," ")" parseIdentifier,
        return []
      ]
  _ <- parseLineBreak
  return (Import name alias exposing)

parseTest :: Parser Stmt
parseTest = do
  _ <- P.char '>'
  _ <- P.oneOrMore P.space
  P.commit CTest
  expr <- parseExpr P.spaces
  _ <- parseLineBreak
  let typeAssertion (Ann a _) = Just a
      typeAssertion (Meta _ a) = typeAssertion a
      typeAssertion _ = Nothing
  result <-
    P.oneOf
      [ do
          result <- parseExpr P.spaces
          _ <- parseLineBreak
          return result,
        case typeAssertion expr of
          Just a -> return a
          Nothing -> return (Tag "True" [])
      ]
  return (Test expr result)

-- File
parseFile :: String -> Parser File
parseFile name = do
  P.commit CFile
  stmts <- P.zeroOrMore parseStmt
  _ <- P.whitespaces
  _ <- P.endOfFile
  return (File name stmts)

parseModule :: String -> Module -> IO Module
parseModule filename mod | filename `elem` map (\f -> f.name) mod.files = return mod
parseModule filename mod = do
  src <- readFile filename
  case P.parse filename (parseFile filename) src of
    Right (f, _) -> do
      -- TODO: evaluate the module statements
      return (mod {files = f : mod.files})
    Left P.State {name, pos = (row, col), context} -> do
      let loc = intercalate ":" [name, show row, show col]
      putStrLn loc
      print context
      error ("🛑 " ++ loc ++ ": syntax error")
