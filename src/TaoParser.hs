{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TaoParser where

import Control.Monad (void)
import Core
import Data.Bifunctor (Bifunctor (second))
import Data.Char (isSpace, isUpper)
import Data.List (dropWhileEnd, intercalate)
import Flow ((|>))
import qualified Parser as P
import Tao

type TaoParser a = P.Parser ParserContext a

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

parseIdentifier :: TaoParser String
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

parseLineBreak :: TaoParser String
parseLineBreak = do
  parseComment <- P.oneOf ["" <$ P.endOfLine, "" <$ P.char ';', fmap snd parseCommentSingleLine]
  _ <- P.whitespaces
  return parseComment

parseInbetween :: String -> String -> TaoParser a -> TaoParser a
parseInbetween open close parser = do
  _ <- P.text open
  _ <- P.whitespaces
  x <- parser
  _ <- P.whitespaces
  _ <- P.text close
  return x

parseCollection :: String -> String -> String -> TaoParser a -> TaoParser [a]
parseCollection open delim close parser = do
  parseInbetween open close (P.oneOf [parseDelimited delim parser, return []])

parseDelimited :: String -> TaoParser a -> TaoParser [a]
parseDelimited delim parser = do
  let delimiter = P.paddedR P.whitespaces (P.text delim)
  x <- parser
  xs <- P.zeroOrMore (P.paddedL delimiter parser)
  _ <- P.maybe' delimiter
  return (x : xs)

-- Concrete Syntax Tree
parseComment :: TaoParser ([Metadata], String)
parseComment = P.oneOf [parseCommentMultiLine, parseCommentSingleLine]

parseCommentSingleLine :: TaoParser ([Metadata], String)
parseCommentSingleLine = do
  state <- P.getState
  _ <- P.char '#'
  P.commit CComment
  _ <- P.spaces
  line <- P.skipTo P.endOfLine
  return ([Location state.name state.pos], dropWhileEnd isSpace line)

parseCommentMultiLine :: TaoParser ([Metadata], String)
parseCommentMultiLine = do
  state <- P.getState
  delim <- P.chain [P.text "#--", P.zeroOrMore (P.char '-')]
  P.commit CCommentMultiLine
  _ <- P.spaces
  line <- P.skipTo parseLineBreak
  error "TODO: parseCommentMultiLine"
  return ([Location state.name state.pos], dropWhileEnd isSpace line)

parseDocString :: TaoParser String -> TaoParser ([Metadata], String)
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
  error "TODO: TaoDocString"

parseLocation :: TaoParser a -> TaoParser (Metadata, a)
parseLocation parser = do
  state <- P.getState
  x <- parser
  _ <- P.spaces
  return (Location state.name state.pos, x)

parseOp :: String -> TaoParser Metadata
parseOp txt = do
  _ <- P.spaces
  (loc, _) <- parseLocation (P.text txt)
  _ <- P.spaces
  return loc

parseExpr :: TaoParser appDelim -> TaoParser TaoExpr
parseExpr delim = do
  let metaOp f m a b = TaoMeta m (f a b)
  let ops =
        [ P.infixR 1 (metaOp TaoOr) (parseOp "|"),
          P.infixR 2 (metaOp TaoAnn) (parseOp ":"),
          P.infixR 3 (metaOp taoEq) (parseOp "=="),
          P.infixR 4 (metaOp taoLt) (parseOp "<"),
          P.infixR 4 (metaOp taoGt) (parseOp ">"),
          P.infixR 5 (metaOp TaoFun) (parseOp "->"),
          P.infixR 6 (metaOp taoAdd) (parseOp "+"),
          P.infixR 6 (metaOp taoSub) (parseOp "-"),
          P.infixR 7 (metaOp taoMul) (parseOp "*"),
          P.infixL 8 (const TaoApp) (void delim),
          P.infixR 9 (metaOp taoPow) (parseOp "^")
        ]
  P.operators 0 ops parseExprAtom

parseExprAtom :: TaoParser TaoExpr
parseExprAtom = do
  (loc, a) <-
    (parseLocation . P.oneOf)
      [ parseName,
        TaoInt <$> P.integer,
        TaoNum <$> P.number,
        parseTuple,
        parseRecord
      ]
  return (TaoMeta loc a)

parseName :: TaoParser TaoExpr
parseName = do
  name <- parseIdentifier
  case name of
    "Type" -> return TaoKind
    "Int" -> return TaoIntType
    "Num" -> return TaoNumType
    x | startsWithUpper x -> do
      args <- P.zeroOrMore parseExprAtom
      return (TaoTag name args)
    _ -> return (TaoVar name)

parseTuple :: TaoParser TaoExpr
parseTuple = do
  let item = parseExpr P.whitespaces
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        item <- parseInbetween "(" ")" (do p <- item; _ <- P.char ','; return p)
        return (TaoTuple [item]),
      do
        items <- parseCollection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [TaoMeta _ item] -> return item -- discard nested metadata (redundant)
          [item] -> return item
          -- General case tuples: () (x, y, ...)
          _ -> return (TaoTuple items)
    ]

parseRecordField :: TaoParser (String, TaoExpr)
parseRecordField = do
  name <- parseIdentifier
  P.commit (CRecordField name)
  _ <- P.whitespaces
  _ <- P.char ':'
  _ <- P.whitespaces
  value <- parseExpr P.whitespaces
  return (name, value)

parseRecord :: TaoParser TaoExpr
parseRecord = do
  fields <- parseCollection "{" "," "}" parseRecordField
  return (TaoRecord fields)

-- Statements
parseStmt :: TaoParser TaoStmt
parseStmt =
  P.oneOf
    [ fmap (\(ts, p, a) -> TaoDef ts p a) parseDefinition,
      parseImport,
      parseTest,
      fmap (uncurry TaoComment) parseComment
    ]

parseDefinition :: TaoParser ([(String, TaoExpr)], TaoExpr, TaoExpr)
parseDefinition = do
  let annotation = do
        x <- parseIdentifier
        _ <- P.spaces
        _ <- P.char ':'
        _ <- P.spaces
        ty <- parseExpr P.spaces
        _ <- parseLineBreak
        return (x, ty)
  types <- P.zeroOrMore annotation
  pattern' <- parseExpr P.spaces
  _ <- P.whitespaces
  _ <- P.char '='
  P.commit CDefinition
  _ <- P.whitespaces
  value <- parseExpr P.spaces
  _ <- parseLineBreak
  return (types, pattern', value)

parseImport :: TaoParser TaoStmt
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
  return (TaoImport name alias exposing)

parseTest :: TaoParser TaoStmt
parseTest = do
  _ <- P.char '>'
  _ <- P.oneOrMore P.space
  P.commit CTest
  expr <- parseExpr P.spaces
  _ <- parseLineBreak
  let typeAssertion (TaoAnn a _) = Just a
      typeAssertion (TaoMeta _ a) = typeAssertion a
      typeAssertion _ = Nothing
  result <-
    P.oneOf
      [ do
          result <- parseExpr P.spaces
          _ <- parseLineBreak
          return result,
        case typeAssertion expr of
          Just a -> return a
          Nothing -> return (TaoTag "True" [])
      ]
  return (TaoTest expr result)

-- File
parseFile :: String -> TaoParser TaoFile
parseFile name = do
  P.commit CFile
  stmts <- P.zeroOrMore parseStmt
  _ <- P.whitespaces
  _ <- P.endOfFile
  return (name, stmts)

parseModule :: String -> TaoModule -> IO TaoModule
parseModule filename mod | filename `elem` map fst mod.files = return mod
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
