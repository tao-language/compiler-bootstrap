module TaoParser where

import Control.Monad (foldM, void)
import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import Data.Char (isSpace, isUpper)
import Data.Function ((&))
import Data.List (dropWhileEnd, intercalate, sort)
import qualified Parser as P
import System.Directory (doesDirectoryExist, doesFileExist, findFiles, listDirectory)
import System.FilePath (dropExtension, splitDirectories, splitFileName, splitPath, takeBaseName, takeFileName, (</>))
import Tao

type Parser a = P.Parser ParserContext a

data ParserContext
  = CModule
  | CDefinition
  | CImport
  | CTest
  | CComment
  | CCommentMultiLine
  | CDocString
  | CRecordField String
  | CCase
  | CMatch
  deriving (Eq, Show)

data SyntaxError
  = SyntaxError
  { filename :: String,
    row :: Int,
    col :: Int,
    sourceCode :: String,
    context :: [ParserContext]
  }
  deriving (Eq)

instance Show SyntaxError where
  show :: SyntaxError -> String
  show e = do
    let loc = intercalate ":" [e.filename, show e.row, show e.col]
    intercalate
      "\n"
      [ "🛑 " ++ loc ++ ": syntax error " ++ show e.context,
        "",
        showSnippet (e.row, e.col) 3 3 e.sourceCode,
        ""
      ]

keywords :: [String]
keywords =
  [ "type",
    "if",
    "else",
    "match"
  ]

-- Utilities
startsWithUpper :: String -> Bool
startsWithUpper (c : _) | isUpper c = True
startsWithUpper _ = False

parseName :: Parser Char -> Parser String
parseName firstChar = do
  let validChars =
        [ P.letter,
          P.digit,
          P.char '_',
          P.paddedR (P.lookaheadNot $ P.char '>') (P.char '-')
        ]
  c <- firstChar
  cs <- P.zeroOrMore (P.oneOf validChars)
  case c : cs of
    name | name `elem` keywords -> P.fail'
    name -> return name

parseNameVar :: Parser String
parseNameVar = parseName P.lowercase

parseNameTag :: Parser String
parseNameTag = parseName P.uppercase

parseLineBreak :: Parser String
parseLineBreak = do
  P.oneOf
    [ "" <$ P.endOfLine,
      "" <$ P.char ';',
      "" <$ P.lookahead (P.charIf (`elem` [')', '}', ']'])),
      parseCommentSingleLine
    ]

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
  let delimiter = P.padded P.whitespaces (P.text delim)
  x <- parser
  xs <- P.zeroOrMore (P.paddedL delimiter parser)
  _ <- P.maybe' delimiter
  return (x : xs)

-- Concrete Syntax Tree
parseComment :: Parser String
parseComment = P.oneOf [parseCommentMultiLine, parseCommentSingleLine]

parseCommentSingleLine :: Parser String
parseCommentSingleLine = do
  _ <- P.char '#'
  P.commit CComment
  _ <- P.spaces
  line <- P.skipTo P.endOfLine
  _ <- P.whitespaces
  return (dropWhileEnd isSpace line)

parseCommentMultiLine :: Parser String
parseCommentMultiLine = do
  delim <- P.chain [P.text "#--", P.zeroOrMore (P.char '-')]
  P.commit CCommentMultiLine
  _ <- P.spaces
  line <- P.skipTo parseLineBreak
  _ <- P.whitespaces
  error "TODO: parseCommentMultiLine"
  return (dropWhileEnd isSpace line)

parseAtom :: Parser Expr
parseAtom = do
  a <-
    P.oneOf
      [ Any <$ P.word "_",
        IntType <$ P.word "Int",
        NumType <$ P.word "Num",
        Var <$> parseNameVar,
        do
          name <- parseNameTag
          _ <- P.spaces
          args <- P.zeroOrMore parseAtom
          return (tag name args),
        do
          _ <- P.char '.'
          x <- P.oneOf [parseNameVar, fmap show P.integer]
          return (traitFun x),
        Int <$> P.integer,
        Num <$> P.number,
        do
          items <- parseCollection "(" "," ")" (parseExpr 0 P.whitespaces)
          return (and' items),
        do
          _ <- P.char '$'
          x <- parseName $ P.oneOf [P.letter, P.char '_']
          args <-
            P.oneOf
              [ do
                  _ <- P.spaces
                  P.oneOf
                    [ parseCollection "(" "," ")" (parseExpr 0 P.whitespaces),
                      return []
                    ],
                return []
              ]
          return (Call x args),
        parseMatch,
        parseRecord
      ]
  P.oneOf
    [ do
        _ <- P.char '.'
        x <- P.oneOf [parseNameVar, fmap show P.integer]
        return (Trait a x),
      return a
    ]

parseExpr :: Int -> Parser appDelim -> Parser Expr
parseExpr prec delim = do
  let parseOp txt = do
        _ <- P.whitespaces
        _ <- P.text txt
        _ <- P.whitespaces
        return ()
  let ops =
        [ P.atom 0 (Match []) parseCases,
          P.prefix 0 For $ do
            _ <- P.char '@'
            _ <- P.whitespaces
            xs <- P.zeroOrMore $ do
              x <- parseNameVar
              _ <- P.whitespaces
              return x
            _ <- P.char '.'
            _ <- P.whitespaces
            return xs,
          P.infixR 1 (const Or) (parseOp "|"),
          P.infixR 2 (const Ann) (parseOp ":"),
          P.infixR 3 (const eq) (parseOp "=="),
          P.infixR 4 (const lt) (parseOp "<"),
          P.infixR 4 (const gt) (parseOp ">"),
          P.infixR 5 (const Fun) (parseOp "->"),
          P.infixR 6 (const add) (parseOp "+"),
          P.infixR 6 (const sub) (parseOp "-"),
          P.infixR 7 (const mul) (parseOp "*"),
          P.infixL 8 (const App) (void delim),
          P.infixR 9 (const pow) (parseOp "^"),
          P.prefix 10 (const neg) (parseOp "-")
        ]
  P.operators prec ops $ do
    a <- parseAtom
    _ <- P.spaces
    return a

parseRecordField :: Parser (String, Expr)
parseRecordField = do
  name <- parseNameVar
  P.commit (CRecordField name)
  _ <- P.spaces
  maybeType <- P.maybe' $ do
    _ <- P.whitespaces
    _ <- P.char ':'
    _ <- P.whitespaces
    parseExpr 0 P.whitespaces
  maybeValue <- P.maybe' $ do
    _ <- P.whitespaces
    _ <- P.char '='
    _ <- P.whitespaces
    parseExpr 0 P.whitespaces
  case (maybeValue, maybeType) of
    (Just value, Just type') -> return (name, Ann value type')
    (Just value, Nothing) -> return (name, value)
    (Nothing, Just type') -> return (name, Ann (Var name) type')
    (Nothing, Nothing) -> return (name, Var name)

parseRecord :: Parser Expr
parseRecord = do
  fields <- parseCollection "{" "," "}" parseRecordField
  return (Record fields)

parseCases :: Parser [Expr]
parseCases = do
  _ <- P.char '{'
  _ <- P.whitespaces
  cases <- P.oneOrMore $ do
    _ <- P.char '|'
    _ <- P.whitespaces
    a <- parseExpr 2 P.spaces
    _ <- P.whitespaces
    return a
  _ <- P.whitespaces
  _ <- P.char '}'
  return cases

parseMatch :: Parser Expr
parseMatch = do
  _ <- P.word "match"
  P.commit CMatch
  _ <- P.spaces
  args <-
    P.oneOf
      [ do
          arg <- parseAtom
          _ <- P.spaces
          args <- P.zeroOrMore $ do
            _ <- P.char ','
            _ <- P.spaces
            arg <- parseAtom
            _ <- P.spaces
            return arg
          return (arg : args),
        return []
      ]
  _ <- P.whitespaces
  Match args <$> parseCases

-- Statements
parseStmt :: Parser Stmt
parseStmt = do
  comments <- P.zeroOrMore parseComment
  stmt <-
    P.oneOf
      [ parseImport,
        Def <$> parseDef,
        TypeDef <$> parseTypeDef,
        parseTest
      ]
  _ <- P.spaces
  _ <- parseLineBreak
  _ <- P.whitespaces
  return stmt

parseModulePath :: Parser (String, String)
parseModulePath = do
  pkg <- parseNameVar
  path <- P.zeroOrMore $ do
    _ <- P.char '/'
    name <- parseNameVar
    return ('/' : name)
  let modulePath = concat (pkg : path)
  return (modulePath, takeBaseName modulePath)

parseImport :: Parser Stmt
parseImport = do
  _ <- P.word "import"
  P.commit CImport
  _ <- P.spaces
  (path, alias) <- parseModulePath
  _ <- P.spaces
  exposing <-
    P.oneOf
      [ do
          parseCollection "(" "," ")" $ do
            name <- parseName P.letter
            _ <- P.spaces
            P.oneOf
              [ do
                  _ <- P.word "as"
                  _ <- P.spaces
                  alias <- parseName P.letter
                  return (name, alias),
                return (name, name)
              ],
        return []
      ]
  return (Import path alias exposing)

parseDef :: Parser (Expr, Expr)
parseDef = do
  typeAnnotation <- P.maybe' $ do
    _ <- P.char ':'
    _ <- P.spaces
    t <- parseExpr 0 P.spaces
    _ <- parseLineBreak
    _ <- P.whitespaces
    return (`Ann` t)
  a <- parseExpr 0 P.spaces
  _ <- P.spaces
  _ <- P.char '='
  _ <- P.whitespaces
  b <- parseExpr 0 P.spaces
  case typeAnnotation of
    Just ann -> return (ann a, b)
    Nothing -> return (a, b)

parseTypeDef :: Parser (String, [Expr], Expr)
parseTypeDef = do
  _ <- P.word "type"
  _ <- P.spaces
  name <- parseNameTag
  _ <- P.spaces
  args <- P.zeroOrMore $ do
    arg <- parseExpr 0 P.space
    _ <- P.spaces
    return arg
  _ <- P.char '='
  _ <- P.whitespaces
  body <- parseExpr 0 P.space
  return (name, args, body)

parseTest :: Parser Stmt
parseTest = do
  name <-
    P.oneOf
      [ do
          _ <- P.text "--"
          _ <- P.spaces
          P.skipTo P.endOfLine,
        return ""
      ]
  _ <- P.char '>'
  _ <- P.oneOrMore P.space
  P.commit CTest
  expr <- parseExpr 0 P.spaces
  result <-
    P.oneOf
      [ do
          _ <- parseLineBreak
          _ <- P.spaces
          parseExpr 0 P.spaces,
        return (Tag "True")
      ]
  return (Test name expr result)

pad :: Int -> String -> String
pad = padWith ' '

padWith :: Char -> Int -> String -> String
padWith fill n text = replicate (n - length text) fill ++ text

slice :: Int -> Int -> [a] -> [a]
slice start end xs =
  xs
    & drop (start - 1)
    & take (end - start)

showSnippet :: (Int, Int) -> Int -> Int -> String -> String
showSnippet (row, col) before after src = do
  let divider = "| "
  let rowMark = "* "
  let colMark = "^"
  let start = max 1 (row - before)
  let padding = max (length $ show start) (length $ show (row + after))
  let showLine i line = pad (padding + length rowMark) (show i) ++ divider ++ line
  let linesBefore =
        lines src
          & slice start row
          & zipWith showLine [start ..]
  let highlight =
        lines src
          & slice row (row + 1)
          & map (\line -> pad padding (rowMark ++ show row) ++ divider ++ line)
          & (++ [replicate (col + padding + length divider + 1) ' ' ++ colMark])
  let linesAfter =
        lines src
          & slice (row + 1) (row + after + 1)
          & zipWith showLine [row + 1 ..]
  intercalate "\n" (linesBefore ++ highlight ++ linesAfter)

parseModule :: String -> Parser Module
parseModule name = do
  P.commit CModule
  stmts <- P.zeroOrMore parseStmt
  _ <- P.whitespaces
  comments <- P.zeroOrMore parseComment
  _ <- P.endOfFile
  return (name, stmts)

load :: FilePath -> [FilePath] -> IO (Package, [SyntaxError])
load path dependencies = do
  let pkg = (takeBaseName path, [])
  foldM (flip loadPackage) (pkg, []) (path : dependencies)

loadPackage :: FilePath -> (Package, [SyntaxError]) -> IO (Package, [SyntaxError])
loadPackage path (pkg, errs) = do
  isFile <- doesFileExist path
  case (isFile, path) of
    (True, path) -> do
      let (base, filename) = splitFileName path
      loadModule base filename (pkg, errs)
    (False, base) -> do
      files <- walkDirectory base ""
      foldM (flip (loadModule base)) (pkg, errs) files

loadModule :: FilePath -> FilePath -> (Package, [SyntaxError]) -> IO (Package, [SyntaxError])
loadModule _ filename (pkg, errs) | filename `elem` map fst (snd pkg) = do
  return (pkg, errs)
loadModule base filename (pkg, errs) = do
  src <- readFile (base </> filename)
  let modName = takeBaseName base ++ '/' : dropExtension filename
  case P.parse filename (parseModule modName) src of
    Right (mod, _) -> do
      return (second (mod :) pkg, [])
    Left P.State {name, pos = (row, col), context} -> do
      let err =
            SyntaxError
              { filename = base </> name,
                row = row,
                col = col,
                sourceCode = src,
                context = context
              }
      return (pkg, err : errs)

walkDirectory :: FilePath -> FilePath -> IO [FilePath]
walkDirectory base path = do
  let walk path = do
        isDir <- doesDirectoryExist (base </> path)
        if isDir
          then walkDirectory base path
          else return [path]
  paths <- listDirectory (base </> path)
  files <- mapM walk (sort paths)
  return (map (path </>) (concat files))
