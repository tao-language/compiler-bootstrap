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

parseIdentifier :: Parser String
parseIdentifier = do
  let validChars =
        [ P.letter,
          P.digit,
          P.char '_',
          P.paddedR (P.lookaheadNot $ P.char '>') (P.char '-')
        ]
  c <- P.letter
  cs <- P.zeroOrMore (P.oneOf validChars)
  case c : cs of
    name | name `elem` keywords -> P.fail'
    name -> return name

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
  let delimiter = P.paddedR P.whitespaces (P.text delim)
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

parseDocString :: Parser String -> Parser ([C.Metadata], String)
parseDocString delimiter = do
  error "TODO: DocString"

parseLocation :: Parser a -> Parser (C.Metadata, a)
parseLocation parser = do
  state <- P.getState
  x <- parser
  return (C.Location state.name state.pos, x)

parseOp :: String -> Parser C.Metadata
parseOp txt = do
  _ <- P.spaces
  (loc, _) <- parseLocation (P.text txt)
  _ <- P.spaces
  return loc

parseExprAtom :: Parser Expr
parseExprAtom = do
  (loc, a) <-
    (parseLocation . P.oneOf)
      [ do
          name <- parseIdentifier
          case name of
            x | startsWithUpper x -> do
              _ <- P.spaces
              args <- P.zeroOrMore parseExprAtom
              return (Tag name args)
            _ -> return (Var name),
        do
          _ <- P.char '.'
          x <- P.oneOf [parseIdentifier, fmap show P.integer]
          return (TraitFun x),
        Int <$> P.integer,
        Num <$> P.number,
        do
          a <- parseTuple Tuple (parseExpr 0 P.whitespaces)
          case a of
            Meta _ a -> return a
            a -> return a,
        parseRecord,
        parseMatch
      ]
  a <-
    P.oneOf
      [ do
          _ <- P.char '.'
          x <- P.oneOf [parseIdentifier, fmap show P.integer]
          return (Meta loc (Trait a x)),
        return (Meta loc a)
      ]
  _ <- P.spaces
  return a

parseExpr :: Int -> Parser appDelim -> Parser Expr
parseExpr prec delim = do
  let binary op m a b = Meta m (op a b)
  let ops =
        [ P.atom 0 (match []) (P.oneOrMore parseCase),
          P.infixR 1 (binary Or) (parseOp "|"),
          P.infixR 2 (binary Ann) (parseOp ":"),
          P.infixR 3 (binary eq) (parseOp "=="),
          P.infixR 4 (binary lt) (parseOp "<"),
          P.infixR 4 (binary gt) (parseOp ">"),
          P.infixR 5 (binary Fun) (parseOp "->"),
          P.infixR 6 (binary add) (parseOp "+"),
          P.infixR 6 (binary sub) (parseOp "-"),
          P.infixR 7 (binary mul) (parseOp "*"),
          P.infixL 8 (const App) (void delim),
          P.infixR 9 (binary pow) (parseOp "^")
        ]
  P.operators prec ops parseExprAtom

parseTuple :: ([a] -> a) -> Parser a -> Parser a
parseTuple tup item = do
  P.oneOf
    [ do
        -- One-item tuple: (x,)
        item <- parseInbetween "(" ")" (do p <- item; _ <- P.char ','; return p)
        return (tup [item]),
      do
        items <- parseCollection "(" "," ")" item
        case items of
          -- Parenthesized non-tuple: (x)
          [item] -> return item
          -- General case tuples: () (x, y, ...)
          _ -> return (tup items)
    ]

parseRecordField :: Parser (String, Expr)
parseRecordField = do
  (loc, name) <- parseLocation parseIdentifier
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
    (Nothing, Just type') -> return (name, Ann (Meta loc (Var name)) type')
    (Nothing, Nothing) -> return (name, Meta loc (Var name))

parseRecord :: Parser Expr
parseRecord = do
  fields <- parseCollection "{" "," "}" parseRecordField
  return (record fields)

parseCase :: Parser Case
parseCase = do
  p <- parsePattern
  ps <- P.zeroOrMore $ do
    _ <- P.char ','
    _ <- P.whitespaces
    parsePattern
  guard <- P.maybe' $ do
    _ <- P.word "if"
    _ <- P.whitespaces
    parseExpr 1 P.whitespaces
  _ <- P.text "=>"
  P.commit CCase
  _ <- P.whitespaces
  a <- parseExpr 0 P.spaces
  _ <- parseLineBreak
  _ <- P.spaces
  return (Case (p : ps) guard a)

parseMatch :: Parser Expr
parseMatch = do
  _ <- P.word "match"
  P.commit CMatch
  _ <- P.spaces
  args <- do
    arg <- parseExpr 0 P.spaces
    args <- P.zeroOrMore $ do
      _ <- P.char ','
      _ <- P.spaces
      parseExpr 0 P.spaces
    return (arg : args)
  _ <- parseLineBreak
  _ <- P.spaces
  case' <- parseCase
  cases <- P.zeroOrMore (do _ <- P.whitespaces; parseCase)
  return (match args (case' : cases))

parsePattern :: Parser Pattern
parsePattern = do
  (loc, a) <-
    (parseLocation . P.oneOf)
      [ PAny <$ P.char '_',
        do
          name <- parseIdentifier
          case name of
            x | startsWithUpper x -> do
              _ <- P.spaces
              ps <- P.zeroOrMore parsePattern
              return (PTag name ps)
            _ -> return (PVar name),
        PInt <$> P.integer,
        PNum <$> P.number,
        do
          p <- parseTuple PTuple parsePattern
          case p of
            PMeta _ p -> return p
            p -> return p
            -- , parseRecord
      ]
  _ <- P.spaces
  return (PMeta loc a)

-- Statements
parseStmt :: Parser Stmt
parseStmt = do
  comments <- P.zeroOrMore parseComment
  stmt <-
    P.oneOf
      [ -- fmap Define parseDefinition,
        parseImport,
        parseTest
      ]
  return (foldr (MetaStmt . C.Comment) stmt comments)

parseTypeAnnotation :: Parser (String, Expr)
parseTypeAnnotation = do
  x <- parseIdentifier
  _ <- P.spaces
  _ <- P.char ':'
  _ <- P.spaces
  ty <- parseExpr 0 P.spaces
  _ <- parseLineBreak
  _ <- P.whitespaces
  return (x, ty)

parseImport :: Parser Stmt
parseImport = do
  (loc, _) <- parseLocation (P.word "import")
  P.commit CImport
  _ <- P.spaces
  (path, name) <- do
    prefix <- P.oneOf [P.text "@", P.text ""]
    path <- P.zeroOrMore $ do
      path <- parseIdentifier
      _ <- P.char '/'
      return path
    name <- parseIdentifier
    return (prefix ++ intercalate "/" (path ++ [name]), name)
  _ <- P.spaces
  alias <-
    P.oneOf
      [ do
          _ <- P.word "as"
          _ <- P.spaces
          alias <- parseIdentifier
          _ <- P.spaces
          return alias,
        return name
      ]
  exposing <-
    P.oneOf
      [ do
          parseCollection "(" "," ")" $ do
            name <- parseIdentifier
            _ <- P.spaces
            P.oneOf
              [ do
                  _ <- P.word "as"
                  _ <- P.spaces
                  alias <- parseIdentifier
                  return (name, alias),
                return (name, name)
              ],
        return []
      ]
  _ <- parseLineBreak
  _ <- P.whitespaces
  return (Import path alias exposing)

parseTest :: P.Parser ParserContext Stmt
parseTest = do
  _ <- P.char '>'
  _ <- P.oneOrMore P.space
  P.commit CTest
  expr <- parseExpr 0 P.spaces
  _ <- parseLineBreak
  _ <- P.spaces
  result <-
    P.oneOf
      [ do
          result <- parsePattern
          _ <- parseLineBreak
          return result,
        return (PTag "True" [])
      ]
  _ <- P.whitespaces
  return (Test expr result)

parseModule :: String -> Parser Module
parseModule name = do
  P.commit CModule
  stmts <- P.zeroOrMore parseStmt
  _ <- P.whitespaces
  comments <- P.zeroOrMore parseComment
  _ <- P.endOfFile
  return (Module name stmts)

pad :: Int -> String -> String
pad = padWith ' '

padWith :: Char -> Int -> String -> String
padWith fill n text = replicate (n - length text) fill ++ text

slice :: Int -> Int -> [a] -> [a]
slice start end xs =
  xs
    & drop (start - 1)
    & take (end - start)

parseFile :: FilePath -> FilePath -> Package -> IO Package
parseFile _ filename pkg | filename `elem` map (\f -> f.name) pkg.modules = return pkg
parseFile base filename pkg = do
  src <- readFile (base </> filename)
  case P.parse filename (parseModule (dropExtension filename)) src of
    Right (f, _) -> do
      -- TODO: evaluate the module statements
      return (pkg {modules = f : pkg.modules})
    Left P.State {name, pos = (row, col), context} -> do
      let loc = base </> intercalate ":" [name, show row, show col]
      (error . intercalate "\n")
        [ "🛑 " ++ loc ++ ": syntax error " ++ show context,
          "",
          showSnippet (row, col) 3 3 src,
          ""
        ]

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

parsePackage :: FilePath -> IO Package
parsePackage path = do
  let pkg = Package {name = takeBaseName path, modules = []}
  isFile <- doesFileExist path
  case (isFile, path) of
    (True, path) -> do
      let (base, filename) = splitFileName path
      parseFile base filename pkg
    (False, base) -> do
      files <- walkDirectory base ""
      foldM (flip (parseFile base)) pkg files

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
