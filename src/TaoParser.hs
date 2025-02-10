module TaoParser where

import Control.Monad (foldM, void)
import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import Data.Char (isSpace, isUpper, ord)
import Data.Function ((&))
import Data.List (dropWhileEnd, intercalate, isPrefixOf, isSuffixOf, sort)
import Data.List.Split (endsWith)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)
import qualified Parser as P
import System.Directory (doesDirectoryExist, doesFileExist, doesPathExist, findFiles, getDirectoryContents, listDirectory)
import System.Environment (lookupEnv)
import System.FilePath (dropExtension, splitDirectories, splitExtension, splitFileName, splitPath, takeBaseName, takeDirectory, takeExtension, takeFileName, (</>))
import Tao

type Parser a = P.Parser ParserContext a

keywords :: [String]
keywords =
  [ "and",
    "or",
    "xor",
    "if",
    "then",
    "else",
    "match",
    "type",
    "with"
  ]

-- Utilities
startsWithUpper :: String -> Bool
startsWithUpper (c : _) | isUpper c = True
startsWithUpper _ = False

parseNameBase :: Parser Char -> Parser String
parseNameBase firstChar = do
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

parseNameEscaped :: Parser String
parseNameEscaped = do
  _ <- P.char '`'
  name <- P.zeroOrMore $ do
    P.oneOf
      [ fmap (const '`') (P.text "\\`"),
        P.charIf (/= '`')
      ]
  _ <- P.char '`'
  return name

parseNameVar :: Parser String
parseNameVar =
  P.oneOf
    [ parseNameBase P.lowercase,
      parseNameEscaped,
      parseNameOp
    ]

parseNameTag :: Parser String
parseNameTag =
  P.oneOf
    [ parseNameBase P.uppercase,
      P.paddedL (P.char '^') parseNameEscaped
    ]

parseNameOp :: Parser String
parseNameOp = do
  _ <- P.char '('
  _ <- P.whitespaces
  op <-
    P.oneOf
      [ P.word "and",
        P.word "or",
        P.word "xor",
        P.text "==",
        P.text "!=",
        P.text "<=",
        P.text "<",
        P.text ">=",
        P.text ">",
        P.text "+",
        P.text "-",
        P.text "*",
        P.text "//",
        P.text "/",
        P.text "^"
      ]
  _ <- P.whitespaces
  _ <- P.char ')'
  return op

parseNameOpTag :: Parser String
parseNameOpTag = do
  _ <- P.char '('
  _ <- P.whitespaces
  op <-
    P.oneOf
      [ P.text "::"
      ]
  _ <- P.whitespaces
  _ <- P.char ')'
  return op

parseName :: Parser String
parseName =
  P.oneOf
    [ parseNameBase P.letter,
      parseNameOp,
      parseNameOpTag,
      parseNameEscaped
    ]

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
        IntT <$ P.word "Int",
        NumT <$ P.word "Num",
        Err <$ P.word "!error",
        do
          _ <- P.char 'c'
          quote <- P.oneOf [P.char '\'', P.char '"']
          ch <- P.anyChar
          _ <- P.char quote
          return (tag "Char" [Int (ord ch)]),
        Var <$> parseNameVar,
        Tag <$> parseNameTag,
        Var <$> parseNameOp,
        Tag <$> parseNameOpTag,
        Int <$> P.integer,
        Num <$> P.number,
        do
          _ <- P.char '('
          _ <- P.whitespaces
          expr <- parseBlock
          _ <- P.whitespaces
          _ <- P.char ')'
          return expr,
        do
          _ <- P.char '('
          _ <- P.whitespaces
          op <-
            P.oneOf
              [ P.text "::"
              ]
          _ <- P.whitespaces
          _ <- P.char ')'
          return (fun [Var "a", Var "b"] (tag op [Var "a", Var "b"])),
        do
          items <- parseCollection "(" "," ")" (parseExpr 0 P.whitespaces)
          return (and' items),
        do
          items <- parseCollection "[" "," "]" (parseExpr 0 P.whitespaces)
          return (list items),
        do
          quote <- P.oneOf [P.char '\'', P.char '"']
          chars <- P.zeroOrMore $ do
            ch <- P.anyChar & P.if' (/= quote)
            return (tag "Char" [Int (ord ch)])
          _ <- P.char quote
          return (list chars),
        do
          _ <- P.char '%'
          x <- parseNameBase $ P.oneOf [P.letter, P.char '_']
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
        -- do
        --   _ <- P.word "if"
        --   _ <- P.whitespaces
        --   a <- parseExpr 0 P.whitespaces
        --   _ <- P.whitespaces
        --   _ <- P.word "then"
        --   _ <- P.whitespaces
        --   b <- parseExpr 0 P.whitespaces
        --   _ <- P.whitespaces
        --   _ <- P.word "else"
        --   _ <- P.whitespaces
        --   c <- parseExpr 0 P.whitespaces
        --   return (If a b c),
        parseRecord,
        do
          _ <- P.char '.'
          x <- P.oneOf [parseNameVar, fmap show P.integer]
          return (Var ('.' : x)),
        do
          _ <- P.char '.'
          fields <- parseCollection "{" "," "}" parseRecordField
          return (selectFun fields),
        do
          _ <- P.word "with"
          _ <- P.whitespaces
          fields <- parseCollection "{" "," "}" parseRecordField
          return (withFun fields)
      ]
  P.oneOf
    [ do
        _ <- P.spaces
        _ <- P.word "if"
        _ <- P.whitespaces
        cond <- parseExpr 0 P.spaces
        return (If cond a Err),
      do
        _ <- P.char '.'
        x <- P.oneOf [parseNameVar, fmap show P.integer]
        return (App (Var ('.' : x)) a),
      do
        _ <- P.char '.'
        fields <- parseCollection "{" "," "}" parseRecordField
        return (Select a fields),
      do
        _ <- P.spaces
        _ <- P.word "with"
        _ <- P.whitespaces
        fields <- parseCollection "{" "," "}" parseRecordField
        return (With a fields),
      return a
    ]

parseExpr :: Int -> Parser appDelim -> Parser Expr
parseExpr prec delim = do
  let parseOp txt = do
        let breakChars =
              [ P.whitespace,
                P.letter,
                P.digit,
                P.char '_',
                P.char '.',
                P.char '%',
                P.char '@',
                P.char '(',
                P.char '{'
              ]
        _ <- P.text txt
        _ <- P.lookahead (P.oneOf breakChars)
        _ <- P.whitespaces
        return ()
  let ops =
        [ P.atom id $ do
            a <- parseAtom
            case a of
              Tag k -> do
                args <- P.zeroOrMore $ do
                  _ <- delim
                  parseAtom
                _ <- delim
                return (tag k args)
              a -> do
                _ <- delim
                return a,
          -- P.atom 0 (Match []) parseCases,
          P.atom id parseMatch,
          P.prefixWith 0 For $ do
            _ <- P.char '@'
            _ <- P.whitespaces
            xs <- P.zeroOrMore $ do
              x <- parseNameVar
              _ <- P.whitespaces
              return x
            _ <- P.char '.'
            _ <- P.whitespaces
            return xs,
          P.prefix 0 neg (parseOp "-"),
          P.prefixWith 0 (uncurry If) $ do
            _ <- P.word "if"
            _ <- P.whitespaces
            a <- parseExpr 0 P.whitespaces
            _ <- P.whitespaces
            _ <- P.word "then"
            _ <- P.whitespaces
            b <- parseExpr 0 P.whitespaces
            _ <- P.whitespaces
            _ <- P.word "else"
            _ <- P.whitespaces
            return (a, b),
          P.infixR 1 Or (parseOp "|"),
          P.infixR 2 (var2 "and") (parseOp "and"),
          P.infixR 2 (var2 "or") (parseOp "or"),
          P.infixR 2 (var2 "xor") (parseOp "xor"),
          P.infixR 3 (tag2 "::") (parseOp "::"),
          P.infixR 3 Ann (parseOp ":"),
          P.infixR 4 eq (parseOp "=="),
          P.infixR 4 ne (parseOp "!="),
          P.infixR 5 lt (parseOp "<"),
          P.infixR 5 le (parseOp "<="),
          P.infixR 5 gt (parseOp ">"),
          P.infixR 5 ge (parseOp ">="),
          P.infixRWith 6 (\args a -> fun (a : args)) $ do
            args <- P.zeroOrMore $ do
              _ <- P.char ','
              _ <- P.spaces
              parseExpr 7 P.spaces
            _ <- P.text "->"
            _ <- P.whitespaces
            return args,
          P.infixR 7 add (parseOp "+"),
          P.infixR 7 sub (parseOp "-"),
          P.infixR 8 mul (parseOp "*"),
          P.infixR 8 div' (parseOp "/"),
          P.infixR 8 divI (parseOp "//"),
          P.infixL 9 App (void delim),
          P.infixR 10 pow (parseOp "^"),
          P.prefixWith 11 Meta $ do
            C.Comments <$> P.oneOrMore parseComment,
          P.suffixWith 11 Meta $ do
            _ <- P.spaces
            C.TrailingComment <$> parseCommentSingleLine
        ]
  P.precedence ops prec

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

-- parseCases :: Parser [([String], [Expr], Expr)]
-- parseCases = do
--   _ <- P.char '{'
--   _ <- P.whitespaces
--   cases <- P.oneOrMore $ do
--     _ <- P.char '|'
--     _ <- P.whitespaces
--     xs <-
--       P.oneOf
--         [ do
--             _ <- P.char '@'
--             _ <- P.whitespaces
--             xs <- P.zeroOrMore $ do
--               x <- parseNameVar
--               _ <- P.whitespaces
--               return x
--             _ <- P.char '.'
--             _ <- P.whitespaces
--             return xs,
--           return []
--         ]
--     p <- parseExpr 7 P.whitespaces
--     ps <- P.zeroOrMore $ do
--       _ <- P.char ','
--       _ <- P.whitespaces
--       parseExpr 7 P.whitespaces
--     _ <- P.word "->"
--     _ <- P.whitespaces
--     b <- parseExpr 2 P.whitespaces
--     _ <- P.whitespaces
--     return (xs, p : ps, b)
--   _ <- P.whitespaces
--   _ <- P.char '}'
--   return cases

parseMatch :: Parser Expr
parseMatch = do
  args <-
    P.oneOf
      [ do
          _ <- P.word "match"
          P.commit CMatch
          _ <- P.spaces
          args <-
            P.oneOf
              [ do
                  arg <- parseExpr 1 P.spaces
                  _ <- P.spaces
                  args <- P.zeroOrMore $ do
                    _ <- P.char ','
                    _ <- P.spaces
                    arg <- parseExpr 1 P.spaces
                    _ <- P.spaces
                    return arg
                  return (arg : args),
                return []
              ]
          _ <- P.whitespaces
          return args,
        return []
      ]
  _ <- P.char '{'
  _ <- P.whitespaces
  P.lookahead (P.char '|')
  P.commit CMatch
  cases <- P.oneOrMore $ do
    _ <- P.char '|'
    _ <- P.whitespaces
    (xs, ps) <-
      P.oneOf
        [ do
            _ <- P.char '@'
            _ <- P.whitespaces
            xs <- P.zeroOrMore $ do
              x <- parseNameVar
              _ <- P.whitespaces
              return x
            _ <- P.char '.'
            _ <- P.whitespaces
            p <- parseExpr 7 P.whitespaces
            ps <- P.zeroOrMore $ do
              _ <- P.char ','
              _ <- P.whitespaces
              parseExpr 7 P.whitespaces
            return (xs, p : ps),
          do
            p <- parseExpr 7 P.whitespaces
            ps <- P.zeroOrMore $ do
              _ <- P.char ','
              _ <- P.whitespaces
              parseExpr 7 P.whitespaces
            return (freeVars (and' (p : ps)), p : ps)
        ]
    _ <- P.word "->"
    _ <- P.whitespaces
    b <- parseExpr 2 P.whitespaces
    _ <- P.whitespaces
    return (xs, ps, b)
  _ <- P.whitespaces
  _ <- P.char '}'
  return (Match args cases)

parseBlock :: Parser Expr
parseBlock = do
  P.oneOf
    [ do
        def <- parseDef "="
        _ <- P.spaces
        _ <- parseLineBreak
        _ <- P.whitespaces
        Let def <$> parseBlock,
      do
        def <- parseDef "<-"
        _ <- P.spaces
        _ <- parseLineBreak
        _ <- P.whitespaces
        Bind def <$> parseBlock,
      parseExpr 0 P.spaces
    ]

-- Statements
parseStmt :: Parser Stmt
parseStmt = do
  comments <- P.zeroOrMore parseComment
  stmt <-
    P.oneOf
      [ parseImport,
        Def <$> parseDef "=",
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
            name <- parseName
            _ <- P.spaces
            P.oneOf
              [ do
                  _ <- P.word "as"
                  _ <- P.spaces
                  alias <- parseName
                  return (name, alias),
                return (name, name)
              ],
        return []
      ]
  return (Import path alias exposing)

parseDef :: String -> Parser (Expr, Expr)
parseDef op = do
  typeAnnotation <- P.maybe' $ do
    _ <- P.char ':'
    P.commit CDefinition
    _ <- P.spaces
    t <- parseExpr 0 P.spaces
    _ <- P.spaces
    _ <- parseLineBreak
    _ <- P.whitespaces
    return (`Ann` t)
  a <- parseExpr 0 P.spaces
  _ <- P.spaces
  _ <- P.word op
  P.commit CDefinition
  _ <- P.whitespaces
  b <- parseExpr 0 P.spaces
  case typeAnnotation of
    Just ann -> return (ann a, b)
    Nothing -> return (a, b)

parseTypeDefAlt :: Parser (Expr, Maybe Type)
parseTypeDefAlt = do
  a <- parseExpr 2 P.spaces
  _ <- P.spaces
  mb <- P.maybe' $ do
    _ <- P.text "=>"
    _ <- P.whitespaces
    parseExpr 2 P.spaces
  return (a, mb)

parseTypeDef :: Parser (String, [Expr], [(Expr, Maybe Type)])
parseTypeDef = do
  _ <- P.word "type"
  _ <- P.whitespaces
  name <- parseNameTag
  _ <- P.whitespaces
  args <- P.zeroOrMore $ do
    arg <- parseAtom
    _ <- P.whitespaces
    return arg
  _ <- P.char '='
  _ <- P.whitespaces
  _ <- P.maybe' $ do
    _ <- P.char '|'
    P.whitespaces
  alt <- parseTypeDefAlt
  alts <- P.zeroOrMore $ do
    _ <- P.whitespaces
    _ <- P.char '|'
    _ <- P.whitespaces
    parseTypeDefAlt
  return (name, args, alt : alts)

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
  s <- P.getState
  _ <- P.char '>'
  _ <- P.oneOrMore P.space
  P.commit CTest
  expr <- parseExpr 0 P.spaces
  result <-
    P.oneOf
      [ do
          _ <- P.spaces
          _ <- parseLineBreak
          _ <- P.spaces
          parseExpr 0 P.spaces,
        return (Tag "True")
      ]
  return (Test (UnitTest s.filename s.pos name expr result))

parseModule :: String -> Parser Module
parseModule name = do
  P.commit CModule
  _ <- P.whitespaces
  stmts <- P.zeroOrMore parseStmt
  _ <- P.whitespaces
  comments <- P.zeroOrMore parseComment
  _ <- P.endOfFile
  return (name, stmts)

srcPath :: FilePath -> IO [FilePath]
srcPath path = do
  home <- lookupEnv "HOME"
  let homePath = fromMaybe "." home </> ".tao" </> "src"
  return [takeDirectory path, homePath]
