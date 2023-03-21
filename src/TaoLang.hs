module TaoLang where

import Control.Monad (void)
import qualified Core
import Data.List (sort)
import Flow ((|>))
import Parser
import System.Directory
import System.FilePath ((</>))
import Tao

-- {- TODO:
-- * Type definitions:
--     type Bool = True | False
--     type Vec n a
--       = Nil : Vec 0 a
--       | Cons a (Vec n a): Vec (n + 1) a
-- * Parse until end of file on parseExpr, parseDefs, etc
--   - Maybe get rid of `parse*` or `load*` (?)
-- * AST type
-- * Parse `Err` message
-- -}

-- data Error
--   = SyntaxError !ParserError
--   | TypeError !Core.TypeError
--   deriving (Eq, Show)

-- loadExpr :: String -> IO Expr
-- loadExpr text = case parseExpr text of
--   Right expr -> return expr
--   Left err -> fail ("❌ " ++ show err)

-- loadDefinitions :: String -> IO [Definition]
-- loadDefinitions text = case parseDefinitions text of
--   Right defs -> return defs
--   Left err -> fail ("❌ " ++ show err)

-- f :: Bool -> Int
-- f True = 1

-- loadBlock :: String -> IO ([Definition], Expr)
-- loadBlock text = case parseBlock text of
--   Right (env, expr) -> return (env, expr)
--   Left err -> fail ("❌ " ++ show err)

-- loadFile :: FilePath -> FilePath -> IO Env
-- loadFile moduleName fileName = do
--   src <- readFile (moduleName </> fileName)
--   defs <- loadDefinitions src
--   return (concatMap unpack defs)

-- loadModule :: FilePath -> IO Env
-- loadModule moduleName = do
--   files <- listDirectory moduleName
--   envs <- mapM (loadFile moduleName) (sort files)
--   return (concat envs)

-- parse :: String -> Parser a -> Either Error a
-- parse src parser = case Parser.parse src parser of
--   Right x -> Right x
--   Left err -> Left (SyntaxError err)

-- -- TODO: make sure there are no unparsed inputs
-- parseExpr :: String -> Either Error Expr
-- parseExpr src = TaoLang.parse src (expression 0 "")

-- -- TODO: make sure there are no unparsed inputs
-- parseDefinitions :: String -> Either Error [Definition]
-- parseDefinitions src = TaoLang.parse src (zeroOrMore (definition ""))

-- -- TODO: make sure there are no unparsed inputs
-- parseBlock :: String -> Either Error ([Definition], Expr)
-- parseBlock src = TaoLang.parse src (block "")

-- eval :: Env -> Expr -> Either Error (Expr, Type)
-- eval env expr = case infer env expr of
--   Right (type', _) -> Right (reduce env expr, type')
--   Left err -> Left (TypeError err)

-- keyword :: a -> String -> Parser a
-- keyword x txt = do
--   _ <- text txt |> notFollowedBy (oneOf [void letter, void number, void (char '_'), void (char '\'')])
--   succeed x

-- identifier :: Parser Char -> Parser String
-- identifier firstChar = do
--   -- TODO: support `-` and other characters, maybe URL-like names
--   maybeUnderscore <- maybe' (char '_')
--   c1 <- firstChar
--   cs <- zeroOrMore (oneOf [alphanumeric, char '_'])
--   case maybeUnderscore of
--     Just c0 -> succeed (c0 : c1 : cs)
--     Nothing -> succeed (c1 : cs)

-- comment :: Parser String
-- comment = do
--   -- TODO: support multi-line comments
--   _ <- text "--"
--   _ <- maybe' space
--   until' (== '\n') anyChar

-- emptyLine :: Parser String
-- emptyLine = do
--   _ <- zeroOrMore space
--   comment' <- oneOf [comment, succeed ""]
--   _ <- char '\n'
--   succeed comment'

-- newLine :: String -> Parser [String]
-- newLine indent = do
--   _ <- char '\n'
--   comments <- zeroOrMore emptyLine
--   _ <- text indent
--   succeed comments

-- maybeNewLine :: String -> Parser String
-- maybeNewLine indent =
--   oneOf
--     [ do
--         _ <- newLine indent
--         extra <- oneOrMore space
--         succeed (indent ++ extra),
--       succeed indent
--     ]

-- token :: Parser a -> Parser a
-- token parser = do
--   x <- parser
--   _ <- zeroOrMore space
--   succeed x

-- err :: Parser Expr
-- err = do
--   _ <- token (keyword () "@error")
--   succeed (Err "")

-- typT :: Parser Expr
-- typT = token (keyword TypT "Type")

-- nilT :: Parser Expr
-- nilT = token (keyword NilT "Nil")

-- nil :: Parser Expr
-- nil = do
--   _ <- token (char '(')
--   _ <- token (char ')')
--   succeed Nil

-- intT :: Parser Expr
-- intT = token (keyword IntT "Int")

-- int :: Parser Expr
-- int = do
--   i <- token integer
--   succeed (Int i)

-- numT :: Parser Expr
-- numT = token (keyword NumT "Num")

-- num :: Parser Expr
-- num = do
--   n <- token number
--   succeed (Num n)

-- ctr :: Parser Expr
-- ctr = do
--   tc <- identifier uppercase
--   _ <- char '.'
--   k <- token (identifier uppercase)
--   succeed (Ctr tc k)

-- var :: Parser Expr
-- var = do
--   let reserved = ["as", "if", "then", "else"]
--   x <- token (identifier letter)
--   assert (x `notElem` reserved) "reserved keyword"
--   succeed (Var x)

-- term :: Parser Expr
-- term = oneOf [err, typT, nilT, nil, intT, int, numT, num, ctr, var]

-- for' :: Parser [String]
-- for' = do
--   _ <- token (keyword () "@forall")
--   xs <- oneOrMore (token (identifier lowercase))
--   _ <- token (char '.')
--   succeed xs

-- sumT :: String -> Parser Expr
-- sumT indent = do
--   let alt :: Parser (String, Type)
--       alt = do
--         k <- token (identifier uppercase)
--         _ <- token (char ':')
--         t <- expression 0 indent
--         succeed (k, t)

--   _ <- token (keyword () "@type")
--   ts <- token (identifier uppercase)
--   alts <- collection (token (char '{')) alt (token (char ',')) (token (char '}'))
--   succeed (SumT ts alts)

-- and_ :: String -> Parser Expr
-- and_ indent = do
--   items <-
--     collection
--       (token (char '('))
--       (block indent)
--       (token (char ','))
--       (token (char ')'))
--   succeed (and' (map (uncurry let') items))

-- ifElse :: String -> Parser (Expr -> Expr)
-- ifElse indent = do
--   _ <- token (keyword () "if")
--   cond <- expression 0 indent
--   _ <- token (keyword () "then")
--   then' <- expression 0 indent
--   _ <- token (keyword () "else")
--   succeed (IfElse cond then')

-- lam' :: String -> Parser [Pattern]
-- lam' indent = do
--   _ <- token (char '\\')
--   ps <- oneOrMore (pattern' 0 indent)
--   _ <- token (text "->")
--   succeed ps

-- expression :: Int -> String -> Parser Expr
-- expression prec indent = do
--   let operator op = token (text op)
--   withOperators
--     [ constant term,
--       constant (sumT indent),
--       constant (and_ indent),
--       prefixOp 3 for for',
--       prefixOp 3 lam (lam' indent),
--       prefixOp 3 id (ifElse indent),
--       prefix 8 TypeOf (token (keyword () "@typeOf"))
--     ]
--     [ infixR 1 Or (operator "|"),
--       infixR 2 Ann (operator ":"),
--       infixR 3 FunT (operator "->"),
--       infixL 4 Lt (operator "<"),
--       infixL 5 Add (operator "+"),
--       infixL 5 Sub (operator "-"),
--       infixL 6 Mul (operator "*"),
--       infixL 7 App (succeed ())
--     ]
--     prec

-- anyP :: Parser Pattern
-- anyP = do
--   _ <- token (keyword () "_")
--   succeed AnyP

-- varP :: Parser Pattern
-- varP = do
--   x <- identifier lowercase
--   oneOf
--     [ do
--         _ <- token (char '\'')
--         succeed (EqP (Var x)),
--       do
--         _ <- zeroOrMore space
--         succeed (VarP x)
--     ]

-- termP :: String -> Parser Pattern
-- termP indent = oneOf [anyP, varP, fmap EqP term, andP' indent]

-- asP :: Parser String
-- asP = do
--   _ <- token (keyword () "as")
--   token (identifier lowercase)

-- ifP :: String -> Parser Expr
-- ifP indent = do
--   _ <- token (keyword () "if")
--   expression 2 indent

-- andP' :: String -> Parser Pattern
-- andP' indent = do
--   ps <-
--     collection
--       (token (char '('))
--       (pattern' 0 indent)
--       (token (char ','))
--       (token (char ')'))
--   succeed (andP ps)

-- pattern' :: Int -> String -> Parser Pattern
-- pattern' prec indent = do
--   let operator op = token (text op)
--   withOperators
--     [ constant (termP indent)
--     ]
--     [ infixR 1 OrP (operator "|"),
--       infixR 2 AnnP (operator ":"),
--       postfixOp 3 (flip AsP) asP,
--       postfixOp 3 (flip IfP) (ifP indent),
--       infixL 4 AppP (succeed ())
--     ]
--     prec

-- definition :: String -> Parser Definition
-- definition indent = do
--   let typeAnnotation :: Parser (String, Type)
--       typeAnnotation = do
--         x <- token (identifier letter)
--         _ <- token (char ':')
--         t <- expression 0 indent
--         succeed (x, t)

--   let branch :: Parser ([Pattern], Expr)
--       branch = do
--         ps <- oneOrMore (termP indent)
--         _ <- token (char '=')
--         a <- expression 0 indent
--         succeed (ps, a)

--   let rules :: Parser (Pattern, Expr)
--       rules = do
--         x <- token (identifier letter)
--         r <- branch
--         rs <- zeroOrMore (do _ <- newLine indent; _ <- token (text x); branch)
--         succeed (VarP x, Match (r : rs))

--   let unpack :: Parser (Pattern, Expr)
--       unpack = do
--         p <- termP indent
--         _ <- token (char '=')
--         a <- expression 0 indent
--         succeed (p, a)

--   def <-
--     oneOf
--       [ do
--           (x, t) <- typeAnnotation
--           _ <- token (char '=')
--           a <- expression 0 indent
--           succeed ([(x, t)], VarP x, a),
--         do
--           types <- zeroOrMore (do ann <- typeAnnotation; _ <- newLine indent; succeed ann)
--           (p, a) <- oneOf [rules, unpack]
--           succeed (types, p, a)
--       ]
--   _ <- oneOf [void (newLine indent), void (token (char ';')), endOfFile]
--   succeed def

-- block :: String -> Parser ([Definition], Expr)
-- block indent = do
--   defs <- zeroOrMore (definition indent)
--   a <- expression 0 indent
--   succeed (defs, a)
