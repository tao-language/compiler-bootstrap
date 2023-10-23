{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module Parser where

-- https://eyalkalderon.com/blog/nom-error-recovery/
-- https://arxiv.org/pdf/1806.11150.pdf

import Control.Monad (void)
import qualified Data.Char as Char
import Flow ((|>))

newtype Parser ctx a = Parser (State ctx -> Either (State ctx) (a, State ctx))

data State ctx = State
  { remaining :: !String,
    source :: !String,
    row :: !Int,
    col :: !Int,
    index :: !Int,
    context :: ![ctx]
  }
  deriving (Eq, Show)

instance Functor (Parser ctx) where
  fmap :: (a -> b) -> Parser ctx a -> Parser ctx b
  fmap f (Parser p) =
    Parser
      ( \state -> case p state of
          Right (x, state) -> Right (f x, state)
          Left state -> Left state
      )

instance Applicative (Parser ctx) where
  pure :: a -> Parser ctx a
  pure = ok

  (<*>) :: Parser ctx (a -> b) -> Parser ctx a -> Parser ctx b
  parserF <*> parser = do
    f <- parserF
    fmap f parser

instance Monad (Parser ctx) where
  (>>=) :: Parser ctx a -> (a -> Parser ctx b) -> Parser ctx b
  Parser p >>= f =
    Parser
      ( \state -> case p state of
          Right (x, state) -> apply (f x) state
          Left state -> Left state
      )

  return :: a -> Parser ctx a
  return = pure

apply :: Parser ctx a -> State ctx -> Either (State ctx) (a, State ctx)
apply (Parser p) = p

parse :: String -> Parser ctx a -> String -> Either (State ctx) (a, State ctx)
parse source (Parser p) remaining =
  p State {remaining = remaining, source = source, row = 1, col = 1, index = 0, context = []}

ok :: a -> Parser ctx a
ok x = Parser (\state -> Right (x, state))

fail' :: Parser ctx a
fail' = Parser Left

assert :: Bool -> Parser ctx ()
assert True = ok ()
assert False = fail'

if' :: (a -> Bool) -> Parser ctx a -> Parser ctx a
if' check (Parser p) =
  Parser
    ( \state -> case p state of
        Right (x, state) | check x -> Right (x, state)
        Right _ -> Left state
        Left state -> Left state
    )

oneOf :: [Parser ctx a] -> Parser ctx a
oneOf ps = choose (map (,ok) ps)

choose :: [(Parser ctx a, a -> Parser ctx b)] -> Parser ctx b
choose [] = fail'
choose ((Parser p, branch) : branches) =
  Parser
    ( \state -> case p state of
        Right (x, state) -> apply (branch x) state
        Left _ -> apply (choose branches) state
    )

getState :: Parser ctx (State ctx)
getState = Parser (\state -> Right (state, state))

-- Error handling
scope :: ctx -> Parser ctx a -> Parser ctx a
scope ctx (Parser p) =
  Parser
    ( \state -> case p state of
        Right (x, state) -> Right (x, state)
        Left state -> Left state {context = ctx : state.context}
    )

skipTo :: Parser ctx delim -> Parser ctx String
skipTo delim =
  oneOf
    [ "" <$ delim,
      do
        c <- anyChar
        cs <- skipTo delim
        ok (c : cs)
    ]

try :: Parser ctx a -> Parser ctx b -> Parser ctx (Either b a)
try (Parser p) else' =
  Parser
    ( \state -> case p state of
        Right (x, state) -> apply (ok (Right x)) state
        Left state' -> apply (Left <$> else') state {context = state'.context}
    )

-- Single characters
anyChar :: Parser ctx Char
anyChar =
  Parser
    ( \state -> case state.remaining of
        '\n' : src -> Right ('\n', state {remaining = src, index = state.index + 1, row = state.row + 1, col = 1})
        c : src -> Right (c, state {remaining = src, index = state.index + 1, col = state.col + 1})
        "" -> Left state
    )

char :: Char -> Parser ctx Char
char c = if' (== c) anyChar

charNoCase :: Char -> Parser ctx Char
charNoCase c = if' (\c' -> Char.toLower c == Char.toLower c') anyChar

letter :: Parser ctx Char
letter = if' Char.isLetter anyChar

lowercase :: Parser ctx Char
lowercase = if' Char.isLower anyChar

uppercase :: Parser ctx Char
uppercase = if' Char.isUpper anyChar

digit :: Parser ctx Char
digit = if' Char.isDigit anyChar

alphanumeric :: Parser ctx Char
alphanumeric = if' Char.isAlphaNum anyChar

punctuation :: Parser ctx Char
punctuation = if' Char.isPunctuation anyChar

space :: Parser ctx Char
space = if' (`elem` " \t") anyChar

spaces :: Parser ctx String
spaces = zeroOrMore space

whitespace :: Parser ctx Char
whitespace = if' (`elem` " \t\n\r\f\v") anyChar

whitespaces :: Parser ctx String
whitespaces = zeroOrMore whitespace

paddedL :: Parser ctx padding -> Parser ctx a -> Parser ctx a
paddedL padding parser = do
  _ <- padding
  parser

paddedR :: Parser ctx padding -> Parser ctx a -> Parser ctx a
paddedR padding parser = do
  x <- parser
  _ <- padding
  ok x

padded :: Parser ctx padding -> Parser ctx a -> Parser ctx a
padded padding = inbetween padding padding

inbetween :: Parser ctx start -> Parser ctx end -> Parser ctx a -> Parser ctx a
inbetween start end parser = do
  _ <- start
  x <- parser
  _ <- end
  ok x

endOfFile :: Parser ctx ()
endOfFile =
  Parser
    ( \state -> case state.remaining of
        "" -> Right ((), state)
        _ -> Left state
    )

endOfLine :: Parser ctx ()
endOfLine = oneOf [void $ if' (== '\n') anyChar, endOfFile]

-- Sequences
chain :: [Parser ctx a] -> Parser ctx [a]
chain [] = ok []
chain (p : ps) = do
  x <- p
  xs <- chain ps
  ok (x : xs)

text :: String -> Parser ctx String
text str = chain (fmap char str)

textNoCase :: String -> Parser ctx String
textNoCase str = chain (fmap charNoCase str)

concat :: [Parser ctx [a]] -> Parser ctx [a]
concat parsers = fmap Prelude.concat (chain parsers)

maybe' :: Parser ctx a -> Parser ctx (Maybe a)
maybe' parser = oneOf [fmap Just parser, ok Nothing]

zeroOrOne :: Parser ctx a -> Parser ctx [a]
zeroOrOne parser = oneOf [fmap (: []) parser, ok []]

zeroOrMore :: Parser ctx a -> Parser ctx [a]
zeroOrMore = foldR (:) []

oneOrMore :: Parser ctx a -> Parser ctx [a]
oneOrMore parser = do
  x <- parser
  xs <- zeroOrMore parser
  ok (x : xs)

exactly :: Int -> Parser ctx a -> Parser ctx [a]
exactly n parser = chain (replicate n parser)

atLeast :: Int -> Parser ctx a -> Parser ctx [a]
atLeast min parser | min <= 0 = zeroOrMore parser
atLeast min parser = do
  x <- parser
  xs <- atLeast (min - 1) parser
  ok (x : xs)

atMost :: Int -> Parser ctx a -> Parser ctx [a]
atMost max _ | max <= 0 = ok []
atMost max parser =
  oneOf
    [ do
        x <- parser
        xs <- atMost (max - 1) parser
        ok (x : xs),
      ok []
    ]

between :: Int -> Int -> Parser ctx a -> Parser ctx [a]
between min max parser | min <= 0 = atMost max parser
between min max parser = do
  x <- parser
  xs <- between (min - 1) (max - 1) parser
  ok (x : xs)

foldR :: (a -> b -> b) -> b -> Parser ctx a -> Parser ctx b
foldR f final parser =
  oneOf
    [ do
        x <- parser
        y <- foldR f final parser
        ok (f x y),
      ok final
    ]

foldL :: (b -> a -> b) -> b -> Parser ctx a -> Parser ctx b
foldL f initial parser =
  oneOf
    [ do
        x <- parser
        foldL f (f initial x) parser,
      ok initial
    ]

-- Common
integer :: Parser ctx Int
integer = do
  digits <- oneOrMore digit |> notFollowedBy (char '.')
  ok (read digits)

number :: Parser ctx Double
number = do
  int <- oneOrMore digit
  oneOf
    [ do
        fraction <- Parser.concat [text ".", oneOrMore digit]
        ok (read (int ++ fraction)),
      ok (read int)
    ]

wordChar :: Parser ctx Char
wordChar = oneOf [letter, digit, char '_']

wordEnd :: Parser ctx ()
wordEnd = notFollowedBy wordChar (ok ())

word :: String -> Parser ctx String
word txt = do
  x <- text txt
  _ <- wordEnd
  ok x

followedBy :: Parser ctx a -> Parser ctx b -> Parser ctx b
followedBy (Parser lookahead) parser = do
  state0 <- getState
  x <- parser
  Parser
    ( \state -> case lookahead state of
        Right _ -> Right (x, state)
        Left _ -> Left state0
    )

notFollowedBy :: Parser ctx a -> Parser ctx b -> Parser ctx b
notFollowedBy (Parser lookahead) parser = do
  state0 <- getState
  x <- parser
  Parser
    ( \state -> case lookahead state of
        Right _ -> Left state0
        Left _ -> Right (x, state)
    )

subparserPartial :: Parser ctx delim -> Parser ctx a -> Parser ctx a
subparserPartial delim (Parser p) = do
  before <- getState
  _ <- zeroOrMore (do _ <- ok () |> notFollowedBy delim; anyChar)
  after <- getState
  let len = length before.remaining - length after.remaining
  Parser
    ( \state -> do
        (x, _) <- p before {remaining = take len before.remaining}
        Right (x, state)
    )

subparser :: Parser ctx delim -> Parser ctx a -> Parser ctx a
subparser delim parser = subparserPartial delim (do x <- parser; _ <- endOfFile; ok x)

-- TODO: line
-- TODO: date
-- TODO: time
-- TODO: datetime
-- TODO: email
-- TODO: unixPath
-- TODO: windowsPath
-- TODO: uri
-- TODO: IPv4
-- TODO: IPv6
-- PROGRAMMING LANGUAGES
-- TODO: identifier
-- TODO: intBin
-- TODO: intOct
-- TODO: intHex
-- TODO: intExp
-- TODO: numberExp
-- TODO: quotedText
-- TODO: collection : ([a] -> b) -> Parser open -> Parser ctx a -> Parser delim -> Parser close -> Parser ctx b
-- TODO: comment
-- TODO: multiLineComment

-- Operator precedence
-- https://github.com/zesterer/chumsky/blob/main/src/pratt.rs
data Operator ctx a
  = Prefix !Int !(Parser ctx a -> Parser ctx a)
  | InfixL !Int !(a -> Parser ctx a -> Parser ctx a)
  | InfixR !Int !(a -> Parser ctx a -> Parser ctx a)

prefix :: Int -> (op -> a -> a) -> Parser ctx op -> Operator ctx a
prefix prec f op = do
  let parser expr = do
        op <- op
        x <- expr
        ok (f op x)
  Prefix prec parser

suffix :: Int -> (op -> a -> a) -> Parser ctx op -> Operator ctx a
suffix prec f op = do
  let parser x _ = do
        op <- op
        ok (f op x)
  InfixL prec parser

infixL :: Int -> (op -> a -> a -> a) -> Parser ctx op -> Operator ctx a
infixL prec f op = do
  let parser x expr = do
        op <- op
        y <- expr
        ok (f op x y)
  InfixL prec parser

infixR :: Int -> (op -> a -> a -> a) -> Parser ctx op -> Operator ctx a
infixR prec f op = do
  let parser x expr = do
        op <- op
        y <- expr
        ok (f op x y)
  InfixR prec parser

operators :: Int -> [Operator ctx a] -> Parser ctx a -> Parser ctx a
operators prec ops atom = do
  x <- unary prec ops atom
  binary prec ops atom x

unary :: Int -> [Operator ctx a] -> Parser ctx a -> Parser ctx a
unary prec ops atom = do
  let toUnary (Prefix prec' f) | prec <= prec' = do
        f (operators prec' ops atom)
      toUnary _ = fail'
  oneOf (map toUnary ops ++ [atom])

binary :: Int -> [Operator ctx a] -> Parser ctx a -> a -> Parser ctx a
binary prec ops atom x = do
  let toBinary (InfixL prec' f) | prec < prec' = do
        y <- f x (operators prec' ops atom)
        binary prec ops atom y
      toBinary (InfixR prec' f) | prec <= prec' = do
        y <- f x (operators prec' ops atom)
        binary prec ops atom y
      toBinary _ = fail'
  oneOf (map toBinary ops ++ [ok x])
