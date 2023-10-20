{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module Parser where

-- https://eyalkalderon.com/blog/nom-error-recovery/
-- https://arxiv.org/pdf/1806.11150.pdf

import Control.Monad (void)
import Data.Bifunctor (Bifunctor (first))
import qualified Data.Char as Char
import Flow ((|>))

newtype Parser err a = Parser (State err -> Either (State err) (a, State err))

data State err = State
  { remaining :: !String,
    index :: !Int,
    row :: !Int,
    col :: !Int,
    errors :: ![err]
  }
  deriving (Eq, Show)

instance Functor (Parser err) where
  fmap :: (a -> b) -> Parser err a -> Parser err b
  fmap f (Parser p) =
    Parser
      ( \state -> case p state of
          Right (x, state) -> Right (f x, state)
          Left state -> Left state
      )

instance Applicative (Parser err) where
  pure :: a -> Parser err a
  pure = ok

  (<*>) :: Parser err (a -> b) -> Parser err a -> Parser err b
  parserF <*> parser = do
    f <- parserF
    fmap f parser

instance Monad (Parser err) where
  (>>=) :: Parser err a -> (a -> Parser err b) -> Parser err b
  Parser p >>= f =
    Parser
      ( \state -> case p state of
          Right (x, state) -> apply (f x) state
          Left state -> Left state
      )

  return :: a -> Parser err a
  return = pure

apply :: Parser err a -> State err -> Either (State err) (a, State err)
apply (Parser p) = p

parse :: Parser err a -> String -> Either (State err) (a, State err)
parse (Parser p) remaining =
  p State {remaining = remaining, index = 0, row = 1, col = 1, errors = []}

ok :: a -> Parser err a
ok x = Parser (\state -> Right (x, state))

fail' :: Parser err a
fail' = Parser Left

assert :: Bool -> Parser err ()
assert True = ok ()
assert False = fail'

if' :: (a -> Bool) -> Parser err a -> Parser err a
if' check (Parser p) =
  Parser
    ( \state -> case p state of
        Right (x, state) | check x -> Right (x, state)
        Right _ -> Left state
        Left state -> Left state
    )

oneOf :: [Parser err a] -> Parser err a
oneOf ps = choose (map (,ok) ps)

choose :: [(Parser err a, a -> Parser err b)] -> Parser err b
choose [] = fail'
choose ((Parser p, branch) : branches) =
  Parser
    ( \state -> case p state of
        Right (x, state) -> apply (branch x) state
        Left state -> apply (choose branches) state
    )

getState :: Parser err (State err)
getState = Parser (\state -> Right (state, state))

-- Error handling
expect :: err -> Parser err a -> Parser err a
expect err (Parser p) =
  Parser
    ( \state -> case p state of
        Right (x, state) -> Right (x, state)
        Left state -> Left state {errors = err : state.errors}
    )

skipTo :: Parser err delim -> Parser err String
skipTo delim =
  oneOf
    [ "" <$ delim,
      do
        c <- anyChar
        cs <- skipTo delim
        ok (c : cs)
    ]

try :: Parser err a -> Parser err b -> Parser err (Either b a)
try parser else' = oneOf [Right <$> parser, Left <$> else']

-- Single characters
anyChar :: Parser err Char
anyChar =
  Parser
    ( \state -> case state.remaining of
        '\n' : src -> Right ('\n', state {remaining = src, index = state.index + 1, row = state.row + 1, col = 1})
        c : src -> Right (c, state {remaining = src, index = state.index + 1, col = state.col + 1})
        "" -> Left state
    )

char :: Char -> Parser err Char
char c = if' (== c) anyChar

charNoCase :: Char -> Parser err Char
charNoCase c = if' (\c' -> Char.toLower c == Char.toLower c') anyChar

letter :: Parser err Char
letter = if' Char.isLetter anyChar

lowercase :: Parser err Char
lowercase = if' Char.isLower anyChar

uppercase :: Parser err Char
uppercase = if' Char.isUpper anyChar

digit :: Parser err Char
digit = if' Char.isDigit anyChar

alphanumeric :: Parser err Char
alphanumeric = if' Char.isAlphaNum anyChar

punctuation :: Parser err Char
punctuation = if' Char.isPunctuation anyChar

space :: Parser err Char
space = if' (`elem` " \t") anyChar

spaces :: Parser err String
spaces = zeroOrMore space

whitespace :: Parser err Char
whitespace = if' (`elem` " \t\n\r\f\v") anyChar

whitespaces :: Parser err String
whitespaces = zeroOrMore whitespace

paddedL :: Parser err padding -> Parser err a -> Parser err a
paddedL padding parser = do
  _ <- padding
  parser

paddedR :: Parser err padding -> Parser err a -> Parser err a
paddedR padding parser = do
  x <- parser
  _ <- padding
  ok x

padded :: Parser err padding -> Parser err a -> Parser err a
padded padding = inbetween padding padding

inbetween :: Parser err start -> Parser err end -> Parser err a -> Parser err a
inbetween start end parser = do
  _ <- start
  x <- parser
  _ <- end
  ok x

endOfFile :: Parser err ()
endOfFile =
  Parser
    ( \state -> case state.remaining of
        "" -> Right ((), state)
        _ -> Left state
    )

endOfLine :: Parser err ()
endOfLine = oneOf [void $ if' (== '\n') anyChar, endOfFile]

-- Sequences
chain :: [Parser err a] -> Parser err [a]
chain [] = ok []
chain (p : ps) = do
  x <- p
  xs <- chain ps
  ok (x : xs)

text :: String -> Parser err String
text str = chain (fmap char str)

textNoCase :: String -> Parser err String
textNoCase str = chain (fmap charNoCase str)

concat :: [Parser err [a]] -> Parser err [a]
concat parsers = fmap Prelude.concat (chain parsers)

maybe' :: Parser err a -> Parser err (Maybe a)
maybe' parser = oneOf [fmap Just parser, ok Nothing]

zeroOrOne :: Parser err a -> Parser err [a]
zeroOrOne parser = oneOf [fmap (: []) parser, ok []]

zeroOrMore :: Parser err a -> Parser err [a]
zeroOrMore = foldR (:) []

oneOrMore :: Parser err a -> Parser err [a]
oneOrMore parser = do
  x <- parser
  xs <- zeroOrMore parser
  ok (x : xs)

exactly :: Int -> Parser err a -> Parser err [a]
exactly n parser = chain (replicate n parser)

atLeast :: Int -> Parser err a -> Parser err [a]
atLeast min parser | min <= 0 = zeroOrMore parser
atLeast min parser = do
  x <- parser
  xs <- atLeast (min - 1) parser
  ok (x : xs)

atMost :: Int -> Parser err a -> Parser err [a]
atMost max _ | max <= 0 = ok []
atMost max parser =
  oneOf
    [ do
        x <- parser
        xs <- atMost (max - 1) parser
        ok (x : xs),
      ok []
    ]

between :: Int -> Int -> Parser err a -> Parser err [a]
between min max parser | min <= 0 = atMost max parser
between min max parser = do
  x <- parser
  xs <- between (min - 1) (max - 1) parser
  ok (x : xs)

foldR :: (a -> b -> b) -> b -> Parser err a -> Parser err b
foldR f final parser =
  oneOf
    [ do
        x <- parser
        y <- foldR f final parser
        ok (f x y),
      ok final
    ]

foldL :: (b -> a -> b) -> b -> Parser err a -> Parser err b
foldL f initial parser =
  oneOf
    [ do
        x <- parser
        foldL f (f initial x) parser,
      ok initial
    ]

-- Common
integer :: Parser err Int
integer = do
  digits <- oneOrMore digit |> notFollowedBy (char '.')
  ok (read digits)

number :: Parser err Double
number = do
  int <- oneOrMore digit
  oneOf
    [ do
        fraction <- Parser.concat [text ".", oneOrMore digit]
        ok (read (int ++ fraction)),
      ok (read int)
    ]

wordChar :: Parser err Char
wordChar = oneOf [letter, digit, char '_']

wordEnd :: Parser err ()
wordEnd = notFollowedBy wordChar (ok ())

word :: String -> Parser err String
word txt = do
  x <- text txt
  _ <- wordEnd
  ok x

followedBy :: Parser err a -> Parser err b -> Parser err b
followedBy (Parser lookahead) parser = do
  x <- parser
  Parser
    ( \state -> case lookahead state of
        Right _ -> Right (x, state)
        Left _ -> Left state
    )

notFollowedBy :: Parser err a -> Parser err b -> Parser err b
notFollowedBy (Parser lookahead) parser = do
  x <- parser
  Parser
    ( \state -> case lookahead state of
        Right _ -> Left state
        Left _ -> Right (x, state)
    )

subparserPartial :: Parser err delim -> Parser err a -> Parser err a
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

subparser :: Parser err delim -> Parser err a -> Parser err a
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
-- TODO: collection : ([a] -> b) -> Parser open -> Parser err a -> Parser delim -> Parser close -> Parser err b
-- TODO: comment
-- TODO: multiLineComment

-- Operator precedence
-- https://github.com/zesterer/chumsky/blob/main/src/pratt.rs
data Operator err a
  = Prefix !Int !(Parser err a -> Parser err a)
  | InfixL !Int !(a -> Parser err a -> Parser err a)
  | InfixR !Int !(a -> Parser err a -> Parser err a)

prefix :: Int -> (op -> a -> a) -> Parser err op -> Operator err a
prefix prec f op = do
  let parser expr = do
        op <- op
        x <- expr
        ok (f op x)
  Prefix prec parser

suffix :: Int -> (op -> a -> a) -> Parser err op -> Operator err a
suffix prec f op = do
  let parser x _ = do
        op <- op
        ok (f op x)
  InfixL prec parser

infixL :: Int -> (op -> a -> a -> a) -> Parser err op -> Operator err a
infixL prec f op = do
  let parser x expr = do
        op <- op
        y <- expr
        ok (f op x y)
  InfixL prec parser

infixR :: Int -> (op -> a -> a -> a) -> Parser err op -> Operator err a
infixR prec f op = do
  let parser x expr = do
        op <- op
        y <- expr
        ok (f op x y)
  InfixR prec parser

operators :: Int -> [Operator err a] -> Parser err a -> Parser err a
operators prec ops atom = do
  x <- unary prec ops atom
  binary prec ops atom x

unary :: Int -> [Operator err a] -> Parser err a -> Parser err a
unary prec ops atom = do
  let toUnary (Prefix prec' f) | prec <= prec' = do
        f (operators prec' ops atom)
      toUnary _ = fail'
  oneOf (map toUnary ops ++ [atom])

binary :: Int -> [Operator err a] -> Parser err a -> a -> Parser err a
binary prec ops atom x = do
  let toBinary (InfixL prec' f) | prec < prec' = do
        y <- f x (operators prec' ops atom)
        binary prec ops atom y
      toBinary (InfixR prec' f) | prec <= prec' = do
        y <- f x (operators prec' ops atom)
        binary prec ops atom y
      toBinary _ = fail'
  oneOf (map toBinary ops ++ [ok x])
