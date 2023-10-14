{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Parser where

import Control.Monad (void)
import qualified Data.Char as Char
import Flow ((|>))

newtype Parser a = Parser (State -> Either State (a, State))

data State = State
  { source :: !String,
    row :: !Int,
    col :: !Int
  }
  deriving (Eq, Show)

instance Functor Parser where
  fmap :: (a -> b) -> Parser a -> Parser b
  fmap f (Parser p) =
    Parser
      ( \state -> do
          (x, state) <- p state
          Right (f x, state)
      )

instance Applicative Parser where
  pure :: a -> Parser a
  pure = succeed

  (<*>) :: Parser (a -> b) -> Parser a -> Parser b
  parserF <*> parser = do
    f <- parserF
    fmap f parser

instance Monad Parser where
  (>>=) :: Parser a -> (a -> Parser b) -> Parser b
  Parser p >>= f =
    Parser
      ( \state -> do
          (x, state) <- p state
          let (Parser p') = f x
          p' state
      )

  return :: a -> Parser a
  return = pure

parse :: Parser a -> String -> Either State (a, State)
parse (Parser p) source = do
  let state = State {source = source, row = 1, col = 1}
  p state

succeed :: a -> Parser a
succeed value = Parser (\state -> Right (value, state))

fail' :: Parser a
fail' = Parser Left

assert :: Bool -> Parser ()
assert check = if check then succeed () else fail'

orElse :: Parser a -> Parser a -> Parser a
orElse (Parser else') (Parser p) = do
  Parser
    ( \state ->
        case p state of
          Left _ -> else' state
          x -> x
    )

oneOf :: [Parser a] -> Parser a
oneOf [] = fail'
oneOf (p : ps) = p |> orElse (oneOf ps)

endOfFile :: Parser ()
endOfFile =
  Parser
    ( \state -> case state.source of
        "" -> Right ((), state)
        _ -> Left state
    )

endOfLine :: Parser ()
endOfLine = oneOf [void $ char '\n', endOfFile]

-- Single characters
charIf :: (Char -> Bool) -> Parser Char
charIf condition =
  Parser
    ( \state -> case state.source of
        c : _ | not (condition c) -> Left state
        '\n' : src -> Right ('\n', state {source = src, row = state.row + 1, col = 1})
        c : src -> Right (c, state {source = src, col = state.col + 1})
        "" -> Left state
    )

anyChar :: Parser Char
anyChar = charIf (const True)

space :: Parser Char
space = charIf (`elem` " \t")

spaces :: Parser String
spaces = zeroOrMore space

whitespace :: Parser Char
whitespace = charIf (`elem` " \t\n\r\f\v")

whitespaces :: Parser String
whitespaces = zeroOrMore whitespace

letter :: Parser Char
letter = charIf Char.isLetter

lowercase :: Parser Char
lowercase = charIf Char.isLower

uppercase :: Parser Char
uppercase = charIf Char.isUpper

digit :: Parser Char
digit = charIf Char.isDigit

alphanumeric :: Parser Char
alphanumeric = charIf Char.isAlphaNum

punctuation :: Parser Char
punctuation = charIf Char.isPunctuation

char :: Char -> Parser Char
char c = charIf (\ch -> Char.toLower c == Char.toLower ch)

charExcept :: [Char] -> Parser Char
charExcept notAllowed = charIf (`notElem` notAllowed)

charCaseSensitive :: Char -> Parser Char
charCaseSensitive c = charIf (== c)

-- Sequences
chain :: [Parser a] -> Parser [a]
chain [] = succeed []
chain (p : ps) = do
  x <- p
  xs <- chain ps
  succeed (x : xs)

maybe' :: Parser a -> Parser (Maybe a)
maybe' parser = fmap Just parser |> orElse (succeed Nothing)

zeroOrOne :: Parser a -> Parser [a]
zeroOrOne parser = fmap (: []) parser |> orElse (succeed [])

zeroOrMore :: Parser a -> Parser [a]
zeroOrMore = foldR (:) []

oneOrMore :: Parser a -> Parser [a]
oneOrMore parser = do
  x <- parser
  xs <- zeroOrMore parser
  succeed (x : xs)

exactly :: Int -> Parser a -> Parser [a]
exactly n parser = chain (replicate n parser)

atLeast :: Int -> Parser a -> Parser [a]
atLeast min parser | min <= 0 = zeroOrMore parser
atLeast min parser = do
  x <- parser
  xs <- atLeast (min - 1) parser
  succeed (x : xs)

atMost :: Int -> Parser a -> Parser [a]
atMost max _ | max <= 0 = succeed []
atMost max parser =
  do
    x <- parser
    xs <- atMost (max - 1) parser
    succeed (x : xs)
    |> orElse (succeed [])

between :: Int -> Int -> Parser a -> Parser [a]
between min max parser | min <= 0 = atMost max parser
between min max parser = do
  x <- parser
  xs <- between (min - 1) (max - 1) parser
  succeed (x : xs)

-- TODO: split :: Parser delim -> Parser a -> Parser [a]
until' :: (a -> Bool) -> Parser a -> Parser [a]
until' done parser =
  do
    x <- parser
    _ <- assert (not (done x))
    xs <- until' done parser
    succeed (x : xs)
    |> orElse (succeed [])

foldL :: (b -> a -> b) -> b -> Parser a -> Parser b
foldL f initial parser =
  do
    x <- parser
    foldL f (f initial x) parser
    |> orElse (succeed initial)

foldR :: (a -> b -> b) -> b -> Parser a -> Parser b
foldR f final parser =
  do
    x <- parser
    y <- foldR f final parser
    succeed (f x y)
    |> orElse (succeed final)

-- Common
integer :: Parser Int
integer = do
  digits <- oneOrMore digit |> notFollowedBy (char '.')
  succeed (read digits)

number :: Parser Double
number = do
  int <- oneOrMore digit
  oneOf
    [ do
        _ <- char '.'
        fraction <- oneOrMore digit
        succeed (read $ concat [int, ".", fraction]),
      do succeed (read int)
    ]

text :: String -> Parser String
text str = chain (fmap char str)

textCaseSensitive :: String -> Parser String
textCaseSensitive str = chain (fmap charCaseSensitive str)

textUntil :: Parser end -> Parser String
textUntil delim =
  oneOf
    [ do
        _ <- delim
        succeed "",
      do
        c <- anyChar
        cs <- textUntil delim
        succeed (c : cs)
    ]

wordChar :: Parser Char
wordChar = oneOf [letter, digit, char '_']

wordEnd :: Parser ()
wordEnd = oneOf [succeed () |> notFollowedBy wordChar]

word :: String -> Parser String
word txt = do
  x <- text txt
  _ <- wordEnd
  succeed x

followedBy :: Parser a -> Parser b -> Parser b
followedBy (Parser lookahead) parser = do
  x <- parser
  Parser
    ( \state -> case lookahead state of
        Right _ -> Right (x, state)
        Left _ -> Left state
    )

notFollowedBy :: Parser a -> Parser b -> Parser b
notFollowedBy (Parser lookahead) parser = do
  x <- parser
  Parser
    ( \state -> case lookahead state of
        Right _ -> Left state
        Left _ -> Right (x, state)
    )

-- TODO
getState :: Parser State
getState = Parser (\state -> Right (state, state))

subparserPartial :: Parser delim -> Parser a -> Parser a
subparserPartial delim (Parser p) = do
  before <- getState
  _ <- zeroOrMore (do _ <- succeed () |> notFollowedBy delim; anyChar)
  after <- getState
  let len = length before.source - length after.source
  Parser
    ( \state -> do
        (x, _) <- p before {source = take len before.source}
        Right (x, state)
    )

subparser :: Parser delim -> Parser a -> Parser a
subparser delim parser = subparserPartial delim (do x <- parser; _ <- endOfFile; succeed x)

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
-- TODO: collection : ([a] -> b) -> Parser open -> Parser a -> Parser delim -> Parser close -> Parser b
-- TODO: comment
-- TODO: multiLineComment

-- Operator precedence
type Prefix a = (Int -> Parser a) -> Parser a

type Infix a = a -> Int -> (Int -> Parser a) -> Parser a

atom :: Parser a -> Prefix a
atom parser _ = parser

prefix :: Int -> (a -> a) -> Parser op -> Prefix a
prefix prec f = prefixOp prec (\_ x -> f x)

prefixOp :: Int -> (op -> a -> a) -> Parser op -> Prefix a
prefixOp prec f op expr = do
  op <- op
  x <- expr prec
  succeed (f op x)

inbetween :: Parser open -> Parser close -> Prefix a
inbetween = inbetweenOp (\_ _ x -> x)

inbetweenOp :: (open -> close -> a -> a) -> Parser open -> Parser close -> Prefix a
inbetweenOp f open close expr = do
  open <- open
  x <- expr 0
  close <- close
  succeed (f open close x)

infixL :: Int -> (a -> a -> a) -> Parser op -> Infix a
infixL prec f = infixLOp prec (\_ x y -> f x y)

infixLOp :: Int -> (op -> a -> a -> a) -> Parser op -> Infix a
infixLOp prec f op x prec' expr = do
  assert (prec > prec')
  op <- op
  y <- expr prec
  succeed (f op x y)

infixR :: Int -> (a -> a -> a) -> Parser op -> Infix a
infixR prec f = infixROp prec (\_ x y -> f x y)

infixROp :: Int -> (op -> a -> a -> a) -> Parser op -> Infix a
infixROp prec f op x prec' expr = do
  assert (prec >= prec')
  op <- op
  y <- expr prec
  succeed (f op x y)

postfix :: Int -> (a -> a) -> Parser op -> Infix a
postfix prec f = postfixOp prec (\_ x -> f x)

postfixOp :: Int -> (op -> a -> a) -> Parser op -> Infix a
postfixOp prec f op x prec' _ = do
  assert (prec > prec')
  op <- op
  succeed (f op x)

withOperators :: [Prefix a] -> [Infix a] -> Int -> Parser a
withOperators prefix infix' prec = do
  let expr prec = do
        x <- oneOf (fmap (\op -> op expr) prefix)
        binary prec x

      binary prec x =
        oneOf
          [ do
              y <- oneOf (fmap (\op -> op x prec expr) infix')
              binary prec y,
            succeed x
          ]

  expr prec
