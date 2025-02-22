module Parser where

-- https://eyalkalderon.com/blog/nom-error-recovery/
-- https://arxiv.org/pdf/1806.11150.pdf

import Control.Monad (void)
import qualified Data.Char as Char
import Data.Function ((&))
import qualified Debug.Trace as Debug
import Location (Location (..), Position (..), Range (..))
import qualified Location as Loc
import Stdlib (filterMap)

newtype Parser ctx a
  = Parser (State ctx -> Either (State ctx) (a, State ctx))

data State ctx = State
  { remaining :: String,
    filename :: String,
    pos :: Position,
    index :: Int,
    context :: [ctx]
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

parse :: Parser ctx a -> FilePath -> String -> Either (State ctx) (a, State ctx)
parse (Parser p) filename remaining =
  p
    State
      { remaining = remaining,
        filename = filename,
        pos = Pos 1 1,
        index = 0,
        context = []
      }

parseFrom :: Position -> String -> Parser ctx a -> Parser ctx a
parseFrom pos remaining (Parser p) =
  Parser
    ( \state -> case p state {pos = pos, remaining = remaining} of
        Right (x, _) -> Right (x, state)
        Left state -> Left state
    )

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
oneOf [] = fail'
oneOf (Parser p : choices) =
  Parser
    ( \state1 -> case p state1 {context = []} of
        Right (x, state2) -> Right (x, state2 {context = state1.context})
        Left State {context = []} -> apply (oneOf choices) state1
        Left state2 -> Left state2 {context = state2.context ++ state1.context}
    )

getState :: Parser ctx (State ctx)
getState = Parser (\state -> Right (state, state))

-- Error handling
commit :: ctx -> Parser ctx ()
commit ctx = Parser (\state -> Right ((), state {context = ctx : state.context}))

skipTo :: Parser ctx delim -> Parser ctx String
skipTo delim =
  oneOf
    [ "" <$ delim,
      do
        c <- anyChar
        cs <- skipTo delim
        ok (c : cs)
    ]

recover :: [Parser ctx until] -> Parser ctx (State ctx, Int)
recover until = do
  state1 <- getState
  _ <- anyChar
  _ <- skipTo (lookahead $ oneOf until)
  state2 <- getState
  return (state1, state2.index - state1.index)

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
    ( \state -> do
        case state.remaining of
          '\n' : src -> Right ('\n', state {remaining = src, index = state.index + 1, pos = Pos (state.pos.row + 1) 1})
          c : src -> Right (c, state {remaining = src, index = state.index + 1, pos = Pos state.pos.row (state.pos.col + 1)})
          "" -> Left state
    )

char :: Char -> Parser ctx Char
char c = charIf (== c)

charNoCase :: Char -> Parser ctx Char
charNoCase c = if' (\c' -> Char.toLower c == Char.toLower c') anyChar

charIf :: (Char -> Bool) -> Parser ctx Char
charIf f = if' f anyChar

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
endOfLine = oneOf [void $ char '\n', endOfFile]

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
  digits <- oneOrMore digit
  lookaheadNot (char '.')
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

wordStart :: Parser ctx ()
wordStart = lookahead wordChar

wordEnd :: Parser ctx ()
wordEnd = lookaheadNot wordChar

word :: String -> Parser ctx String
word txt = do
  x <- text txt
  _ <- wordEnd
  ok x

lookahead :: Parser ctx a -> Parser ctx ()
lookahead (Parser p) =
  Parser
    ( \state -> case p state of
        Right _ -> Right ((), state)
        Left _ -> Left state
    )

lookaheadNot :: Parser ctx a -> Parser ctx ()
lookaheadNot (Parser p) =
  Parser
    ( \state -> case p state of
        Right _ -> Left state
        Left _ -> Right ((), state)
    )

subparserPartial :: Parser ctx delim -> Parser ctx a -> Parser ctx a
subparserPartial delim (Parser p) = do
  before <- getState
  _ <- zeroOrMore (do _ <- lookaheadNot delim; anyChar)
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

position :: Parser ctx Position
position = do
  state <- getState
  return state.pos

location :: Position -> Parser ctx Location
location start = do
  state <- getState
  return $
    Location
      { filename = state.filename,
        range = Range start state.pos
      }

-- Operator precedence
-- https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
-- https://github.com/zesterer/chumsky/blob/main/tutorial.md
data ExprParser ctx a
  = Atom (Parser ctx a -> Parser ctx a)
  | Prefix Int (Parser ctx a -> Parser ctx a)
  | InfixL Int (a -> Parser ctx a -> Parser ctx a)
  | InfixR Int (a -> Parser ctx a -> Parser ctx a)

atom :: (a -> b) -> Parser ctx a -> ExprParser ctx b
atom f p =
  Atom $ \_ -> do
    f <$> p

group :: Parser ctx open -> Parser ctx close -> ExprParser ctx a
group open close =
  Atom $ \expr -> do
    _ <- open
    x <- expr
    _ <- close
    return x

prefix :: (Show op, Show a) => Int -> (Location -> op -> a -> a) -> Parser ctx spaces -> Parser ctx op -> ExprParser ctx a
prefix p f spaces op = do
  Prefix p $ \expr -> do
    s <- getState
    op <- op
    end <- position
    _ <- spaces
    let loc = Location s.filename (Range s.pos end)
    f loc op <$> expr

suffix :: (Show op, Show a) => Int -> (Location -> op -> a -> a) -> Parser ctx spaces -> Parser ctx op -> ExprParser ctx a
suffix p f spaces op = do
  InfixL p $ \x _ -> do
    _ <- spaces
    s <- getState
    op <- op
    end <- position
    let loc = Location s.filename (Range s.pos end)
    return (f loc op x)

infixL :: Int -> (Location -> op -> a -> a -> a) -> Parser ctx spaces -> Parser ctx op -> ExprParser ctx a
infixL p f spaces op =
  InfixL p $ \x expr -> do
    _ <- spaces
    s <- getState
    op <- op
    end <- position
    _ <- spaces
    let loc = Location s.filename (Range s.pos end)
    f loc op x <$> expr

infixR :: Int -> (Location -> op -> a -> a -> a) -> Parser ctx spaces -> Parser ctx op -> ExprParser ctx a
infixR p f spaces op =
  InfixR p $ \x expr -> do
    _ <- spaces
    s <- getState
    op <- op
    end <- position
    _ <- spaces
    let loc = Location s.filename (Range s.pos end)
    f loc op x <$> expr

precedence :: [ExprParser ctx a] -> Int -> Parser ctx a
precedence ops p = do
  let unary = \case
        Atom op -> do
          op (precedence ops 0)
        Prefix q op | p <= q -> do
          op (precedence ops q)
        _ -> fail'
      binary x = \case
        InfixL q op | p < q -> do
          y <- op x (precedence ops q)
          loop y
        InfixR q op | p <= q -> do
          y <- op x (precedence ops q)
          loop y
        _ -> fail'
      loop x = oneOf (map (binary x) ops ++ [return x])
  x <- oneOf (map unary ops)
  loop x
