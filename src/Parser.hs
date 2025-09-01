module Parser where

-- https://youtu.be/RDalzi7mhdY?si=606x1zQEgpW51Zh-
-- https://eyalkalderon.com/blog/nom-error-recovery/
-- https://arxiv.org/pdf/1806.11150.pdf
-- https://blog.jsbarretto.com/post/parser-combinators-and-error-recovery
-- https://docs.rs/chumsky/0.10.1/chumsky/guide/index.html

import Control.Monad (void)
import qualified Data.Char as Char
import Data.Function ((&))
import Data.List (intercalate)
import qualified Debug.Trace as Debug
import Location (Location (..), Position (..), Range (..))
import qualified Location as Loc
import Stdlib (filterMap)

-- TODO:
-- p.delimitedBy(open, close)
-- p.separatedBy(sep)
-- p.paddedBy(trim)
-- p.mapError(f)
-- p.recoverWith(r)
-- p.rewind()

newtype Parser a
  = Parser (State -> Either State (a, State))

-- TODO: find a way to keep a stack trace for syntax errors
data State = State
  { remaining :: String,
    filename :: String,
    pos :: Position,
    index :: Int,
    expected :: String,
    committed :: String
  }
  deriving (Eq, Show)

instance Functor Parser where
  fmap :: (a -> b) -> Parser a -> Parser b
  fmap f parser = do
    x <- parser
    return (f x)

instance Applicative Parser where
  pure :: a -> Parser a
  pure = ok

  (<*>) :: Parser (a -> b) -> Parser a -> Parser b
  parserF <*> parser = do
    f <- parserF
    fmap f parser

instance Monad Parser where
  (>>=) :: Parser a -> (a -> Parser b) -> Parser b
  Parser p >>= f =
    Parser
      ( \s1 -> case p s1 of
          Right (x, s2) -> apply (f x) s2
          Left s2 -> Left s2
      )

  return :: a -> Parser a
  return = pure

locSpan :: State -> State -> Location
locSpan start end = Location start.filename (Range start.pos end.pos)

apply :: Parser a -> State -> Either State (a, State)
apply (Parser p) = p

parse :: Parser a -> FilePath -> String -> Either State (a, State)
parse (Parser p) filename remaining =
  p
    State
      { remaining = remaining,
        filename = filename,
        pos = Pos 1 1,
        index = 0,
        expected = "",
        committed = ""
      }

parseFrom :: Position -> String -> Parser a -> Parser a
parseFrom pos remaining (Parser p) =
  Parser
    ( \state -> case p state {pos = pos, remaining = remaining} of
        Right (x, _) -> Right (x, state)
        Left state -> Left state
    )

ok :: a -> Parser a
ok x = Parser (\state -> Right (x, state))

fail' :: Parser a
fail' = Parser Left

assert :: Bool -> Parser ()
assert True = ok ()
assert False = fail'

not' :: Parser a -> Parser ()
not' (Parser p) =
  Parser
    ( \state -> case p state of
        Right _ -> Left state
        Left state -> Right ((), state)
    )

if' :: (a -> Bool) -> Parser a -> Parser a
if' check (Parser p) =
  Parser
    ( \state -> case p state of
        Right (x, state) | check x -> Right (x, state)
        Right _ -> Left state
        Left state -> Left state
    )

oneOf :: [Parser a] -> Parser a
oneOf [] = fail'
oneOf (Parser p : choices) = do
  Parser
    ( \s1 -> case p s1 of
        Right (x, s2) -> Right (x, s2)
        Left s2 -> apply (oneOf choices) s1
    )

commitOneOf :: [Parser a] -> Parser a
commitOneOf [] = fail'
commitOneOf (Parser p : choices) = do
  Parser
    ( \s1 -> case p s1 {committed = ""} of
        Right (x, s2) -> Right (x, s2 {committed = s1.committed})
        Left s2 | s2.committed == "" -> apply (commitOneOf choices) s1
        Left s2 -> Left s1 {expected = s2.expected}
    )

choose :: (a -> a -> Either () ()) -> [Parser a] -> Parser a
choose _ [] = fail'
choose _ [p] = p
choose f (Parser p : ps) = do
  let (Parser q) = choose f ps
  Parser $ \state -> case (p state, q state) of
    (Right (x, s1), Right (y, s2)) -> case f x y of
      Left () -> Right (x, s1)
      Right () -> Right (y, s2)
    (Right result, Left _) -> Right result
    (Left _, Right result) -> Right result
    (Left _, Left s2) -> Left s2

chooseShortest :: [Parser [a]] -> Parser [a]
chooseShortest = do
  let f [] _ = Left ()
      f _ [] = Right ()
      f (_ : xs) (_ : ys) = f xs ys
  choose f

chooseLongest :: [Parser [a]] -> Parser [a]
chooseLongest = do
  let f _ [] = Left ()
      f [] _ = Right ()
      f (_ : xs) (_ : ys) = f xs ys
  choose f

state :: Parser State
state = Parser (\state -> Right (state, state))

-- Error handling
expect :: String -> Parser a -> Parser a
expect message (Parser p) =
  Parser
    ( \s1 -> case p s1 of
        Right (x, s2) -> Right (x, s2)
        Left s2 -> Left (s2 {expected = message})
    )

commit :: String -> Parser a -> Parser a
commit message parser = do
  x <- expect message parser
  commit' message
  return x

commit' :: String -> Parser ()
commit' message = Parser (\s -> Right ((), s {committed = message}))

uncommit :: Parser ()
uncommit = Parser (\s -> Right ((), s {committed = ""}))

recover :: Parser a -> ((State, State, a) -> b) -> Parser b -> Parser b
recover recovery catch (Parser p) =
  Parser
    ( \s1 -> case p s1 of
        Right (x, s2) -> Right (x, s2)
        Left s2 -> do
          let recover' = do
                start <- state
                x <- recovery
                end <- state
                return (catch (start, end, x))
          apply recover' s1 {expected = s2.expected}
    )

skip :: Parser a -> Parser ()
skip parser = do
  _ <- parser
  return ()

thenSkip :: Parser skip -> Parser a -> Parser a
thenSkip skip parser = do
  _ <- skip
  parser

skipThen :: Parser a -> Parser skip -> Parser a
skipThen parser skip = do
  x <- parser
  _ <- skip
  return x

until' :: Parser stop -> Parser a -> Parser [a]
until' stop parser =
  oneOf
    [ [] <$ lookahead stop,
      do
        x <- parser
        xs <- until' stop parser
        return (x : xs)
    ]

textUntil :: Parser stop -> Parser String
textUntil stop = until' stop anyChar

untilNested :: ([(open, Parser close)], [(open, close)]) -> Parser stop -> [(Parser open, Parser close)] -> Parser a -> Parser ([a], [open], [(open, close)])
untilNested (stack, errors) stop groups parser = do
  oneOf
    [ ([], map fst stack, errors) <$ lookahead stop,
      do
        x <- parser
        (xs, stack, errors) <- untilNested (stack, errors) stop groups parser
        return (x : xs, stack, errors)
    ]

while :: (a -> Bool) -> Parser a -> Parser [a]
while cond parser = until' (not' $ if' cond parser) parser

textWhile :: (Char -> Bool) -> Parser String
textWhile cond = while cond anyChar

skipUntil :: Parser skip -> Parser a -> Parser a
skipUntil skip parser =
  oneOf
    [ parser,
      do _ <- skip; skipUntil skip parser
    ]

-- Single characters
anyChar :: Parser Char
anyChar =
  expect "character" $
    Parser
      ( \state -> do
          case state.remaining of
            '\n' : src -> Right ('\n', state {remaining = src, index = state.index + 1, pos = Pos (state.pos.row + 1) 1})
            c : src -> Right (c, state {remaining = src, index = state.index + 1, pos = Pos state.pos.row (state.pos.col + 1)})
            "" -> Left state
      )

char :: Char -> Parser Char
char c = expect (show c) $ charIf (== c)

charNoCase :: Char -> Parser Char
charNoCase c = expect (show c ++ " (case insensitive)") $ if' (\c' -> Char.toLower c == Char.toLower c') anyChar

charIf :: (Char -> Bool) -> Parser Char
charIf f = if' f anyChar

charOf :: [Char] -> Parser Char
charOf chars =
  expect
    ("one of " ++ intercalate ", " (map show chars))
    (charIf (`elem` chars))

letter :: Parser Char
letter = expect "letter" $ if' Char.isLetter anyChar

lowercase :: Parser Char
lowercase = expect "lowercase letter" $ if' Char.isLower anyChar

uppercase :: Parser Char
uppercase = expect "uppercase letter" $ if' Char.isUpper anyChar

digit :: Parser Char
digit = expect "digit" $ if' Char.isDigit anyChar

alphanumeric :: Parser Char
alphanumeric = expect "letter or digit" $ if' Char.isAlphaNum anyChar

punctuation :: Parser Char
punctuation = if' Char.isPunctuation anyChar

space :: Parser Char
space = if' (`elem` " \t") anyChar

spaces :: Parser String
spaces = zeroOrMore space

whitespace :: Parser Char
whitespace = if' (`elem` " \t\n\r\f\v") anyChar

whitespaces :: Parser String
whitespaces = zeroOrMore whitespace

paddedL :: Parser padding -> Parser a -> Parser a
paddedL padding parser = do
  _ <- padding
  parser

paddedR :: Parser padding -> Parser a -> Parser a
paddedR padding parser = do
  x <- parser
  _ <- padding
  ok x

padded :: Parser padding -> Parser a -> Parser a
padded padding = inbetween padding padding

inbetween :: Parser start -> Parser end -> Parser a -> Parser a
inbetween start end parser = do
  _ <- start
  x <- parser
  _ <- end
  ok x

endOfFile :: Parser ()
endOfFile =
  Parser
    ( \state -> case state.remaining of
        "" -> Right ((), state)
        _ -> Left state
    )

endOfLine :: Parser ()
endOfLine = oneOf [void $ char '\n', endOfFile]

-- Sequences
chain :: [Parser a] -> Parser [a]
chain [] = ok []
chain (p : ps) = do
  x <- p
  xs <- chain ps
  ok (x : xs)

text :: String -> Parser String
text str = expect (show str) $ chain (fmap char str)

textNoCase :: String -> Parser String
textNoCase str = expect (show str ++ " (case insensitive)") $ chain (fmap charNoCase str)

concat :: [Parser [a]] -> Parser [a]
concat parsers = fmap Prelude.concat (chain parsers)

maybe' :: Parser a -> Parser (Maybe a)
maybe' parser = oneOf [fmap Just parser, ok Nothing]

zeroOrOne :: Parser a -> Parser [a]
zeroOrOne parser = oneOf [fmap (: []) parser, ok []]

zeroOrMore :: Parser a -> Parser [a]
zeroOrMore = foldR (:) []

oneOrMore :: Parser a -> Parser [a]
oneOrMore parser = do
  x <- parser
  xs <- zeroOrMore parser
  ok (x : xs)

exactly :: Int -> Parser a -> Parser [a]
exactly n parser = chain (replicate n parser)

atLeast :: Int -> Parser a -> Parser [a]
atLeast min parser | min <= 0 = zeroOrMore parser
atLeast min parser = do
  x <- parser
  xs <- atLeast (min - 1) parser
  ok (x : xs)

atMost :: Int -> Parser a -> Parser [a]
atMost max _ | max <= 0 = ok []
atMost max parser =
  oneOf
    [ do
        x <- parser
        xs <- atMost (max - 1) parser
        ok (x : xs),
      ok []
    ]

between :: Int -> Int -> Parser a -> Parser [a]
between min max parser | min <= 0 = atMost max parser
between min max parser = do
  x <- parser
  xs <- between (min - 1) (max - 1) parser
  ok (x : xs)

foldR :: (a -> b -> b) -> b -> Parser a -> Parser b
foldR f final parser =
  oneOf
    [ do
        x <- parser
        y <- foldR f final parser
        ok (f x y),
      ok final
    ]

foldL :: (b -> a -> b) -> b -> Parser a -> Parser b
foldL f initial parser =
  oneOf
    [ do
        x <- parser
        foldL f (f initial x) parser,
      ok initial
    ]

-- Common
integer :: Parser Int
integer = do
  sign <- oneOf [do _ <- char '-'; return (-1), return 1]
  _ <- spaces
  digits <- oneOrMore digit
  lookaheadNot (char '.')
  ok (read digits * sign)

number :: Parser Double
number = do
  sign <- oneOf [do _ <- char '-'; return (-1), return 1]
  _ <- spaces
  int <- oneOrMore digit
  num <-
    oneOf
      [ do
          fraction <- Parser.concat [text ".", oneOrMore digit]
          ok (read (int ++ fraction)),
        ok (read int)
      ]
  ok (num * sign)

wordChar :: Parser Char
wordChar = oneOf [letter, digit, char '_']

wordStart :: Parser Char
wordStart = lookahead wordChar

wordEnd :: Parser ()
wordEnd = lookaheadNot wordChar

word :: String -> Parser String
word txt = do
  x <- text txt
  _ <- wordEnd
  ok x

lookahead :: Parser a -> Parser a
lookahead (Parser p) =
  Parser
    ( \state -> case p state of
        Right (x, _) -> Right (x, state)
        Left _ -> Left state
    )

lookaheadNot :: Parser a -> Parser ()
lookaheadNot (Parser p) =
  Parser
    ( \state -> case p state of
        Right _ -> Left state
        Left _ -> Right ((), state)
    )

subparserPartial :: Parser delim -> Parser a -> Parser a
subparserPartial delim (Parser p) = do
  before <- state
  _ <- zeroOrMore (do _ <- lookaheadNot delim; anyChar)
  after <- state
  let len = length before.remaining - length after.remaining
  Parser
    ( \state -> do
        (x, _) <- p before {remaining = take len before.remaining}
        Right (x, state)
    )

subparser :: Parser delim -> Parser a -> Parser a
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
-- TODO: collection : ([a] -> b) -> Parser open -> Parser a -> Parser delim -> Parser close -> Parser b
-- TODO: comment
-- TODO: multiLineComment

position :: Parser Position
position = do
  state <- state
  return state.pos

location :: Position -> Parser Location
location start = do
  state <- state
  return $
    Location
      { filename = state.filename,
        range = Range start state.pos
      }

-- Operator precedence
-- https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
-- https://github.com/zesterer/chumsky/blob/main/tutorial.md
data ExprParser a
  = Atom (Parser a -> Parser a)
  | Prefix Int (Parser a -> Parser a)
  | InfixL Int (a -> Parser a -> Parser a)
  | InfixR Int (a -> Parser a -> Parser a)

atom :: (a -> b) -> Parser a -> ExprParser b
atom f p =
  Atom $ \_ -> do
    f <$> p

group :: Parser open -> Parser close -> Parser spaces -> ExprParser a
group open close spaces =
  Atom $ \expr -> do
    _ <- open
    _ <- spaces
    x <- expr
    _ <- spaces
    _ <- close
    return x

prefix :: (Show op, Show a) => Int -> (Location -> op -> a -> a) -> Parser spaces -> Parser op -> ExprParser a
prefix p f spaces op = do
  Prefix p $ \expr -> do
    s <- state
    op <- op
    end <- position
    _ <- spaces
    let loc = Location s.filename (Range s.pos end)
    f loc op <$> expr

suffix :: (Show op, Show a) => Int -> (Location -> op -> a -> a) -> Parser spaces -> Parser op -> ExprParser a
suffix p f spaces op = do
  InfixL p $ \x _ -> do
    _ <- spaces
    s <- state
    op <- op
    end <- position
    let loc = Location s.filename (Range s.pos end)
    return (f loc op x)

infixL :: Int -> (Location -> op -> a -> a -> a) -> Parser spaces -> Parser op -> ExprParser a
infixL p f spaces op =
  InfixL p $ \x expr -> do
    _ <- spaces
    s <- state
    op <- op
    end <- position
    _ <- spaces
    let loc = Location s.filename (Range s.pos end)
    f loc op x <$> expr

infixR :: Int -> (Location -> op -> a -> a -> a) -> Parser spaces -> Parser op -> ExprParser a
infixR p f spaces op =
  InfixR p $ \x expr -> do
    _ <- spaces
    s <- state
    op <- op
    end <- position
    _ <- spaces
    let loc = Location s.filename (Range s.pos end)
    f loc op x <$> expr

precedence :: [ExprParser a] -> Int -> Parser a
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
