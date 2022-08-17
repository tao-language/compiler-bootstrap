module Parser where

import qualified Data.Char as Char

newtype Parser a = Parser (State -> Either ParserError (a, State))

data State = State
  { source :: String,
    indentation :: String,
    row :: Int,
    col :: Int
  }
  deriving (Eq, Show)

data ParserError = ParserError String State
  deriving (Eq, Show)

(|>) :: a -> (a -> b) -> b
(|>) x f = f x

infixl 1 |>

instance Functor Parser where
  fmap f (Parser p) =
    Parser
      ( \state -> do
          (x, state) <- p state
          Right (f x, state)
      )

instance Applicative Parser where
  pure = succeed
  parserF <*> parser = do
    f <- parserF
    fmap f parser

instance Monad Parser where
  Parser p >>= f =
    Parser
      ( \state -> do
          (x, state) <- p state
          let (Parser p') = f x
          p' state
      )
  return x = succeed x

parse :: String -> Parser a -> Either ParserError a
parse source (Parser p) = do
  let state = State {source = source, indentation = "", row = 1, col = 1}
  fmap fst (p state)

succeed :: a -> Parser a
succeed value = Parser (\state -> Right (value, state))

expected :: String -> Parser a
expected message = Parser (Left . ParserError message)

assert :: Bool -> String -> Parser ()
assert check message = if check then succeed () else expected message

orElse :: Parser a -> Parser a -> Parser a
orElse (Parser else') (Parser p) = do
  Parser
    ( \state ->
        case p state of
          Left _ -> else' state
          x -> x
    )

oneOf :: [Parser a] -> Parser a
oneOf [] = expected "a valid choice"
oneOf (p : ps) = p |> orElse (oneOf ps)

endOfFile :: Parser ()
endOfFile = do
  let eof :: State -> Either ParserError ((), State)
      eof state = case source state of
        "" -> Right ((), state)
        _ -> Left (ParserError "end of file" state)
  Parser eof

endOfLine :: Parser ()
endOfLine = oneOf [do _ <- char '\n'; succeed (), endOfFile]

-- Single characters

anyChar :: Parser Char
anyChar = do
  let advance :: State -> Either ParserError (Char, State)
      advance state = case source state of
        '\n' : source -> Right ('\n', state {source = source, row = row state + 1, col = 1})
        ch : source -> Right (ch, state {source = source, col = col state + 1})
        "" -> Left (ParserError "a character" state)
  Parser advance

charIf :: (Char -> Bool) -> String -> Parser Char
charIf condition message = do
  ch <- anyChar
  _ <- assert (condition ch) message
  succeed ch

space :: Parser Char
space = charIf Char.isSpace "a blank space"

letter :: Parser Char
letter = charIf Char.isLetter "a letter"

lowercase :: Parser Char
lowercase = charIf Char.isLower "a lowercase letter"

uppercase :: Parser Char
uppercase = charIf Char.isUpper "an uppercase letter"

digit :: Parser Char
digit = charIf Char.isDigit "a digit from 0 to 9"

alphanumeric :: Parser Char
alphanumeric = charIf Char.isAlphaNum "a letter or digit"

punctuation :: Parser Char
punctuation = charIf Char.isPunctuation "a punctuation character"

char :: Char -> Parser Char
char c = charIf (\ch -> Char.toLower c == Char.toLower ch) ("the character '" <> [c] <> "'")

charCaseSensitive :: Char -> Parser Char
charCaseSensitive c = charIf (== c) ("the character '" <> [c] <> "' (case sensitive)")

-- Sequences
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

chain :: [Parser a] -> Parser [a]
chain [] = succeed []
chain (p : ps) = do
  x <- p
  xs <- chain ps
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
    _ <- assert (not (done x)) ""
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
integer =
  do
    digits <- oneOrMore digit
    succeed (read digits)
    |> orElse (expected "an integer value like 123")

number :: Parser Float
number =
  do
    int <- oneOrMore digit
    oneOf
      [ do
          _ <- char '.'
          fraction <- oneOrMore digit
          succeed (read $ concat [int, ['.'], fraction]),
        do succeed (read int)
      ]
    |> orElse (expected "a number like 123 or 3.14")

text :: String -> Parser String
text str =
  chain (fmap char str)
    |> orElse (expected $ "the text '" <> str <> "'")

textCaseSensitive :: String -> Parser String
textCaseSensitive str =
  chain (fmap charCaseSensitive str)
    |> orElse (expected $ "the text '" <> str <> "' (case sensitive)")

token :: Parser a -> Parser a
token parser = do
  -- let empty :: Parser Bool
  --     empty = do
  --       _ <- zeroOrMore (oneOf [char ' ', char '\t', char '\r'])
  --       oneOf [fmap (const True) (char '\n'), succeed False]
  -- -- TODO: checkIndent
  -- let checkIndent :: a -> Parser a
  --     checkIndent x = succeed x
  -- x <- parser
  -- newline <- empty
  -- if newline
  --   then checkIndent x
  --   else succeed x
  x <- parser
  _ <- zeroOrMore space
  succeed x

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

type Infix a = Int -> a -> Prefix a

atom :: (a -> b) -> Parser a -> Prefix b
atom f parser _ = do
  x <- token parser
  succeed (f x)

prefix :: (op -> a -> a) -> Parser op -> Prefix a
prefix f op expr = do
  op' <- token op
  y <- expr 0
  succeed (f op' y)

inbetween :: (open -> a -> a) -> Parser open -> Parser close -> Prefix a
inbetween f open close expr = do
  open' <- token open
  y <- expr 0
  _ <- zeroOrMore space -- allow the close delimiter to be "out of indentation"
  _ <- token close
  succeed (f open' y)

-- TODO: rename to infixLeft
infixL :: Int -> (op -> a -> a -> a) -> Parser op -> Infix a
infixL opPrec f op prec x expr = do
  _ <- assert (prec < opPrec) ("infixL " ++ show opPrec)
  op' <- token op
  y <- expr opPrec
  succeed (f op' x y)

-- TODO: rename to infixRight
infixR :: Int -> (op -> a -> a -> a) -> Parser op -> Infix a
infixR opPrec f op prec x expr = do
  _ <- assert (prec <= opPrec) ("infixR " ++ show opPrec)
  op' <- token op
  y <- expr opPrec
  succeed (f op' x y)

withOperators :: [Prefix a] -> [Infix a] -> Parser a
withOperators prefix infix' =
  let unary f = oneOf (fmap (\op -> op f) prefix)
      binary x f prec = oneOf (fmap (\op -> op x f prec) infix')
      expr prec = do
        x <- unary expr
        expr2 prec x
      expr2 prec x =
        do
          y <- binary prec x expr
          expr2 prec y
          |> orElse (succeed x)
   in expr 0

indented :: Parser a -> Parser a
indented parser = do
  -- TODO: token should take care of both checking and bookkeeping of indentations
  parser