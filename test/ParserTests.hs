module ParserTests where

import qualified Data.Char as Char
import Location (Position (..))
import Parser
import Test.Hspec (SpecWith, describe, it, shouldBe)

data Expr -- for `operators`
  = Var String
  | Neg Expr
  | At Expr
  | Fac Expr
  | Add Expr Expr
  | Mul Expr Expr
  | Sub Expr Expr
  | Pow Expr Expr
  deriving (Eq)

instance Show Expr where
  show :: Expr -> String
  show (Var x) = x
  show (Neg x) = "(-" ++ show x ++ ")"
  show (At x) = "(@" ++ show x ++ ")"
  show (Fac x) = "(" ++ show x ++ "!)"
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Pow x y) = "(" ++ show x ++ " ^ " ++ show y ++ ")"

run :: SpecWith ()
run = describe "--==☯ Parser ☯==--" $ do
  let parse' :: Parser a -> String -> Either String (a, String)
      parse' parser txt = case parse parser "ParserTests" txt of
        Right (x, state) -> Right (x, state.remaining)
        Left state -> Left state.remaining
  let parseExpected :: Parser a -> String -> (Maybe a, String, String)
      parseExpected parser txt = case parse parser "ParserTests" txt of
        Right (x, state) -> (Just x, state.expected, state.remaining)
        Left state -> (Nothing, state.expected, state.remaining)
  let parseShow :: (Show a) => Parser a -> String -> Maybe String
      parseShow parser txt = case parse parser "ParserTests" txt of
        Right (x, _) -> Just (show x)
        Left _ -> Nothing

  it "☯ ok" $ do
    let p = parse' (ok True)
    p "a" `shouldBe` Right (True, "a")

  it "☯ fail'" $ do
    let p = parse' (fail' :: Parser ())
    p "a" `shouldBe` Left "a"

  it "☯ anyChar" $ do
    let p = parse' anyChar
    p "" `shouldBe` Left ""
    p "abc" `shouldBe` Right ('a', "bc")
    p "1bc" `shouldBe` Right ('1', "bc")
    p "_bc" `shouldBe` Right ('_', "bc")

  it "☯ state" $ do
    let parser = do
          s1 <- state
          _ <- anyChar
          s2 <- state
          ok (s1, s2)
    let p = parse' parser
    let s1 = State {remaining = "abc", filename = "ParserTests", pos = Pos 1 1, index = 0, expected = "", committed = False}
    let s2 = s1 {remaining = "bc", index = 1, pos = Pos 1 2}
    p "abc" `shouldBe` Right ((s1, s2), "bc")

  it "☯ if'" $ do
    let p = parse' (if' (== 'a') anyChar)
    p "a" `shouldBe` Right ('a', "")
    p "b" `shouldBe` Left "b"

  it "☯ char" $ do
    let p = parse' (char 'a')
    p "abc" `shouldBe` Right ('a', "bc")
    p "Abc" `shouldBe` Left "Abc"
    p "0bc" `shouldBe` Left "0bc"
    p ".bc" `shouldBe` Left ".bc"

  it "☯ charNoCase" $ do
    let p = parse' (charNoCase 'a')
    p "abc" `shouldBe` Right ('a', "bc")
    p "Abc" `shouldBe` Right ('A', "bc")
    p "0bc" `shouldBe` Left "0bc"
    p ".bc" `shouldBe` Left ".bc"

  it "☯ letter" $ do
    let p = parse' letter
    p "abc" `shouldBe` Right ('a', "bc")
    p "Abc" `shouldBe` Right ('A', "bc")
    p "0bc" `shouldBe` Left "0bc"
    p ".bc" `shouldBe` Left ".bc"

  it "☯ lowercase" $ do
    let p = parse' lowercase
    p "abc" `shouldBe` Right ('a', "bc")
    p "Abc" `shouldBe` Left "Abc"
    p "0bc" `shouldBe` Left "0bc"
    p ".bc" `shouldBe` Left ".bc"

  it "☯ uppercase" $ do
    let p = parse' uppercase
    p "abc" `shouldBe` Left "abc"
    p "Abc" `shouldBe` Right ('A', "bc")
    p "0bc" `shouldBe` Left "0bc"
    p ".bc" `shouldBe` Left ".bc"

  it "☯ digit" $ do
    let p = parse' digit
    p "abc" `shouldBe` Left "abc"
    p "Abc" `shouldBe` Left "Abc"
    p "0bc" `shouldBe` Right ('0', "bc")
    p ".bc" `shouldBe` Left ".bc"

  it "☯ alphanumeric" $ do
    let p = parse' alphanumeric
    p "abc" `shouldBe` Right ('a', "bc")
    p "Abc" `shouldBe` Right ('A', "bc")
    p "0bc" `shouldBe` Right ('0', "bc")
    p ".bc" `shouldBe` Left ".bc"

  it "☯ punctuation" $ do
    let p = parse' punctuation
    p "abc" `shouldBe` Left "abc"
    p "Abc" `shouldBe` Left "Abc"
    p "0bc" `shouldBe` Left "0bc"
    p ".bc" `shouldBe` Right ('.', "bc")

  it "☯ space" $ do
    let p = parse' space
    p " bc" `shouldBe` Right (' ', "bc")
    p "\tbc" `shouldBe` Right ('\t', "bc")
    p "\nbc" `shouldBe` Left "\nbc"
    p "\rbc" `shouldBe` Left "\rbc"
    p "\fbc" `shouldBe` Left "\fbc"
    p "\vbc" `shouldBe` Left "\vbc"
    p "abc" `shouldBe` Left "abc"

  it "☯ whitespace" $ do
    let p = parse' whitespace
    p " bc" `shouldBe` Right (' ', "bc")
    p "\tbc" `shouldBe` Right ('\t', "bc")
    p "\nbc" `shouldBe` Right ('\n', "bc")
    p "\rbc" `shouldBe` Right ('\r', "bc")
    p "\fbc" `shouldBe` Right ('\f', "bc")
    p "\vbc" `shouldBe` Right ('\v', "bc")
    p "abc" `shouldBe` Left "abc"

  it "☯ oneOf" $ do
    let p = parse' (oneOf [char 'a', char 'A'])
    p "abc" `shouldBe` Right ('a', "bc")
    p "Abc" `shouldBe` Right ('A', "bc")
    p "0bc" `shouldBe` Left "0bc"

  it "☯ endOfFile" $ do
    let p = parse' endOfFile
    p "" `shouldBe` Right ((), "")
    p "\nabc" `shouldBe` Left "\nabc"
    p "abc" `shouldBe` Left "abc"

  it "☯ endOfLine" $ do
    let p = parse' endOfLine
    p "" `shouldBe` Right ((), "")
    p "\nabc" `shouldBe` Right ((), "abc")
    p "abc" `shouldBe` Left "abc"

  it "☯ chain" $ do
    let p = parse' (chain [char 'a', char 'b'])
    p "abc" `shouldBe` Right ("ab", "c")

  it "☯ text" $ do
    let p = parse' (text "hello")
    p "hello!" `shouldBe` Right ("hello", "!")
    p "Hello!" `shouldBe` Left "Hello!"
    p "h" `shouldBe` Left ""

  it "☯ textNoCase" $ do
    let p = parse' (textNoCase "hello")
    p "hello!" `shouldBe` Right ("hello", "!")
    p "Hello!" `shouldBe` Right ("Hello", "!")
    p "h" `shouldBe` Left ""

  it "☯ maybe'" $ do
    let p = parse' (maybe' letter)
    p "abc" `shouldBe` Right (Just 'a', "bc")
    p "ab" `shouldBe` Right (Just 'a', "b")
    p "a" `shouldBe` Right (Just 'a', "")
    p "" `shouldBe` Right (Nothing, "")

  it "☯ zeroOrOne" $ do
    let p = parse' (zeroOrOne letter)
    p "abc." `shouldBe` Right ("a", "bc.")
    p "ab." `shouldBe` Right ("a", "b.")
    p "a." `shouldBe` Right ("a", ".")
    p "." `shouldBe` Right ("", ".")

  it "☯ foldR" $ do
    let p = parse' (foldR (:) "" letter)
    p "" `shouldBe` Right ("", "")
    p "abc" `shouldBe` Right ("abc", "")

  it "☯ foldL" $ do
    let p = parse' (foldL (flip (:)) "" letter)
    p "" `shouldBe` Right ("", "")
    p "abc" `shouldBe` Right ("cba", "")

  it "☯ zeroOrMore" $ do
    let p = parse' (zeroOrMore letter)
    p "abc." `shouldBe` Right ("abc", ".")
    p "ab." `shouldBe` Right ("ab", ".")
    p "a." `shouldBe` Right ("a", ".")
    p "." `shouldBe` Right ("", ".")

  it "☯ oneOrMore" $ do
    let p = parse' (oneOrMore letter)
    p "abc" `shouldBe` Right ("abc", "")
    p "ab" `shouldBe` Right ("ab", "")
    p "a" `shouldBe` Right ("a", "")
    p "" `shouldBe` Left ""

  it "☯ exactly" $ do
    let p = parse' (exactly 2 letter)
    p "abc" `shouldBe` Right ("ab", "c")
    p "ab" `shouldBe` Right ("ab", "")
    p "a" `shouldBe` Left ""
    p "" `shouldBe` Left ""

  it "☯ atLeast" $ do
    let p = parse' (atLeast 2 letter)
    p "abc" `shouldBe` Right ("abc", "")
    p "ab" `shouldBe` Right ("ab", "")
    p "a" `shouldBe` Left ""
    p "" `shouldBe` Left ""

  it "☯ atMost" $ do
    let p = parse' (atMost 2 letter)
    p "abc" `shouldBe` Right ("ab", "c")
    p "ab" `shouldBe` Right ("ab", "")
    p "a" `shouldBe` Right ("a", "")
    p "" `shouldBe` Right ("", "")

  it "☯ between" $ do
    let p = parse' (between 1 2 letter)
    p "abc" `shouldBe` Right ("ab", "c")
    p "ab" `shouldBe` Right ("ab", "")
    p "a" `shouldBe` Right ("a", "")
    p "" `shouldBe` Left ""

  it "☯ expect" $ do
    let p = parseExpected (char 'a')
    p "abc" `shouldBe` (Just 'a', "", "bc")
    p "bc" `shouldBe` (Nothing, "'a'", "bc")

  it "☯ commit" $ do
    let parser = commit "committed" letter
    let p = parseExpected parser
    p "" `shouldBe` (Nothing, "letter", "")
    p "abc" `shouldBe` (Just 'a', "committed", "bc")
    p "123" `shouldBe` (Nothing, "letter", "123")

  it "☯ LL(k) parser -- expect + commit + oneOf" $ do
    let letters = do
          x <- commit "letter!" letter
          xs <- oneOrMore letter
          return (x : xs)
    let digits = do
          x <- commit "digit!" digit
          xs <- oneOrMore digit
          return (x : xs)
    let p = parseExpected (expect "alphanum" $ oneOf [letters, digits])
    p "" `shouldBe` (Nothing, "alphanum", "")
    p "a" `shouldBe` (Nothing, "alphanum", "a")
    p "a2" `shouldBe` (Nothing, "alphanum", "a2")
    p "ab" `shouldBe` (Just "ab", "", "")
    p "1" `shouldBe` (Nothing, "alphanum", "1")
    p "1b" `shouldBe` (Nothing, "alphanum", "1b")
    p "12" `shouldBe` (Just "12", "", "")

  it "☯ skipTo" $ do
    let p = parse' (skipTo (char '.'))
    p "" `shouldBe` Left ""
    p ".abc" `shouldBe` Right ("", ".abc")
    p "a.bc" `shouldBe` Right ("a", ".bc")
    p "ab.c" `shouldBe` Right ("ab", ".c")
    p "abc." `shouldBe` Right ("abc", ".")
    p "abc" `shouldBe` Left "abc"

  it "☯ integer" $ do
    let p = parse' integer
    p "42" `shouldBe` Right (42, "")
    p "a" `shouldBe` Left "a"

  it "☯ number" $ do
    let p = parse' number
    p "3.14" `shouldBe` Right (3.14, "")
    p "3" `shouldBe` Right (3.0, "")
    p "a" `shouldBe` Left "a"

  it "☯ lookahead" $ do
    let p = parse' (lookahead letter)
    p "abc" `shouldBe` Right ((), "abc")
    p "123" `shouldBe` Left "123"

  it "☯ lookaheadNot" $ do
    let p = parse' (lookaheadNot letter)
    p "abc" `shouldBe` Left "abc"
    p "123" `shouldBe` Right ((), "123")

  it "☯ subparser" $ do
    let p = parse' (subparser (text "--}") (zeroOrMore anyChar))
    p "--}abc" `shouldBe` Right ("", "--}abc")
    p "a--}bc" `shouldBe` Right ("a", "--}bc")
    p "ab--}c" `shouldBe` Right ("ab", "--}c")
    p "abc--}" `shouldBe` Right ("abc", "--}")

  it "☯ precedence" $ do
    let ops =
          [ atom Var (oneOrMore letter),
            group (text "(") (text ")") spaces,
            infixL 1 (\_ _ -> Add) spaces (text "+"),
            infixL 1 (\_ _ -> Sub) spaces (text "-"),
            infixL 2 (\_ _ -> Mul) spaces (text "*"),
            prefix 3 (\_ _ -> Neg) spaces (text "-"),
            infixR 4 (\_ _ -> Pow) spaces (text "^"),
            suffix 5 (\_ _ -> Fac) spaces (text "!"),
            prefix 5 (\_ _ -> At) spaces (text "@")
          ]
        expr = precedence ops 0

    let p = parseShow expr
    -- Unary operators
    p "x" `shouldBe` Just "x"
    p "-x" `shouldBe` Just "(-x)"
    p "x!" `shouldBe` Just "(x!)"
    p "-x!" `shouldBe` Just "(-(x!))"
    p "@x!" `shouldBe` Just "((@x)!)"
    p "--x" `shouldBe` Just "(-(-x))"
    p "-@x" `shouldBe` Just "(-(@x))"
    p "@-x" `shouldBe` Nothing

    -- Binary operators
    p "x + y" `shouldBe` Just "(x + y)"
    p "x - y" `shouldBe` Just "(x - y)"
    p "x * y" `shouldBe` Just "(x * y)"
    p "x ^ y" `shouldBe` Just "(x ^ y)"
    p "-x - -y" `shouldBe` Just "((-x) - (-y))"
    p "x + y + z" `shouldBe` Just "((x + y) + z)"
    p "x + y - z" `shouldBe` Just "((x + y) - z)"
    p "x - y + z" `shouldBe` Just "((x - y) + z)"
    p "x + y * z" `shouldBe` Just "(x + (y * z))"
    p "x * y + z" `shouldBe` Just "((x * y) + z)"
    p "x * y * z" `shouldBe` Just "((x * y) * z)"
    p "x * y ^ z" `shouldBe` Just "(x * (y ^ z))"
    p "x ^ y * z" `shouldBe` Just "((x ^ y) * z)"
    p "x ^ y ^ z" `shouldBe` Just "(x ^ (y ^ z))"
    p "(x ^ y) ^ z" `shouldBe` Just "((x ^ y) ^ z)"
    p "x ^ (y ^ z)" `shouldBe` Just "(x ^ (y ^ z))"
