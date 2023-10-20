{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}

module ParserTests where

import qualified Data.Char as Char
import Flow ((|>))
import Parser
import Test.Hspec (SpecWith, describe, it, shouldBe)

type Context = String

data Expr -- for `operators`
  = Var !String
  | Neg !Expr
  | At !Expr
  | Factorial !Expr
  | Add !Expr !Expr
  | Mul !Expr !Expr
  | Sub !Expr !Expr
  | Pow !Expr !Expr
  deriving (Eq)

instance Show Expr where
  show :: Expr -> String
  show (Var x) = x
  show (Neg x) = "(-" ++ show x ++ ")"
  show (At x) = "(@" ++ show x ++ ")"
  show (Factorial x) = "(" ++ show x ++ "!)"
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Pow x y) = "(" ++ show x ++ " ^ " ++ show y ++ ")"

run :: SpecWith ()
run = describe "--==☯ Parser ☯==--" $ do
  let parse' :: Parser Context a -> String -> Either String (a, String)
      parse' parser txt = case parse "test" parser txt of
        Right (x, state) -> Right (x, state.remaining)
        Left state -> Left state.remaining
  let parseErrors :: Parser Context a -> String -> (Maybe a, [Context], String)
      parseErrors parser txt = case parse "test" parser txt of
        Right (x, state) -> (Just x, state.context, state.remaining)
        Left state -> (Nothing, state.context, state.remaining)
  let parseShow :: (Show a) => Parser Context a -> String -> Maybe String
      parseShow parser txt = case parse "test" parser txt of
        Right (x, _) -> Just (show x)
        Left _ -> Nothing

  it "☯ ok" $ do
    let p = parse' (ok True)
    p "a" `shouldBe` Right (True, "a")

  it "☯ fail'" $ do
    let p = parse' (fail' :: Parser Context ())
    p "a" `shouldBe` Left "a"

  it "☯ anyChar" $ do
    let p = parse' anyChar
    p "" `shouldBe` Left ""
    p "abc" `shouldBe` Right ('a', "bc")
    p "1bc" `shouldBe` Right ('1', "bc")
    p "_bc" `shouldBe` Right ('_', "bc")

  it "☯ getState" $ do
    let parser = do
          s1 <- getState
          _ <- anyChar
          s2 <- getState
          ok (s1, s2)
    let p = parse' parser
    let s1 = State {remaining = "abc", name = "test", row = 1, col = 1, index = 0, context = []}
    let s2 = s1 {remaining = "bc", index = 1, col = 2}
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

  it "☯ choose" $ do
    let p = parse' (choose [(char 'a', const $ char 'b'), (char 'A', const $ char 'B'), (ok '\0', const $ char '_')])
    p "abc" `shouldBe` Right ('b', "c")
    p "aBc" `shouldBe` Left "Bc"
    p "Abc" `shouldBe` Left "bc"
    p "ABc" `shouldBe` Right ('B', "c")
    p "0bc" `shouldBe` Left "0bc"

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

  it "☯ scope" $ do
    let p = parseErrors (scope "letter" letter)
    p "abc" `shouldBe` (Just 'a', [], "bc")
    p "_bc" `shouldBe` (Nothing, ["letter"], "_bc")

  it "☯ skipTo" $ do
    let p = parse' (skipTo (char '.'))
    p "" `shouldBe` Left ""
    p ".abc" `shouldBe` Right ("", "abc")
    p "a.bc" `shouldBe` Right ("a", "bc")
    p "ab.c" `shouldBe` Right ("ab", "c")
    p "abc." `shouldBe` Right ("abc", "")
    p "abc" `shouldBe` Left "abc"

  it "☯ try" $ do
    let p = parseErrors (try (do x <- scope "letters" $ oneOrMore letter; _ <- scope "dot" $ char '.'; ok x) (scope "failed dot" $ skipTo (char '.')))
    p ".abc" `shouldBe` (Just $ Left "", ["letters"], "abc")
    p "_.abc" `shouldBe` (Just $ Left "_", ["letters"], "abc")
    p "a_.bc" `shouldBe` (Just $ Left "a_", ["dot"], "bc")
    p "ab.c" `shouldBe` (Just $ Right "ab", [], "c")
    p "abc." `shouldBe` (Just $ Right "abc", [], "")
    p "abc" `shouldBe` (Nothing, ["failed dot", "dot"], "abc")

  it "☯ integer" $ do
    let p = parse' integer
    p "42" `shouldBe` Right (42, "")
    p "a" `shouldBe` Left "a"

  it "☯ number" $ do
    let p = parse' number
    p "3.14" `shouldBe` Right (3.14, "")
    p "3" `shouldBe` Right (3.0, "")
    p "a" `shouldBe` Left "a"

  it "☯ followedBy" $ do
    let p = parse' (letter |> followedBy (char 'b'))
    p "abc" `shouldBe` Right ('a', "bc")
    p "a_c" `shouldBe` Left "a_c"

  it "☯ notFollowedBy" $ do
    let p = parse' (letter |> notFollowedBy (char 'b'))
    p "abc" `shouldBe` Left "abc"
    p "a_c" `shouldBe` Right ('a', "_c")

  it "☯ subparser" $ do
    let p = parse' (subparser (text "--}") (zeroOrMore anyChar))
    p "--}abc" `shouldBe` Right ("", "--}abc")
    p "a--}bc" `shouldBe` Right ("a", "--}bc")
    p "ab--}c" `shouldBe` Right ("ab", "--}c")
    p "abc--}" `shouldBe` Right ("abc", "--}")

  it "☯ operators" $ do
    let op x = padded whitespaces (text x)
        ops =
          [ infixL 1 (const Add) (op "+"),
            infixL 1 (const Sub) (op "-"),
            infixL 2 (const Mul) (op "*"),
            prefix 3 (const Neg) (op "-"),
            infixR 4 (const Pow) (op "^"),
            suffix 5 (const Factorial) (op "!"),
            prefix 5 (const At) (op "@")
          ]
        atom =
          oneOf
            [ inbetween (op "(") (op ")") expr,
              Var <$> oneOrMore letter
            ]
        expr = operators 0 ops atom

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
