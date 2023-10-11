module ParserTests where

import Flow ((|>))
import Parser
import Test.Hspec (SpecWith, describe, it, shouldBe)

run :: SpecWith ()
run = describe "--==☯ Parser ☯==--" $ do
  let parse' :: Parser a -> String -> Maybe (a, String)
      parse' parser source = case parse "test" parser source of
        Right (x, State {source = remaining}) -> Just (x, remaining)
        Left _ -> Nothing

  describe "☯ Control flow" $ do
    it "☯ succeed" $ do
      parse' (succeed True) "abc" `shouldBe` Just (True, "abc")

    it "☯ fail'" $ do
      parse' (fail' :: Parser ()) "abc" `shouldBe` Nothing

    it "☯ fmap" $ do
      parse' (fmap not (succeed True)) "abc" `shouldBe` Just (False, "abc")

    it "☯ orElse" $ do
      parse' (succeed True |> orElse (succeed False)) "abc" `shouldBe` Just (True, "abc")
      parse' (fail' |> orElse (succeed False)) "abc" `shouldBe` Just (False, "abc")

    it "☯ oneOf" $ do
      parse' (oneOf [] :: Parser ()) "abc" `shouldBe` Nothing
      parse' (oneOf [char 'a']) "abc" `shouldBe` Just ('a', "bc")
      parse' (oneOf [char 'b', char 'a']) "abc" `shouldBe` Just ('a', "bc")

    it "☯ endOfFile" $ do
      let p = parse' endOfFile
      p "" `shouldBe` Just ((), "")
      p "\nabc" `shouldBe` Nothing
      p "abc" `shouldBe` Nothing

    it "☯ endOfLine" $ do
      let p = parse' endOfLine
      p "" `shouldBe` Just ((), "")
      p "\nabc" `shouldBe` Just ((), "abc")
      p "abc" `shouldBe` Nothing

  describe "☯ Single characters" $ do
    it "☯ anyChar" $ do
      let p = parse' anyChar
      p "abc" `shouldBe` Just ('a', "bc")
      p "1bc" `shouldBe` Just ('1', "bc")
      p "_bc" `shouldBe` Just ('_', "bc")
      p "" `shouldBe` Nothing

    it "☯ space" $ do
      let p = parse' space
      p " bc" `shouldBe` Just (' ', "bc")
      p "\tbc" `shouldBe` Just ('\t', "bc")
      -- p "\nbc" `shouldBe` Just ('\n', "bc")
      p "\rbc" `shouldBe` Just ('\r', "bc")
      p "\fbc" `shouldBe` Just ('\f', "bc")
      p "\vbc" `shouldBe` Just ('\v', "bc")
      p "abc" `shouldBe` Nothing

    it "☯ letter" $ do
      let p = parse' letter
      p "abc" `shouldBe` Just ('a', "bc")
      p "Abc" `shouldBe` Just ('A', "bc")
      p "0bc" `shouldBe` Nothing
      p ".bc" `shouldBe` Nothing

    it "☯ lowercase" $ do
      let p = parse' lowercase
      p "abc" `shouldBe` Just ('a', "bc")
      p "Abc" `shouldBe` Nothing
      p "0bc" `shouldBe` Nothing
      p ".bc" `shouldBe` Nothing

    it "☯ uppercase" $ do
      let p = parse' uppercase
      p "abc" `shouldBe` Nothing
      p "Abc" `shouldBe` Just ('A', "bc")
      p "0bc" `shouldBe` Nothing
      p ".bc" `shouldBe` Nothing

    it "☯ digit" $ do
      let p = parse' digit
      p "abc" `shouldBe` Nothing
      p "Abc" `shouldBe` Nothing
      p "0bc" `shouldBe` Just ('0', "bc")
      p ".bc" `shouldBe` Nothing

    it "☯ alphanumeric" $ do
      let p = parse' alphanumeric
      p "abc" `shouldBe` Just ('a', "bc")
      p "Abc" `shouldBe` Just ('A', "bc")
      p "0bc" `shouldBe` Just ('0', "bc")
      p ".bc" `shouldBe` Nothing

    it "☯ punctuation" $ do
      let p = parse' punctuation
      p "abc" `shouldBe` Nothing
      p "Abc" `shouldBe` Nothing
      p "0bc" `shouldBe` Nothing
      p ".bc" `shouldBe` Just ('.', "bc")

    it "☯ char" $ do
      let p = parse' (char 'a')
      p "abc" `shouldBe` Just ('a', "bc")
      p "Abc" `shouldBe` Just ('A', "bc")
      p "0bc" `shouldBe` Nothing
      p ".bc" `shouldBe` Nothing

    it "☯ charCaseSensitive" $ do
      let p = parse' (charCaseSensitive 'a')
      p "abc" `shouldBe` Just ('a', "bc")
      p "Abc" `shouldBe` Nothing
      p "0bc" `shouldBe` Nothing
      p ".bc" `shouldBe` Nothing

  describe "☯ Sequences" $ do
    it "☯ chain" $ do
      let p = parse' (chain [char '_', letter, digit])
      p "_A5." `shouldBe` Just ("_A5", ".")

    it "☯ maybe'" $ do
      let p = parse' (maybe' letter)
      p "abc" `shouldBe` Just (Just 'a', "bc")
      p "ab" `shouldBe` Just (Just 'a', "b")
      p "a" `shouldBe` Just (Just 'a', "")
      p "" `shouldBe` Just (Nothing, "")

    it "☯ zeroOrOne" $ do
      let p = parse' (zeroOrOne letter)
      p "abc" `shouldBe` Just ("a", "bc")
      p "ab" `shouldBe` Just ("a", "b")
      p "a" `shouldBe` Just ("a", "")
      p "" `shouldBe` Just ("", "")

    it "☯ zeroOrMore" $ do
      let p = parse' (zeroOrMore letter)
      p "abc" `shouldBe` Just ("abc", "")
      p "ab" `shouldBe` Just ("ab", "")
      p "a" `shouldBe` Just ("a", "")
      p "" `shouldBe` Just ("", "")

    it "☯ oneOrMore" $ do
      let p = parse' (oneOrMore letter)
      p "abc" `shouldBe` Just ("abc", "")
      p "ab" `shouldBe` Just ("ab", "")
      p "a" `shouldBe` Just ("a", "")
      p "" `shouldBe` Nothing

    it "☯ exactly" $ do
      let p = parse' (exactly 2 letter)
      p "abc" `shouldBe` Just ("ab", "c")
      p "ab" `shouldBe` Just ("ab", "")
      p "a" `shouldBe` Nothing
      p "" `shouldBe` Nothing

    it "☯ atLeast" $ do
      let p = parse' (atLeast 2 letter)
      p "abc" `shouldBe` Just ("abc", "")
      p "ab" `shouldBe` Just ("ab", "")
      p "a" `shouldBe` Nothing
      p "" `shouldBe` Nothing

    it "☯ atMost" $ do
      let p = parse' (atMost 2 letter)
      p "abc" `shouldBe` Just ("ab", "c")
      p "ab" `shouldBe` Just ("ab", "")
      p "a" `shouldBe` Just ("a", "")
      p "" `shouldBe` Just ("", "")

    it "☯ between" $ do
      let p = parse' (between 1 2 letter)
      p "abc" `shouldBe` Just ("ab", "c")
      p "ab" `shouldBe` Just ("ab", "")
      p "a" `shouldBe` Just ("a", "")
      p "" `shouldBe` Nothing

    -- it "☯ split" $ do
    --   p "" (split (char ',') letter) `shouldBe` Just []
    --   p "a,b,c" (split (char ',') letter) `shouldBe` Just ['a', 'b', 'c']

    it "☯ until" $ do
      let p = parse' (until' (== 'c') letter)
      p "abc" `shouldBe` Just ("ab", "c")
      p "ab1" `shouldBe` Just ("ab", "1")
      p "ab" `shouldBe` Just ("ab", "")
      p "" `shouldBe` Just ("", "")

    it "☯ foldL" $ do
      let p = parse' (foldL (flip (:)) "" letter)
      p "" `shouldBe` Just ("", "")
      p "abc" `shouldBe` Just ("cba", "")

    it "☯ foldR" $ do
      let p = parse' (foldR (:) "" letter)
      p "" `shouldBe` Just ("", "")
      p "abc" `shouldBe` Just ("abc", "")

  describe "☯ Common" $ do
    it "☯ integer" $ do
      let p = parse' integer
      p "11" `shouldBe` Just (11, "")
      p "a" `shouldBe` Nothing

    it "☯ number" $ do
      let p = parse' number
      p "3.14" `shouldBe` Just (3.14, "")
      p "3" `shouldBe` Just (3.0, "")
      p "a" `shouldBe` Nothing

    it "☯ text" $ do
      let p = parse' (text "hello")
      p "hello!" `shouldBe` Just ("hello", "!")
      p "Hello!" `shouldBe` Just ("Hello", "!")
      p "H" `shouldBe` Nothing

    it "☯ textCaseSensitive" $ do
      let p = parse' (textCaseSensitive "hello")
      p "hello!" `shouldBe` Just ("hello", "!")
      p "Hello!" `shouldBe` Nothing
      p "H" `shouldBe` Nothing

    it "☯ followedBy" $ do
      let p = parse' (letter |> followedBy (char 'b'))
      p "abc" `shouldBe` Just ('a', "bc")
      p "a_c" `shouldBe` Nothing

    it "☯ notFollowedBy" $ do
      let p = parse' (letter |> notFollowedBy (char 'b'))
      p "abc" `shouldBe` Nothing
      p "a_c" `shouldBe` Just ('a', "_c")

    -- it "☯ tok (TODO: rename to token)" $ do
    --   p "a" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', "")]
    --   p "a" (oneOrMore $ tok " " letter) `shouldBe` Nothing
    --   p " a" (oneOrMore $ tok " " letter) `shouldBe` Just [('a', " ")]
    --   p "  a" (oneOrMore $ tok " " letter) `shouldBe` Just [('a', "  ")]
    --   p "ab" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', ""), ('b', "")]
    --   p "a b" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', ""), ('b', "")]
    --   p "a \nb" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', ""), ('b', "")]
    --   p "a \n  b" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', ""), ('b', "  ")]

    -- it "☯ token" $ do
    --   p "a" (oneOrMore (token letter)) `shouldBe` Just "a"
    --   p "a b" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   p "a\tb" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   -- p "a\nb" (oneOrMore (token letter)) `shouldBe` Just "a"
    --   -- p "a\n b" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   -- p "a\n\n b" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   -- p "a\n   \n b" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   True `shouldBe` True

    it "☯ subparser" $ do
      let p = parse' (subparser (text "--}") (zeroOrMore anyChar))
      p "--}abc" `shouldBe` Just ("", "--}abc")
      p "a--}bc" `shouldBe` Just ("a", "--}bc")
      p "ab--}c" `shouldBe` Just ("ab", "--}c")
      p "abc--}" `shouldBe` Just ("abc", "--}")

    it "☯ collection" $ do
      let p = parse' (collection (char '[') letter (char ',') (char ']'))
      p "" `shouldBe` Nothing
      p "[" `shouldBe` Nothing
      p "[]" `shouldBe` Just ("", "")
      p "[a]" `shouldBe` Just ("a", "")
      p "[a,]" `shouldBe` Just ("a", "")
      p "[a,b,c]" `shouldBe` Just ("abc", "")
      p "[a,b,c,]" `shouldBe` Just ("abc", "")

    it "☯ withOperators" $ do
      let calculator =
            withOperators
              [ constant number,
                prefix 4 (\x -> -x) (char '-'),
                inbetween (char '(') (char ')')
              ]
              [ infixL 1 (+) (char '+'),
                infixL 1 (-) (char '-'),
                infixL 2 (*) (char '*'),
                infixR 3 (**) (char '^')
              ]
              0

      let p = parse' calculator
      p "1" `shouldBe` Just (1.0, "")
      p "-1" `shouldBe` Just (-1.0, "")
      p "--1" `shouldBe` Just (1.0, "")
      p "1+2" `shouldBe` Just (3.0, "")
      p "1-2" `shouldBe` Just (-1.0, "")
      p "1*2" `shouldBe` Just (2.0, "")
      p "1^2" `shouldBe` Just (1.0, "")
      p "1+2+3" `shouldBe` Just (6.0, "")
      p "1-2-3" `shouldBe` Just (-4.0, "")
      p "1+2*3" `shouldBe` Just (7.0, "")
      p "3*2+1" `shouldBe` Just (7.0, "")
      p "2^2^3" `shouldBe` Just (256.0, "")
      p "1+-2+3" `shouldBe` Just (2.0, "")
      p "(1+2)*3" `shouldBe` Just (9.0, "")
