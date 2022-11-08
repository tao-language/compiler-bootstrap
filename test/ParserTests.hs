module ParserTests where

import Parser
import Test.Hspec (SpecWith, describe, it, shouldBe)

parserTests :: SpecWith ()
parserTests = describe "--== Parser ==--" $ do
  let parse' :: String -> Parser a -> Maybe a
      parse' source parser = case parse source parser of
        Left (ParserError _ _) -> Nothing
        Right x -> Just x

  describe "☯ Control flow" $ do
    it "☯ succeed" $ do
      parse' "abc" (succeed True) `shouldBe` Just True

    it "☯ expected" $ do
      parse' "abc" (expected "something" :: Parser ()) `shouldBe` Nothing

    it "☯ fmap" $ do
      parse' "abc" (fmap not (succeed True)) `shouldBe` Just False

    it "☯ orElse" $ do
      parse' "abc" (succeed True |> orElse (succeed False)) `shouldBe` Just True
      parse' "abc" (expected "something" |> orElse (succeed False)) `shouldBe` Just False

    it "☯ oneOf" $ do
      parse' "abc" (oneOf [] :: Parser ()) `shouldBe` Nothing
      parse' "abc" (oneOf [char 'a']) `shouldBe` Just 'a'
      parse' "abc" (oneOf [char 'b', char 'a']) `shouldBe` Just 'a'

    it "☯ endOfFile" $ do
      parse' "" endOfFile `shouldBe` Just ()
      parse' "\n" endOfFile `shouldBe` Nothing
      parse' "a" endOfFile `shouldBe` Nothing

    it "☯ endOfLine" $ do
      parse' "" endOfLine `shouldBe` Just ()
      parse' "\n" endOfLine `shouldBe` Just ()
      parse' "a" endOfLine `shouldBe` Nothing

  describe "☯ Single characters" $ do
    it "☯ anyChar" $ do
      parse' "abc" anyChar `shouldBe` Just 'a'
      parse' "" anyChar `shouldBe` Nothing

    it "☯ space" $ do
      parse' " " space `shouldBe` Just ' '
      parse' "\t" space `shouldBe` Just '\t'
      -- parse' "\n" space `shouldBe` Just '\n'
      parse' "\r" space `shouldBe` Just '\r'
      parse' "\f" space `shouldBe` Just '\f'
      parse' "\v" space `shouldBe` Just '\v'
      parse' "a" space `shouldBe` Nothing

    it "☯ letter" $ do
      parse' "a" letter `shouldBe` Just 'a'
      parse' "A" letter `shouldBe` Just 'A'
      parse' " " letter `shouldBe` Nothing

    it "☯ lowercase" $ do
      parse' "a" lowercase `shouldBe` Just 'a'
      parse' "A" lowercase `shouldBe` Nothing

    it "☯ uppercase" $ do
      parse' "A" uppercase `shouldBe` Just 'A'
      parse' "a" uppercase `shouldBe` Nothing

    it "☯ digit" $ do
      parse' "0" digit `shouldBe` Just '0'
      parse' "a" digit `shouldBe` Nothing

    it "☯ alphanumeric" $ do
      parse' "0" alphanumeric `shouldBe` Just '0'
      parse' "a" alphanumeric `shouldBe` Just 'a'
      parse' " " alphanumeric `shouldBe` Nothing

    it "☯ punctuation" $ do
      parse' "." punctuation `shouldBe` Just '.'
      parse' "?" punctuation `shouldBe` Just '?'
      parse' " " punctuation `shouldBe` Nothing

    it "☯ char" $ do
      parse' "a" (char 'a') `shouldBe` Just 'a'
      parse' "A" (char 'a') `shouldBe` Just 'A'
      parse' " " (char 'a') `shouldBe` Nothing

    it "☯ charCaseSensitive" $ do
      parse' "a" (charCaseSensitive 'a') `shouldBe` Just 'a'
      parse' "A" (charCaseSensitive 'a') `shouldBe` Nothing

  describe "☯ Sequences" $ do
    it "☯ maybe'" $ do
      parse' "abc!" (maybe' letter) `shouldBe` Just (Just 'a')
      parse' "_bc!" (maybe' letter) `shouldBe` Just Nothing

    it "☯ zeroOrOne" $ do
      parse' "abc!" (zeroOrOne letter) `shouldBe` Just ['a']
      parse' "_bc!" (zeroOrOne letter) `shouldBe` Just []

    it "☯ zeroOrMore" $ do
      parse' "abc!" (zeroOrMore letter) `shouldBe` Just ['a', 'b', 'c']
      parse' "_bc!" (zeroOrMore letter) `shouldBe` Just []

    it "☯ oneOrMore" $ do
      parse' "abc!" (oneOrMore letter) `shouldBe` Just ['a', 'b', 'c']
      parse' "_bc!" (oneOrMore letter) `shouldBe` Nothing

    it "☯ chain" $ do
      parse' "_A5" (chain [] :: Parser [()]) `shouldBe` Just []
      parse' "_A5" (chain [char '_', letter, digit]) `shouldBe` Just ['_', 'A', '5']

    it "☯ exactly" $ do
      parse' "aaa" (exactly 2 (char 'a')) `shouldBe` Just "aa"
      parse' "abc" (exactly 2 (char 'a')) `shouldBe` Nothing

    it "☯ atLeast" $ do
      parse' "aaa" (atLeast 2 (char 'a')) `shouldBe` Just "aaa"
      parse' "abc" (atLeast 2 (char 'a')) `shouldBe` Nothing

    it "☯ atMost" $ do
      parse' "aaa" (atMost 2 (char 'a')) `shouldBe` Just "aa"
      parse' "abc" (atMost 2 (char 'a')) `shouldBe` Just "a"

    it "☯ between" $ do
      parse' "aaa" (between 1 2 (char 'a')) `shouldBe` Just "aa"
      parse' "abc" (between 1 2 (char 'a')) `shouldBe` Just "a"
      parse' "_" (between 1 2 (char 'a')) `shouldBe` Nothing

    -- it "☯ split" $ do
    --   parse' "" (split (char ',') letter) `shouldBe` Just []
    --   parse' "a,b,c" (split (char ',') letter) `shouldBe` Just ['a', 'b', 'c']

    it "☯ until" $ do
      parse' "abc" (until' (== 'c') letter) `shouldBe` Just "ab"
      parse' "ab1" (until' (== 'c') letter) `shouldBe` Just "ab"
      parse' "ab" (until' (== 'c') letter) `shouldBe` Just "ab"
      parse' "" (until' (== 'c') letter) `shouldBe` Just ""

    it "☯ foldL" $ do
      parse' "." (foldL (flip (:)) "" letter) `shouldBe` Just ""
      parse' "abc." (foldL (flip (:)) "" letter) `shouldBe` Just "cba"

    it "☯ foldR" $ do
      parse' "." (foldR (:) "" letter) `shouldBe` Just ""
      parse' "abc." (foldR (:) "" letter) `shouldBe` Just "abc"

  describe "☯ Common" $ do
    it "☯ integer" $ do
      parse' "11" integer `shouldBe` Just 11
      parse' "a" integer `shouldBe` Nothing

    it "☯ number" $ do
      parse' "3.14" number `shouldBe` Just 3.14
      parse' "3" number `shouldBe` Just 3.0
      parse' "a" number `shouldBe` Nothing

    it "☯ text" $ do
      parse' "Hello" (text "hello") `shouldBe` Just "Hello"
      parse' "H" (text "hello") `shouldBe` Nothing

    it "☯ textCaseSensitive" $ do
      parse' "hello" (textCaseSensitive "hello") `shouldBe` Just "hello"
      parse' "Hello" (textCaseSensitive "hello") `shouldBe` Nothing

    -- it "☯ tok (TODO: rename to token)" $ do
    --   parse' "a" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', "")]
    --   parse' "a" (oneOrMore $ tok " " letter) `shouldBe` Nothing
    --   parse' " a" (oneOrMore $ tok " " letter) `shouldBe` Just [('a', " ")]
    --   parse' "  a" (oneOrMore $ tok " " letter) `shouldBe` Just [('a', "  ")]
    --   parse' "ab" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', ""), ('b', "")]
    --   parse' "a b" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', ""), ('b', "")]
    --   parse' "a \nb" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', ""), ('b', "")]
    --   parse' "a \n  b" (oneOrMore $ tok "" letter) `shouldBe` Just [('a', ""), ('b', "  ")]

    -- it "☯ token" $ do
    --   parse' "a" (oneOrMore (token letter)) `shouldBe` Just "a"
    --   parse' "a b" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   parse' "a\tb" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   -- parse' "a\nb" (oneOrMore (token letter)) `shouldBe` Just "a"
    --   -- parse' "a\n b" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   -- parse' "a\n\n b" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   -- parse' "a\n   \n b" (oneOrMore (token letter)) `shouldBe` Just "ab"
    --   True `shouldBe` True

    it "☯ collection" $ do
      let collection' = collection (char '[') (char ']') (char ',') letter
      parse' "" collection' `shouldBe` Nothing
      parse' "[" collection' `shouldBe` Nothing
      parse' "[]" collection' `shouldBe` Just ""
      parse' "[a]" collection' `shouldBe` Just "a"
      parse' "[a,b,c]" collection' `shouldBe` Just "abc"

    it "☯ withOperators" $ do
      let calculator =
            withOperators
              [ prefix (\_ x -> - x) (char '-'),
                atom id number,
                inbetween (const id) (char '(') (char ')')
              ]
              [ infixL 1 (const (+)) (char '+'),
                infixL 1 (const (-)) (char '-'),
                infixL 2 (const (*)) (char '*'),
                infixR 3 (const (**)) (char '^')
              ]
      parse "1" calculator `shouldBe` Right 1.0
      parse "-1" calculator `shouldBe` Right (-1.0)
      parse "--1" calculator `shouldBe` Right 1.0
      parse "1+2" calculator `shouldBe` Right 3.0
      parse "1-2-3" calculator `shouldBe` Right (-4.0)
      parse "1+2*3" calculator `shouldBe` Right 7.0
      parse "3*2+1" calculator `shouldBe` Right 7.0
      parse "2^2^3" calculator `shouldBe` Right 256.0
      -- parse "1+-2+3" calculator `shouldBe` Right 1.0
      parse "(1+2)*3" calculator `shouldBe` Right 9.0
