module ParserTests where

import Parser
import Test.Hspec (SpecWith, describe, it, shouldBe)

parserTests :: SpecWith ()
parserTests = describe "--== Parser ==--" $ do
  let parse' :: String -> Parser a -> Either String a
      parse' source parser = case parse source parser of
        Left (ParserError message _) -> Left message
        Right x -> Right x

  describe "☯ Control flow" $ do
    it "☯ succeed" $ do
      parse' "abc" (succeed True) `shouldBe` Right True

    it "☯ expected" $ do
      parse' "abc" (expected "something" :: Parser ()) `shouldBe` Left "something"

    it "☯ fmap" $ do
      parse' "abc" (fmap not (succeed True)) `shouldBe` Right False

    it "☯ orElse" $ do
      parse' "abc" (succeed True |> orElse (succeed False)) `shouldBe` Right True
      parse' "abc" (expected "something" |> orElse (succeed False)) `shouldBe` Right False

    it "☯ oneOf" $ do
      parse' "abc" (oneOf [] :: Parser ()) `shouldBe` Left "a valid choice"
      parse' "abc" (oneOf [char 'a']) `shouldBe` Right 'a'
      parse' "abc" (oneOf [char 'b', char 'a']) `shouldBe` Right 'a'

    it "☯ endOfFile" $ do
      parse' "" endOfFile `shouldBe` Right ()
      parse' "a" endOfFile `shouldBe` Left "end of file"

    it "☯ endOfLine" $ do
      parse' "\n" endOfLine `shouldBe` Right ()
      parse' "" endOfLine `shouldBe` Right ()

  describe "☯ Single characters" $ do
    it "☯ anyChar" $ do
      parse' "abc" anyChar `shouldBe` Right 'a'
      parse' "" anyChar `shouldBe` Left "a character"

    it "☯ space" $ do
      parse' " " space `shouldBe` Right ' '
      parse' "\t" space `shouldBe` Right '\t'
      parse' "\n" space `shouldBe` Right '\n'
      parse' "\r" space `shouldBe` Right '\r'
      parse' "\f" space `shouldBe` Right '\f'
      parse' "\v" space `shouldBe` Right '\v'
      parse' "a" space `shouldBe` Left "a blank space"

    it "☯ letter" $ do
      parse' "a" letter `shouldBe` Right 'a'
      parse' "A" letter `shouldBe` Right 'A'
      parse' " " letter `shouldBe` Left "a letter"

    it "☯ lowercase" $ do
      parse' "a" lowercase `shouldBe` Right 'a'
      parse' "A" lowercase `shouldBe` Left "a lowercase letter"

    it "☯ uppercase" $ do
      parse' "A" uppercase `shouldBe` Right 'A'
      parse' "a" uppercase `shouldBe` Left "an uppercase letter"

    it "☯ digit" $ do
      parse' "0" digit `shouldBe` Right '0'
      parse' "a" digit `shouldBe` Left "a digit from 0 to 9"

    it "☯ alphanumeric" $ do
      parse' "0" alphanumeric `shouldBe` Right '0'
      parse' "a" alphanumeric `shouldBe` Right 'a'
      parse' " " alphanumeric `shouldBe` Left "a letter or digit"

    it "☯ punctuation" $ do
      parse' "." punctuation `shouldBe` Right '.'
      parse' "?" punctuation `shouldBe` Right '?'
      parse' " " punctuation `shouldBe` Left "a punctuation character"

    it "☯ char" $ do
      parse' "a" (char 'a') `shouldBe` Right 'a'
      parse' "A" (char 'a') `shouldBe` Right 'A'
      parse' " " (char 'a') `shouldBe` Left "the character 'a'"

    it "☯ charCaseSensitive" $ do
      parse' "a" (charCaseSensitive 'a') `shouldBe` Right 'a'
      parse' "A" (charCaseSensitive 'a') `shouldBe` Left "the character 'a' (case sensitive)"

  describe "☯ Sequences" $ do
    it "☯ maybe'" $ do
      parse' "abc!" (maybe' letter) `shouldBe` Right (Just 'a')
      parse' "_bc!" (maybe' letter) `shouldBe` Right Nothing

    it "☯ zeroOrOne" $ do
      parse' "abc!" (zeroOrOne letter) `shouldBe` Right ['a']
      parse' "_bc!" (zeroOrOne letter) `shouldBe` Right []

    it "☯ zeroOrMore" $ do
      parse' "abc!" (zeroOrMore letter) `shouldBe` Right ['a', 'b', 'c']
      parse' "_bc!" (zeroOrMore letter) `shouldBe` Right []

    it "☯ oneOrMore" $ do
      parse' "abc!" (oneOrMore letter) `shouldBe` Right ['a', 'b', 'c']
      parse' "_bc!" (oneOrMore letter) `shouldBe` Left "a letter"

    it "☯ chain" $ do
      parse' "_A5" (chain [] :: Parser [()]) `shouldBe` Right []
      parse' "_A5" (chain [char '_', letter, digit]) `shouldBe` Right ['_', 'A', '5']

    it "☯ exactly" $ do
      parse' "aaa" (exactly 2 (char 'a')) `shouldBe` Right "aa"
      parse' "abc" (exactly 2 (char 'a')) `shouldBe` Left "the character 'a'"

    it "☯ atLeast" $ do
      parse' "aaa" (atLeast 2 (char 'a')) `shouldBe` Right "aaa"
      parse' "abc" (atLeast 2 (char 'a')) `shouldBe` Left "the character 'a'"

    it "☯ atMost" $ do
      parse' "aaa" (atMost 2 (char 'a')) `shouldBe` Right "aa"
      parse' "abc" (atMost 2 (char 'a')) `shouldBe` Right "a"

    it "☯ between" $ do
      parse' "aaa" (between 1 2 (char 'a')) `shouldBe` Right "aa"
      parse' "abc" (between 1 2 (char 'a')) `shouldBe` Right "a"
      parse' "_" (between 1 2 (char 'a')) `shouldBe` Left "the character 'a'"

    -- it "☯ split" $ do
    --   parse' "" (split (char ',') letter) `shouldBe` Right []
    --   parse' "a,b,c" (split (char ',') letter) `shouldBe` Right ['a', 'b', 'c']

    it "☯ until" $ do
      parse' "abc" (until' (== 'c') letter) `shouldBe` Right "ab"
      parse' "ab1" (until' (== 'c') letter) `shouldBe` Right "ab"
      parse' "ab" (until' (== 'c') letter) `shouldBe` Right "ab"
      parse' "" (until' (== 'c') letter) `shouldBe` Right ""

    it "☯ foldL" $ do
      parse' "." (foldL (flip (:)) "" letter) `shouldBe` Right ""
      parse' "abc." (foldL (flip (:)) "" letter) `shouldBe` Right "cba"

    it "☯ foldR" $ do
      parse' "." (foldR (:) "" letter) `shouldBe` Right ""
      parse' "abc." (foldR (:) "" letter) `shouldBe` Right "abc"

  describe "☯ Common" $ do
    it "☯ integer" $ do
      parse' "11" integer `shouldBe` Right 11
      parse' "a" integer `shouldBe` Left "an integer value like 123"

    it "☯ number" $ do
      parse' "3.14" number `shouldBe` Right 3.14
      parse' "3" number `shouldBe` Right 3.0
      parse' "a" number `shouldBe` Left "a number like 123 or 3.14"

    it "☯ text" $ do
      parse' "Hello" (text "hello") `shouldBe` Right "Hello"
      parse' "H" (text "hello") `shouldBe` Left "the text 'hello'"

    it "☯ textCaseSensitive" $ do
      parse' "hello" (textCaseSensitive "hello") `shouldBe` Right "hello"
      parse' "Hello" (textCaseSensitive "hello") `shouldBe` Left "the text 'hello' (case sensitive)"

    it "☯ token" $ do
      parse' "a" (oneOrMore (token letter)) `shouldBe` Right "a"
      parse' "a b" (oneOrMore (token letter)) `shouldBe` Right "ab"
      parse' "a\tb" (oneOrMore (token letter)) `shouldBe` Right "ab"
      -- parse' "a\nb" (oneOrMore (token letter)) `shouldBe` Right "a"
      -- parse' "a\n b" (oneOrMore (token letter)) `shouldBe` Right "ab"
      -- parse' "a\n\n b" (oneOrMore (token letter)) `shouldBe` Right "ab"
      -- parse' "a\n   \n b" (oneOrMore (token letter)) `shouldBe` Right "ab"
      True `shouldBe` True

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
      parse "- 1" calculator `shouldBe` Right (-1.0)
      parse "--1" calculator `shouldBe` Right 1.0
      parse "1+2" calculator `shouldBe` Right 3.0
      parse "1 + 2" calculator `shouldBe` Right 3.0
      parse "1 - 2 - 3" calculator `shouldBe` Right (-4.0)
      parse "1 + 2 * 3" calculator `shouldBe` Right 7.0
      parse "3 * 2 + 1" calculator `shouldBe` Right 7.0
      parse "2 ^ 2 ^ 3" calculator `shouldBe` Right 256.0
      -- parse "1+-2+3" calculator `shouldBe` Right 1.0
      parse "(1+2)*3" calculator `shouldBe` Right 9.0
      parse "( 1 + 2 ) * 3" calculator `shouldBe` Right 9.0

    it "☯ indented" $ do
      let indented' = oneOrMore (indented (oneOrMore (token letter)))
      parse' "a" indented' `shouldBe` Right ["a"]
      parse' "a b" indented' `shouldBe` Right ["ab"]
      -- parse' "a b\nc" indented' `shouldBe` Right ["ab", "c"]
      -- parse' "a b\n c" indented' `shouldBe` Right ["abc"]
      -- parse' "a b\n c\nd" indented' `shouldBe` Right ["abc", "d"]
      -- parse' "a b\n c\n d" indented' `shouldBe` Right ["abc", "cd"]
      -- parse' "a b\n c\n  d" indented' `shouldBe` Right ["abcd"]
      -- parse' "a b\n c\n\n\n  d" indented' `shouldBe` Right ["abcd"]
      True `shouldBe` True
