module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (intercalate, isInfixOf)
import System.FilePath (dropExtension)
import Tao
import TaoParser
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let name = "examples/empty.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    testAll [] pkg `shouldBe` []

  let name = "examples/comments.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    testAll [] pkg `shouldBe` []

  -- let name = "examples/comments-multiline.tao"
  -- it ("☯ " ++ name) $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   testAll [] pkg `shouldBe` []

  let name = "examples/tests.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass "examples/tests" "Pass",
            TestFail "examples/tests" "Fail" (Int 42, Int 0) (Int 42)
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/atoms.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass "examples/atoms" "Any",
            TestPass "examples/atoms" "Unit",
            TestPass "examples/atoms" "IntType",
            TestPass "examples/atoms" "NumType",
            TestPass "examples/atoms" "Int",
            TestPass "examples/atoms" "Num",
            TestPass "examples/atoms" "Tag",
            TestPass "examples/atoms" "Err"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/def-var.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass "examples/def-var" "Untyped",
            TestPass "examples/def-var" "Typed",
            TestPass "examples/def-var" "Typed inline"
          ]
    testAll [] pkg `shouldBe` testResults

  -- let name = "errors"
  -- it ("☯ " ++ name) $ do
  --   let results =
  --         [ TestFail
  --             UnitTest
  --               { path = "examples/errors/wrong-result",
  --                 name = "",
  --                 expr = x,
  --                 expect = Int 0
  --               }
  --             (Int 42)
  --         ]
  --   test' name `shouldReturn` Right results

  -- -- let name = "traits"
  -- -- it ("☯ " ++ name) $ do
  -- --   test' name [] `shouldReturn` Right []

  -- let name = "tuples-def"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` Right [TestPass ("examples/" ++ name) ""]

  -- let name = "tuples-properties"
  -- it ("☯ " ++ name) $ do
  --   test' name [] `shouldReturn` Right []

  -- TODO: Tags

  -- let name = "records-def"
  -- it ("☯ " ++ name) $ do
  --   test' name [] `shouldReturn` Right []

  -- let name = "records-properties"
  -- it ("☯ " ++ name) $ do
  --   test' name [] `shouldReturn` Right []

  -- TODO: "records-select"
  -- TODO: "records-update"
  -- TODO: "records-reorder"
  -- TODO: "records-positional"
  -- TODO: "records-mixed-positional"
  -- TODO: "records-default-values"

  -- TODO: Unions
  -- TODO: Choices (?)

  it "☯ TODO" $ do
    True `shouldBe` True
