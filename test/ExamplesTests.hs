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
  let name = "examples/empty"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    testAll [] pkg `shouldBe` []

  let name = "examples/comments"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    testAll [] pkg `shouldBe` []

  -- let name = "examples/comments-multiline"
  -- it ("☯ " ++ name) $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   testAll [] pkg `shouldBe` []

  let name = "examples/tests"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Pass",
            TestFail name "Fail" (Int 42, Int 0) (Int 42)
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expr-atoms"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Any",
            TestPass name "Unit",
            TestPass name "IntType",
            TestPass name "NumType",
            TestPass name "Int",
            TestPass name "Num",
            TestPass name "Tag",
            TestPass name "Err"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expr-for"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "For bound",
            TestPass name "For unbound",
            TestPass name "For alpha equivalence"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expr-fun"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Fun implicit binding",
            TestPass name "Fun explicit binding",
            TestPass name "Fun alpha equivalence"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expr-app"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "App Any",
            TestPass name "App Unit",
            TestPass name "App IntType",
            TestPass name "App NumType",
            TestPass name "App Int",
            TestPass name "App Num",
            TestPass name "App Tag",
            TestPass name "App For",
            TestPass name "App Fun",
            TestPass name "App App",
            TestPass name "App And",
            TestPass name "App Or first",
            TestPass name "App Or second",
            TestPass name "App Or fail",
            TestPass name "App Ann",
            -- TestPass name "App Call",
            -- TestPass name "App Op1",
            -- TestPass name "App Op2",
            -- TestPass name "App Let",
            -- TestPass name "App Bind",
            -- TestPass name "App If",
            -- TestPass name "App Match",
            -- TestPass name "App Record",
            -- TestPass name "App Trait",
            -- TestPass name "App Select",
            -- TestPass name "App With",
            TestPass name "App Err"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expr-call"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Call constant",
            TestPass name "Call no args",
            TestPass name "Call args"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/def-var"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Untyped",
            TestPass name "Typed",
            TestPass name "Typed inline"
          ]
    testAll [] pkg `shouldBe` testResults

  -- let name = "examples/def-fun"
  -- it ("☯ " ++ name) $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass name "Function pattern",
  --           TestPass name "Function body"
  --         ]
  --   testAll [] pkg `shouldBe` testResults

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
