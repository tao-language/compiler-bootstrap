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
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)

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
            TestFail name "Fail" (i1, i2) i1
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expr-atoms"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Any match",
            TestPass name "Any match 1",
            TestPass name "Any match 2",
            TestPass name "Unit match",
            TestFail name "Unit match fail" (Unit, i1) Unit,
            TestPass name "IntType match",
            TestFail name "IntType match fail" (IntType, NumType) IntType,
            TestPass name "NumType match",
            TestFail name "NumType match fail" (NumType, IntType) NumType,
            TestPass name "Int match",
            TestFail name "Int match fail" (i1, i2) i1,
            TestPass name "Num match",
            TestFail name "Num match fail" (Num 3.14, Num 0.0) (Num 3.14),
            TestPass name "Tag match",
            TestFail name "Tag match fail" (Tag "A", Tag "B") (Tag "A"),
            TestPass name "Err match",
            TestFail name "Err match fail" (Err, i1) Err
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
            TestPass name "Fun alpha equivalence",
            TestPass name "Fun args list"
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

  let name = "examples/expr-and"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "And match",
            TestFail name "And match fail 1" (And i1 i2, i1) (And i1 i2),
            TestFail name "And match fail 2" (And i1 i2, And i1 i1) (And i1 i2),
            TestFail name "And match fail 3" (And i1 i2, And i2 i2) (And i1 i2)
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expr-or"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Or match first",
            TestPass name "Or match second",
            TestFail name "Or match fail" (Or i1 i2, i3) (Or i1 i2),
            TestPass name "Or match any"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expr-ann"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Ann match",
            TestPass name "Ann match drop type",
            TestFail name "Ann match fail" (Ann i1 IntType, i2) i1
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

  -- Let (Expr, Expr) Expr
  -- Bind (Expr, Expr) Expr
  -- If Expr Expr Expr
  -- Match [Expr] [Expr]
  -- Record [(String, Expr)]
  -- Select Expr [(String, Expr)]
  -- With Expr [(String, Expr)]

  let name = "examples/def-atoms"
  it ("☯ " ++ name) $ do
    -- There are no bindings, so there aren't any tests to run.
    -- Just make sure there are no syntax errors.
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults = []
    testAll [] pkg `shouldBe` testResults

  let name = "examples/def-var"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Var match"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/def-for"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "For match",
            TestFail name "For match fail" (y, i1) Err
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/def-fun"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Fun match 1",
            TestPass name "Fun match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/def-app"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "App match 1",
            TestPass name "App match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/def-and"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "And match 1",
            TestPass name "And match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  -- let name = "examples/def-or"
  -- it ("☯ " ++ name) $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass name "And match 1",
  --           TestPass name "And match 2"
  --         ]
  --   testAll [] pkg `shouldBe` testResults

  let name = "examples/def-ann"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Ann match inline type",
            TestPass name "Ann match type annotation"
          ]
    testAll [] pkg `shouldBe` testResults

  -- Call String [Expr]
  -- Trait Expr String
  -- Op1 Op1 Expr
  -- Op2 Op2 Expr Expr
  -- Let (Expr, Expr) Expr
  -- Bind (Expr, Expr) Expr
  -- If Expr Expr Expr
  -- Match [Expr] [Expr]
  -- Record [(String, Expr)]
  -- Select Expr [(String, Expr)]
  -- With Expr [(String, Expr)]

  -- let name = "examples/def-trait"
  -- it ("☯ " ++ name) $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass name "Neg"
  --         ]
  --   testAll [] pkg `shouldBe` testResults

  -- let name = "examples/def-op1"
  -- it ("☯ " ++ name) $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass name "Neg"
  --         ]
  --   testAll [] pkg `shouldBe` testResults

  -- Op2 Op2 Expr Expr

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
