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
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
  let (xT, xT') = (Var "xT", C.Var "xT")
  let (yT, yT') = (Var "yT", C.Var "yT")
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  let (i1', i2', i3') = (C.Int 1, C.Int 2, C.Int 3)

  let name = "examples/empty"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    testAll [] pkg `shouldBe` []

  let name = "examples/comments"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    testAll [] pkg `shouldBe` []

  -- let name = "examples/comments-multiline"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   testAll [] pkg `shouldBe` []

  let name = "examples/tests"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Pass",
            TestFail name "Fail" (i1, i2) (i1', C.IntT) i1,
            TestPass name "Shortcut pass",
            TestFail name "Shortcut fail" (i1, i2) (i1', C.IntT) i1
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/atoms"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Any match",
            TestPass name "Any match 1",
            TestPass name "Any match 2",
            TestPass name "Unit match",
            TestFail name "Unit match fail" (Unit, i1) (C.Unit, C.Unit) Unit,
            TestPass name "IntT match",
            TestFail name "IntT match fail" (IntT, NumT) (C.IntT, C.IntT) IntT,
            TestPass name "NumT match",
            TestFail name "NumT match fail" (NumT, IntT) (C.NumT, C.NumT) NumT,
            TestPass name "Int match",
            TestFail name "Int match fail" (i1, i2) (i1', C.IntT) i1,
            TestPass name "Num match",
            TestFail name "Num match fail" (Num 3.14, Num 0.0) (C.Num 3.14, C.NumT) (Num 3.14),
            TestPass name "Tag match",
            TestFail name "Tag match fail" (Tag "A", Tag "B") (C.Tag "A", C.Tag "A") (Tag "A"),
            TestPass name "Err match",
            TestFail name "Err match fail" (Err, i1) (C.Err, C.Err) Err
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/for"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "For bound",
            TestPass name "For unbound",
            TestPass name "For alpha equivalence"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/fun"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Fun implicit binding",
            TestPass name "Fun explicit binding",
            TestPass name "Fun alpha equivalence",
            TestPass name "Fun args list"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/app"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "App Any",
            TestPass name "App Unit",
            TestPass name "App IntT",
            TestPass name "App NumT",
            TestPass name "App Int",
            TestPass name "App Num",
            TestPass name "App Tag",
            TestPass name "App Ann",
            TestPass name "App And",
            TestPass name "App Or first",
            TestPass name "App Or second",
            TestPass name "App Or fail",
            TestPass name "App For",
            TestPass name "App Fun",
            -- TestPass name "App App",
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

  let name = "examples/expressions/and"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "And match",
            TestFail name "And match fail 1" (And i1 i2, i1) (C.And i1' i2', C.And C.IntT C.IntT) (And i1 i2),
            TestFail name "And match fail 2" (And i1 i2, And i1 i1) (C.And i1' i2', C.And C.IntT C.IntT) (And i1 i2),
            TestFail name "And match fail 3" (And i1 i2, And i2 i2) (C.And i1' i2', C.And C.IntT C.IntT) (And i1 i2)
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/or"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Or match 1",
            TestPass name "Or match 2",
            TestPass name "Or match 3",
            TestPass name "Or match 4",
            TestFail name "Or match fail" (Or i1 i2, i3) (C.Or i1' i2', C.IntT) (Or i1 i2)
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/ann"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Ann match",
            TestPass name "Ann match drop type",
            TestFail name "Ann match fail" (Ann i1 IntT, i2) (C.Ann i1' C.IntT, C.IntT) i1
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/call"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Call constant",
            TestPass name "Call no args",
            TestPass name "Call args"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/op2"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Add",
            TestPass name "Sub"
          ]
    testAll [] pkg `shouldBe` testResults

  -- Let (Expr, Expr) Expr
  -- Bind (Expr, Expr) Expr
  -- If Expr Expr Expr
  -- Match [Expr] [Expr]
  -- Record [(String, Expr)]
  -- Select Expr [(String, Expr)]
  -- With Expr [(String, Expr)]

  let name = "examples/definitions/atoms"
  it ("☯ " ++ name ++ ".tao") $ do
    -- There are no bindings, so there aren't any tests to run.
    -- Just make sure there are no syntax errors.
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults = []
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/var"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Var match"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/overload"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Overload match 1",
            TestPass name "Overload match 2",
            TestFail name "Overload fail" (x, i3) (C.Let [("x", C.Or i1' i2')] x', C.IntT) (Or i1 i2)
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/ann"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Ann match inline type",
            TestPass name "Ann match type annotation"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/and"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "And match 1",
            TestPass name "And match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/or"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Or match 1",
            TestPass name "Or match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/for"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "For match",
            TestFail name "For match fail" (y, i1) (C.Let [("y", C.Let [("z", i2')] (C.def ["y"] (C.And y' z', C.And i1' i1') y'))] (C.Ann y' C.IntT), C.IntT) Err
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/fun"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Fun match 1",
            TestPass name "Fun match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/app"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "App match 1",
            TestPass name "App match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/call"
  it ("☯ " ++ name ++ ".tao") $ do
    (pkg, syntaxErrors) <- load name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name "Call match",
            TestFail name "Call match fail" (y, i1) (C.Let [("y", C.def ["yT", "y"] (C.Ann (C.Call "f" [C.Ann y' yT']) (C.Call "f" [yT']), C.Ann (C.Call "g" [C.Ann i1' C.IntT]) (C.Call "g" [C.IntT])) y')] y', C.Err) Err
          ]
    testAll [] pkg `shouldBe` testResults

  -- Op1 Op1 Expr
  -- Op2 Op2 Expr Expr
  -- Let (Expr, Expr) Expr
  -- Bind (Expr, Expr) Expr
  -- If Expr Expr Expr
  -- Match [Expr] [Expr]
  -- Record [(String, Expr)]
  -- Select Expr [(String, Expr)]
  -- With Expr [(String, Expr)]

  -- let name = "examples/definitions/trait"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass name "Neg"
  --         ]
  --   testAll [] pkg `shouldBe` testResults

  -- let name = "examples/definitions/op1"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass name "Neg"
  --         ]
  --   testAll [] pkg `shouldBe` testResults

  -- Op2 Op2 Expr Expr

  -- let name = "errors"
  -- it ("☯ " ++ name ++ ".tao") $ do
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
  -- -- it ("☯ " ++ name ++ ".tao") $ do
  -- --   test' name [] `shouldReturn` Right []

  -- let name = "tuples-def"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   test' name `shouldReturn` Right [TestPass ("examples/" ++ name ++ ".tao") ""]

  -- let name = "tuples-properties"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   test' name [] `shouldReturn` Right []

  -- TODO: Tags

  -- let name = "records-def"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   test' name [] `shouldReturn` Right []

  -- let name = "records-properties"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   test' name [] `shouldReturn` Right []

  -- TODO: "records-select"
  -- TODO: "records-update"
  -- TODO: "records-reorder"
  -- TODO: "records-positional"
  -- TODO: "records-mixed-positional"
  -- TODO: "records-default-values"

  -- TODO: Unions
  -- TODO: Choices (?)

  -- let name = "examples/factorial"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (pkg, syntaxErrors) <- load name []
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass name "Call match"
  --         -- , TestFail name "Call match fail" (y, i1) (C.Let [("y", C.def ["yT", "y"] (C.Ann (C.Call "f" [C.Ann y' yT']) (C.Call "f" [yT']), C.Ann (C.Call "g" [C.Ann i1' C.IntT]) y') (C.Call "g" [C.IntT]))] y', C.Err) Err
  --         ]
  --   testAll [] pkg `shouldBe` testResults

  it "☯ TODO" $ do
    True `shouldBe` True
