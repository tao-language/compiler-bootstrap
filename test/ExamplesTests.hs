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
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  let (i1', i2', i3') = (C.Int 1, C.Int 2, C.Int 3)

  let name = "examples/empty.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    testAll [] pkg `shouldBe` []

  let name = "examples/comments.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    testAll [] pkg `shouldBe` []

  -- let name = "examples/comments-multiline.tao"
  -- it ("☯ " ++ name) $ do
  --   (pkg, syntaxErrors) <- load "" name []
  --   syntaxErrors `shouldBe` []
  --   testAll [] pkg `shouldBe` []

  let name = "examples/tests.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "Pass",
            TestFail name (6, 1) "Fail" i1 i2 i1,
            TestPass name (10, 1) "Shortcut pass",
            TestFail name (13, 1) "Shortcut fail" i1 i2 i1
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/atoms.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "Any match",
            TestPass name (6, 1) "Any match 1",
            TestPass name (10, 1) "Any match 2",
            TestPass name (14, 1) "Unit match",
            TestFail name (18, 1) "Unit match fail" Unit i1 Unit,
            TestPass name (22, 1) "IntT match",
            TestFail name (26, 1) "IntT match fail" IntT NumT IntT,
            TestPass name (30, 1) "NumT match",
            TestFail name (34, 1) "NumT match fail" NumT IntT NumT,
            TestPass name (38, 1) "Int match",
            TestFail name (42, 1) "Int match fail" i1 i2 i1,
            TestPass name (46, 1) "Num match",
            TestFail name (50, 1) "Num match fail" (Num 3.14) (Num 0.0) (Num 3.14),
            TestPass name (54, 1) "Tag match",
            TestFail name (58, 1) "Tag match fail" (Tag "A") (Tag "B") (Tag "A"),
            TestPass name (62, 1) "Err match",
            TestFail name (66, 1) "Err match fail" Err i1 Err
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/for.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (4, 1) "For bound",
            TestPass name (8, 1) "For unbound",
            TestPass name (12, 1) "For alpha equivalence"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/fun.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (5, 1) "Fun implicit binding",
            TestPass name (9, 1) "Fun explicit binding",
            TestPass name (13, 1) "Fun alpha equivalence",
            TestPass name (17, 1) "Fun args list"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/app.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "App Any",
            TestPass name (6, 1) "App Unit",
            TestPass name (10, 1) "App IntT",
            TestPass name (14, 1) "App NumT",
            TestPass name (18, 1) "App Int",
            TestPass name (22, 1) "App Num",
            TestPass name (26, 1) "App Tag",
            TestPass name (30, 1) "App Ann",
            TestPass name (34, 1) "App And",
            TestPass name (38, 1) "App Or first",
            TestPass name (42, 1) "App Or second",
            TestPass name (46, 1) "App Or fail",
            TestPass name (50, 1) "App For",
            TestPass name (54, 1) "App Fun",
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
            TestPass name (81, 1) "App Err"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/and.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (5, 1) "And match",
            TestFail name (9, 1) "And match fail 1" (And i1 i2) i1 (And i1 i2),
            TestFail name (13, 1) "And match fail 2" (And i1 i2) (And i1 i1) (And i1 i2),
            TestFail name (17, 1) "And match fail 3" (And i1 i2) (And i2 i2) (And i1 i2)
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/or.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "Or match 1",
            TestPass name (6, 1) "Or match 2",
            TestPass name (10, 1) "Or match 3",
            TestPass name (14, 1) "Or match 4",
            TestFail name (18, 1) "Or match fail" (Or i1 i2) i3 (Or i1 i2)
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/ann.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "Ann match",
            TestPass name (6, 1) "Ann match drop type",
            TestFail name (10, 1) "Ann match fail" (Ann i1 IntT) i2 i1
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/expressions/call.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "Call constant",
            TestPass name (6, 1) "Call no args",
            TestPass name (13, 1) "Call args"
          ]
    testAll [] pkg `shouldBe` testResults

  -- Let (Expr, Expr) Expr
  -- Bind (Expr, Expr) Expr
  -- If Expr Expr Expr
  -- Match [Expr] [Expr]
  -- Record [(String, Expr)]
  -- Select Expr [(String, Expr)]
  -- With Expr [(String, Expr)]

  let name = "examples/definitions/atoms.tao"
  it ("☯ " ++ name) $ do
    -- There are no bindings, so there aren't any tests to run.
    -- Just make sure there are no syntax errors.
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults = []
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/var.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (4, 1) "Var match"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/overload.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (6, 1) "Overload match 1",
            TestPass name (10, 1) "Overload match 2",
            TestFail name (14, 1) "Overload fail" x i3 (Or i1 i2)
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/ann.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (4, 1) "Ann match inline type",
            TestPass name (11, 1) "Ann match type annotation"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/and.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (4, 1) "And match 1",
            TestPass name (8, 1) "And match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/or.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (4, 1) "Or match 1",
            TestPass name (8, 1) "Or match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/for.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (6, 1) "For match",
            TestFail name (12, 1) "For match fail" y i1 Err
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/fun.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (4, 1) "Fun match 1",
            TestPass name (8, 1) "Fun match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/app.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (4, 1) "App match 1",
            TestPass name (8, 1) "App match 2"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/call.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (4, 1) "Call match",
            TestFail name (10, 1) "Call match fail" y i1 Err
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/definitions/op2.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (14, 1) "Add",
            TestPass name (18, 1) "Sub",
            TestPass name (22, 1) "Mul",
            TestPass name (26, 1) "Pow"
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

  -- let name = "examples/definitions/trait.tao"
  -- it ("☯ " ++ name) $ do
  --   (pkg, syntaxErrors) <- load "" name []
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass name "Neg"
  --         ]
  --   testAll [] pkg `shouldBe` testResults

  -- let name = "examples/definitions/op1.tao"
  -- it ("☯ " ++ name) $ do
  --   (pkg, syntaxErrors) <- load "" name []
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass name "Neg"
  --         ]
  --   testAll [] pkg `shouldBe` testResults

  -- Op2 Op2 Expr Expr

  -- let name = "errors.tao"
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

  let name = "examples/syntax-sugar/list.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "Nil",
            TestPass name (6, 1) "Cons infix",
            TestPass name (10, 1) "Cons prefix",
            TestPass name (14, 1) "Cons Cons"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/syntax-sugar/char.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "Char single quote",
            TestPass name (6, 1) "Char double quote"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/syntax-sugar/string.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "String single quote",
            TestPass name (6, 1) "String double quote"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/prelude/arithmetic-int.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "prelude" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "Add",
            TestPass name (6, 1) "Sub",
            TestPass name (10, 1) "Mul",
            TestPass name (14, 1) "Div",
            TestPass name (18, 1) "Div Int",
            TestPass name (22, 1) "Pow"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/prelude/arithmetic-num.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "prelude" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "Add",
            TestPass name (6, 1) "Sub",
            TestPass name (10, 1) "Mul",
            TestPass name (14, 1) "Div",
            TestPass name (18, 1) "Div Int",
            TestPass name (22, 1) "Pow"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/prelude/bool-not.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "prelude" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "T",
            TestPass name (6, 1) "F",
            TestPass name (10, 1) "Error"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/prelude/bool-and.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "prelude" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "TT",
            TestPass name (6, 1) "TF",
            TestPass name (10, 1) "FT",
            TestPass name (14, 1) "FF",
            TestPass name (18, 1) "Error"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/prelude/bool-or.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "prelude" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "TT",
            TestPass name (6, 1) "TF",
            TestPass name (10, 1) "FT",
            TestPass name (14, 1) "FF",
            TestPass name (18, 1) "Error"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/prelude/bool-xor.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "prelude" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (2, 1) "TT",
            TestPass name (6, 1) "TF",
            TestPass name (10, 1) "FT",
            TestPass name (14, 1) "FF",
            TestPass name (18, 1) "Error"
          ]
    testAll [] pkg `shouldBe` testResults

  let name = "examples/factorial.tao"
  it ("☯ " ++ name) $ do
    (pkg, syntaxErrors) <- load "prelude" name []
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass name (7, 1) "0",
            TestPass name (10, 1) "1",
            TestPass name (13, 1) "2",
            TestPass name (16, 1) "3",
            TestPass name (19, 1) "4",
            TestPass name (22, 1) "5"
          ]
    testAll [] pkg `shouldBe` testResults
