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

  let name = "examples/empty"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    testAll [] ctx `shouldBe` []

  let name = "examples/comments"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    testAll [] ctx `shouldBe` []

  -- let name = "examples/comments-multiline"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (ctx, syntaxErrors) <- load [name]
  --   syntaxErrors `shouldBe` []
  --   testAll [] ctx `shouldBe` []

  let name = "examples/tests"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Pass",
            TestFail (name ++ ".tao") (6, 1) "Fail" i1 i2 i1,
            TestPass (name ++ ".tao") (10, 1) "Shortcut pass",
            TestFail (name ++ ".tao") (13, 1) "Shortcut fail" i1 i2 i1
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/expressions/atoms"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Any match",
            TestPass (name ++ ".tao") (6, 1) "Any match 1",
            TestPass (name ++ ".tao") (10, 1) "Any match 2",
            TestPass (name ++ ".tao") (14, 1) "Unit match",
            TestFail (name ++ ".tao") (18, 1) "Unit match fail" Unit i1 Unit,
            TestPass (name ++ ".tao") (22, 1) "IntT match",
            TestFail (name ++ ".tao") (26, 1) "IntT match fail" IntT NumT IntT,
            TestPass (name ++ ".tao") (30, 1) "NumT match",
            TestFail (name ++ ".tao") (34, 1) "NumT match fail" NumT IntT NumT,
            TestPass (name ++ ".tao") (38, 1) "Int match",
            TestFail (name ++ ".tao") (42, 1) "Int match fail" i1 i2 i1,
            TestPass (name ++ ".tao") (46, 1) "Num match",
            TestFail (name ++ ".tao") (50, 1) "Num match fail" (Num 3.14) (Num 0.0) (Num 3.14),
            TestPass (name ++ ".tao") (54, 1) "Tag match",
            TestFail (name ++ ".tao") (58, 1) "Tag match fail" (Tag "A") (Tag "B") (Tag "A"),
            TestPass (name ++ ".tao") (62, 1) "Err match",
            TestFail (name ++ ".tao") (66, 1) "Err match fail" Err i1 Err
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/expressions/for"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (4, 1) "For bound",
            TestPass (name ++ ".tao") (8, 1) "For unbound",
            TestPass (name ++ ".tao") (12, 1) "For alpha equivalence"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/expressions/fun"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (5, 1) "Fun implicit binding",
            TestPass (name ++ ".tao") (9, 1) "Fun explicit binding",
            TestPass (name ++ ".tao") (13, 1) "Fun alpha equivalence",
            TestPass (name ++ ".tao") (17, 1) "Fun args list"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/expressions/app"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "App Any",
            TestPass (name ++ ".tao") (6, 1) "App Unit",
            TestPass (name ++ ".tao") (10, 1) "App IntT",
            TestPass (name ++ ".tao") (14, 1) "App NumT",
            TestPass (name ++ ".tao") (18, 1) "App Int",
            TestPass (name ++ ".tao") (22, 1) "App Num",
            TestPass (name ++ ".tao") (26, 1) "App Tag",
            TestPass (name ++ ".tao") (30, 1) "App Ann",
            TestPass (name ++ ".tao") (34, 1) "App And",
            TestPass (name ++ ".tao") (38, 1) "App Or first",
            TestPass (name ++ ".tao") (42, 1) "App Or second",
            TestPass (name ++ ".tao") (46, 1) "App Or fail",
            TestPass (name ++ ".tao") (50, 1) "App For",
            TestPass (name ++ ".tao") (54, 1) "App Fun",
            -- TestPass (name ++ ".tao") "App App",
            -- TestPass (name ++ ".tao") "App Call",
            -- TestPass (name ++ ".tao") "App Op1",
            -- TestPass (name ++ ".tao") "App Op2",
            -- TestPass (name ++ ".tao") "App Let",
            -- TestPass (name ++ ".tao") "App Bind",
            -- TestPass (name ++ ".tao") "App If",
            -- TestPass (name ++ ".tao") "App Match",
            -- TestPass (name ++ ".tao") "App Record",
            -- TestPass (name ++ ".tao") "App Trait",
            -- TestPass (name ++ ".tao") "App Select",
            -- TestPass (name ++ ".tao") "App With",
            TestPass (name ++ ".tao") (81, 1) "App Err"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/expressions/and"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (5, 1) "And match",
            TestFail (name ++ ".tao") (9, 1) "And match fail 1" (And i1 i2) i1 (And i1 i2),
            TestFail (name ++ ".tao") (13, 1) "And match fail 2" (And i1 i2) (And i1 i1) (And i1 i2),
            TestFail (name ++ ".tao") (17, 1) "And match fail 3" (And i1 i2) (And i2 i2) (And i1 i2)
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/expressions/or"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Or match 1",
            TestPass (name ++ ".tao") (6, 1) "Or match 2",
            TestPass (name ++ ".tao") (10, 1) "Or match 3",
            TestPass (name ++ ".tao") (14, 1) "Or match 4",
            TestFail (name ++ ".tao") (18, 1) "Or match fail" (Or i1 i2) i3 (Or i1 i2)
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/expressions/ann"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Ann match",
            TestPass (name ++ ".tao") (6, 1) "Ann match drop type",
            TestFail (name ++ ".tao") (10, 1) "Ann match fail" (Ann i1 IntT) i2 i1
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/expressions/call"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Call constant",
            TestPass (name ++ ".tao") (6, 1) "Call no args",
            TestPass (name ++ ".tao") (13, 1) "Call args"
          ]
    testAll [] ctx `shouldBe` testResults

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
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults = []
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/var"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (4, 1) "Var match"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/overload"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (6, 1) "Overload match 1",
            TestPass (name ++ ".tao") (10, 1) "Overload match 2",
            TestFail (name ++ ".tao") (14, 1) "Overload fail" x i3 (Or i1 i2)
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/ann"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (4, 1) "Ann match inline type",
            TestPass (name ++ ".tao") (11, 1) "Ann match type annotation"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/and"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (4, 1) "And match 1",
            TestPass (name ++ ".tao") (8, 1) "And match 2"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/or"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (4, 1) "Or match 1",
            TestPass (name ++ ".tao") (8, 1) "Or match 2"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/for"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (6, 1) "For match",
            TestFail (name ++ ".tao") (12, 1) "For match fail" y i1 Err
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/fun"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (4, 1) "Fun match 1",
            TestPass (name ++ ".tao") (8, 1) "Fun match 2"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/app"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (4, 1) "App match 1",
            TestPass (name ++ ".tao") (8, 1) "App match 2"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/call"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (4, 1) "Call match",
            TestFail (name ++ ".tao") (10, 1) "Call match fail" y i1 Err
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/definitions/op2"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (14, 1) "Add",
            TestPass (name ++ ".tao") (18, 1) "Sub",
            TestPass (name ++ ".tao") (22, 1) "Mul",
            TestPass (name ++ ".tao") (26, 1) "Pow"
          ]
    testAll [] ctx `shouldBe` testResults

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
  --   (ctx, syntaxErrors) <- load [name]
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass (name ++ ".tao") "Neg"
  --         ]
  --   testAll [] ctx `shouldBe` testResults

  -- let name = "examples/definitions/op1"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (ctx, syntaxErrors) <- load [name]
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ TestPass (name ++ ".tao") "Neg"
  --         ]
  --   testAll [] ctx `shouldBe` testResults

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

  let name = "examples/syntax-sugar/list"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Nil",
            TestPass (name ++ ".tao") (6, 1) "Cons infix",
            TestPass (name ++ ".tao") (10, 1) "Cons prefix",
            TestPass (name ++ ".tao") (14, 1) "Cons Cons"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/syntax-sugar/char"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Char single quote",
            TestPass (name ++ ".tao") (6, 1) "Char double quote"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/syntax-sugar/string"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "String single quote",
            TestPass (name ++ ".tao") (6, 1) "String double quote"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/prelude/arithmetic-int"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Add",
            TestPass (name ++ ".tao") (6, 1) "Sub",
            TestPass (name ++ ".tao") (10, 1) "Mul",
            TestPass (name ++ ".tao") (14, 1) "Div",
            TestPass (name ++ ".tao") (18, 1) "Div Int",
            TestPass (name ++ ".tao") (22, 1) "Pow"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/prelude/arithmetic-num"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Add",
            TestPass (name ++ ".tao") (6, 1) "Sub",
            TestPass (name ++ ".tao") (10, 1) "Mul",
            TestPass (name ++ ".tao") (14, 1) "Div",
            TestPass (name ++ ".tao") (18, 1) "Div Int",
            TestPass (name ++ ".tao") (22, 1) "Pow"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/prelude/comparison"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "Eq 1 1",
            TestPass (name ++ ".tao") (5, 1) "Eq 1 2",
            TestPass (name ++ ".tao") (8, 1) "Eq 2 1",
            TestPass (name ++ ".tao") (11, 1) "Ne 1 1",
            TestPass (name ++ ".tao") (14, 1) "Ne 1 2",
            TestPass (name ++ ".tao") (17, 1) "Ne 2 1",
            TestPass (name ++ ".tao") (20, 1) "Lt 1 1",
            TestPass (name ++ ".tao") (23, 1) "Lt 1 2",
            TestPass (name ++ ".tao") (26, 1) "Lt 2 1",
            TestPass (name ++ ".tao") (29, 1) "Le 1 1",
            TestPass (name ++ ".tao") (32, 1) "Le 1 2",
            TestPass (name ++ ".tao") (35, 1) "Le 2 1",
            TestPass (name ++ ".tao") (38, 1) "Gt 1 1",
            TestPass (name ++ ".tao") (41, 1) "Gt 1 2",
            TestPass (name ++ ".tao") (44, 1) "Gt 2 1",
            TestPass (name ++ ".tao") (47, 1) "Ge 1 1",
            TestPass (name ++ ".tao") (50, 1) "Ge 1 2",
            TestPass (name ++ ".tao") (53, 1) "Ge 2 1"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/prelude/bool-not"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "T",
            TestPass (name ++ ".tao") (6, 1) "F",
            TestPass (name ++ ".tao") (10, 1) "Error"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/prelude/bool-and"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "TT",
            TestPass (name ++ ".tao") (6, 1) "TF",
            TestPass (name ++ ".tao") (10, 1) "FT",
            TestPass (name ++ ".tao") (14, 1) "FF",
            TestPass (name ++ ".tao") (18, 1) "Error"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/prelude/bool-or"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "TT",
            TestPass (name ++ ".tao") (6, 1) "TF",
            TestPass (name ++ ".tao") (10, 1) "FT",
            TestPass (name ++ ".tao") (14, 1) "FF",
            TestPass (name ++ ".tao") (18, 1) "Error"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/prelude/bool-xor"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (2, 1) "TT",
            TestPass (name ++ ".tao") (6, 1) "TF",
            TestPass (name ++ ".tao") (10, 1) "FT",
            TestPass (name ++ ".tao") (14, 1) "FF",
            TestPass (name ++ ".tao") (18, 1) "Error"
          ]
    testAll [] ctx `shouldBe` testResults

  let name = "examples/factorial"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load ["examples/factorial.tao"]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ TestPass (name ++ ".tao") (7, 1) "0",
            TestPass (name ++ ".tao") (10, 1) "1",
            TestPass (name ++ ".tao") (13, 1) "2",
            TestPass (name ++ ".tao") (16, 1) "3",
            TestPass (name ++ ".tao") (19, 1) "4",
            TestPass (name ++ ".tao") (22, 1) "5"
          ]
    testAll [] ctx `shouldBe` testResults
