module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Data.Function ((&))
import Data.List (intercalate, isInfixOf)
import Load
import Location (Position (..))
import System.FilePath (dropExtension)
import Tao
import TaoParser
import Test.Hspec

test :: Context -> [Either (String, Expr, Expr) String]
test ctx = do
  let output = \case
        TestPass {name} -> Right name
        TestFail {name, expected, got} -> Left (name, expected, got)
  map output (testAll [] ctx)

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
    test ctx `shouldBe` []

  let name = "examples/comments"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    test ctx `shouldBe` []

  -- let name = "examples/comments-multiline"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (ctx, syntaxErrors) <- load [name]
  --   syntaxErrors `shouldBe` []
  --   test ctx `shouldBe` []

  let name = "examples/tests"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Pass",
            Left ("Fail", i2, i1),
            Right "Shortcut pass",
            Left ("Shortcut fail", i2, i1)
          ]
    test ctx `shouldBe` testResults

  let name = "examples/expressions/atoms"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Any match",
            Right "Any match 1",
            Right "Any match 2",
            Right "Unit match",
            Left ("Unit match fail", i1, Unit),
            Right "IntT match",
            Left ("IntT match fail", NumT, IntT),
            Right "NumT match",
            Left ("NumT match fail", IntT, NumT),
            Right "Int match",
            Left ("Int match fail", i2, i1),
            Right "Num match",
            Left ("Num match fail", Num 0.0, Num 3.14),
            Right "Tag match",
            Left ("Tag match fail", Tag "B", Tag "A"),
            Right "Err match",
            Left ("Err match fail", i1, Err)
          ]
    test ctx `shouldBe` testResults

  let name = "examples/expressions/for"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "For bound",
            Right "For unbound",
            Right "For alpha equivalence"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/expressions/fun"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Fun implicit binding",
            Right "Fun explicit binding",
            Right "Fun alpha equivalence",
            Right "Fun args list"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/expressions/app"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "App Any",
            Right "App Unit",
            Right "App IntT",
            Right "App NumT",
            Right "App Int",
            Right "App Num",
            Right "App Tag",
            Right "App Ann",
            Right "App And",
            Right "App Or first",
            Right "App Or second",
            Right "App Or fail",
            Right "App For",
            Right "App Fun",
            -- Right "App App",
            -- Right "App Call",
            -- Right "App Op1",
            -- Right "App Op2",
            -- Right "App Let",
            -- Right "App Bind",
            -- Right "App If",
            -- Right "App Match",
            -- Right "App Record",
            -- Right "App Trait",
            -- Right "App Select",
            -- Right "App With",
            Right "App Err"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/expressions/and"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "And match",
            Left ("And match fail 1", i1, And i1 i2),
            Left ("And match fail 2", And i1 i1, And i1 i2),
            Left ("And match fail 3", And i2 i2, And i1 i2)
          ]
    test ctx `shouldBe` testResults

  let name = "examples/expressions/or"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Or match 1",
            Right "Or match 2",
            Right "Or match 3",
            Right "Or match 4",
            Left ("Or match fail", i3, Or i1 i2)
          ]
    test ctx `shouldBe` testResults

  let name = "examples/expressions/ann"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Ann match",
            Right "Ann match drop type",
            Left ("Ann match fail", i2, i1)
          ]
    test ctx `shouldBe` testResults

  let name = "examples/expressions/call"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Call constant",
            Right "Call no args",
            Right "Call args"
          ]
    test ctx `shouldBe` testResults

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
    test ctx `shouldBe` testResults

  let name = "examples/definitions/var"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Var match"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/definitions/overload"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Overload match 1",
            Right "Overload match 2",
            Left ("Overload fail", i3, Or i1 i2)
          ]
    test ctx `shouldBe` testResults

  let name = "examples/definitions/ann"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Ann match inline type",
            Right "Ann match type annotation"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/definitions/and"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "And match 1",
            Right "And match 2"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/definitions/or"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Or match 1",
            Right "Or match 2"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/definitions/for"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "For match",
            Left ("For match fail", i1, Err)
          ]
    test ctx `shouldBe` testResults

  let name = "examples/definitions/fun"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Fun match 1",
            Right "Fun match 2"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/definitions/app"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "App match 1",
            Right "App match 2"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/definitions/call"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Call match",
            Left ("Call match fail", i1, Err)
          ]
    test ctx `shouldBe` testResults

  let name = "examples/definitions/op2"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Add",
            Right "Sub",
            Right "Mul",
            Right "Pow"
          ]
    test ctx `shouldBe` testResults

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
  --         [ Right "Neg"
  --         ]
  --   test ctx `shouldBe` testResults

  -- let name = "examples/definitions/op1"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (ctx, syntaxErrors) <- load [name]
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ Right "Neg"
  --         ]
  --   test ctx `shouldBe` testResults

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
          [ Right "Nil",
            Right "Cons infix",
            Right "Cons prefix",
            Right "Cons Cons"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/syntax-sugar/char"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Char single quote",
            Right "Char double quote"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/syntax-sugar/string"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "String single quote",
            Right "String double quote"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/prelude/arithmetic-int"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Add",
            Right "Sub",
            Right "Mul",
            Right "Div",
            Right "Div Int",
            Right "Pow"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/prelude/arithmetic-num"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Add",
            Right "Sub",
            Right "Mul",
            Right "Div",
            Right "Div Int",
            Right "Pow"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/prelude/comparison"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "Eq 1 1",
            Right "Eq 1 2",
            Right "Eq 2 1",
            Right "Ne 1 1",
            Right "Ne 1 2",
            Right "Ne 2 1",
            Right "Lt 1 1",
            Right "Lt 1 2",
            Right "Lt 2 1",
            Right "Le 1 1",
            Right "Le 1 2",
            Right "Le 2 1",
            Right "Gt 1 1",
            Right "Gt 1 2",
            Right "Gt 2 1",
            Right "Ge 1 1",
            Right "Ge 1 2",
            Right "Ge 2 1"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/prelude/bool-not"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "T",
            Right "F",
            Right "Error"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/prelude/bool-and"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "TT",
            Right "TF",
            Right "FT",
            Right "FF",
            Right "Error"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/prelude/bool-or"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "TT",
            Right "TF",
            Right "FT",
            Right "FF",
            Right "Error"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/prelude/bool-xor"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load [name]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "TT",
            Right "TF",
            Right "FT",
            Right "FF",
            Right "Error"
          ]
    test ctx `shouldBe` testResults

  let name = "examples/factorial"
  it ("☯ " ++ name ++ ".tao") $ do
    (ctx, syntaxErrors) <- load ["examples/factorial.tao"]
    syntaxErrors `shouldBe` []
    (ctx, syntaxErrors) <- include "prelude" ctx
    syntaxErrors `shouldBe` []
    let testResults =
          [ Right "0",
            Right "1",
            Right "2",
            Right "3",
            Right "4",
            Right "5"
          ]
    test ctx `shouldBe` testResults
