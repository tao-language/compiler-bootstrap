module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Data.Function ((&))
import Data.List (intercalate, isInfixOf)
import Error
import Load
import Location
import System.FilePath (dropExtension)
import Tao
import Test
import Test.Hspec

data Result a
  = Pass String
  | Fail String a a
  deriving (Eq)

instance (Show a) => Show (Result a) where
  show :: Result a -> String
  show = \case
    Pass name -> "✅ " ++ name ++ "\n"
    Fail name expected got -> "❌ " ++ name ++ "\n" ++ show expected ++ "\n" ++ show got ++ "\n"

test :: Context -> Package -> [Result Expr]
test ctx pkg = do
  let output = \case
        TestPass {name} -> Pass name
        TestFail {name, expected, got} -> Fail name (dropMeta expected) (dropMeta got)
  map output (testAll ctx pkg)

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
  let (xT, xT') = (Var "xT", C.Var "xT")
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  let (i1', i2', i3') = (C.Int 1, C.Int 2, C.Int 3)
  let loc f r1 c1 r2 c2 = Meta (C.Loc (Location f (Range (Pos r1 c1) (Pos r2 c2))))
  let err a = Err (customError a)

  let name = "examples/empty"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    test ctx pkg `shouldBe` []

  let name = "examples/comments"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    test ctx pkg `shouldBe` []

  -- let name = "examples/comments-multiline"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (ctx, syntaxErrors) <- load [name]
  --   check pkg `shouldBe` []
  --   syntaxErrors `shouldBe` []
  --   test ctx `shouldBe` []

  let name = "examples/tests"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Pass",
            Fail "Fail" i2 i1,
            Pass "Shortcut pass",
            Fail "Shortcut fail" i2 i1
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/expressions/atoms"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Any match",
            Pass "Any match 1",
            Pass "Any match 2",
            Pass "Unit match",
            Fail "Unit match fail" i1 (Err $ typeMismatch (Tuple []) IntT),
            Pass "IntT match",
            Pass "NumT match",
            Pass "Int match",
            Fail "Int match fail" i2 i1,
            Pass "Num match",
            Fail "Num match fail" (Num 0.0) (Num 3.14),
            Pass "Tag match",
            Pass "Err match",
            Fail "Err match fail" i1 (err $ loc (name ++ ".tao") 54 10 54 11 Any)
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/expressions/for"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "For bound",
            Pass "For unbound",
            Pass "For alpha equivalence"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/expressions/fun"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Fun implicit binding",
            Pass "Fun explicit binding",
            Pass "Fun alpha equivalence",
            Pass "Fun args list"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/expressions/app"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "App Any",
            Pass "App Unit",
            Pass "App IntT",
            Pass "App NumT",
            Pass "App Int",
            Pass "App Num",
            Pass "App Tag",
            Pass "App Ann",
            Pass "App And",
            Pass "App Or first",
            Pass "App Or second",
            Pass "App Or fail",
            Pass "App For",
            Pass "App Fun",
            Pass "App App",
            Pass "App Call",
            Pass "App Op1",
            Pass "App Op2",
            -- Pass "App Let",
            -- Pass "App Bind",
            -- Pass "App If",
            -- Pass "App Match",
            -- Pass "App Record",
            -- Pass "App Trait",
            -- Pass "App Select",
            -- Pass "App With",
            Pass "App Err"
          ]
    test ctx pkg `shouldBe` testResults

  -- let name = "examples/expressions/and"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   pkg <- load [name]
  --   check pkg `shouldBe` []
  --   let ctx = pkg
  --   let testResults =
  --         [ Pass "And match",
  --           Fail "And match fail 1" i1 (And i1 i2),
  --           Fail "And match fail 2" (And i1 i1) (And i1 i2),
  --           Fail "And match fail 3" (And i2 i2) (And i1 i2)
  --         ]
  --   test ctx pkg `shouldBe` testResults

  let name = "examples/expressions/or"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Or match 1",
            Pass "Or match 2",
            Pass "Or match 3",
            Pass "Or match 4",
            Fail "Or match fail" i3 (Or i1 i2)
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/expressions/ann"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Ann match",
            Fail "Ann match type mismatch" i1 (Err $ typeMismatch IntT (loc (name ++ ".tao") 6 7 6 10 NumT)),
            Fail "Ann match fail" i2 i1
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/expressions/call"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Call constant",
            Pass "Call no args",
            Pass "Call args"
          ]
    test ctx pkg `shouldBe` testResults

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
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults = []
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/var"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Var match"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/overload"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Overload match 1",
            Pass "Overload match 2",
            Fail "Overload fail" i3 (Or (Ann i1 IntT) (Ann i2 IntT))
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/ann"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Ann match inline type",
            Pass "Ann match type annotation"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/and"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "And match 1",
            Pass "And match 2"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/or"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Or match 1",
            Pass "Or match 2"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/for"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "For match",
            Fail "For match fail" i1 (Ann (Err $ unhandledCase i2 i1) IntT)
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/fun"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Fun match 1",
            Pass "Fun match 2"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/app"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "App match 1",
            Pass "App match 2"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/call"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Call match",
            Fail "Call match fail" i1 (err Any)
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/definitions/op2"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "`Op` def",
            Pass "(Op) def",
            Pass "Infix def"
          ]
    test ctx pkg `shouldBe` testResults

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
  --         [ Pass "Neg"
  --         ]
  --   test ctx `shouldBe` testResults

  -- let name = "examples/definitions/op1"
  -- it ("☯ " ++ name ++ ".tao") $ do
  --   (ctx, syntaxErrors) <- load [name]
  --   syntaxErrors `shouldBe` []
  --   let testResults =
  --         [ Pass "Neg"
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
  --   test' name `shouldReturn` Pass results

  let name = "examples/syntax-sugar/list"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Nil",
            Pass "Cons infix",
            Pass "Cons prefix",
            Pass "Cons Cons"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/syntax-sugar/char"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "Char single quote",
            Pass "Char double quote"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/syntax-sugar/string"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    let ctx = pkg
    let testResults =
          [ Pass "String single quote",
            Pass "String double quote"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/prelude/arithmetic-int"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    let testResults =
          [ Pass "Add",
            Pass "Sub",
            Pass "Mul",
            Pass "Div",
            Pass "Div Int",
            Pass "Pow"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/prelude/arithmetic-num"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    let testResults =
          [ Pass "Add",
            Pass "Sub",
            Pass "Mul",
            Pass "Div",
            Pass "Div Int",
            Pass "Pow"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/prelude/comparison"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    let testResults =
          [ Pass "Eq 1 1",
            Pass "Eq 1 2",
            Pass "Eq 2 1",
            Pass "Ne 1 1",
            Pass "Ne 1 2",
            Pass "Ne 2 1",
            Pass "Lt 1 1",
            Pass "Lt 1 2",
            Pass "Lt 2 1",
            Pass "Le 1 1",
            Pass "Le 1 2",
            Pass "Le 2 1",
            Pass "Gt 1 1",
            Pass "Gt 1 2",
            Pass "Gt 2 1",
            Pass "Ge 1 1",
            Pass "Ge 1 2",
            Pass "Ge 2 1"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/prelude/bool-not"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    let testResults =
          [ Pass "T",
            Pass "F",
            Pass "Error"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/prelude/bool-and"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    let testResults =
          [ Pass "TT",
            Pass "TF",
            Pass "FT",
            Pass "FF",
            Pass "Error"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/prelude/bool-or"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    let testResults =
          [ Pass "TT",
            Pass "TF",
            Pass "FT",
            Pass "FF",
            Pass "Error"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/prelude/bool-xor"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    let testResults =
          [ Pass "TT",
            Pass "TF",
            Pass "FT",
            Pass "FF",
            Pass "Error"
          ]
    test ctx pkg `shouldBe` testResults

  let name = "examples/factorial"
  it ("☯ " ++ name ++ ".tao") $ do
    pkg <- load ["examples/factorial.tao"]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    let testResults =
          [ Pass "0",
            Pass "1",
            Pass "2",
            Pass "3",
            Pass "4",
            Pass "5"
          ]
    test ctx pkg `shouldBe` testResults
