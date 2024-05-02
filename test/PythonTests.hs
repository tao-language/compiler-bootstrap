module PythonTests where

import PrettyPrint (pretty)
import Python
import System.Directory (doesDirectoryExist)
import System.FilePath ((</>))
import Tao
import TaoParser (parsePackage)
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Python ☯==--" $ do
  let options = defaultBuildOptions
  let ctx = PyCtx {globals = [], locals = [], nameIndex = 0}
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PyName "x", PyName "y", PyName "z")
  let (a', b') = (PyName "a", PyName "b")

  it "☯ emitExpr" $ do
    emitExpr options ctx Any `shouldBe` (ctx, PyName "_")
    emitExpr options ctx IntType `shouldBe` (ctx, PyName "int")
    emitExpr options ctx NumType `shouldBe` (ctx, PyName "float")
    emitExpr options ctx (Int 42) `shouldBe` (ctx, PyInteger 42)
    emitExpr options ctx (Num 3.14) `shouldBe` (ctx, PyFloat 3.14)
    emitExpr options ctx (Var "x") `shouldBe` (ctx, PyName "x")
    emitExpr options ctx (Tag "A" []) `shouldBe` (ctx, pyCall (PyName "A") [])
    emitExpr options ctx (Tag "A" [x, y]) `shouldBe` (ctx, pyCall (PyName "A") [x', y'])
    emitExpr options ctx (Tuple []) `shouldBe` (ctx, PyTuple [])
    emitExpr options ctx (Tuple [x, y]) `shouldBe` (ctx, PyTuple [x', y'])
    -- emitExpr ctx (Record []) `shouldBe` (ctx, PyDict [])
    -- emitExpr ctx (Record [("a", x), ("b", y)]) `shouldBe` (ctx, PyDict [(a', x'), (b', y')])
    -- emitExpr ctx (Trait x "y") `shouldBe` (ctx, pyCall (PyAttribute x' "y") [])
    -- emitExpr ctx ListNil `shouldBe` (ctx, pyCall (PyName "_ListNil") [])
    -- emitExpr ctx ListCons `shouldBe` (ctx, pyCall (PyName "_ListCons") [])
    -- emitExpr ctx TextNil `shouldBe` (ctx, pyCall (PyName "_TextNil") [])
    -- emitExpr ctx TextCons `shouldBe` (ctx, pyCall (PyName "_TextCons") [])
    -- emitExpr ctx (Type []) `shouldBe` (ctx, pyCall (PyName "Type") [PyList []])
    -- emitExpr ctx (Type ["A", "B"]) `shouldBe` (ctx, pyCall (PyName "Type") [PyList [PyName "A", PyName "B"]])
    -- emitExpr ctx (Fun x y) `shouldBe`
    -- Fun Expr Expr
    -- App Expr Expr
    -- Let (Expr, Expr) Expr
    -- Bind (Expr, Expr) Expr
    -- TypeDef String [Expr] Expr
    -- MatchFun [Expr]
    -- Match [Expr] [Expr]
    -- Or Expr Expr
    -- Ann Expr Expr
    -- Op1 C.UnaryOp Expr
    -- Op2 C.BinaryOp Expr Expr
    -- Meta C.Metadata Expr
    -- Err
    True `shouldBe` True

  it "☯ emitStmt Import" $ do
    emitStmt options (Import [] "mod" "mod" []) ctx `shouldBe` ctx {globals = [PyImport "mod" Nothing]}
    emitStmt options (Import [] "mod" "alias" []) ctx `shouldBe` ctx {globals = [PyImport "mod" (Just "alias")]}
    emitStmt options (Import [] "mod" "mod" [("a", "a"), ("b", "c")]) ctx `shouldBe` ctx {globals = [PyImport "mod" Nothing, PyImportFrom "mod" [("a", Nothing), ("b", Just "c")]]}

  it "☯ emitStmt Def" $ do
    emitStmt options (Def (DefName [] "x" [] y)) ctx `shouldBe` ctx {locals = [PyAssign [x'] y']}

  it "☯ emitModule" $ do
    let stmts =
          [ Def (DefName [] "x" [] (Int 1)),
            Def (DefName [] "y" [] (Int 2))
          ]
    let emitStmts =
          [ PyAssign [x'] (PyInteger 1),
            PyAssign [y'] (PyInteger 2)
          ]
    emitModule options (Module [] "mod" stmts) `shouldBe` PyModule {name = "mod", body = emitStmts}

  it "☯ build" $ do
    pkg <- parsePackage "examples/simple"
    pkg.name `shouldBe` "simple"
    map (\m -> (m.path, m.name)) pkg.modules `shouldBe` [([], "main"), (["submodule"], "subfile")]

    -- Check package
    build options "build" pkg `shouldReturn` "build/python"
    doesDirectoryExist "build/python" `shouldReturn` True
    -- TODO: add pyproject.toml
    -- TODO: add README.md
    -- TODO: add LICENSE

    -- Check source files
    readFile "build/python/simple/__init__.py" `shouldReturn` ""
    readFile "build/python/simple/main.py" `shouldReturn` "x = 1"
    readFile "build/python/simple/submodule/__init__.py" `shouldReturn` ""
    readFile "build/python/simple/submodule/subfile.py" `shouldReturn` "y = 2"

    -- Check tests

    -- Check docs

    True `shouldBe` True
