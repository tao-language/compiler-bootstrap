module PythonTests where

import Control.Monad (forM)
import Data.List (sort)
import Python
import qualified Subprocess
import System.Directory (doesDirectoryExist, doesFileExist, getDirectoryContents, withCurrentDirectory)
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
    emitExpr options ctx (Int 42) `shouldBe` (ctx, PyInteger 42)
    emitExpr options ctx (Num 3.14) `shouldBe` (ctx, PyFloat 3.14)
    emitExpr options ctx (Var "x") `shouldBe` (ctx, PyName "x")
    emitExpr options ctx (Tag "Int") `shouldBe` (ctx, PyName "int")
    emitExpr options ctx (Tag "Num") `shouldBe` (ctx, PyName "float")
    emitExpr options ctx (Tag "A") `shouldBe` (ctx, pyCall (PyName "A") [])
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
    emitStmt options "pkg" (Import "mod" "mod" []) ctx `shouldBe` ctx {globals = [PyImport "pkg.mod" Nothing]}
    emitStmt options "pkg" (Import "mod" "alias" []) ctx `shouldBe` ctx {globals = [PyImport "pkg.mod" (Just "alias")]}
    emitStmt options "pkg" (Import "mod" "mod" [("a", "a"), ("b", "c")]) ctx `shouldBe` ctx {globals = [PyImport "pkg.mod" Nothing, PyImportFrom "pkg.mod" [("a", Nothing), ("b", Just "c")]]}

  it "☯ emitStmt Def" $ do
    emitStmt options "pkg" (Def (NameDef [] "x" [] y)) ctx `shouldBe` ctx {locals = [PyAssign [x'] y']}

  it "☯ emitModule" $ do
    let stmts =
          [ Def (NameDef [] "x" [] (Int 1)),
            Def (NameDef [] "y" [] (Int 2))
          ]
    let emitStmts =
          [ PyAssign [x'] (PyInteger 1),
            PyAssign [y'] (PyInteger 2)
          ]
    emitModule options "pkg" (Module "mod" stmts) `shouldBe` PyModule {name = "mod", body = emitStmts}

  it "☯ build" $ do
    putStrLn "> parsePackage"
    pkg <- parsePackage "examples/simple"
    pkg.name `shouldBe` "simple"
    putStrLn "> build"
    build options "build" pkg `shouldReturn` "build/python"

    -- let taoModules =
    --       [ "def-function",
    --         "def-variable",
    --         "empty",
    --         "imports",
    --         "sub-module/sub-file"
    --       ]
    -- sort (map (\m -> m.name) pkg.modules) `shouldBe` taoModules

    -- let pythonFiles =
    --       [ "build/python/pyproject.toml",
    --         "build/python/simple/__init__.py",
    --         "build/python/simple/def_function.py",
    --         "build/python/simple/def_variable.py",
    --         "build/python/simple/empty.py",
    --         "build/python/simple/imports.py",
    --         "build/python/simple/sub_module/__init__.py",
    --         "build/python/simple/sub_module/sub_file.py",
    --         "build/python/test/__init__.py",
    --         "build/python/test/sub_module/__init__.py",
    --         "build/python/test/sub_module/test_sub_file.py",
    --         "build/python/test/test_def_function.py",
    --         "build/python/test/test_def_variable.py",
    --         "build/python/test/test_empty.py",
    --         "build/python/test/test_imports.py"
    --       ]
    -- fmap sort (getRecursiveContents "build/python") `shouldReturn` pythonFiles

    -- Run generated tests
    Subprocess.run "build/python" "python" ["-m", "venv", "env"]
    Subprocess.run "build/python" "env/bin/pip" ["install", "-U", "pip"]
    Subprocess.run "build/python" "env/bin/pip" ["install", "-e", "."]
    Subprocess.run "build/python" "env/bin/python" ["-m", "unittest", "-v"]

-- https://book.realworldhaskell.org/read/io-case-study-a-library-for-searching-the-filesystem.html
getRecursiveContents :: FilePath -> IO [FilePath]
getRecursiveContents topdir = do
  names <- getDirectoryContents topdir
  let properNames = filter (`notElem` [".", ".."]) names
  paths <- forM properNames $ \name -> do
    let path = topdir </> name
    isDirectory <- doesDirectoryExist path
    if isDirectory
      then getRecursiveContents path
      else return [path]
  return (concat paths)
