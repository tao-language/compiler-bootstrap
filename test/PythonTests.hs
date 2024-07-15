module PythonTests where

import Control.Monad (forM)
import Data.List (sort)
import Python
import qualified Subprocess
import System.Directory (doesDirectoryExist, doesFileExist, getDirectoryContents, removeDirectoryRecursive, removeFile, withCurrentDirectory)
import System.FilePath ((</>))
import Tao
import TaoParser (parsePackage)
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Python ☯==--" $ do
  let options = defaultBuildOptions {packageName = "pkg"}
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PyName "x", PyName "y", PyName "z")
  let (a', b') = (PyName "a", PyName "b")

  it "☯ emit Expr" $ do
    let emit' :: Expr -> ([PyStmt], PyExpr)
        emit' expr = emit options (expr, [] :: Context)
    emit' (Int 42) `shouldBe` ([], PyInteger 42)
    emit' (Num 3.14) `shouldBe` ([], PyFloat 3.14)
    emit' (Var "x") `shouldBe` ([], PyName "x")
    emit' (Tag "Int" []) `shouldBe` ([], PyName "int")
    emit' (Tag "Num" []) `shouldBe` ([], PyName "float")
    emit' (Tag "A" []) `shouldBe` ([], pyCall (PyName "A") [])
    emit' (Tag "A" [x, y]) `shouldBe` ([], pyCall (PyName "A") [x', y'])
    emit' (Tuple []) `shouldBe` ([], PyTuple [])
    emit' (Tuple [x, y]) `shouldBe` ([], PyTuple [x', y'])
    emit' (Record []) `shouldBe` ([], PyDict [])
    emit' (Record [("a", x), ("b", y)]) `shouldBe` ([], PyDict [(PyString "a", x'), (PyString "b", y')])
    emit' (Trait x "y") `shouldBe` ([], PyAttribute x' "y")
    -- emit' (Type [], []) `shouldBe` ([], pyCall (PyName "Type") [PyList []])
    -- emit' (Type ["A", "B"]) `shouldBe` (, pyCall (PyName "Type") [PyList [PyName "A", PyName "B"]])
    -- emit' (Fun x y) `shouldBe`
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

  it "☯ emit Stmt" $ do
    let emit' :: Stmt -> [PyStmt]
        emit' stmt = emit options (stmt, [] :: Context)
    emit' (Import "pkg" "mod" "@pkg.mod" []) `shouldBe` [PyImport "pkg.mod" Nothing]
    emit' (Import "pkg" "mod" "alias" []) `shouldBe` [PyImport "pkg.mod" (Just "alias")]
    emit' (Import "pkg" "mod" "@pkg.mod" [("a", "a"), ("b", "c")]) `shouldBe` [PyImport "pkg.mod" Nothing, PyImportFrom "pkg.mod" [("a", Nothing), ("b", Just "c")]]
    emit' (var "x" y) `shouldBe` [PyAssign [x'] y']

  it "☯ emit [Stmt]" $ do
    let emit' :: [Stmt] -> [PyStmt]
        emit' stmts = emit options (stmts, [] :: Context)
    let stmts =
          []
    True `shouldBe` True

  it "☯ emit Module" $ do
    let emit' :: Module -> PyModule
        emit' mod = emit options (mod, [] :: Context)
    let stmts =
          [ var "x" (Int 1),
            var "y" (Int 2)
          ]
    let expected =
          [ PyAssign [x'] (PyInteger 1),
            PyAssign [y'] (PyInteger 2)
          ]
    emit' (Module "mod" stmts) `shouldBe` PyModule {name = "mod", body = expected}

  it "☯ emit Package" $ do
    let stmts =
          [ var "x" (Int 1),
            var "y" (Int 2)
          ]
    let pySrc =
          [ PyAssign [x'] (PyInteger 1),
            PyAssign [y'] (PyInteger 2)
          ]
    let pyTest = []
    -- emit options (Package "my_pkg" [Module "my-mod" stmts]) `shouldBe` PyPackage "my-pkg" [PyModule "my_mod" pySrc] [PyModule "my_mod_test" pyTest]
    True `shouldBe` True

  it "☯ build" $ do
    putStrLn "> parsePackage"
    pkg <- parsePackage "examples"
    pkg.name `shouldBe` "examples"
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

    -- Setup the Python project.
    Subprocess.run "build/python" "python" ["-m", "venv", "env"]
    Subprocess.run "build/python" "env/bin/pip" ["install", "-U", "pip"]
    Subprocess.run "build/python" "env/bin/pip" ["install", "-e", "."]

    -- Run the tests, we expect a test failure.
    Subprocess.run "build/python" "env/bin/python" ["-m", "unittest", "-v"]
      `shouldThrow` anyException

    -- Remove the failing tests, and it should pass now.
    let failingTestsDir = "build/python/test/errors/"
    putStrLn ("> rm -r " ++ failingTestsDir)
    removeDirectoryRecursive failingTestsDir
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
