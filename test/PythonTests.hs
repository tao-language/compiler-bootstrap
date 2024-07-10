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
    let emit' = emit :: BuildOptions -> Expr -> ([PyStmt], PyExpr)
    emit' options (Int 42) `shouldBe` ([], PyInteger 42)
    emit' options (Num 3.14) `shouldBe` ([], PyFloat 3.14)
    emit' options (Var "x") `shouldBe` ([], PyName "x")
    -- emit' options (Tag "Int" []) `shouldBe` ([], PyName "int")
    -- emit' options (Tag "Num" []) `shouldBe` ([], PyName "float")
    -- emit' options (Tag "A" []) `shouldBe` ([], pyCall (PyName "A") [])
    -- emit' options (Tag "A" [x, y]) `shouldBe` ([], pyCall (PyName "A") [x', y'])
    -- emit' options (Tuple []) `shouldBe` ([], PyTuple [])
    -- emit' options (Tuple [x, y]) `shouldBe` ([], PyTuple [x', y'])
    -- emit'  (Record []) `shouldBe` (, PyDict [])
    -- emit'  (Record [("a", x), ("b", y)]) `shouldBe` (, PyDict [(a', x'), (b', y')])
    -- emit'  (Trait x "y") `shouldBe` (, pyCall (PyAttribute x' "y") [])
    -- emit'  ListNil `shouldBe` (, pyCall (PyName "_ListNil") [])
    -- emit'  ListCons `shouldBe` (, pyCall (PyName "_ListCons") [])
    -- emit'  TextNil `shouldBe` (, pyCall (PyName "_TextNil") [])
    -- emit'  TextCons `shouldBe` (, pyCall (PyName "_TextCons") [])
    -- emit'  (Type []) `shouldBe` (, pyCall (PyName "Type") [PyList []])
    -- emit'  (Type ["A", "B"]) `shouldBe` (, pyCall (PyName "Type") [PyList [PyName "A", PyName "B"]])
    -- emit'  (Fun x y) `shouldBe`
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

  it "☯ emit Import" $ do
    emit options (Import "pkg" "mod" "@pkg.mod" []) `shouldBe` [PyImport "pkg.mod" Nothing]
    emit options (Import "pkg" "mod" "alias" []) `shouldBe` [PyImport "pkg.mod" (Just "alias")]
    emit options (Import "pkg" "mod" "@pkg.mod" [("a", "a"), ("b", "c")]) `shouldBe` [PyImport "pkg.mod" Nothing, PyImportFrom "pkg.mod" [("a", Nothing), ("b", Just "c")]]

  it "☯ emit Def" $ do
    emit options (var "x" y) `shouldBe` [PyAssign [x'] y']

  it "☯ emitModule" $ do
    let stmts =
          [ var "x" (Int 1),
            var "y" (Int 2)
          ]
    let emits =
          [ PyAssign [x'] (PyInteger 1),
            PyAssign [y'] (PyInteger 2)
          ]
    emit options (Module "mod" stmts) `shouldBe` PyModule {name = "mod", body = emits}

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
