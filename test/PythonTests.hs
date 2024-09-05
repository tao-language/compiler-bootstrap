module PythonTests where

import Control.Monad (forM)
import Data.List (sort)
import Python
import qualified Subprocess
import System.Directory (doesDirectoryExist, doesFileExist, getDirectoryContents, removeDirectoryRecursive, removeFile, withCurrentDirectory)
import System.FilePath ((</>))
import qualified Tao as T
import TaoParser (parsePackage)
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Python ☯==--" $ do
  let options = defaultBuildOptions {packageName = "pkg"}
  let (x, y, z) = (T.Var "x", T.Var "y", T.Var "z")
  let (xP, yP, zP) = (T.PVar "x", T.PVar "y", T.PVar "z")
  let (x', y', z') = (Name "x", Name "y", Name "z")
  let (a', b') = (Name "a", Name "b")

  it "☯ emit Expr" $ do
    let emit' :: T.Expr -> ([Stmt], Expr)
        emit' = emit options
    emit' (T.Int 42) `shouldBe` ([], Integer 42)
    emit' (T.Num 3.14) `shouldBe` ([], Float 3.14)
    emit' (T.Var "x") `shouldBe` ([], Name "x")
    emit' (T.Tag "Type" []) `shouldBe` ([], Name "type")
    emit' (T.Tag "Int" []) `shouldBe` ([], Name "int")
    emit' (T.Tag "Num" []) `shouldBe` ([], Name "float")
    emit' (T.Tag "A" []) `shouldBe` ([], call "A" [])
    emit' (T.Tag "A" [x, y]) `shouldBe` ([], call "A" [x', y'])
    emit' (T.Tuple []) `shouldBe` ([], Tuple [])
    emit' (T.Tuple [x, y]) `shouldBe` ([], Tuple [x', y'])
    emit' (T.record [("", x), ("b", y)]) `shouldBe` ([], Tuple [x', y'])
    emit' (T.record [("a", x), ("b", y)]) `shouldBe` ([], record [("a", x'), ("b", y')])
    emit' (T.Trait x "y") `shouldBe` ([], Attribute x' "y")
    emit' (T.TraitFun "x") `shouldBe` ([], Lambda ["_"] (Attribute (Name "_") "x"))
    emit' (T.Fun x y) `shouldBe` ([], callable [x'] y')
    emit' (T.fun [x, y] z) `shouldBe` ([], callable [x', y'] z')
    emit' (T.App x y) `shouldBe` ([], call "x" [y'])
    emit' (T.app x [y, z]) `shouldBe` ([], call "x" [y', z'])
    emit' (T.Or x y) `shouldBe` ([], bitOr x' y')
    emit' (T.let' xP y z) `shouldBe` ([assign "x" y'], z')
    -- emit' (T.Bind (xP, y) z) `shouldBe` ([assign "x" (call "y" [])], z')
    -- Lambda [String] Expr
    -- Match [Expr] [Case]
    -- If Expr Expr Expr
    -- Ann Expr Expr
    -- Op String [Expr]
    -- Meta C.Metadata Expr
    -- Err
    True `shouldBe` True

  it "☯ emit Stmt" $ do
    let emit' :: T.Stmt -> [Stmt]
        emit' = emit options
    emit' (T.Import "mod" "" []) `shouldBe` [Import "mod" Nothing]
    emit' (T.Import "mod" "alias" []) `shouldBe` [Import "mod" (Just "alias")]
    emit' (T.Import "@pkg/mod" "" []) `shouldBe` [Import "pkg.mod" Nothing]
    emit' (T.Import "mod" "" [("x", "")]) `shouldBe` [Import "mod" Nothing, ImportFrom "mod" [("x", Nothing)]]
    emit' (T.Import "mod" "" [("x", "y")]) `shouldBe` [Import "mod" Nothing, ImportFrom "mod" [("x", Just "y")]]
    emit' (T.var "x" y) `shouldBe` [Assign [x'] y']
    emit' (T.var "a" (T.Tag "Point" [T.Int 1, T.Int 2])) `shouldBe` [Assign [a'] (call "Point" [Integer 1, Integer 2])]
    -- emit' (var "a" (Tag "Point" [("y", Int 2), ("", Int 1)])) `shouldBe` [Assign [a'] (Call (Name "Point") [] [("x", Integer 1), ("y", Integer 2)])]
    -- emit' (varT "a" (Var "Point") (record [("y", Int 2), ("", Int 1)])) `shouldBe` [Assign [a'] (Call (Name "Point") [] [("x", Integer 1), ("y", Integer 2)])]
    True `shouldBe` True

  it "☯ emit [Stmt]" $ do
    let emit' :: [T.Stmt] -> [Stmt]
        emit' = emit options
    emit' [] `shouldBe` []
    emit' [T.var "x" (T.Int 1)] `shouldBe` [Assign [Name "x"] (Integer 1)]

  it "☯ emit Module" $ do
    let emit' :: T.Module -> Module
        emit' = emit options
    let stmts =
          [ T.var "x" (T.Int 1),
            T.var "y" (T.Int 2)
          ]
    let expected =
          [ ImportFrom "pkg.__prelude__" [("*", Nothing)],
            Assign [x'] (Integer 1),
            Assign [y'] (Integer 2)
          ]
    emit' (T.Module "mod" stmts) `shouldBe` Module {name = "mod", body = expected}

  it "☯ emit Package" $ do
    let stmts =
          [ T.var "x" (T.Int 1),
            T.var "y" (T.Int 2)
          ]
    let pySrc =
          [ Assign [x'] (Integer 1),
            Assign [y'] (Integer 2)
          ]
    let pyTest = []
    -- emit options (Package "my_pkg" [Module "my-mod" stmts]) `shouldBe` Package "my-pkg" [Module "my_mod" pySrc] [Module "my_mod_test" pyTest]
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

    -- Setup the thon project.
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
