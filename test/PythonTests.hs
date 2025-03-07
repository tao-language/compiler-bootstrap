module PythonTests where

import Control.Monad (forM)
import Data.List (sort)
import Load (load)
import Python
import qualified Subprocess
import System.Directory (doesDirectoryExist, doesFileExist, getDirectoryContents, removeDirectoryRecursive, removeFile, withCurrentDirectory)
import System.FilePath ((</>))
import qualified Tao as T
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Python ☯==--" $ do
  let options = defaultBuildOptions
  let (x, y, z) = (T.Var "x", T.Var "y", T.Var "z")
  let (xP, yP, zP) = (T.Var "x", T.Var "y", T.Var "z")
  let (x', y', z') = (Name "x", Name "y", Name "z")
  let (a', b') = (Name "a", Name "b")

  it "☯ emit Expr" $ do
    let emit' :: T.Expr -> ([Stmt], Expr)
        emit' = emit options
    emit' T.Any `shouldBe` ([], None)
    -- emit' T.Unit `shouldBe` ([], Tuple [])
    emit' T.IntT `shouldBe` ([], Name "int")
    emit' T.NumT `shouldBe` ([], Name "float")
    emit' (T.Int 42) `shouldBe` ([], Integer 42)
    emit' (T.Num 3.14) `shouldBe` ([], Float 3.14)
    -- emit' (T.Tag "Bool") `shouldBe` ([], Name "bool")
    -- emit' (T.Tag "True") `shouldBe` ([], Bool True)
    -- emit' (T.Tag "False") `shouldBe` ([], Bool False)
    -- emit' (T.Tag "A") `shouldBe` ([], Tuple [String "A"])
    emit' (T.Var "x") `shouldBe` ([], x')
    emit' (T.Ann x y) `shouldBe` ([], x')
    -- emit' (T.tag "A" [x, y]) `shouldBe` ([], Tuple [String "A", x', y'])
    -- emit' (T.And x y) `shouldBe` ([], Tuple [x', y'])
    -- emit' (T.and' [x, y, z]) `shouldBe` ([], Tuple [x', y', z'])
    emit' (T.Or x y) `shouldBe` ([], bitOr x' y')
    emit' (T.For ["x"] y) `shouldBe` ([], y')
    -- emit' (T.Fun x y) `shouldBe` ([], callable [x'] y')
    -- emit' (T.fun [x, y] z) `shouldBe` ([], callable [x', y'] z')
    -- emit' (T.App x y) `shouldBe` ([], call "x" [y'])
    -- emit' (T.app x [y, z]) `shouldBe` ([], call "x" [y', z'])
    -- Call String [Expr]
    -- Op1 Op1 Expr
    -- Op2 Op2 Expr Expr
    -- emit' (T.Match [] []) `shouldBe` ([Assign [Name "_match"] (notImplementedError "error")], Name "_match")
    -- If Expr Expr Expr
    -- emit' (T.Let (T.Var "x", y) z) `shouldBe` ([assign "x" y'], z')
    -- emit' (T.Bind (xP, y) z) `shouldBe` ([assign "x" (call "y" [])], z')
    -- Record [(String, Expr)]
    -- Select Expr [(String, Expr)]
    -- With Expr [(String, Expr)]
    -- Err
    True `shouldBe` True

  it "☯ emit Stmt" $ do
    let emit' :: T.Stmt -> [Stmt]
        emit' = emit options
    emit' (T.Import "mod" "mod" []) `shouldBe` [Import "mod" Nothing]
    emit' (T.Import "mod" "m" []) `shouldBe` [Import "mod" (Just "m")]
    emit' (T.Import "path-to/mod" "mod" []) `shouldBe` [Import "path_to.mod" Nothing]
    emit' (T.Import "mod" "mod" [("x", "x")]) `shouldBe` [Import "mod" Nothing, ImportFrom "mod" [("x", Nothing)]]
    emit' (T.Import "mod" "mod" [("x", "y")]) `shouldBe` [Import "mod" Nothing, ImportFrom "mod" [("x", Just "y")]]
    emit' (T.Def (x, y)) `shouldBe` [Assign [x'] y']
    -- emit' (T.Def (T.Var "a", T.Tag "Point" [T.Int 1, T.Int 2])) `shouldBe` [Assign [a'] (call "Point" [Integer 1, Integer 2])]
    -- emit' (var "a" (Tag "Point" [("y", Int 2), ("", Int 1)])) `shouldBe` [Assign [a'] (Call (Name "Point") [] [("x", Integer 1), ("y", Integer 2)])]
    -- emit' (varT "a" (Var "Point") (record [("y", Int 2), ("", Int 1)])) `shouldBe` [Assign [a'] (Call (Name "Point") [] [("x", Integer 1), ("y", Integer 2)])]
    True `shouldBe` True

  -- it "☯ emit [Stmt]" $ do
  --   -- let emit' :: [T.Stmt] -> [Stmt]
  --   --     emit' = emit options
  --   -- emit' [] `shouldBe` []
  --   -- emit' [T.Def (T.Var "x", T.Int 1)] `shouldBe` [Assign [Name "x"] (Integer 1)]
  --   True `shouldBe` True

  -- it "☯ emit Module" $ do
  --   -- let emit' :: T.Module -> Module
  --   --     emit' = emit options {prefix = "@pkg"}
  --   -- let stmts =
  --   --       [ T.Def (T.Var "x", T.Int 1),
  --   --         T.Def (T.Var "y", T.Int 2)
  --   --       ]
  --   -- let expected =
  --   --       [ ImportFrom "pkg.__prelude__" [("*", Nothing)],
  --   --         Assign [x'] (Integer 1),
  --   --         Assign [y'] (Integer 2)
  --   --       ]
  --   -- emit' ("mod", stmts) `shouldBe` Module {name = "mod", body = expected}
  --   True `shouldBe` True

  -- it "☯ emit Package" $ do
  --   let stmts =
  --         [ T.Def (x, T.Int 1),
  --           T.Def (y, T.Int 2)
  --         ]
  --   let pySrc =
  --         [ Assign [x'] (Integer 1),
  --           Assign [y'] (Integer 2)
  --         ]
  --   let pyTest = []
  --   -- emit options (Package "my_pkg" [Module "my-mod" stmts]) `shouldBe` Package "my-pkg" [Module "my_mod" pySrc] [Module "my_mod_test" pyTest]
  --   True `shouldBe` True

  it "☯ build factorial" $ do
    putStrLn "  ☯ build factorial"
    ctx <- load ["examples/factorial"]
    build options ctx `shouldReturn` "build"
    Subprocess.run "build" "python" ["-m", "venv", "env"]
    Subprocess.run "build" "env/bin/pip" ["install", "-e", "."]
    Subprocess.run "build" "env/bin/python" ["-m", "unittest", "-v", "examples.factorial_test"]

  -- it "☯ build" $ do
  --   putStrLn "> parsePackage"
  --   (pkg, s, errors) <- loadPackage "examples"
  --   pkg.name `shouldBe` "@examples"
  --   putStrLn "> build"
  --   build options "build" pkg `shouldReturn` "build/python"

  --   -- let taoModules =
  --   --       [ "def-function",
  --   --         "def-variable",
  --   --         "empty",
  --   --         "imports",
  --   --         "sub-module/sub-file"
  --   --       ]
  --   -- sort (map (\m -> m.name) pkg.modules) `shouldBe` taoModules

  --   -- let pythonFiles =
  --   --       [ "build/python/pyproject.toml",
  --   --         "build/python/simple/__init__.py",
  --   --         "build/python/simple/def_function.py",
  --   --         "build/python/simple/def_variable.py",
  --   --         "build/python/simple/empty.py",
  --   --         "build/python/simple/imports.py",
  --   --         "build/python/simple/sub_module/__init__.py",
  --   --         "build/python/simple/sub_module/sub_file.py",
  --   --         "build/python/test/__init__.py",
  --   --         "build/python/test/sub_module/__init__.py",
  --   --         "build/python/test/sub_module/test_sub_file.py",
  --   --         "build/python/test/test_def_function.py",
  --   --         "build/python/test/test_def_variable.py",
  --   --         "build/python/test/test_empty.py",
  --   --         "build/python/test/test_imports.py"
  --   --       ]
  --   -- fmap sort (getRecursiveContents "build/python") `shouldReturn` pythonFiles

  --   -- Setup the thon project.
  --   Subprocess.run "build/python" "python" ["-m", "venv", "env"]
  --   Subprocess.run "build/python" "env/bin/pip" ["install", "-U", "pip"]
  --   Subprocess.run "build/python" "env/bin/pip" ["install", "-e", "."]

  --   -- Run the tests, we expect a test failure.
  --   Subprocess.run "build/python" "env/bin/python" ["-m", "unittest", "-v"]
  --     `shouldThrow` anyException

  --   -- Remove the failing tests, and it should pass now.
  --   let failingTestsDir = "build/python/test/errors/"
  --   putStrLn ("> rm -r " ++ failingTestsDir)
  --   removeDirectoryRecursive failingTestsDir
  --   Subprocess.run "build/python" "env/bin/python" ["-m", "unittest", "-v"]

  it "☯ TODO" $ do
    True `shouldBe` True

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
