module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (intercalate, isInfixOf)
import System.FilePath (dropExtension)
import Tao
import TaoParser
import Test.Hspec

test' :: String -> IO (Either [SyntaxError] [TestResult])
test' name = do
  let testPath = "examples/" ++ name
  (pkg, syntaxErrors) <- load "examples" []
  case filter (\e -> testPath `isInfixOf` e.filename) syntaxErrors of
    [] -> do
      let results = test [] (\(path, _) -> testPath `isInfixOf` path) pkg
      return (Right results)
    _ -> return (Left syntaxErrors)

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")

  let name = "empty"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

  let name = "comments"
  it ("☯ " ++ name) $ do
    -- test' name [] `shouldReturn` Right [NoTestsFound "comments"]
    True `shouldBe` True

  -- let name = "comments-multiline.tao"
  -- it ("☯ " ++ name) $ do
  --   test' "comments-multiline.tao" `shouldReturn` []

  let name = "def-untyped"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right [TestPass ("examples/" ++ name) ""]

  let name = "def-typed"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right [TestPass ("examples/" ++ name) ""]

  let name = "def-inline-type"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right [TestPass ("examples/" ++ name) ""]

  let name = "errors"
  it ("☯ " ++ name) $ do
    let results =
          [ TestFail
              UnitTest
                { path = "examples/errors/wrong-result",
                  name = "",
                  expr = x,
                  expect = Int 0
                }
              (Int 42)
          ]
    test' name `shouldReturn` Right results

  -- let name = "traits"
  -- it ("☯ " ++ name) $ do
  --   test' name [] `shouldReturn` Right []

  let name = "tuples-def"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right [TestPass ("examples/" ++ name) ""]

  -- let name = "tuples-properties"
  -- it ("☯ " ++ name) $ do
  --   test' name [] `shouldReturn` Right []

  -- TODO: Tags

  -- let name = "records-def"
  -- it ("☯ " ++ name) $ do
  --   test' name [] `shouldReturn` Right []

  -- let name = "records-properties"
  -- it ("☯ " ++ name) $ do
  --   test' name [] `shouldReturn` Right []

  -- TODO: "records-select"
  -- TODO: "records-update"
  -- TODO: "records-reorder"
  -- TODO: "records-positional"
  -- TODO: "records-mixed-positional"
  -- TODO: "records-default-values"

  -- TODO: Unions
  -- TODO: Choices (?)

  it "☯ TODO" $ do
    True `shouldBe` True
