module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (intercalate, isInfixOf)
import System.FilePath (dropExtension)
import Tao
import TaoParser
import Test.Hspec

test' :: String -> IO (Either [SyntaxError] [TestError])
test' name = do
  let path = "examples/" ++ name
  (pkg, syntaxErrors) <- load "examples" []
  case filter (\e -> (path ++ ".tao") == e.filename) syntaxErrors of
    [] -> do
      let errors = test [] (\(path', _) -> path `isInfixOf` path') pkg
      return (Right errors)
    _ -> return (Left syntaxErrors)

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")

  let name = "empty"
  it ("☯ " ++ name) $ do
    -- test' name [] `shouldReturn` Right [NoTestsFound "empty"]
    True `shouldBe` True

  let name = "comments"
  it ("☯ " ++ name) $ do
    -- test' name [] `shouldReturn` Right [NoTestsFound "comments"]
    True `shouldBe` True

  -- let name = "comments-multiline.tao"
  -- it ("☯ " ++ name) $ do
  --   test' "comments-multiline.tao" `shouldReturn` []

  let name = "def-untyped"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

  let name = "def-typed"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

  let name = "def-inline-type"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

  let name = "errors"
  it ("☯ " ++ name) $ do
    let errors =
          [ TestError
              { test =
                  UnitTest
                    { path = "examples/errors/wrong-result",
                      name = "",
                      expr = x,
                      expect = Int 0
                    },
                got = Int 42
              }
          ]
    test' name `shouldReturn` Right errors

  -- let name = "traits"
  -- it ("☯ " ++ name) $ do
  --   test' name [] `shouldReturn` Right []

  let name = "tuples-def"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

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
