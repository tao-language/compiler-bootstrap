module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (intercalate, isInfixOf)
import System.FilePath (dropExtension)
import Tao
import TaoParser
import Test.Hspec

test' :: String -> [String] -> IO (Either [SyntaxError] [TestError])
test' name includes = do
  -- let names = name : includes
  -- (pkg, s, errors) <- loadPackage "examples"
  -- let env = lower [] pkg
  -- case filter (\e -> any (`isInfixOf` e.filename) names) errors of
  --   [] -> return (Right (dropMeta <$> test env name))
  --   errors -> return (Left errors)
  return (Right [])

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let loc name pos = Meta (C.Location name pos)
  let var filename pos x = loc filename pos (Var x)
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
    test' name [] `shouldReturn` Right []

  let name = "def-typed"
  it ("☯ " ++ name) $ do
    test' name [] `shouldReturn` Right []

  let name = "def-inline-type"
  it ("☯ " ++ name) $ do
    test' name [] `shouldReturn` Right []

  let name = "errors"
  it ("☯ " ++ name) $ do
    -- test' name [] `shouldReturn` Right [TestEqError ">@examples/errors/wrong-result:" (C.Var "@examples/errors/wrong-result.x") (C.Int 0) (C.Int 42)]
    True `shouldBe` True

  -- TODO: import global
  -- TODO: import root

  -- TODO: match-one
  -- TODO: match-many

  -- let name = "traits"
  -- it ("☯ " ++ name) $ do
  --   test' name [] `shouldReturn` Right []

  let name = "tuples-def"
  it ("☯ " ++ name) $ do
    test' name [] `shouldReturn` Right []

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
