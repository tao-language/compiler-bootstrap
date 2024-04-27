module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Tao
import TaoParser
import Test.Hspec

test' :: String -> IO [TestError]
test' name = do
  pkg <- parsePackage name (Package {name = name, modules = []})
  return (test pkg)

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let loc name pos = Meta (C.Location name pos)
  let (x, y, z) = (Var "x", Var "y", Var "z")

  let name = "examples/empty.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "examples/comments.tao"
  it ("☯ " ++ name) $ do
    test' "examples/comments.tao" `shouldReturn` []

  -- let name = "examples/comments-multiline.tao"
  -- it ("☯ " ++ name) $ do
  --   test' "examples/comments-multiline.tao" `shouldReturn` []

  let name = "examples/variables.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "examples/variables-typed.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "examples/tests.tao"
  it ("☯ " ++ name) $ do
    let name = "examples/tests.tao"
    test' name `shouldReturn` [TestEqError (loc name (18, 3) x) (Int 42) (Int 0)]

  -- let name = "examples/arithmetic.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/arithmetic-sugar.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/arithmetic-division-by-zero.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/comparison.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/functions.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/functions-lambda.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/functions-application.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/pattern-matching.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/union-types.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/tuples.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/records.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "examples/literals-numbers.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  it "☯ TODO" $ do
    True `shouldBe` True
