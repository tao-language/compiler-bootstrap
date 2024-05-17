module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Tao
import TaoParser
import Test.Hspec

test' :: String -> IO [TestError]
test' name = do
  pkg <- parseFile "examples" name (Package {name = name, modules = []})
  return (test pkg)

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let loc name pos = Meta (C.Location name pos)
  let (x, y, z) = (Var "x", Var "y", Var "z")

  let name = "empty.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "comments.tao"
  it ("☯ " ++ name) $ do
    test' "comments.tao" `shouldReturn` []

  -- let name = "comments-multiline.tao"
  -- it ("☯ " ++ name) $ do
  --   test' "comments-multiline.tao" `shouldReturn` []

  let name = "variables.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "variables-typed.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "tests.tao"
  it ("☯ " ++ name) $ do
    let name = "tests.tao"
    test' name `shouldReturn` [TestEqError (loc name (18, 3) (Var "tests.tao:tests#x")) (Int 42) (Int 0)]

  -- let name = "arithmetic.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "arithmetic-sugar.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "arithmetic-division-by-zero.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "comparison.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "functions.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "functions-lambda.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "functions-application.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "pattern-matching.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "union-types.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "tuples.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "records.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- let name = "literals-numbers.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  it "☯ TODO" $ do
    True `shouldBe` True
