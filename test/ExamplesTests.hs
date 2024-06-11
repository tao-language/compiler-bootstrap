module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (intercalate)
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
  let ploc name pos = PMeta (C.Location name pos)
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

  let name = "def-variable.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "def-function.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "test-errors.tao"
  it ("☯ " ++ name) $ do
    let name = "test-errors.tao"
    let m row col = loc name (row, col)
    let pm row col = ploc name (row, col)
    test' name `shouldReturn` [TestEqError (m 3 3 $ Var "test-errors.tao:test-errors#x") (Int 42) (pm 4 1 $ PInt 0)]

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
