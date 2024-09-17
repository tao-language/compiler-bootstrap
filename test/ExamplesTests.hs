module ExamplesTests where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (intercalate)
import System.FilePath (dropExtension)
import Tao
import TaoParser
import Test.Hspec

test' :: String -> IO [TestError]
test' name = do
  pkg <- parsePackage "examples"
  return (test (dropMeta pkg) name)

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let loc name pos = Meta (C.Location name pos)
  let ploc name pos = PMeta (C.Location name pos)
  let var filename pos x = loc filename pos (Var x)
  let (x, y, z) = (Var "x", Var "y", Var "z")

  let name = "empty"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` [NoTestsFound "empty"]

  let name = "comments"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` [NoTestsFound "comments"]

  -- let name = "comments-multiline.tao"
  -- it ("☯ " ++ name) $ do
  --   test' "comments-multiline.tao" `shouldReturn` []

  let name = "def-variable"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "def-function"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "errors"
  it ("☯ " ++ name) $ do
    let expected =
          [TestEqError (Var "@examples:errors/wrong-result.x") (Int 42) (PInt 0)]
    test' name `shouldReturn` expected

  let name = "imports"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "tuples"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "records"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  it "☯ TODO" $ do
    True `shouldBe` True
