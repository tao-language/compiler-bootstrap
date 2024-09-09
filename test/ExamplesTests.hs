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
  return (test pkg name)

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let loc name pos = Meta (C.Location name pos)
  let ploc name pos = PMeta (C.Location name pos)
  let var filename pos x = loc filename pos (Var x)
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

  let name = "errors"
  it ("☯ " ++ name) $ do
    let expected =
          [ let file = "errors/wrong-result.tao"
                x = "@examples:errors/wrong-result.x"
             in TestEqError (var file (3, 3) x) (Int 42) (ploc file (4, 1) $ PInt 0)
          ]
    test' name `shouldReturn` expected

  let name = "imports.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  let name = "tuples.tao"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` []

  -- let name = "records.tao"
  -- it ("☯ " ++ name) $ do
  --   test' name `shouldReturn` []

  -- it "☯ examples" $ do
  --   pkg <- parsePackage "examples"
  --   map dropMeta (test pkg) `shouldBe` []

  it "☯ TODO" $ do
    True `shouldBe` True
