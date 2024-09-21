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
  (pkg, errors) <- parsePackage "examples"
  case filter (\e -> name `isInfixOf` e.filename) errors of
    [] -> do
      let pkg' = pkg {modules = filter (\m -> name `isInfixOf` m.name) pkg.modules}
      return (Right $ test (dropMeta pkg') name)
    errors -> return (Left errors)

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let loc name pos = Meta (C.Location name pos)
  let ploc name pos = PMeta (C.Location name pos)
  let var filename pos x = loc filename pos (Var x)
  let (x, y, z) = (Var "x", Var "y", Var "z")

  let name = "empty"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right [NoTestsFound "empty"]

  let name = "comments"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right [NoTestsFound "comments"]

  -- let name = "comments-multiline.tao"
  -- it ("☯ " ++ name) $ do
  --   test' "comments-multiline.tao" `shouldReturn` []

  let name = "def-variable"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

  let name = "def-function"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

  let name = "errors"
  it ("☯ " ++ name) $ do
    let expected =
          [ TestEqError (Var "@examples:errors/wrong-result.x") (Int 42) (PInt 0)
          ]
    test' name `shouldReturn` Right expected

  let name = "imports/basic"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

  let name = "tuples"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

  let name = "records"
  it ("☯ " ++ name) $ do
    test' name `shouldReturn` Right []

  it "☯ TODO" $ do
    True `shouldBe` True
