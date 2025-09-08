module PreludeTests where

import qualified Core as C
import Data.Bifunctor (second)
import Data.Function ((&))
import Data.List (intercalate, isInfixOf)
import Error
import Load
import Location
import Stdlib (filterMap)
import System.FilePath (dropExtension)
import Tao
import Test
import Test.Hspec

data Result a
  = Pass String
  | Fail String a a
  deriving (Eq)

instance (Show a) => Show (Result a) where
  show :: Result a -> String
  show = \case
    Pass name -> "✅ " ++ name ++ "\n"
    Fail name expected got -> "❌ " ++ name ++ "\n" ++ show expected ++ "\n" ++ show got ++ "\n"

test :: Context -> Package -> [String]
test ctx pkg = do
  let failed = \case
        TestPass name -> Nothing
        TestFail (name, _, expected) got -> do
          Just (name ++ "\n" ++ show expected ++ "\n" ++ show got ++ "\n")
  filterMap failed (testAll ctx pkg)

run :: SpecWith ()
run = describe "--==☯ Prelude tests ☯==--" $ do
  let name = "prelude/@arithmetic-int"
  it ("☯ " ++ name) $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    test ctx pkg `shouldBe` []

  let name = "prelude/@arithmetic-num"
  it ("☯ " ++ name) $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    test ctx pkg `shouldBe` []

  let name = "prelude/@bool"
  it ("☯ " ++ name) $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    test ctx pkg `shouldBe` []

  let name = "prelude/@maybe"
  it ("☯ " ++ name) $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    test ctx pkg `shouldBe` []

  let name = "prelude/@result"
  it ("☯ " ++ name) $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    test ctx pkg `shouldBe` []

  let name = "prelude/@comparison"
  it ("☯ " ++ name) $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    test ctx pkg `shouldBe` []

  let name = "prelude/@function"
  it ("☯ " ++ name) $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    test ctx pkg `shouldBe` []

  let name = "prelude/@list"
  it ("☯ " ++ name) $ do
    pkg <- load [name]
    check pkg `shouldBe` []
    ctx <- include "prelude" pkg
    test ctx pkg `shouldBe` []
