module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
  -- it "☯ toCoreP" $ do
  --   True `shouldBe` True

  it "☯ toCore" $ do
    toCore Knd `shouldBe` C.Knd
    toCore IntT `shouldBe` C.IntT
    toCore NumT `shouldBe` C.NumT
    toCore (Int 42) `shouldBe` C.Int 42
    toCore (Num 3.14) `shouldBe` C.Num 3.14
    toCore (Tag "A") `shouldBe` C.Tag "A"
    toCore (Var "x") `shouldBe` C.Var "x"

  it "☯ TODO" $ do
    True `shouldBe` True