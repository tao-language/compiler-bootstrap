module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
  let (i0, i1, i2) = (Int 0, Int 1, Int 2)
  let (i0', i1', i2') = (C.Int 0, C.Int 1, C.Int 2)
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
  let (_x, _y) = (VarP "x", VarP "y")
  let (_x', _y') = (C.VarP "x", C.VarP "y")

  it "☯ fun" $ do
    fun [] x `shouldBe` x
    fun [x] y `shouldBe` Fun x y
    fun [x, y] z `shouldBe` Fun x (Fun y z)

  it "☯ lam" $ do
    lam [] x `shouldBe` x
    lam [_x] y `shouldBe` Match [([_x], y)]
    lam [_x, _y] z `shouldBe` Match [([_x, _y], z)]

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ or'" $ do
    or' [] `shouldBe` Err
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

  -- it "☯ toCoreP" $ do
  --   True `shouldBe` True

  it "☯ toCore" $ do
    toCore Err `shouldBe` C.Err
    toCore (Int 1) `shouldBe` C.Int 1
    toCore (Num 1.1) `shouldBe` C.Num 1.1
    -- TODO: Knd, IntT, NumT
    toCore (Var "x") `shouldBe` C.Var "x"
    toCore (Fun x y) `shouldBe` C.Fun x' y'
    toCore (Match []) `shouldBe` C.Err
    toCore (Match [([_x], x)]) `shouldBe` C.Lam _x' x'
    toCore (Match [([_x, _y], x)]) `shouldBe` C.lam [_x', _y'] x'
    toCore (Match [([_x], x), ([_y], y)]) `shouldBe` C.Or (C.Lam _x' x') (C.Lam _y' y')
    toCore (App x y) `shouldBe` C.App x' y'
    toCore (Ann x (For ["x", "y"] z)) `shouldBe` C.Ann x' (C.For ["x", "y"] z')
    toCore (Or x y) `shouldBe` C.Or x' y'

  -- it "☯ fromCoreP" $ do
  --   True `shouldBe` True

  it "☯ fromCore" $ do
    True `shouldBe` True