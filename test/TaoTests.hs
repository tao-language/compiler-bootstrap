module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  let (i1', i2', i3') = (C.Int 1, C.Int 2, C.Int 3)
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
  let (_x, _y) = (PVar "x", PVar "y")
  -- let (_x', _y') = (C.VarP "x", C.VarP "y")

  it "☯ fun" $ do
    fun [] x `shouldBe` x
    fun [x] y `shouldBe` Fun x y
    fun [x, y] z `shouldBe` Fun x (Fun y z)

  it "☯ lam" $ do
    lam [] x `shouldBe` x
    lam [_x] y `shouldBe` Lam _x y
    lam [_x, _y] z `shouldBe` Lam _x (Lam _y z)

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
    toCore Err `shouldBe` C.Err C.Tup
    toCore (Int 1) `shouldBe` C.Int 1
    toCore (Num 1.1) `shouldBe` C.Num 1.1
    -- TODO: Knd, IntT, NumT
    toCore (Var "x") `shouldBe` C.Var "x"
    toCore (Fun x y) `shouldBe` C.Fun x' y'
    toCore (Match []) `shouldBe` C.Err C.Tup
    -- toCore (Match [([_x], x)]) `shouldBe` C.Lam _x' x'
    -- toCore (Match [([_x, _y], x)]) `shouldBe` C.lam [_x', _y'] x'
    -- toCore (Match [([_x], x), ([_y], y)]) `shouldBe` C.Or (C.Lam _x' x') (C.Lam _y' y')
    toCore (App x y) `shouldBe` C.App x' y'
    toCore (Ann x (For ["x", "y"] z)) `shouldBe` C.Ann x' (C.For ["x", "y"] z')
    toCore (Or x y) `shouldBe` C.Or x' y'
    toCore (Add x y) `shouldBe` C.add x' y'
    toCore (Sub x y) `shouldBe` C.sub x' y'
    toCore (Mul x y) `shouldBe` C.mul x' y'

  -- it "☯ fromCoreP" $ do
  --   True `shouldBe` True

  it "☯ fromCore" $ do
    True `shouldBe` True

  it "☯ eval" $ do
    let env = [("x", i1), ("f", Lam _x x)]
    eval env (App (Var "f") (Var "x")) `shouldBe` i1

  it "☯ infer" $ do
    let env = [("x", i1), ("f", Lam _x x)]
    eval env (App (Var "f") (Var "x")) `shouldBe` i1

  it "☯ overload" $ do
    let addOverloads =
          [ ([PIsInt "x", PIsInt "y"], Add x y),
            ([PIsInt "x", PIsNum "y"], Add (Int2Num x) y),
            ([PCtr "A", PCtr "B"], Ctr "C")
          ]

    let env = [("+", Match addOverloads)]
    let add a b = app (Var "+") [a, b]
    eval env (add (Int 1) (Int 2)) `shouldBe` Int 3
    eval' env (add (Int 1) (Num 2.2)) `shouldBe` C.Num 3.2
    eval env (add (Num 1.1) (Int 2)) `shouldBe` Err
    eval env (add (Ctr "A") (Ctr "B")) `shouldBe` Ctr "C"
