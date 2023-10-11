module TaoTests_bak where

import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
  -- let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  -- let (i1', i2', i3') = (C.Int 1, C.Int 2, C.Int 3)
  -- let (a, b, c) = (Var "a", Var "b", Var "c")
  -- let (x, y, z) = (Var "x", Var "y", Var "z")
  -- let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
  -- let (_x, _y) = (PVar "x", PVar "y")
  -- -- let (_x', _y') = (C.VarP "x", C.VarP "y")

  -- it "☯ fun" $ do
  --   fun [] x `shouldBe` x
  --   fun [x] y `shouldBe` Fun x y
  --   fun [x, y] z `shouldBe` Fun x (Fun y z)

  -- it "☯ lam" $ do
  --   lam [] x `shouldBe` x
  --   lam [_x] y `shouldBe` Lam _x y
  --   lam [_x, _y] z `shouldBe` Lam _x (Lam _y z)

  -- it "☯ app" $ do
  --   app x [] `shouldBe` x
  --   app x [y] `shouldBe` App x y
  --   app x [y, z] `shouldBe` App (App x y) z

  -- it "☯ or'" $ do
  --   or' [] `shouldBe` Err
  --   or' [x] `shouldBe` x
  --   or' [x, y] `shouldBe` Or x y
  --   or' [x, y, z] `shouldBe` Or x (Or y z)

  -- -- it "☯ toCoreP" $ do
  -- --   True `shouldBe` True

  -- it "☯ toCore basic" $ do
  --   toCore Err `shouldBe` C.Err []
  --   toCore Knd `shouldBe` C.Knd
  --   toCore IntT `shouldBe` C.IntT
  --   toCore NumT `shouldBe` C.NumT
  --   toCore (Int 1) `shouldBe` C.Int 1
  --   toCore (Num 1.1) `shouldBe` C.Num 1.1
  --   toCore (Tag "A") `shouldBe` C.Tag "A"
  --   toCore (Var "x") `shouldBe` C.Var "x"
  --   toCore (Fun x y) `shouldBe` C.Fun x' y'
  --   toCore (App x y) `shouldBe` C.App x' y'
  --   toCore (Ann x (For ["x", "y"] z)) `shouldBe` C.Ann x' (C.For ["x", "y"] z')
  --   toCore (Or x y) `shouldBe` C.Or x' y'
  --   toCore (If x y) `shouldBe` C.If x' y'
  --   toCore (Rec []) `shouldBe` C.Rec []
  --   toCore (Rec [("a", x), ("b", y)]) `shouldBe` C.Rec [("a", x'), ("b", y')]
  --   toCore (Add x y) `shouldBe` C.addI x' y'
  --   toCore (Sub x y) `shouldBe` C.sub x' y'
  --   toCore (Mul x y) `shouldBe` C.mul x' y'
  --   toCore (Pow x y) `shouldBe` C.pow x' y'
  --   toCore (Eq x y) `shouldBe` C.eq x' y'
  --   toCore (Lt x y) `shouldBe` C.lt x' y'
  --   toCore (Gt x y) `shouldBe` C.gt x' y'
  --   toCore (Int2Num x) `shouldBe` C.int2num x'

  -- it "☯ toCore pattern matching" $ do
  --   toCore (Lam PAny y) `shouldBe` C.Lam "_" y'
  --   toCore (Lam PAny (Var "_")) `shouldBe` C.Lam "_1" (C.Var "_")
  --   toCore (Lam PAny (Lam PAny y)) `shouldBe` C.Lam "_" (C.Lam "_" y')
  --   toCore (Lam PTyp y) `shouldBe` C.Lam "$1" (C.If (C.eq (C.Var "$1") C.Knd) y')
  --   -- toCore (Lam PFun y) `shouldBe` C.Lam "$1" (C.If (C.eq (C.Var "$1") C.Fun) y')
  --   toCore (Lam PIntT y) `shouldBe` C.Lam "$1" (C.If (C.eq (C.Var "$1") C.IntT) y')
  --   toCore (Lam PNumT y) `shouldBe` C.Lam "$1" (C.If (C.eq (C.Var "$1") C.NumT) y')
  --   toCore (Lam (PInt 0) y) `shouldBe` C.Lam "$1" (C.If (C.eq (C.Var "$1") (C.Int 0)) y')
  --   toCore (Lam (PVar "x") y) `shouldBe` C.Lam "x" y'
  --   toCore (Lam (PApp _x _y) z) `shouldBe` C.Lam "$1" (C.let' [("x", C.Fst (C.Var "$1")), ("y", C.Snd (C.Var "$1"))] z')

  -- it "☯ toCore syntax sugar" $ do
  --   toCore (Match []) `shouldBe` C.Err []
  --   -- toCore (Match [([_x], x)]) `shouldBe` C.Lam "x" x'
  --   -- toCore (Match [([_x, _y], x)]) `shouldBe` C.lam [_x', _y'] x'
  --   -- toCore (Match [([_x], x), ([_y], y)]) `shouldBe` C.Or (C.Lam _x' x') (C.Lam _y' y')
  --   True `shouldBe` True

  -- it "☯ fromCore" $ do
  --   True `shouldBe` True

  -- -- it "☯ eval" $ do
  -- --   let env = [("x", i1), ("f", Lam _x x)]
  -- --   eval env (App (Var "f") (Var "x")) `shouldBe` i1

  -- -- it "☯ infer" $ do
  -- --   let env = [("x", i1), ("f", Lam _x x)]
  -- --   eval env (App (Var "f") (Var "x")) `shouldBe` i1

  -- it "☯ overload" $ do
  --   -- let addOverloads =
  --   --       [ ([PInt "x", PInt "y"], Add x y),
  --   --         ([PInt "x", PNum "y"], Add (Int2Num x) y),
  --   --         ([PIfCtr "A", PIfCtr "B"], Ctr "C")
  --   --       ]

  --   -- let env = [("+", Match addOverloads)]
  --   -- let add a b = app (Var "+") [a, b]
  --   -- eval env (add (Int 1) (Int 2)) `shouldBe` Int 3
  --   -- eval' env (add (Int 1) (Num 2.2)) `shouldBe` C.Num 3.2
  --   -- eval env (add (Num 1.1) (Int 2)) `shouldBe` Err
  --   -- eval env (add (Ctr "A") (Ctr "B")) `shouldBe` Ctr "C"
  --   True `shouldBe` True

  it "☯ TODO" $ do
    True `shouldBe` True