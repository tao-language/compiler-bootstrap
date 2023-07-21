module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec (SpecWith, describe, it, shouldBe)

taoTests :: SpecWith ()
taoTests = describe "--==☯ Tao ☯==--" $ do
  let a = Var "a"
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (VarP "x", VarP "y", VarP "z")

  it "☯ for" $ do
    for [] x `shouldBe` x
    for ["x"] y `shouldBe` For "x" y
    for ["x", "y"] z `shouldBe` For "x" (For "y" z)

  it "☯ fun" $ do
    fun [] x `shouldBe` x
    fun [x] y `shouldBe` Fun x y
    fun [x, y] z `shouldBe` Fun x (Fun y z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  -- it "☯ lam" $ do
  --   lam [] x `shouldBe` x
  --   lam [x'] y `shouldBe` Lam' x' y
  --   lam [x', y'] z `shouldBe` Lam' x' (Lam' y' z)

  it "☯ toCore" $ do
    toCore (Var "Type") `shouldBe` Right C.Knd
    toCore (Var "Int") `shouldBe` Right C.IntT
    toCore (Var "Num") `shouldBe` Right C.NumT
    toCore (Int 1) `shouldBe` Right (C.Int 1)
    toCore (Num 1) `shouldBe` Right (C.Num 1)
    toCore (Var "x") `shouldBe` Right (C.Var "x")
    toCore (For "x" y) `shouldBe` Right (C.For "x" (C.Var "y"))
    toCore (Fun x y) `shouldBe` Right (C.Fun (C.Var "x") (C.Var "y"))
    toCore (App x y) `shouldBe` Right (C.App (C.Var "x") (C.Var "y"))
    toCore (Ann x y) `shouldBe` Right (C.Ann (C.Var "x") (C.Var "y"))
    toCore (Let [Untyped "x" y] z) `shouldBe` Right (C.Let [("x", C.Var "y")] (C.Var "z"))
    -- toCore (Ctr "A" []) `shouldBe` Right (C.Ctr "A" [])
    -- toCore (Ctr "B" [x, y]) `shouldBe` Right (C.Ctr "B" [C.Var "x", C.Var "y"])
    -- toCore (Case x [("A", y)] z) `shouldBe` Right (C.Case (C.Var "x") [("A", C.Var "y")] (C.Var "z"))
    -- toCore (CaseI x [(1, y)] z) `shouldBe` Right (C.CaseI (C.Var "x") [(1, C.Var "y")] (C.Var "z"))
    -- toCore (Match []) `shouldBe` Left (TypeError C.EmptyCase)
    -- toCore (Match [Br [] (Int 1)]) `shouldBe` Right (C.Int 1)
    -- toCore (Match [Br [VarP "x"] (Int 1)]) `shouldBe` Right (C.Lam' "x" $ C.Int 1)
    -- toCore (Match [Br [VarP "x"] (Int 1), Br [] (Int 2)]) `shouldBe` Left (TypeError C.MatchNumPatternsMismatch)
    True `shouldBe` True
