module CoreTests where

import Core
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--== Core language ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")

  it "☯ occurs" $ do
    occurs "x" x `shouldBe` True
    occurs "x" y `shouldBe` False
    occurs "x" (FunT x y) `shouldBe` True
    occurs "x" (FunT y x) `shouldBe` True
    occurs "x" (Lam [] "x" x) `shouldBe` False
    occurs "x" (Lam [] "y" x) `shouldBe` True
    occurs "x" (Lam [("x", Int 1)] "y" x) `shouldBe` False
    occurs "x" (App x y) `shouldBe` True
    occurs "x" (App y x) `shouldBe` True

  it "☯ reduce" $ do
    let env = [("x", Int 1), ("y", y)]
    reduce env TypT `shouldBe` TypT
    reduce env IntT `shouldBe` IntT
    reduce env (Int 1) `shouldBe` Int 1
    reduce env (Var "x") `shouldBe` Int 1
    reduce env (Var "y") `shouldBe` y
    reduce env (Var "z") `shouldBe` z
    -- reduce env (FunT x y) `shouldBe` FunT (Int 1) y
    reduce env (Lam [] "y" x) `shouldBe` Lam env "y" x
    reduce env (Lam [("x", Int 2)] "y" x) `shouldBe` Lam (("x", Int 2) : env) "y" x
    reduce env (App (lam ["x"] x) x) `shouldBe` Int 1
    reduce env (App (lam ["x"] y) x) `shouldBe` y
    reduce env (App y x) `shouldBe` App y (Int 1)
    reduce env (Fix "f" x) `shouldBe` Fix "f" x

  it "☯ Built-in functions" $ do
    let env = [("x", Int 1), ("y", Int 2), ("z", z)]
    reduce env (add x x) `shouldBe` Int 2
    reduce env (sub x x) `shouldBe` Int 0
    reduce env (mul x x) `shouldBe` Int 1
    reduce env (eq x x) `shouldBe` lam ["True", "False"] (Var "True")
    reduce env (eq x y) `shouldBe` lam ["True", "False"] (Var "False")
    reduce env (add (add x x) (add x x)) `shouldBe` Int 4
    reduce env (add (add x x) z) `shouldBe` add (Int 2) z
    reduce env (add z (add x x)) `shouldBe` add z (Int 2)

-- it "☯ eval" $ do
--   let env = [("x", Int 1), ("y", y)]
--   eval env (Lam [] "y" x) `shouldBe` Lam [] "y" (Int 1)
--   eval env (Lam [("x", Int 2)] "y" x) `shouldBe` Lam [] "y" (Int 2)
--   eval env (App y x) `shouldBe` App y (Int 1)
--   eval env (Fix "x" x) `shouldBe` x
--   eval env (Fix "y" x) `shouldBe` Int 1
--   eval env (Fix "x" (FunT x x)) `shouldBe` Fix "x" (FunT x x)
