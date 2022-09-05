module ReducerTests where

import Lambda
import Reducer
import Test.Hspec

reducerTests :: SpecWith ()
reducerTests = describe "--== ☯ Reducer ☯ ==--" $ do
  it "☯ Constant expression" $ do
    True `shouldBe` True

--   -- Normal form
--   evaluate Err `shouldBe` Err
--   evaluate (Var "x") `shouldBe` Var "x"
--   evaluate (Int 1) `shouldBe` Int 1
--   evaluate (App (Var "x") (Var "y")) `shouldBe` App (Var "x") (Var "y")
--   evaluate (Lam "x" (Var "y")) `shouldBe` Lam "x" (Var "y")
--   evaluate (Call "f") `shouldBe` Call "f"

-- it "☯ Error application" $ do
--   evaluate (App Err (Int 1)) `shouldBe` Err

-- it "☯ Lambda application" $ do
--   -- Beta / β-reduction
--   let (x, y, z) = (Var "x", Var "y", Var "z")
--   evaluate (App (Lam "x" y) z) `shouldBe` y
--   evaluate (App (Lam "x" x) z) `shouldBe` z
--   evaluate (App (Lam "x" (App x x)) z) `shouldBe` App z z
--   evaluate (App (Lam "x" (Lam "y" x)) z) `shouldBe` Lam "y" z

-- it "☯ Built-in functions" $ do
--   -- Delta / δ-reduction
--   let (i1, i2) = (int 1, int 2)
--   evaluate (add i1 i1 empty) `shouldBe` Int 2
--   evaluate (sub i1 i1 empty) `shouldBe` Int 0
--   evaluate (mul i1 i1 empty) `shouldBe` Int 1
--   evaluate (eq i1 i1 empty) `shouldBe` Lam "T" (Lam "F" (Var "T"))
--   evaluate (eq i1 i2 empty) `shouldBe` Lam "T" (Lam "F" (Var "F"))
--   evaluate (add (add i1 i1) (add i1 i1) empty) `shouldBe` Int 4
--   evaluate (add (add i1 i1) (var "y") empty) `shouldBe` add (int 2) (var "y") empty
--   evaluate (add (var "x") (add i1 i1) empty) `shouldBe` add (var "x") (int 2) empty
--   evaluate (add (var "x") (var "y") empty) `shouldBe` add (var "x") (var "y") empty

-- -- it "☯ Lambda evaluation" $ do
-- --   evaluate (Lam "x" (add (int 1) (int 1) empty)) `shouldBe` Lam "x" (Int 2)

-- it "☯ Fixed point recursion" $ do
--   evaluate (App Fix (Lam "f" (Var "x"))) `shouldBe` Var "x"
