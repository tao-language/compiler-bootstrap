{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PVar "x", PVar "y", PVar "z")
  let (i0, i1, i2) = (Int 0, Int 1, Int 2)

  -- it "☯ toCoreP" $ do
  --   True `shouldBe` True

  it "☯ toCore" $ do
    let env = []
    toCore env Knd `shouldBe` C.Knd
    toCore env IntT `shouldBe` C.IntT
    toCore env NumT `shouldBe` C.NumT
    toCore env (Int 42) `shouldBe` C.Int 42
    toCore env (Num 3.14) `shouldBe` C.Num 3.14
    toCore env (Tag "A") `shouldBe` C.Tag "A"
    toCore env (Var "x") `shouldBe` C.Var "x"

  -- it "☯ stmtToCore" $ do
  --   -- stmtToCore [] (newLetDef {name = "x"}) `shouldBe` []
  --   True `shouldBe` True

  -- it "☯ moduleToCore" $ do
  --   True `shouldBe` True

  it "☯ eval" $ do
    let eval' stmts = eval (newModule {stmts = stmts})
    eval' [] x `shouldBe` x
    eval' [letDef "x" y] x `shouldBe` y
    eval' [letDef "x" y, letDef "y" z] x `shouldBe` z
    eval' [letDef "x" z, letDef "y" x] y `shouldBe` z
    eval' [letTrait PIntT "x" y] (Trait i0 "x") `shouldBe` App y i0
    eval' [letTrait PNumT "x" y] (Trait i0 "x") `shouldBe` Err (C.PatternMatchError C.PNumT C.IntT)
    eval' [unbox x' i0] y `shouldBe` app (Var "*=") [IntT, i0, Lam x' y]
    eval' [unbox x' i0, letTrait PIntT "*=" y] z `shouldBe` app y [i0, Lam x' z]
    eval' [letTrait PIntT "*=" y, unbox x' i0] z `shouldBe` app y [i0, Lam x' z]
    eval' [letTrait PNumT "*=" y, unbox x' i0] z `shouldBe` Err (C.PatternMatchError C.PNumT C.IntT)
