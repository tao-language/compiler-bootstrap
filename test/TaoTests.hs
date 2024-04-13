{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TaoTests where

import Core (Error (..))
import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  -- let (x', y', z') = (PVar "x", PVar "y", PVar "z")
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
    toCore env (Tuple []) `shouldBe` C.Tag "()"
    toCore env (Tuple [x, y]) `shouldBe` C.app (C.Tag "()") [C.Var "x", C.Var "y"]
    toCore env (Record []) `shouldBe` C.Tag "()"
    toCore env (Record [("a", x), ("b", y)]) `shouldBe` C.app (C.Tag "()") [C.Var "x", C.Var "y"]
    toCore env (Trait (Int 1) "a") `shouldBe` C.app (C.Var "a") [C.IntT, C.Int 1]
    toCore env (Trait (Num 1.1) "a") `shouldBe` C.app (C.Var "a") [C.NumT, C.Num 1.1]
    toCore env (Trait x "a") `shouldBe` C.app (C.Var "a") [C.Err $ C.UndefinedVar "x", C.Var "x"]
    toCore env (Fun x y) `shouldBe` C.Fun (C.Var "x") (C.Var "y")
    toCore env (App x y) `shouldBe` C.App (C.Var "x") (C.Var "y")
    toCore env (Or x y) `shouldBe` C.Or (C.Var "x") (C.Var "y")
    toCore env (Ann x (For [] y)) `shouldBe` C.Ann (C.Var "x") (C.Var "y")
    toCore env (Ann x (For ["a"] y)) `shouldBe` C.Ann (C.Var "x") (C.For "a" (C.Var "y"))
    toCore env (Op1 C.Int2Num x) `shouldBe` C.Op1 C.Int2Num (C.Var "x")
    toCore env (Op2 C.Add x y) `shouldBe` C.Op2 C.Add (C.Var "x") (C.Var "y")
    toCore env (Typ "T" ["A", "B"]) `shouldBe` C.Typ "T" ["A", "B"]
    toCore env (Let ([], x, y) z) `shouldBe` C.let' (C.Var "x", C.Var "y") (C.Var "z")
    toCore env (Let ([("x", For [] IntT)], x, y) z) `shouldBe` C.let' (C.Ann (C.Var "x") C.IntT, C.Var "y") (C.Var "z")
    toCore env (Let ([], Ann x (For [] IntT), y) z) `shouldBe` C.let' (C.Ann (C.Var "x") C.IntT, C.Var "y") (C.Var "z")
    toCore env (Meta (C.Location "src" (1, 2)) x) `shouldBe` C.Meta (C.Location "src" (1, 2)) (C.Var "x")
    toCore env (Err C.NotImplementedError) `shouldBe` C.Err C.NotImplementedError

  it "☯ fromCore" $ do
    fromCore C.Knd `shouldBe` Knd
    fromCore C.IntT `shouldBe` IntT
    fromCore C.NumT `shouldBe` NumT
    fromCore (C.Int 42) `shouldBe` Int 42
    fromCore (C.Num 3.14) `shouldBe` Num 3.14
    fromCore (C.Tag "A") `shouldBe` Tag "A"
    fromCore (C.Var "x") `shouldBe` Var "x"
    fromCore (C.For "a" (C.Var "x")) `shouldBe` Var "x"
    fromCore (C.Fix "x" (C.Var "x")) `shouldBe` Var "x"
    fromCore (C.Fun (C.Var "x") (C.Var "y")) `shouldBe` Fun x y
    fromCore (C.App (C.Var "x") (C.Var "y")) `shouldBe` App x y
    fromCore (C.Or (C.Var "x") (C.Var "y")) `shouldBe` Or x y
    fromCore (C.Ann (C.Var "x") (C.Var "y")) `shouldBe` Ann x (For [] y)
    fromCore (C.Ann (C.Var "x") (C.For "a" $ C.Var "y")) `shouldBe` Ann x (For ["a"] y)
    fromCore (C.Op1 C.Int2Num (C.Var "x")) `shouldBe` Op1 C.Int2Num x
    fromCore (C.Op2 C.Add (C.Var "x") (C.Var "y")) `shouldBe` Op2 C.Add x y
    fromCore (C.Typ "T" ["A", "B"]) `shouldBe` Typ "T" ["A", "B"]
    -- Let
    -- Let typed
    -- Let recursive
    fromCore (C.Meta (C.Location "src" (1, 2)) (C.Var "x")) `shouldBe` Meta (C.Location "src" (1, 2)) x
    fromCore (C.Err NotImplementedError) `shouldBe` Err NotImplementedError

  it "☯ checkTypes" $ do
    True `shouldBe` True

  it "☯ eval" $ do
    -- let eval' stmts = eval (newModule {stmts = stmts})
    -- eval' [] x `shouldBe` x
    -- eval' [letDef "x" y] x `shouldBe` y
    -- eval' [letDef "x" y, letDef "y" z] x `shouldBe` z
    -- eval' [letDef "x" z, letDef "y" x] y `shouldBe` z
    -- eval' [letTrait PIntT "x" y] (Trait i0 "x") `shouldBe` App y i0
    -- eval' [letTrait PNumT "x" y] (Trait i0 "x") `shouldBe` Err (C.PatternMatchError C.PNumT C.IntT)
    -- eval' [unbox x' i0] y `shouldBe` app (Var "*=") [IntT, i0, Lam x' y]
    -- eval' [unbox x' i0, letTrait PIntT "*=" y] z `shouldBe` app y [i0, Lam x' z]
    -- eval' [letTrait PIntT "*=" y, unbox x' i0] z `shouldBe` app y [i0, Lam x' z]
    -- eval' [letTrait PNumT "*=" y, unbox x' i0] z `shouldBe` Err (C.PatternMatchError C.PNumT C.IntT)
    True `shouldBe` True
