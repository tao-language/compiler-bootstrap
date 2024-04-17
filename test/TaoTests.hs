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
run = describe "--==☯ TaoTests ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")

  let sourceName = "TaoParserTests"
  let loc row col = C.Location sourceName (row, col)

  it "☯ toCore" $ do
    let env = []
    toCore env (Int 42) `shouldBe` C.Int 42
    toCore env (Num 3.14) `shouldBe` C.Num 3.14
    toCore env (Var "x") `shouldBe` C.Var "x"
    toCore env (Tag "Type" []) `shouldBe` C.Knd
    toCore env (Tag "Int" []) `shouldBe` C.IntT
    toCore env (Tag "Num" []) `shouldBe` C.NumT
    toCore env (Tag "A" []) `shouldBe` C.Tag "A"
    toCore env (Tag "A" [x, y]) `shouldBe` C.app (C.Tag "A") [x', y']
    toCore env (Tuple []) `shouldBe` C.Tag "()"
    toCore env (Tuple [x, y]) `shouldBe` C.app (C.Tag "()") [x', y']
    toCore env (Record []) `shouldBe` C.Rec []
    toCore env (Record [("a", x), ("b", y)]) `shouldBe` C.Rec [("a", x'), ("b", y')]
    toCore env (Trait (Int 1) "x") `shouldBe` C.app x' [C.IntT, C.Int 1]
    toCore env (Trait (Var "y") "x") `shouldBe` C.app x' [C.Err (C.UndefinedVar "y"), y']
    toCore env (Fun x y) `shouldBe` C.Fun x' y'
    toCore env (App x y) `shouldBe` C.App x' y'
    toCore env (Or x y) `shouldBe` C.Or x' y'
    toCore env (Ann x y) `shouldBe` C.Ann x' y'
    toCore env (Op1 C.Int2Num x) `shouldBe` C.Op1 C.Int2Num x'
    toCore env (Op2 C.Add x y) `shouldBe` C.Op2 C.Add x' y'
    -- toCore env (Let (x, y) z) `shouldBe` _
    toCore env (Meta (loc 1 2) x) `shouldBe` C.Meta (loc 1 2) x'
    toCore env (Err (C.TODO "err")) `shouldBe` C.Err (C.TODO "err")
