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
run = describe "--==☯  ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")

  it "☯ toCore" $ do
    let env = []
    toCore env (Int 42) `shouldBe` C.Int 42
    toCore env (Num 3.14) `shouldBe` C.Num 3.14
    toCore env (Var "x") `shouldBe` C.Var "x"
    toCore env (Tag "Type" []) `shouldBe` C.Knd
    toCore env (Tag "Int" []) `shouldBe` C.IntT
    toCore env (Tag "Num" []) `shouldBe` C.NumT
    toCore env (Tag "A" []) `shouldBe` C.Tag "A"
    toCore env (Tag "A" [x, y]) `shouldBe` C.app (C.Tag "A") [C.Var "x", C.Var "y"]
    -- (Tuple []) `shouldBe` _
    -- (Tuple [x, y]) `shouldBe` _
    -- (Record []) `shouldBe` _
    -- (Record [("a", x), ("b", y)]) `shouldBe` _
    -- (Fun x y) `shouldBe` _
    -- (App x y) `shouldBe` _
    -- (Or x y) `shouldBe` _
    -- (Ann x y) `shouldBe` _
    -- (Op1 Int2Num x) `shouldBe` _
    -- (Op2 Add x y) `shouldBe` _
    -- (Let (x, y) z) `shouldBe` _
    -- (Meta (loc 1 2) x) `shouldBe` _
    -- (Err (ToDoError "TODO")) `shouldBe` _
    True `shouldBe` True

-- Kind `shouldBe` _
-- IntType `shouldBe` _
-- NumType `shouldBe` _
-- (Int 42) `shouldBe` _
-- (Num 3.14) `shouldBe` _
-- (Var "x") `shouldBe` _
-- (Tag "A" []) `shouldBe` _
-- (Tag "A" [x, y]) `shouldBe` _
-- (Tuple []) `shouldBe` _
-- (Tuple [x, y]) `shouldBe` _
-- (Record []) `shouldBe` _
-- (Record [("a", x), ("b", y)]) `shouldBe` _
-- (Fun x y) `shouldBe` _
-- (App x y) `shouldBe` _
-- (Or x y) `shouldBe` _
-- (Ann x y) `shouldBe` _
-- (Op1 Int2Num x) `shouldBe` _
-- (Op2 Add x y) `shouldBe` _
-- (Let (x, y) z) `shouldBe` _
-- (Meta (loc 1 2) x) `shouldBe` _
-- (Err (ToDoError "TODO")) `shouldBe` _