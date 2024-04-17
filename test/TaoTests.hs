{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TaoTests where

import Core
import qualified Parser as P
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
  let (x, y, z) = (TaoVar "x", TaoVar "y", TaoVar "z")

  it "☯ exprToCore" $ do
    let env = []
    exprToCore env (TaoInt 42) `shouldBe` Int 42
    exprToCore env (TaoNum 3.14) `shouldBe` Num 3.14
    exprToCore env (TaoVar "x") `shouldBe` Var "x"
    exprToCore env (TaoTag "A" []) `shouldBe` Tag "A"
    exprToCore env (TaoTag "Type" []) `shouldBe` Knd
    exprToCore env (TaoTag "Int" []) `shouldBe` IntT
    exprToCore env (TaoTag "Num" []) `shouldBe` NumT
    -- (TaoTag "A" []) `shouldBe` _
    -- (TaoTag "A" [x, y]) `shouldBe` _
    -- (TaoTuple []) `shouldBe` _
    -- (TaoTuple [x, y]) `shouldBe` _
    -- (TaoRecord []) `shouldBe` _
    -- (TaoRecord [("a", x), ("b", y)]) `shouldBe` _
    -- (TaoFun x y) `shouldBe` _
    -- (TaoApp x y) `shouldBe` _
    -- (TaoOr x y) `shouldBe` _
    -- (TaoAnn x y) `shouldBe` _
    -- (TaoOp1 Int2Num x) `shouldBe` _
    -- (TaoOp2 Add x y) `shouldBe` _
    -- (TaoLet (x, y) z) `shouldBe` _
    -- (TaoMeta (loc 1 2) x) `shouldBe` _
    -- (TaoErr (ToDoError "TODO")) `shouldBe` _
    True `shouldBe` True

-- TaoKind `shouldBe` _
-- TaoIntType `shouldBe` _
-- TaoNumType `shouldBe` _
-- (TaoInt 42) `shouldBe` _
-- (TaoNum 3.14) `shouldBe` _
-- (TaoVar "x") `shouldBe` _
-- (TaoTag "A" []) `shouldBe` _
-- (TaoTag "A" [x, y]) `shouldBe` _
-- (TaoTuple []) `shouldBe` _
-- (TaoTuple [x, y]) `shouldBe` _
-- (TaoRecord []) `shouldBe` _
-- (TaoRecord [("a", x), ("b", y)]) `shouldBe` _
-- (TaoFun x y) `shouldBe` _
-- (TaoApp x y) `shouldBe` _
-- (TaoOr x y) `shouldBe` _
-- (TaoAnn x y) `shouldBe` _
-- (TaoOp1 Int2Num x) `shouldBe` _
-- (TaoOp2 Add x y) `shouldBe` _
-- (TaoLet (x, y) z) `shouldBe` _
-- (TaoMeta (loc 1 2) x) `shouldBe` _
-- (TaoErr (ToDoError "TODO")) `shouldBe` _