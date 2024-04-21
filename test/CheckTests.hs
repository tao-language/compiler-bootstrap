{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module CheckTests where

import Check
import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Check ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let f = Var "f"

  it "☯ checkTypes" $ do
    let defs =
          [ Def f (Ann f (Fun IntType NumType)),
            Def x (Ann (Int 42) NumType),
            Def y (App f (Int 42)),
            Def z (App f (Tag "A" []))
          ]
    let mod = Module {name = "checkTypes", files = [File "f" defs]}
    checkTypes mod `shouldBe` [Error (C.TypeMismatch C.IntT C.NumT), Error (C.TypeMismatch (C.Tag "A") C.IntT)]

  it "☯ test" $ do
    let defs = []
    let mod = Module {name = "test", files = [File "f" defs]}
    True `shouldBe` True
