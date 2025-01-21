module PatchTests where

import Patch
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ PatchTests ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)

  it "☯ plan" $ do
    let steps = [(["steps"], [(x, y)])]
    plan steps ["examples/patch:constant"] `shouldReturn` (steps ++ [(["constant"], [(i1, i2)])], [])
    plan steps ["examples/patch:imports"] `shouldReturn` (steps ++ [(["imports", "constant"], [(i1, i2)]), (["imports"], [(i2, i3)])], [])
    plan steps ["examples/patch:constant", "examples/patch:constant"] `shouldReturn` (steps ++ [(["constant"], [(i1, i2), (i1, i2)])], [])
    plan steps ["examples/patch:constant", "examples/patch:imports"] `shouldReturn` (steps ++ [(["constant"], [(i1, i2)]), (["imports", "constant"], [(i1, i2)]), (["imports"], [(i2, i3)])], [])

  it "☯ apply Expr" $ do
    let ctx = [("mod", [Def (x, i1)])]
    let apply' rule = apply (ctx, "mod", rule)
    apply' (x, y) x `shouldBe` y
    apply' (x, y) z `shouldBe` y
    apply' (x, y) i1 `shouldBe` y
    apply' (x, y) i2 `shouldBe` y
    apply' (For [] x, y) x `shouldBe` y
    apply' (For [] x, y) z `shouldBe` z
    apply' (For [] x, y) i1 `shouldBe` y
    apply' (For [] x, y) i2 `shouldBe` i2
    apply' (For ["x"] x, y) x `shouldBe` y
    apply' (For ["x"] x, y) z `shouldBe` y
    apply' (For ["x"] x, y) i1 `shouldBe` y
    apply' (For ["x"] x, y) i2 `shouldBe` y

  it "☯ apply Stmt" $ do
    let ctx = [("mod", [Def (x, i1)])]
    let apply' rule = apply (ctx, "mod", [rule])
    apply' (x, y) (Def (x, x)) `shouldBe` Def (x, y)
