module PatchTests where

import Error
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
    plan steps ["examples/patch:constant"] `shouldReturn` (steps ++ [(["constant"], [(i1, i2)])])
    plan steps ["examples/patch:imports"] `shouldReturn` (steps ++ [(["imports", "constant"], [(i1, i2)]), (["imports"], [(i2, i3)])])
    plan steps ["examples/patch:constant", "examples/patch:constant"] `shouldReturn` (steps ++ [(["constant"], [(i1, i2), (i1, i2)])])
    plan steps ["examples/patch:constant", "examples/patch:imports"] `shouldReturn` (steps ++ [(["constant"], [(i1, i2)]), (["imports", "constant"], [(i1, i2)]), (["imports"], [(i2, i3)])])

  it "☯ applyPatch Expr" $ do
    let ctx = [("mod", [def (x, i1)])]
    let apply' rule = dropTypes . applyPatch (ctx, "mod", rule)
    apply' (x, y) x `shouldBe` y
    apply' (x, y) z `shouldBe` Err (undefinedVar "z")
    apply' (x, y) i1 `shouldBe` y
    apply' (x, y) i2 `shouldBe` y
    apply' (x, y) x `shouldBe` y
    -- apply' (x, y) z `shouldBe` z
    apply' (x, y) i1 `shouldBe` y
  -- apply' (x, y) i2 `shouldBe` i2

  it "☯ applyPatch Stmt" $ do
    let ctx = [("mod", [def (x, i1)])]
    let apply' rule = applyPatch (ctx, "mod", [rule])
    -- apply' (x, y) (def (x, x)) `shouldBe` Def (x, Ann y Any)
    () `shouldBe` () -- TODO
