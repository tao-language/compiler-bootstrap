module CoreTests where

import Core
import qualified Lambda as L
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--== Core tests ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let ctx = defineType "T" [] [("A", 0), ("B", 1)] empty

  it "☯ unpack" $ do
    unpack (PAny, x) `shouldBe` []
    unpack (PAs PAny "x", y) `shouldBe` [("x", y)]

  it "☯ compile" $ do
    compile ctx x `shouldBe` Just (L.Var "x")
    compile ctx (Int 1) `shouldBe` Just (L.Int 1)
    compile ctx (App x []) `shouldBe` Just (L.Var "x")
    compile ctx (App x [y]) `shouldBe` Just (L.App (L.Var "x") (L.Var "y"))
    compile ctx (App x [y, z]) `shouldBe` Just (L.app (L.Var "x") [L.Var "y", L.Var "z"])
    compile ctx (Let [] x) `shouldBe` Just (L.Var "x")
    compile ctx (Let [("x", y)] x) `shouldBe` Just (L.let' [("x", L.Var "y")] (L.Var "x"))
    compile ctx (Cases [([PAs PAny "x"], x)]) `shouldBe` Just (L.Lam "x" (L.Var "x"))

  it "☯ compileCases" $ do
    compileCases ctx "" [] `shouldBe` Nothing
    compileCases ctx "" [([], x), ([], y)] `shouldBe` Just (L.Var "x")
    compileCases ctx "" [([PAny], x)] `shouldBe` Just (L.Lam "%0" (L.Var "x"))
    compileCases ctx "x" [([PAny], x)] `shouldBe` Just (L.Lam "x" (L.Var "x"))
    compileCases ctx "" [([PAs PAny "x"], x)] `shouldBe` Just (L.Lam "x" (L.Var "x"))
    compileCases ctx "" [([PInt 1], x)] `shouldBe` Nothing
    compileCases ctx "" [([PInt 1], x), ([PAny], y)] `shouldBe` Just (L.Lam "%0" (L.app (L.eq (L.Var "%0") (L.Int 1)) [L.Var "x", L.App (L.Lam "%0" (L.Var "y")) (L.Var "%0")]))
    compileCases ctx "" [([PCtr "Unknown" []], x)] `shouldBe` Nothing
    compileCases ctx "" [([PCtr "A" []], x)] `shouldBe` Nothing
    compileCases ctx "" [([PCtr "B" [PAny]], x)] `shouldBe` Nothing
    compileCases ctx "" [([PCtr "A" []], x), ([PCtr "B" [PAny]], y)] `shouldBe` Just (L.Lam "%0" (L.app (L.Var "%0") [L.Var "x", L.Lam "%0" (L.Var "y")]))

  -- TODO: test inferName
  -- TODO: test findAlts
  -- TODO: test matchAny
  -- TODO: test matchCtr
  -- TODO: test remaining

  it "☯ bindings" $ do
    bindings PAny `shouldBe` []
    bindings (PAs PAny "x") `shouldBe` ["x"]
    bindings (PInt 1) `shouldBe` []
    bindings (PCtr "A" []) `shouldBe` []
    bindings (PCtr "A" [PAs PAny "x", PAs PAny "y"]) `shouldBe` ["x", "y"]
