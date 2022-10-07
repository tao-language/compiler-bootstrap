module CoreTests where

import Core
import qualified Lambda as L
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--== Core tests ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x_, y_, z_) = (PAs PAny "x", PAs PAny "y", PAs PAny "z")

  it "☯ unpack" $ do
    unpack (PAny, x) `shouldBe` []
    unpack (PAs PAny "x", y) `shouldBe` [("x", y)]

  it "☯ compile" $ do
    let ctx = defineType "T" [] [("A", 0), ("B", 1)] []
    compile ctx x `shouldBe` Just (L.Var "x")
    compile ctx (Int 1) `shouldBe` Just (L.Int 1)
    compile ctx (App x []) `shouldBe` Just (L.Var "x")
    compile ctx (App x [y]) `shouldBe` Just (L.App (L.Var "x") (L.Var "y"))
    compile ctx (App x [y, z]) `shouldBe` Just (L.app (L.Var "x") [L.Var "y", L.Var "z"])
  -- compile ctx (App x [Ann y z]) `shouldBe` Just (L.app (L.Var "x") [L.Var "y", L.Var "z"])
  -- compile ctx (Let [] x) `shouldBe` Just (L.Var "x")
  -- compile ctx (Let [("x", y)] x) `shouldBe` Just (L.let' [("x", L.Var "y")] (L.Var "x"))
  -- compile ctx (Cases [([x_], x)]) `shouldBe` Just (L.Lam "x" (L.Var "x"))
  -- TODO: compile types

  it "☯ compileCases" $ do
    let ctx = defineType "T" [] [("A", 0), ("B", 1)] []
    compileCases ctx [] `shouldBe` Nothing
  -- compileCases ctx [([], Int 1), ([], Int 2)] `shouldBe` Just (L.Int 1)
  -- compileCases ctx [([PAny], Int 1)] `shouldBe` Just (L.Lam "%1" (L.Int 1))
  -- compileCases ctx [([x_], Int 1)] `shouldBe` Just (L.Lam "x" (L.Int 1))
  -- compileCases ctx [([x_, y_], Int 1)] `shouldBe` Just (L.lam ["x", "y"] (L.Int 1))
  -- compileCases ctx [([PInt 0], Int 1)] `shouldBe` Nothing
  -- compileCases ctx [([PInt 0], Int 1), ([x_], Int 2)] `shouldBe` Just (L.Lam "x" (L.app (L.eq (L.Var "x") (L.Int 0)) [L.Int 1, L.Int 2]))
  -- compileCases ctx [([PCtr "Unknown" []], Int 1)] `shouldBe` Nothing
  -- compileCases ctx [([PCtr "A" []], Int 1)] `shouldBe` Nothing
  -- compileCases ctx [([PCtr "B" [x_]], Int 1)] `shouldBe` Nothing
  -- compileCases ctx [([PCtr "A" []], Int 1), ([PCtr "B" [x_]], Int 2)] `shouldBe` Just (L.Lam "%1" (L.app (L.Var "%1") [L.Int 1, L.Lam "x" (L.Int 2)]))
  -- compileCases ctx [([PCtr "A" [], x_], Int 1), ([PCtr "B" [y_], z_], Int 2)] `shouldBe` Just (L.Lam "%1" (L.app (L.Var "%1") [L.Lam "x" (L.Int 1), L.lam ["y", "z"] (L.Int 2)]))
  -- compileCases ctx [([PAnn x_ y_], Int 1)] `shouldBe` Just (L.lam ["x", "y"] (L.Int 1))
  -- compileCases ctx [([PAnn (PInt 0) x_], Int 1), ([y_], Int 2)] `shouldBe` Just (L.Lam "y" (L.app (L.eq (L.Var "y") (L.Int 0)) [L.Lam "x" (L.Int 1), L.Lam "%1" (L.Int 2)]))

  it "☯ inferName" $ do
    inferName "x" [] `shouldBe` "x"
    inferName "x" [x_] `shouldBe` "x"
    inferName "x" [y_] `shouldBe` ""
    inferName "" [x_] `shouldBe` "x"
    inferName "" [PAnn x_ PAny] `shouldBe` "x"
    inferName "" [PAny, x_] `shouldBe` "x"

  it "☯ findAlts" $ do
    let ctx = defineType "T" [] [("A", 0), ("B", 1)] []
    findAlts ctx [] `shouldBe` Nothing
    findAlts ctx [PAny] `shouldBe` Nothing
    findAlts ctx [PInt 0] `shouldBe` Nothing
    findAlts ctx [PCtr "Unknown" []] `shouldBe` Nothing
    findAlts ctx [PCtr "A" []] `shouldBe` Just [("A", 0), ("B", 1)]
    findAlts ctx [PCtr "B" [PAny]] `shouldBe` Just [("A", 0), ("B", 1)]
    findAlts ctx [PAs (PCtr "A" []) "x"] `shouldBe` Just [("A", 0), ("B", 1)]
    findAlts ctx [PAnn (PCtr "A" []) PAny] `shouldBe` Just [("A", 0), ("B", 1)]
    findAlts ctx [PAny, PCtr "A" []] `shouldBe` Just [("A", 0), ("B", 1)]

  it "☯ chompDefault" $ do
    chompDefault "x" ([PAny, y_], Int 0) `shouldBe` Just ([y_], Int 0)
    chompDefault "x" ([PInt 0, y_], Int 0) `shouldBe` Nothing
    chompDefault "x" ([PCtr "A" [], y_], Int 0) `shouldBe` Nothing
    chompDefault "x" ([x_, y_], Int 0) `shouldBe` Just ([y_], Int 0)
    chompDefault "x" ([y_, z_], Int 0) `shouldBe` Just ([z_], Let [("y", x)] (Int 0))
  -- chompDefault "x" ([PAnn (y_) PAny, z_], Int 0) `shouldBe` Just ([z_], Let [("y", x)] (Int 0))

  it "☯ chompCtr" $ do
    chompCtr "x" ("A", 0) ([PAny, y_], Int 0) `shouldBe` Just ([y_], Int 0)
    chompCtr "x" ("B", 1) ([PAny, y_], Int 0) `shouldBe` Just ([PAny, y_], Int 0)
    chompCtr "x" ("A", 0) ([PInt 0, y_], Int 0) `shouldBe` Nothing
    chompCtr "x" ("A", 0) ([PCtr "A" [], y_], Int 0) `shouldBe` Just ([y_], Int 0)
    chompCtr "x" ("B", 1) ([PCtr "A" [], y_], Int 0) `shouldBe` Nothing
    chompCtr "x" ("B", 1) ([PCtr "B" [y_], z_], Int 0) `shouldBe` Just ([y_, z_], Int 0)
    chompCtr "x" ("A", 0) ([x_, y_], Int 0) `shouldBe` Just ([y_], Int 0)
    chompCtr "x" ("A", 0) ([y_, z_], Int 0) `shouldBe` Just ([z_], Let [("y", x)] (Int 0))
  -- chompCtr "x" ("A", 0) ([PAnn (y_) PAny, z_], Int 0) `shouldBe` Just ([z_], Let [("y", x)] (Int 0))

  it "☯ bindings" $ do
    bindings PAny `shouldBe` []
    bindings x_ `shouldBe` ["x"]
    bindings (PInt 1) `shouldBe` []
    bindings (PCtr "A" []) `shouldBe` []
    bindings (PCtr "A" [x_, y_]) `shouldBe` ["x", "y"]
