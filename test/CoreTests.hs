module CoreTests where

import Core
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--== Core language ==--" $ do
  it "☯ app" $ do
    app (var "x") [] empty `shouldBe` Var "x"
    app (var "x") [var "y"] empty `shouldBe` App (Var "x") (Var "y")
    app (var "x") [var "y", var "z"] empty `shouldBe` App (App (Var "x") (Var "y")) (Var "z")

  it "☯ lam" $ do
    lam [] (var "x") empty `shouldBe` Var "x"
    lam ["x"] (var "y") empty `shouldBe` Lam "x" (Var "y")
    lam ["x", "y"] (var "z") empty `shouldBe` Lam "x" (Lam "y" (Var "z"))

  it "☯ built-in operators" $ do
    add (var "x") (var "y") empty `shouldBe` App (App (Call "+") (Var "x")) (Var "y")
    sub (var "x") (var "y") empty `shouldBe` App (App (Call "-") (Var "x")) (Var "y")
    mul (var "x") (var "y") empty `shouldBe` App (App (Call "*") (Var "x")) (Var "y")
    eq (var "x") (var "y") empty `shouldBe` App (App (Call "==") (Var "x")) (Var "y")

  it "☯ if" $ do
    if' (var "x") (var "y") (var "z") empty `shouldBe` App (App (Var "x") (Var "y")) (Var "z")

  it "☯ let'" $ do
    let' [] err empty `shouldBe` Err
    let' [("x", int 1)] (var "y") empty `shouldBe` Var "y"
    let' [("x", int 1)] (var "x") empty `shouldBe` App (Lam "x" (Var "x")) (App Fix (Lam "x" (Int 1)))
    let' [("x", var "x")] (var "x") empty `shouldBe` App (Lam "x" (Var "x")) (App Fix (Lam "x" (Var "x")))
    let' [("x", var "y"), ("y", int 1)] (var "x") empty `shouldBe` let' [("x", let' [("y", int 1)] (var "y"))] (var "x") empty
    let' [("x", int 1), ("y", var "x")] (var "y") empty `shouldBe` let' [("y", let' [("x", int 1)] (var "x"))] (var "y") empty

  it "☯ inferName" $ do
    inferName "x" [] `shouldBe` "x"
    inferName "" [([bind "x"], int 1)] `shouldBe` "x"
    inferName "x" [([bind "x"], int 1)] `shouldBe` "x"
    inferName "x" [([bind "y"], int 1)] `shouldBe` ""

  it "☯ newName" $ do
    newName "x" [] `shouldBe` "x0"
    newName "x" ["x"] `shouldBe` "x1"
    newName "x" ["x", "x1"] `shouldBe` "x2"

  it "☯ match" $ do
    let ctx = defineType "T" [] [("A", 0), ("B", 1)] empty
    match "" [] ctx `shouldBe` Err
    match "" [([], int 1), ([], int 2)] ctx `shouldBe` Int 1
    match "" [([PAny], var "x")] ctx `shouldBe` Lam "%0" (Var "x")
    match "x" [([PAny], var "x")] ctx `shouldBe` Lam "x" (Var "x")
    match "" [([bind "x"], var "x")] ctx `shouldBe` Lam "x" (Var "x")
    match "" [([PInt 1], var "x")] ctx `shouldBe` lam ["%0"] (if' (eq (var "%0") (int 1)) (var "x") (app err [var "%0"])) empty
    match "" [([PInt 1], var "x"), ([PAny], var "y")] ctx `shouldBe` lam ["%0"] (if' (eq (var "%0") (int 1)) (var "x") (app (lam ["%0"] (var "y")) [var "%0"])) empty
    match "" [([PCtr "Unknown" []], var "x")] ctx `shouldBe` Lam "%0" Err
    match "" [([PCtr "A" []], var "x")] ctx `shouldBe` lam ["%0"] (app (var "%0") [var "x", err]) empty
    match "" [([PCtr "B" [PAny]], var "x")] ctx `shouldBe` lam ["%0"] (app (var "%0") [err, lam ["%0"] (var "x")]) empty

  it "☯ bindings" $ do
    bindings PAny `shouldBe` []
    bindings (PAs PAny "x") `shouldBe` ["x"]
    bindings (PInt 1) `shouldBe` []
    bindings (PCtr "A" []) `shouldBe` []
    bindings (PCtr "A" [PAs PAny "x", PAs PAny "y"]) `shouldBe` ["x", "y"]

  it "☯ bindVar" $ do
    let bindVar' binding x = let (x', a') = bindVar binding x in (x', a' empty)
    bindVar' (PAny, var "y") "x" `shouldBe` ("x", Var "y")
    bindVar' (bind "x", var "y") "x" `shouldBe` ("x", Var "y")
    bindVar' (bind "x", var "y") "z" `shouldBe` ("z", letVar ("x", var "y") (var "z") empty)

  it "☯ unpack" $ do
    let unpack' def = fmap (\(p, a) -> (p, a empty)) (unpack def)
    unpack' (PAny, int 1) `shouldBe` []
    unpack' (bind "x", int 1) `shouldBe` [("x", Int 1)]

  it "☯ nameIndex" $ do
    nameIndex "" "" `shouldBe` Nothing
    nameIndex "" "x" `shouldBe` Nothing
    nameIndex "" "42" `shouldBe` Just 42
    nameIndex "x" "x42" `shouldBe` Just 42
    nameIndex "x" "y42" `shouldBe` Nothing

  it "☯ lastNameIndex" $ do
    lastNameIndex "x" [] `shouldBe` Nothing
    lastNameIndex "x" ["x"] `shouldBe` Just 0
    lastNameIndex "x" ["x1"] `shouldBe` Just 1
    lastNameIndex "x" ["x", "x1"] `shouldBe` Just 1
    lastNameIndex "x" ["x1", "x"] `shouldBe` Just 1
    lastNameIndex "x" ["x1", "x2"] `shouldBe` Just 2
    lastNameIndex "x" ["x2", "x1"] `shouldBe` Just 2

  it "☯ freeVariables" $ do
    freeVariables (Var "x") `shouldBe` ["x"]
    freeVariables (Int 1) `shouldBe` []
    freeVariables (App (Var "x") (Var "x")) `shouldBe` ["x"]
    freeVariables (App (Var "x") (Var "y")) `shouldBe` ["x", "y"]
    freeVariables (Lam "x" (Var "x")) `shouldBe` []
    freeVariables (Lam "x" (Var "y")) `shouldBe` ["y"]
    freeVariables (Call "+") `shouldBe` []
