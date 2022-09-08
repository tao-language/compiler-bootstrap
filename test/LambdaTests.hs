module LambdaTests where

import Lambda
import Test.Hspec

lambdaTests :: SpecWith ()
lambdaTests = describe "--== Lambda calculus ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")

  it "☯ lam" $ do
    lam [] x `shouldBe` Var "x"
    lam ["x"] y `shouldBe` Lam "x" y
    lam ["x", "y"] z `shouldBe` Lam "x" (Lam "y" z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ built-in operators" $ do
    add x y `shouldBe` App (App (Call "+") x) y
    sub x y `shouldBe` App (App (Call "-") x) y
    mul x y `shouldBe` App (App (Call "*") x) y
    eq x y `shouldBe` App (App (Call "==") x) y

  it "☯ letVar" $ do
    letVar ("x", y) z `shouldBe` App (Lam "x" z) y

  it "☯ letRec" $ do
    letRec ("x", y) z `shouldBe` letVar ("x", App Fix (Lam "x" y)) z

  it "☯ let'" $ do
    let' [] x `shouldBe` x
    let' [("x", y)] z `shouldBe` z
    let' [("x", y)] x `shouldBe` letRec ("x", y) x
    let' [("x", y), ("y", z)] x `shouldBe` letRec ("x", letRec ("y", z) y) x

  it "☯ substitute" $ do
    substitute "x" y x `shouldBe` y
    substitute "x" y z `shouldBe` z
    substitute "x" y (Lam "x" x) `shouldBe` Lam "x" x
    substitute "x" y (Lam "z" x) `shouldBe` Lam "z" y
    substitute "x" y (App x x) `shouldBe` App y y
    substitute "x" y (Ann x x) `shouldBe` Ann y y
    substitute "x" y (Fun x x) `shouldBe` Fun y y

  it "☯ occurs" $ do
    occurs "x" x `shouldBe` True
    occurs "x" y `shouldBe` False
    occurs "x" (Lam "x" x) `shouldBe` False
    occurs "x" (Lam "y" x) `shouldBe` True
    occurs "x" (App x y) `shouldBe` True
    occurs "x" (App y x) `shouldBe` True
    occurs "x" (Ann x y) `shouldBe` True
    occurs "x" (Ann y x) `shouldBe` True
    occurs "x" (Fun x y) `shouldBe` True
    occurs "x" (Fun y x) `shouldBe` True

  it "☯ bind" $ do
    let bind' x a = fmap (\s -> s (Var x)) (bind x a)
    bind' "x" x `shouldBe` Just x
    bind' "x" y `shouldBe` Just y
    bind' "x" (App x y) `shouldBe` Nothing
    bind' "x" (App y x) `shouldBe` Nothing
    bind' "x" (App y y) `shouldBe` Just (App y y)

  it "☯ unify" $ do
    let unify' x a b = fmap (\s -> s (Var x)) (unify a b)
    unify' "x" (Int 0) (Int 1) `shouldBe` Nothing
    unify' "x" (Int 1) (Int 1) `shouldBe` Just x
    unify' "x" x IntT `shouldBe` Just IntT
    unify' "x" IntT x `shouldBe` Just IntT
    unify' "x" (App x x) (App IntT IntT) `shouldBe` Just IntT
    unify' "x" (Ann x x) (Ann IntT IntT) `shouldBe` Just IntT
    unify' "x" (Fun x x) (Fun IntT IntT) `shouldBe` Just IntT
    unify' "x" (For "x" x) (App y y) `shouldBe` Just (App y y)
    unify' "x1" (For "x" x) (App x x) `shouldBe` Just (App x x)
    unify' "x" (App y y) (For "x" x) `shouldBe` Just (App y y)
    unify' "x1" (App x x) (For "x" x) `shouldBe` Just (App x x)

  it "☯ unify2" $ do
    let unify2' a b = fmap (\s -> s x) (unify2 a b)
    unify2' (x, IntT) (x, IntT) `shouldBe` Just IntT
    unify2' (x, IntT) (IntT, x) `shouldBe` Just IntT
    unify2' (x, IntT) (x, Int 1) `shouldBe` Nothing
    unify2' (x, IntT) (Int 1, x) `shouldBe` Nothing

  it "☯ inferType" $ do
    let env = [("x", IntT)]
    let inferType' env a = fmap fst (inferType env a)
    inferType' env Typ `shouldBe` Just Typ
    inferType' env IntT `shouldBe` Just Typ
    inferType' env (Int 1) `shouldBe` Just IntT
    inferType' env x `shouldBe` Just IntT
    inferType' env y `shouldBe` Nothing
    inferType' env (Lam "x" x) `shouldBe` Just (For "x1" $ Fun (Var "x1") (Var "x1"))
    inferType' env (Lam "y" x) `shouldBe` Just (For "y" $ Fun y IntT)
    inferType' env (App (Lam "x" x) (Int 1)) `shouldBe` Just IntT
    inferType' env Fix `shouldBe` Just (For "a" (Fun (Var "a") (Var "a")))
    inferType' env (Call "f") `shouldBe` Just (for ["a", "b"] (Fun (Var "a") (Var "b")))
    inferType' env (Ann (Int 1) x) `shouldBe` Just IntT
    inferType' env (Ann (Int 1) Typ) `shouldBe` Nothing
    inferType' env (For "x" y) `shouldBe` Just Typ
    inferType' env (Fun x y) `shouldBe` Just Typ

  it "☯ freeVariables" $ do
    freeVariables x `shouldBe` ["x"]
    freeVariables (Int 1) `shouldBe` []
    freeVariables (App x x) `shouldBe` ["x"]
    freeVariables (App x y) `shouldBe` ["x", "y"]
    freeVariables (Lam "x" x) `shouldBe` []
    freeVariables (Lam "x" y) `shouldBe` ["y"]
    freeVariables (Call "+") `shouldBe` []

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

  it "☯ newName" $ do
    newName [] "x" `shouldBe` "x"
    newName ["x"] "x" `shouldBe` "x1"
    newName ["x", "x1"] "x" `shouldBe` "x2"
