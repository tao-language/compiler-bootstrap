module LambdaTests where

import Lambda
import Test.Hspec

lambdaTests :: SpecWith ()
lambdaTests = describe "--== Lambda calculus ==--" $ do
  let (a, b) = (Var "a", Var "b")
  let (f, g) = (Var "f", Var "g")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let env =
        [ ("f", Ann f (T [] (Fun IntT (Typ 42)))),
          ("g", Ann g (T ["a", "b"] (Fun a b))),
          ("x", Int 1),
          ("y", y)
        ]

  it "☯ lam" $ do
    lam [] x `shouldBe` Var "x"
    lam ["x"] y `shouldBe` Lam [] "x" y
    lam ["x", "y"] z `shouldBe` Lam [] "x" (Lam [] "y" z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ built-in operators" $ do
    add x y `shouldBe` App (App (Call "+") x) y
    sub x y `shouldBe` App (App (Call "-") x) y
    mul x y `shouldBe` App (App (Call "*") x) y
    eq x y `shouldBe` App (App (Call "==") x) y

  it "☯ let'" $ do
    let' [] x `shouldBe` x
    let' [("x", y)] z `shouldBe` z
    let' [("x", y)] x `shouldBe` y
    let' [("x", x)] x `shouldBe` Fix "x" x
    let' [("x", y), ("y", z)] x `shouldBe` z
    let' [("x", z), ("y", x)] y `shouldBe` z

  it "☯ reduce" $ do
    reduce IntT env `shouldBe` IntT
    reduce (Typ 0) env `shouldBe` Typ 0
    reduce (Int 1) env `shouldBe` Int 1
    reduce (Var "x") env `shouldBe` Int 1
    reduce (Var "y") env `shouldBe` y
    reduce (Var "z") env `shouldBe` z
    reduce (Lam [] "y" x) env `shouldBe` Lam env "y" x
    reduce (Lam [("x", Int 2)] "y" x) env `shouldBe` Lam (("x", Int 2) : env) "y" x
    reduce (App (lam ["x"] x) x) env `shouldBe` Int 1
    reduce (App (lam ["x"] y) x) env `shouldBe` y
    -- reduce (App Fix (Lam [] "f" x)) env `shouldBe` Fix
    reduce (App y x) env `shouldBe` App y (Int 1)
    -- reduce (App f x) env `shouldBe` Ann (App f (Int 1)) (T [] (Typ 42))
    reduce (Fun x y) env `shouldBe` Fun (Int 1) y
    reduce (Ann x (T [] IntT)) env `shouldBe` Int 1
    reduce (Ann y (T [] IntT)) env `shouldBe` Ann y (T [] IntT)

  it "☯ Built-in functions" $ do
    let (i1, i2) = (Int 1, Int 2)
    reduce (add i1 i1) env `shouldBe` Int 2
    reduce (sub i1 i1) env `shouldBe` Int 0
    reduce (mul i1 i1) env `shouldBe` Int 1
    reduce (eq i1 i1) env `shouldBe` lam ["T", "F"] (Var "T")
    reduce (eq i1 i2) env `shouldBe` lam ["T", "F"] (Var "F")
    reduce (add (add i1 i1) (add i1 i1)) env `shouldBe` Int 4
    reduce (add (add i1 i1) (Var "y")) env `shouldBe` add (Int 2) y
    reduce (add y (add i1 i1)) env `shouldBe` add y (Int 2)
    reduce (add x y) env `shouldBe` add (Int 1) y

  it "☯ eval" $ do
    eval (Lam [] "y" x) env `shouldBe` Lam [] "y" (Int 1)
    eval (Lam [("x", Int 2)] "y" x) env `shouldBe` Lam [] "y" (Int 2)
    eval (App y x) env `shouldBe` App y (Int 1)
    eval (Fix "y" x) env `shouldBe` Int 1
    eval (Fix "x" x) env `shouldBe` Fix "x" x

  it "☯ occurs" $ do
    occurs "x" x `shouldBe` True
    occurs "x" y `shouldBe` False
    occurs "x" (Lam [] "x" x) `shouldBe` False
    occurs "x" (Lam [] "y" x) `shouldBe` True
    occurs "x" (Lam [("x", Int 1)] "y" x) `shouldBe` False
    occurs "x" (App x y) `shouldBe` True
    occurs "x" (App y x) `shouldBe` True
    -- occurs "x" (Ann x y) `shouldBe` True
    -- occurs "x" (Ann y x) `shouldBe` True
    occurs "x" (Fun x y) `shouldBe` True
    occurs "x" (Fun y x) `shouldBe` True

  it "☯ substitute" $ do
    substitute "x" y x `shouldBe` y
    substitute "x" y z `shouldBe` z
    substitute "x" y (Lam [] "x" x) `shouldBe` Lam [] "x" x
    substitute "x" y (Lam [] "z" x) `shouldBe` Lam [] "z" y
    substitute "x" y (Lam [("x", Int 1)] "z" x) `shouldBe` Lam [("x", Int 1)] "z" x
    substitute "x" y (App x x) `shouldBe` App y y
    -- substitute "x" y (Ann x x) `shouldBe` Ann y y
    substitute "x" y (Fun x x) `shouldBe` Fun y y

  it "☯ unify" $ do
    unify IntT IntT env `shouldBe` Just env
    unify (Typ 0) (Typ 0) env `shouldBe` Just env
    unify (Typ 0) (Typ 1) env `shouldBe` Nothing
    unify (Int 1) (Int 1) env `shouldBe` Just env
    unify (Int 1) (Int 2) env `shouldBe` Nothing
    unify (Var "x") (Int 1) env `shouldBe` Just env
    unify (Var "x") (Int 2) env `shouldBe` Nothing
    unify (Var "z") (Int 1) env `shouldBe` Just (("z", Int 1) : env)
    unify (Int 1) (Var "x") env `shouldBe` Just env
    unify (Int 2) (Var "x") env `shouldBe` Nothing
    unify (Int 1) (Var "z") env `shouldBe` Just (("z", Int 1) : env)
    unify (App (Var "z") x) (App y x) env `shouldBe` Just (("z", y) : env)
    unify (App y x) (App y (Var "z")) env `shouldBe` Just (("z", Int 1) : env)
    unify (Fun (Var "z") x) (Fun y x) env `shouldBe` Just (("z", y) : env)
    unify (Fun y x) (Fun y (Var "z")) env `shouldBe` Just (("z", Int 1) : env)

  it "☯ infer" $ do
    infer IntT env `shouldBe` Just (Typ 0, env)
    infer (Typ 0) env `shouldBe` Just (Typ 1, env)
    infer (Int 1) env `shouldBe` Just (IntT, env)
    infer (Var "x") env `shouldBe` Just (IntT, env)
    infer (Var "y") env `shouldBe` Just (y, env)
    infer (Var "z") env `shouldBe` Nothing
    infer (Var "f") env `shouldBe` Just (Fun IntT (Typ 42), env)
    infer (Var "g") env `shouldBe` Just (Fun a b, ("b", b) : ("a", a) : env)
    infer (Lam [] "a" x) env `shouldBe` Just (Fun a IntT, ("a", a) : ("a", a) : env)
    infer (Lam [] "x" x) env `shouldBe` Just (Fun (Var "x1") (Var "x1"), ("x", Var "x1") : ("x1", Var "x1") : env)
    infer (App x x) env `shouldBe` Nothing
    infer (App f (Typ 0)) env `shouldBe` Nothing
    infer (App f (Int 1)) env `shouldBe` Just (Typ 42, env)
    infer (App g (Int 1)) env `shouldBe` Just (b, ("a", IntT) : ("b", b) : ("a", a) : env)
    infer (App (Lam [] "a" a) (Int 1)) env `shouldBe` Just (IntT, ("a", IntT) : ("a", a) : ("a", a) : env)
    infer (Fun (Int 1) (Typ 42)) env `shouldBe` Just (Typ 0, env)
    infer (Fun (Var "z") (Typ 42)) env `shouldBe` Nothing
    infer (Fun (Typ 42) (Var "z")) env `shouldBe` Nothing
    infer (Ann (Var "z") (T [] IntT)) env `shouldBe` Nothing
    infer (Ann x (T [] IntT)) env `shouldBe` Just (IntT, env)
    infer (Ann x (T [] (Typ 0))) env `shouldBe` Nothing
    infer (Ann (Lam [] "a" a) (T [] (Fun IntT IntT))) env `shouldBe` Just (Fun IntT IntT, ("a", IntT) : ("a", a) : ("a", a) : env)
    infer (Call "a") env `shouldBe` Just (a, ("a", a) : env)
    infer (Call "x") env `shouldBe` Just (Var "x1", ("x1", Var "x1") : env)
    infer (Fix "f" (Int 1)) env `shouldBe` Just (IntT, env)

  it "☯ freeVariables" $ do
    freeVariables x `shouldBe` ["x"]
    freeVariables (Int 1) `shouldBe` []
    freeVariables (App x x) `shouldBe` ["x"]
    freeVariables (App x y) `shouldBe` ["x", "y"]
    freeVariables (Lam [] "x" x) `shouldBe` []
    freeVariables (Lam [] "x" y) `shouldBe` ["y"]
    freeVariables (Lam [("y", Int 1)] "x" y) `shouldBe` []
    freeVariables (Call "+") `shouldBe` []

  it "☯ readNameIdx" $ do
    readNameIdx "" "" `shouldBe` Nothing
    readNameIdx "" "x" `shouldBe` Nothing
    readNameIdx "" "42" `shouldBe` Just 42
    readNameIdx "x" "x42" `shouldBe` Just 42
    readNameIdx "x" "y42" `shouldBe` Nothing

  it "☯ findNameIdx" $ do
    findNameIdx [] "x" `shouldBe` Nothing
    findNameIdx ["x"] "x" `shouldBe` Just 0
    findNameIdx ["x1"] "x" `shouldBe` Just 1
    findNameIdx ["x", "x1"] "x" `shouldBe` Just 1
    findNameIdx ["x1", "x"] "x" `shouldBe` Just 1
    findNameIdx ["x1", "x2"] "x" `shouldBe` Just 2
    findNameIdx ["x2", "x1"] "x" `shouldBe` Just 2

  it "☯ newName" $ do
    newName [] "x" `shouldBe` "x"
    newName ["x"] "x" `shouldBe` "x1"
    newName ["x", "x1"] "x" `shouldBe` "x2"
