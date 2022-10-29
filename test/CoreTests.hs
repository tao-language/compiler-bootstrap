module CoreTests where

import Core
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--== Core language ==--" $ do
  let lam xs a = foldr (Lam []) a xs
  let add a = App (App (Call "+") a)
  let sub a = App (App (Call "-") a)
  let mul a = App (App (Call "*") a)
  let eq a = App (App (Call "==") a)
  let (a, b, f) = (Var "a", Var "b", Var "f")
  let (x, y, z) = (Var "x", Var "y", Var "z")

  it "☯ let'" $ do
    let' [] x `shouldBe` x
    let' [("x", y)] z `shouldBe` z
    let' [("x", y)] x `shouldBe` y
    let' [("x", x)] x `shouldBe` x
    let' [("x", Fun x x)] x `shouldBe` Fix "x" (Fun x x)
    let' [("x", y), ("y", z)] x `shouldBe` z
    let' [("x", z), ("y", x)] y `shouldBe` z

  it "☯ reduce" $ do
    let env = [("x", Int 1), ("y", y)]
    reduce IntT env `shouldBe` IntT
    reduce (Typ [("A", [])]) env `shouldBe` Typ [("A", [])]
    reduce (Int 1) env `shouldBe` Int 1
    reduce (Var "x") env `shouldBe` Int 1
    reduce (Var "y") env `shouldBe` y
    reduce (Var "z") env `shouldBe` z
    reduce (Lam [] "y" x) env `shouldBe` Lam env "y" x
    reduce (Lam [("x", Int 2)] "y" x) env `shouldBe` Lam (("x", Int 2) : env) "y" x
    reduce (App (lam ["x"] x) x) env `shouldBe` Int 1
    reduce (App (lam ["x"] y) x) env `shouldBe` y
    reduce (App y x) env `shouldBe` App y (Int 1)
    reduce (Fun x y) env `shouldBe` Fun (Int 1) y
    reduce (Ann x (T ["x"] x)) env `shouldBe` Int 1
    reduce (Fix "f" x) env `shouldBe` Fix "f" x

  it "☯ Built-in functions" $ do
    let env = [("x", Int 1), ("y", Int 2), ("z", z)]
    reduce (add x x) env `shouldBe` Int 2
    reduce (sub x x) env `shouldBe` Int 0
    reduce (mul x x) env `shouldBe` Int 1
    reduce (eq x x) env `shouldBe` lam ["T", "F"] (Var "T")
    reduce (eq x y) env `shouldBe` lam ["T", "F"] (Var "F")
    reduce (add (add x x) (add x x)) env `shouldBe` Int 4
    reduce (add (add x x) z) env `shouldBe` add (Int 2) z
    reduce (add z (add x x)) env `shouldBe` add z (Int 2)

  it "☯ eval" $ do
    let env = [("x", Int 1), ("y", y)]
    eval (Lam [] "y" x) env `shouldBe` Lam [] "y" (Int 1)
    eval (Lam [("x", Int 2)] "y" x) env `shouldBe` Lam [] "y" (Int 2)
    eval (App y x) env `shouldBe` App y (Int 1)
    eval (Fix "x" x) env `shouldBe` x
    eval (Fix "y" x) env `shouldBe` Int 1
    eval (Fix "x" (Fun x x)) env `shouldBe` Fix "x" (Fun x x)

  it "☯ occurs" $ do
    occurs "x" x `shouldBe` True
    occurs "x" y `shouldBe` False
    occurs "x" (Lam [] "x" x) `shouldBe` False
    occurs "x" (Lam [] "y" x) `shouldBe` True
    occurs "x" (Lam [("x", Int 1)] "y" x) `shouldBe` False
    occurs "x" (App x y) `shouldBe` True
    occurs "x" (App y x) `shouldBe` True
    occurs "x" (Fun x y) `shouldBe` True
    occurs "x" (Fun y x) `shouldBe` True

  it "☯ substitute" $ do
    substitute "x" y x `shouldBe` y
    substitute "x" y z `shouldBe` z
    substitute "x" y (Lam [] "x" x) `shouldBe` Lam [] "x" x
    substitute "x" y (Lam [] "z" x) `shouldBe` Lam [] "z" y
    substitute "x" y (Lam [("x", Int 1)] "z" x) `shouldBe` Lam [("x", Int 1)] "z" x
    substitute "x" y (App x x) `shouldBe` App y y
    substitute "x" y (Fun x x) `shouldBe` Fun y y

  it "☯ instantiate" $ do
    instantiate (T [] IntT) [] `shouldBe` (IntT, [])
    instantiate (T ["a"] a) [] `shouldBe` (a, [("a", a)])
    instantiate (T ["a"] a) [("a", Int 1)] `shouldBe` (Var "a1", [("a1", Var "a1"), ("a", Int 1)])
    instantiate (T ["a", "b"] (Fun a b)) [] `shouldBe` (Fun a b, [("b", b), ("a", a)])

  it "☯ unify" $ do
    let env = [("x", Int 1), ("y", y)]
    unify IntT IntT env `shouldBe` Just env
    unify (Typ []) (Typ []) env `shouldBe` Just env
    unify (Typ []) (Typ [("A", [])]) env `shouldBe` Nothing
    unify (Int 1) (Int 1) env `shouldBe` Just env
    unify (Int 1) (Int 2) env `shouldBe` Nothing
    unify (Var "y") (Var "y") env `shouldBe` Just env
    unify (Var "x") (Int 1) env `shouldBe` Just env
    unify (Var "x") (Int 2) env `shouldBe` Nothing
    unify (Var "z") (Int 1) env `shouldBe` Just (("z", Int 1) : env)
    unify (Int 1) (Var "x") env `shouldBe` Just env
    unify (Int 2) (Var "x") env `shouldBe` Nothing
    unify (Int 1) (Var "z") env `shouldBe` Just (("z", Int 1) : env)
    unify (App z x) (App y x) env `shouldBe` Just (("z", y) : env)
    unify (App y x) (App y z) env `shouldBe` Just (("z", Int 1) : env)
    unify (Fun z x) (Fun y x) env `shouldBe` Just (("z", y) : env)
    unify (Fun y x) (Fun y z) env `shouldBe` Just (("z", Int 1) : env)

  it "☯ infer" $ do
    let env = [("x", Int 1), ("y", y), ("f", Ann f (T ["a"] (Fun IntT a)))]
    infer IntT env `shouldBe` Just (Typ [], env)
    infer (Typ [("A", [])]) env `shouldBe` Just (Typ [], env)
    infer (Int 1) env `shouldBe` Just (IntT, env)
    infer (Var "x") env `shouldBe` Just (IntT, env)
    infer (Var "y") env `shouldBe` Just (y, env)
    infer (Var "z") env `shouldBe` Nothing
    infer (Var "f") env `shouldBe` Just (Fun IntT a, ("a", a) : env)
    infer (Lam [] "a" x) env `shouldBe` Just (Fun a IntT, ("a", a) : ("a", a) : env)
    infer (App x x) env `shouldBe` Nothing
    infer (App f (Typ [])) env `shouldBe` Nothing
    infer (App f (Int 1)) env `shouldBe` Just (a, ("a", a) : env)
    infer (App (Lam [] "a" a) (Int 1)) env `shouldBe` Just (IntT, ("a", IntT) : ("a", a) : ("a", a) : env)
    infer (Fun (Int 1) (Typ [("A", [])])) env `shouldBe` Just (Typ [], env)
    infer (Fun (Var "z") (Typ [])) env `shouldBe` Nothing
    infer (Fun (Typ []) (Var "z")) env `shouldBe` Nothing
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
