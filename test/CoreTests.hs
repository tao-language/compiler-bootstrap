module CoreTests where

import Core
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--== Core language ==--" $ do
  let add a = App (App (Call Add (for ["add"] (Var "add"))) a)
  let sub a = App (App (Call Sub (for ["sub"] (Var "sub"))) a)
  let mul a = App (App (Call Mul (for ["mul"] (Var "mul"))) a)
  let eq a = App (App (Call Eq (for ["eq"] (Var "eq"))) a)
  let (a, b) = (Var "a", Var "b")
  let (f, g) = (Var "f", Var "g")
  let (x, y, z) = (Var "x", Var "y", Var "z")

  it "☯ reduce" $ do
    let env = [("x", Int 1), ("y", y)]
    reduce env IntT `shouldBe` IntT
    reduce env (Typ 1) `shouldBe` Typ 1
    reduce env (Int 1) `shouldBe` Int 1
    reduce env (Var "x") `shouldBe` Int 1
    reduce env (Var "y") `shouldBe` y
    reduce env (Var "z") `shouldBe` z
    reduce env (Lam [] "y" x) `shouldBe` Lam env "y" x
    reduce env (Lam [("x", Int 2)] "y" x) `shouldBe` Lam (("x", Int 2) : env) "y" x
    reduce env (App (lam ["x"] x) x) `shouldBe` Int 1
    reduce env (App (lam ["x"] y) x) `shouldBe` y
    reduce env (App y x) `shouldBe` App y (Int 1)
    reduce env (Fun x y) `shouldBe` Fun (Int 1) y
    reduce env (Ann x (For "x" x)) `shouldBe` Int 1
    reduce env (Fix "f" x) `shouldBe` Fix "f" x

  it "☯ Built-in functions" $ do
    let env = [("x", Int 1), ("y", Int 2), ("z", z)]
    reduce env (add x x) `shouldBe` Int 2
    reduce env (sub x x) `shouldBe` Int 0
    reduce env (mul x x) `shouldBe` Int 1
    reduce env (eq x x) `shouldBe` lam ["T", "F"] (Var "T")
    reduce env (eq x y) `shouldBe` lam ["T", "F"] (Var "F")
    reduce env (add (add x x) (add x x)) `shouldBe` Int 4
    reduce env (add (add x x) z) `shouldBe` add (Int 2) z
    reduce env (add z (add x x)) `shouldBe` add z (Int 2)

  it "☯ eval" $ do
    let env = [("x", Int 1), ("y", y)]
    eval env (Lam [] "y" x) `shouldBe` Lam [] "y" (Int 1)
    eval env (Lam [("x", Int 2)] "y" x) `shouldBe` Lam [] "y" (Int 2)
    eval env (App y x) `shouldBe` App y (Int 1)
    eval env (Fix "x" x) `shouldBe` x
    eval env (Fix "y" x) `shouldBe` Int 1
    eval env (Fix "x" (Fun x x)) `shouldBe` Fix "x" (Fun x x)

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
    let a1 = Var "a1"
    instantiate [] IntT `shouldBe` (IntT, [])
    instantiate [] (For "a" a) `shouldBe` (a, [("a", a)])
    instantiate [("a", IntT)] (For "a" a) `shouldBe` (a1, [("a1", a1), ("a", IntT)])
    instantiate [] (for ["a", "b"] (Fun a b)) `shouldBe` (Fun a b, [("b", b), ("a", a)])

  it "☯ unify" $ do
    let env = [("x", Int 1), ("y", y)]
    unify env IntT IntT `shouldBe` Right env
    unify env (Typ 0) (Typ 0) `shouldBe` Right env
    unify env (Typ 0) (Typ 1) `shouldBe` Left (TypeMismatch (Typ 0) (Typ 1))
    unify env (Int 1) (Int 1) `shouldBe` Right env
    unify env (Int 1) (Int 2) `shouldBe` Left (TypeMismatch (Int 1) (Int 2))
    unify env (Var "y") (Var "y") `shouldBe` Right env
    unify env (Var "x") (Int 1) `shouldBe` Right env
    unify env (Var "x") (Int 2) `shouldBe` Left (TypeMismatch (Int 1) (Int 2))
    unify env (Var "z") (Int 1) `shouldBe` Right (("z", Int 1) : env)
    unify env (Int 1) (Var "x") `shouldBe` Right env
    unify env (Int 2) (Var "x") `shouldBe` Left (TypeMismatch (Int 2) (Int 1))
    unify env (Int 1) (Var "z") `shouldBe` Right (("z", Int 1) : env)
    unify env (App z x) (App y x) `shouldBe` Right (("z", y) : env)
    unify env (App y x) (App y z) `shouldBe` Right (("z", Int 1) : env)
    unify env (Fun z x) (Fun y x) `shouldBe` Right (("z", y) : env)
    unify env (Fun y x) (Fun y z) `shouldBe` Right (("z", Int 1) : env)

  it "☯ infer" $ do
    let a1 = Var "a1"
    let env =
          [ ("x", Int 1),
            ("y", y),
            ("f", Ann f (For "a" $ Fun IntT a)),
            -- ("g", Ann g (For "a" $ Fun a $ For "b" $ Fun b b))
            ("g", Ann g (For "a" $ Fun a a))
          ]
    infer env IntT `shouldBe` Right (Typ 0, env)
    infer env (Typ 1) `shouldBe` Right (Typ 2, env)
    infer env (Int 1) `shouldBe` Right (IntT, env)
    infer env (Var "x") `shouldBe` Right (IntT, env)
    infer env (Var "y") `shouldBe` Right (y, env)
    infer env (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer env (Var "f") `shouldBe` Right (Fun IntT a, ("a", a) : env)
    infer env (Lam [] "a" a) `shouldBe` Right (Fun a1 a1, ("a1", a1) : ("a", Ann a a1) : env)
    infer env (App x x) `shouldBe` Left (NotAFunction x IntT)
    infer env (App f (Typ 0)) `shouldBe` Left (TypeMismatch IntT (Typ 1))
    infer env (App f (Int 1)) `shouldBe` Right (a, ("a", a) : env)
    infer env (App (Lam [] "a" a) (Int 1)) `shouldBe` Right (IntT, ("a1", IntT) : ("a1", a1) : ("a", Ann a a1) : env)
    infer env (Fun (Int 1) (Typ 1)) `shouldBe` Right (Typ 0, env)
    infer env (Fun (Var "z") (Typ 0)) `shouldBe` Left (UndefinedVar "z")
    infer env (Fun (Typ 0) (Var "z")) `shouldBe` Left (UndefinedVar "z")
    infer env (Ann x IntT) `shouldBe` Right (IntT, env)
    infer env (Ann x (Int 0)) `shouldBe` Left (NotAType (Int 0) IntT)
    infer env (Ann x (Typ 0)) `shouldBe` Left (TypeMismatch (Typ 0) IntT)
    infer env (For "x" x) `shouldBe` Right (Typ 0, env)
    infer env (For "x" z) `shouldBe` Left (UndefinedVar "z")
    infer env (Fix "f" (Int 1)) `shouldBe` Right (IntT, ("f", Ann f (for ["a", "b"] (Fun a b))) : env)
    infer env (Call Add (For "a" a)) `shouldBe` Right (a, ("a", a) : env)

  it "☯ freeVariables" $ do
    freeVariables x `shouldBe` ["x"]
    freeVariables (Int 1) `shouldBe` []
    freeVariables (App x x) `shouldBe` ["x"]
    freeVariables (App x y) `shouldBe` ["x", "y"]
    freeVariables (Lam [] "x" x) `shouldBe` []
    freeVariables (Lam [] "x" y) `shouldBe` ["y"]
    freeVariables (Lam [("y", Int 1)] "x" y) `shouldBe` []
    freeVariables (Call Add (For "y" y)) `shouldBe` []

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
