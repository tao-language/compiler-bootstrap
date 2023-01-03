module Core2Tests where

import Core2
import Flow ((|>))
import Test.Hspec

core2Tests :: SpecWith ()
core2Tests = describe "--== Core language ==--" $ do
  let (f, g) = (Var "f", Var "g")
  let (x, y, z) = (Var "x", Var "y", Var "z")

  it "☯ lam" $ do
    lam [] x `shouldBe` x
    lam ["x"] y `shouldBe` Lam [] "x" y
    lam ["x", "y"] z `shouldBe` Lam [] "x" (Lam [] "y" z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ funT" $ do
    funT [] x `shouldBe` x
    funT [x] y `shouldBe` FunT x y
    funT [x, y] z `shouldBe` FunT x (FunT y z)

  it "☯ occurs" $ do
    occurs "x" Err `shouldBe` False
    occurs "x" (Int 1) `shouldBe` False
    occurs "x" (Num 1.1) `shouldBe` False
    occurs "x" (Var "x") `shouldBe` True
    occurs "x" (Var "y") `shouldBe` False
    occurs "x" (Lam [] "x" x) `shouldBe` False
    occurs "x" (Lam [] "y" x) `shouldBe` True
    occurs "x" (App x y) `shouldBe` True
    occurs "x" (App y x) `shouldBe` True
    occurs "x" (App y y) `shouldBe` False
    occurs "x" TypT `shouldBe` False
    occurs "x" IntT `shouldBe` False
    occurs "x" NumT `shouldBe` False
    occurs "x" (ForT "x" x) `shouldBe` False
    occurs "x" (ForT "y" x) `shouldBe` True
    occurs "x" (FunT x y) `shouldBe` True
    occurs "x" (FunT y x) `shouldBe` True
    occurs "x" (FunT y y) `shouldBe` False
    occurs "x" (Op Add) `shouldBe` False

  -- it "☯ newName" $ do
  -- it "☯ substitute" $ do
  -- it "☯ instantiate" $ do
  -- it "☯ set" $ do

  -- it "☯ unify" $ do
  --   let env = [("x", Var "x"), ("y", Var "y")]
  --   unify env IntT IntT `shouldBe` Right (IntT, env)
  --   unify env IntT TypT `shouldBe` Left (TypeMismatch IntT TypT)
  --   unify env x x `shouldBe` Right (x, env)
  --   unify env x IntT `shouldBe` Right (IntT, set ("x", IntT) env)
  --   unify env x (FunT x x) `shouldBe` Left (InfiniteType "x" (FunT x x))
  --   unify env IntT x `shouldBe` Right (IntT, set ("x", IntT) env)
  --   unify env (FunT x x) x `shouldBe` Left (InfiniteType "x" (FunT x x))
  --   unify env (ForT "x" x) IntT `shouldBe` Right (IntT, env)
  --   unify env IntT (ForT "x" x) `shouldBe` Right (IntT, env)
  --   unify env (FunT x TypT) (FunT IntT y) `shouldBe` Right (FunT IntT TypT, set ("x", IntT) $ set ("y", TypT) env)
  --   unify env (FunT IntT TypT) (ForT "x" (FunT x y)) `shouldBe` Right (FunT IntT TypT, set ("y", TypT) env)
  --   unify env (ForT "x" (FunT x y)) (FunT IntT TypT) `shouldBe` Right (FunT IntT TypT, set ("y", TypT) env)
  --   unify env (ForT "x" (FunT x TypT)) (ForT "y" (FunT IntT y)) `shouldBe` Right (FunT IntT TypT, env)
  --   unify env (ForT "x" (FunT x TypT)) (ForT "y" (FunT x y)) `shouldBe` Right (ForT "x" (FunT x TypT), env)
  --   unify env (ForT "x" (FunT x y)) (ForT "y" (FunT IntT y)) `shouldBe` Right (ForT "y" (FunT IntT y), env)

  -- it "☯ instantiate" $ do
  --   let env = [("x", IntT)]
  --   instantiate env IntT `shouldBe` (IntT, env)
  --   instantiate env (ForT "x" x) `shouldBe` (Var "x'", ("x'", Var "x'") : env)
  --   instantiate env (ForT "y" x) `shouldBe` (Var "x", ("y", Var "y") : env)

  it "☯ infer" $ do
    let (a, xT, yT) = (Var "a", Var "xT", Var "yT")
    let env =
          [ ("x", Int 1),
            ("y", Var "y"),
            ("f", Lam [] "x" (Num 0.0)),
            ("g", Ann (Var "g") (ForT "b" $ FunT IntT (Var "b")))
          ]

    infer env Err `shouldBe` Right (Err, env)
    infer env (Int 1) `shouldBe` Right (IntT, env)
    infer env (Num 1.1) `shouldBe` Right (NumT, env)
    infer env (Var "x") `shouldBe` Right (IntT, env)
    infer env (Var "y") `shouldBe` Right (yT, annotate ("y", "yT") env)
    infer env (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer env (Ann x IntT) `shouldBe` Right (IntT, env)
    infer env (Ann x NumT) `shouldBe` Left (TypeMismatch IntT NumT)
    infer env (Ann y IntT) `shouldBe` Right (IntT, annotate ("y", "yT") env |> set ("yT", IntT))
    infer env (Ann y (Int 1)) `shouldBe` Left (NotAType (Int 1))
    infer env (Ann x y) `shouldBe` Right (IntT, set ("y", IntT) env)
    infer env (Lam [] "x" x) `shouldBe` Right (ForT "xT" $ FunT xT xT, env)
    infer env (Lam [] "x" (Ann x IntT)) `shouldBe` Right (FunT IntT IntT, env)
    infer env (lam ["x", "y"] (Ann x IntT)) `shouldBe` Right (FunT IntT (ForT "yT" (FunT yT IntT)), env)
    infer env (App x y) `shouldBe` Left (TypeMismatch IntT (FunT yT a))
    infer env (App f x) `shouldBe` Right (NumT, env)
    infer env (App g x) `shouldBe` Right (ForT "a" a, env)
    infer env (App g (Num 1.1)) `shouldBe` Left (TypeMismatch IntT NumT)
    infer env (Fix "x" x) `shouldBe` Right (ForT "xT" xT, env)
    infer env (Fix "x" (Int 1)) `shouldBe` Right (IntT, env)
    infer env (Fix "x" (Lam [] "y" (App x y))) `shouldBe` Right (ForT "yT" (FunT yT (ForT "a" a)), env)
    infer env TypT `shouldBe` Right (TypT, env)
    infer env IntT `shouldBe` Right (TypT, env)
    infer env NumT `shouldBe` Right (TypT, env)
    infer env (ForT "x" (Int 1)) `shouldBe` Left (NotAType (Int 1))
    infer env (ForT "x" IntT) `shouldBe` Right (TypT, env)
    infer env (ForT "x" x) `shouldBe` Right (TypT, env)
    infer env (FunT (Int 1) IntT) `shouldBe` Left (NotAType (Int 1))
    infer env (FunT IntT (Int 1)) `shouldBe` Left (NotAType (Int 1))
    infer env (FunT IntT IntT) `shouldBe` Right (TypT, env)

  it "☯ eval" $ do
    let env = [("x", Int 1), ("y", Var "y"), ("f", Lam [("z", Num 0.0)] "x" z)]
    eval env (Int 1) `shouldBe` Int 1
    eval env (Num 1.0) `shouldBe` Num 1.0
    eval env (Var "x") `shouldBe` Int 1
    eval env (Var "y") `shouldBe` Var "y"
    eval env (Var "z") `shouldBe` Var "z"
    eval env (Lam [("x", Num 0.0)] "x" x) `shouldBe` Lam [] "x" x
    eval env (Lam [("x", Num 0.0)] "y" x) `shouldBe` Lam [] "y" (Int 1)
    eval env (Lam [("z", Num 0.0)] "x" z) `shouldBe` Lam [] "x" (Num 0.0)
    eval env (App x y) `shouldBe` App (Int 1) y
    eval env (App f x) `shouldBe` Num 0.0
    eval env (App (Lam [] "x" x) x) `shouldBe` Int 1
    eval env (app true [Int 1, Int 2]) `shouldBe` Int 1
    eval env (app false [Int 1, Int 2]) `shouldBe` Int 2
    eval env (App (Fix "f" $ Lam [] "x" $ app x [Int 1, App f true]) true) `shouldBe` Int 1
    eval env (App (Fix "f" $ Lam [] "x" $ app x [Int 1, App f true]) false) `shouldBe` Int 1
    eval env (add (Int 1) (Int 1)) `shouldBe` Int 2
    eval env (add (Num 1.1) (Num 1.1)) `shouldBe` Num 2.2
    eval env (eq (Int 1) (Int 1)) `shouldBe` true
    eval env (eq (Int 0) (Int 1)) `shouldBe` false
    eval env (eq (Num 1.1) (Num 1.1)) `shouldBe` true
    eval env (eq (Num 0.0) (Num 1.1)) `shouldBe` false
