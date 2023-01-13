module Core3Tests where

import Core3
import Flow ((|>))
import Test.Hspec

core3Tests :: SpecWith ()
core3Tests = describe "--== Core language ==--" $ do
  let a = Var "a"
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (xT, yT) = (Var "xT", Var "yT")

  it "☯ lam" $ do
    lam [] x `shouldBe` x
    lam [x] y `shouldBe` Lam x y
    lam [x, y] z `shouldBe` Lam x (Lam y z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ or'" $ do
    or' [] `shouldBe` Err
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

  it "☯ unify" $ do
    let env = [("x", Var "x"), ("y", Var "y")]
    unify env Err Err `shouldBe` Just env
    unify env Err Nil `shouldBe` Nothing
    unify env Nil Nil `shouldBe` Just env
    unify env (Int 1) (Int 1) `shouldBe` Just env
    unify env (Int 1) (Int 2) `shouldBe` Nothing
    unify env (Num 1.1) (Num 1.1) `shouldBe` Just env
    unify env (Num 1.1) (Num 2.2) `shouldBe` Nothing
    -- unify env (Ctr "T" "A" NilT) (Ctr "X" "A" NilT) `shouldBe` Nothing
    -- unify env (Ctr "T" "A" NilT) (Ctr "T" "X" NilT) `shouldBe` Nothing
    -- unify env (Ctr "T" "A" NilT) (Ctr "T" "A" IntT) `shouldBe` Nothing
    -- unify env (Ctr "T" "A" NilT) (Ctr "T" "A" NilT) `shouldBe` Just env
    unify env (Var "x") Nil `shouldBe` Just (set ("x", Nil) env)
    unify env Nil (Var "x") `shouldBe` Just (set ("x", Nil) env)
    unify env (For "x" x) Nil `shouldBe` Just (("x", Nil) : env)
    unify env (For "x" Err) Nil `shouldBe` Nothing
    unify env Nil (For "x" x) `shouldBe` Just (("x", Nil) : env)
    unify env Nil (For "x" Err) `shouldBe` Nothing
    unify env (App x Nil) (App Err y) `shouldBe` Just (set ("x", Err) env |> set ("y", Nil))
    unify env (App Err y) (App x Nil) `shouldBe` Just (set ("x", Err) env |> set ("y", Nil))
    unify env (Or x Err) Nil `shouldBe` Just (set ("x", Nil) env)
    unify env (Or Err x) Nil `shouldBe` Just (set ("x", Nil) env)
    unify env Nil (Or x Err) `shouldBe` Just (set ("x", Nil) env)
    unify env Nil (Or Err x) `shouldBe` Just (set ("x", Nil) env)

  it "☯ reduce" $ do
    let env = [("x", Int 1), ("y", Var "y"), ("a", IntT)]
    reduce env Err `shouldBe` Err
    reduce env Typ `shouldBe` Typ
    reduce env NilT `shouldBe` NilT
    reduce env IntT `shouldBe` IntT
    reduce env NumT `shouldBe` NumT
    reduce env Nil `shouldBe` Nil
    reduce env (Int 1) `shouldBe` Int 1
    reduce env (Num 1.1) `shouldBe` Num 1.1
    -- reduce env (Ctr "T" "A" a) `shouldBe` Ctr "T" "A" IntT
    reduce env (Var "x") `shouldBe` Int 1
    reduce env (Var "y") `shouldBe` Var "y"
    reduce env (Var "z") `shouldBe` Err
    reduce env (For "x" x) `shouldBe` For "x" x
    reduce env (For "y" x) `shouldBe` For "y" (Int 1)
    reduce env (Fun a a) `shouldBe` Fun IntT IntT
    reduce env (Lam x x) `shouldBe` Lam x x
    reduce env (App Err x) `shouldBe` Err
    reduce env (App y x) `shouldBe` App y (Int 1)
    reduce env (App (Lam x y) x) `shouldBe` y
    reduce env (App (Lam y y) x) `shouldBe` Int 1
    reduce env (App (Lam Nil y) x) `shouldBe` Err
    reduce env (App (For "x" (Lam x x)) Nil) `shouldBe` Nil
    -- TODO: App Or
    reduce env (Ann x y) `shouldBe` Ann (Int 1) y
    reduce env (And x x) `shouldBe` And (Int 1) (Int 1)
    reduce env (Or x Err) `shouldBe` Or x Err
    reduce env (Eq x y) `shouldBe` Int 1
    reduce env (Eq y x) `shouldBe` Int 1
    reduce env (Eq x Nil) `shouldBe` Err
    reduce env (Op2 Add (Int 1) (Int 1)) `shouldBe` Int 2
    reduce env (Op2 Add (Num 1.1) (Num 1.1)) `shouldBe` Num 2.2
    reduce env (Op2 Add x y) `shouldBe` Op2 Add (Int 1) y
    reduce env (Op2 Lt (Int 1) (Int 1)) `shouldBe` Err
    reduce env (Op2 Lt (Int 1) (Int 2)) `shouldBe` Int 1
    reduce env (Op2 Lt (Num 1.1) (Num 1.1)) `shouldBe` Err
    reduce env (Op2 Lt (Num 1.1) (Num 2.2)) `shouldBe` Num 1.1
    reduce env (Op2 Lt x y) `shouldBe` Op2 Lt (Int 1) y

  -- it "☯ newName" $ do
  -- it "☯ annotate" $ do

  it "☯ infer" $ do
    let env = [("x", Int 1), ("y", Var "y"), ("i", Ann (Var "i") IntT)]
    infer env Err `shouldBe` Left ErrorType
    infer env Typ `shouldBe` Right (Typ, env)
    infer env NilT `shouldBe` Right (Typ, env)
    infer env IntT `shouldBe` Right (Typ, env)
    infer env NumT `shouldBe` Right (Typ, env)
    infer env Nil `shouldBe` Right (NilT, env)
    infer env (Int 1) `shouldBe` Right (IntT, env)
    infer env (Num 1.1) `shouldBe` Right (NumT, env)
    infer env (Ctr "A") `shouldBe` Left (UntypedCtr "A")
    infer env (Var "x") `shouldBe` Right (IntT, env)
    infer env (Var "y") `shouldBe` Right (For "yT" yT, env)
    infer env (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer env (Var "i") `shouldBe` Right (IntT, env)
    infer env (For "x" x) `shouldBe` Right (For "xT" xT, env)
    infer env (For "x" (Int 1)) `shouldBe` Right (IntT, env)
    infer env (Fun x IntT) `shouldBe` Left (NotAType x IntT)
    infer env (Fun IntT x) `shouldBe` Left (NotAType x IntT)
    infer env (Fun IntT IntT) `shouldBe` Right (Typ, env)
    infer env (Lam x x) `shouldBe` Right (Fun IntT IntT, env)
    infer env (Ann (Int 1) y) `shouldBe` Right (IntT, set ("y", IntT) env)
    infer env (Ann (Int 1) NumT) `shouldBe` Left (TypeMismatch IntT NumT)
    infer env (Ann (Ctr "A") IntT) `shouldBe` Right (IntT, env)
    infer env (App (Int 1) Nil) `shouldBe` Left (TypeMismatch IntT (Fun NilT (Var "_ret")))
    infer env (App (Lam (Int 1) Nil) Nil) `shouldBe` Left (TypeMismatch (Fun IntT NilT) (Fun NilT (Var "_ret")))
    infer env (App (Lam Nil (Int 1)) Nil) `shouldBe` Right (IntT, env)
    infer env (For "x" (App (Lam x x) Nil)) `shouldBe` Right (NilT, env)
    infer env (App (For "x" (Lam x x)) Nil) `shouldBe` Right (NilT, env)
    infer env (And (Int 1) (Num 1.1)) `shouldBe` Right (And IntT NumT, env)
    infer env (Or (Int 1) (Num 1.1)) `shouldBe` Left (TypeMismatch IntT NumT)
    infer env (Or (Int 1) (Int 2)) `shouldBe` Right (IntT, env)
    infer env (Eq (Int 1) (Int 1)) `shouldBe` Right (IntT, env)
    infer env (Eq (Int 1) (Int 2)) `shouldBe` Left (UnifyError (Int 1) (Int 2))
    infer env (Op2 Add (Int 1) (Int 2)) `shouldBe` Right (IntT, env)
    infer env (Op2 Add (Int 1) (Num 1.1)) `shouldBe` Left (TypeMismatch IntT NumT)
    infer env (Op2 Lt (Int 1) (Int 2)) `shouldBe` Right (IntT, env)
    infer env (Op2 Lt (Int 1) (Num 1.1)) `shouldBe` Left (TypeMismatch IntT NumT)

  it "☯ checkType" $ do
    let env = [("x", Int 1), ("y", Var "y")]
    checkType env Err `shouldBe` Left ErrorType
    checkType env Typ `shouldBe` Right env
    checkType env NilT `shouldBe` Right env
    checkType env IntT `shouldBe` Right env
    checkType env NumT `shouldBe` Right env
    checkType env Nil `shouldBe` Left (NotAType Nil NilT)
    checkType env (Int 1) `shouldBe` Left (NotAType (Int 1) IntT)
    checkType env (Num 1.1) `shouldBe` Left (NotAType (Num 1.1) NumT)
    -- checkType env (Ctr "A") `shouldBe` Left (NotAType (Ctr "A") ??)
    checkType env (Var "x") `shouldBe` Left (NotAType (Var "x") IntT)
    checkType env (Var "y") `shouldBe` Right env
    checkType env (For "x" x) `shouldBe` Right env
    checkType env (For "x" (Int 1)) `shouldBe` Left (NotAType (For "x" (Int 1)) IntT)
    checkType env (For "x" IntT) `shouldBe` Right env
    checkType env (Fun x NumT) `shouldBe` Left (NotAType x IntT)
    checkType env (Fun NumT x) `shouldBe` Left (NotAType x IntT)
    checkType env (Fun NumT NumT) `shouldBe` Right env
    checkType env (Lam x x) `shouldBe` Left (NotAType (Lam x x) (Fun IntT IntT))

  describe " -- Examples --" $ do
    let infer' env a = fmap fst (infer env a)

    it "☯ factorial" $ do
      -- f 0 = 1
      -- f n = n * f (n - 1)
      let (f, n) = (Var "f", Var "n")
      let (i0, i1) = (Int 0, Int 1)
      let br1 = Lam i0 i1
      let br2 = For "n" (Lam n $ n `mul` App f (n `sub` i1))
      let env = [("f", or' [br1, br2])]
      reduce env (App f (Int 0)) `shouldBe` Int 1
      reduce env (App f (Int 1)) `shouldBe` Int 1
      reduce env (App f (Int 5)) `shouldBe` Int 120
      infer' env f `shouldBe` Right (Fun IntT IntT)

    it "☯ Bool" $ do
      -- f False = 0
      -- f True = 1
      let f = Var "f"
      let (i0, i1) = (Int 0, Int 1)
      let (bool, true, false) = (Var "Bool", Var "True", Var "False")
      let env =
            [ ("f", or' [Lam false i0, Lam true i1]),
              ("Bool", Typ),
              ("True", Ann (Ctr "True") bool),
              ("False", Ann (Ctr "False") bool)
            ]
      reduce env (App f i0) `shouldBe` Err
      reduce env (App f false) `shouldBe` i0
      reduce env (App f true) `shouldBe` i1

    it "☯ Maybe" $ do
      True `shouldBe` True

    it "☯ List" $ do
      True `shouldBe` True

    it "☯ Vec" $ do
      True `shouldBe` True
