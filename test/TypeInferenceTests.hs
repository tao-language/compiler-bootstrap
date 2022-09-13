module TypeInferenceTests where

import Lambda
import Test.Hspec
import TypeInference

typeInferenceTests :: SpecWith ()
typeInferenceTests = describe "--== Type inference ==--" $ do
  let (x, y) = (Var "x", Var "y")

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
    inferType' env (Call "f") `shouldBe` Just (for ["a", "b"] (Fun (Var "a") (Var "b")))
    inferType' env Fix `shouldBe` Just (For "a" (Fun (Var "a") (Var "a")))
    inferType' env (Ann (Int 1) x) `shouldBe` Just IntT
    inferType' env (Ann (Int 1) Typ) `shouldBe` Nothing
    inferType' env (For "x" y) `shouldBe` Just Typ
    inferType' env (Fun x y) `shouldBe` Just Typ
