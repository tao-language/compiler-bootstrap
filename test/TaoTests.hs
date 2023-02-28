module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec (SpecWith, describe, it, shouldBe)

taoTests :: SpecWith ()
taoTests = describe "--==☯ Tao ☯==--" $ do
  -- let (a, b) = (Var "a", Var "b")
  -- let (a', b') = (VarP "a", VarP "b")
  -- let (x, y, z) = (Var "x", Var "y", Var "z")
  -- let (x', y', z') = (VarP "x", VarP "y", VarP "z")

  -- it "☯ forT" $ do
  --   for [] x `shouldBe` x
  --   for ["x"] y `shouldBe` For "x" y
  --   for ["x", "y"] z `shouldBe` For "x" (For "y" z)

  -- it "☯ funT" $ do
  --   funT [] x `shouldBe` x
  --   funT [x] y `shouldBe` FunT x y
  --   funT [x, y] z `shouldBe` FunT x (FunT y z)

  -- it "☯ app" $ do
  --   app x [] `shouldBe` x
  --   app x [y] `shouldBe` App x y
  --   app x [y, z] `shouldBe` App (App x y) z

  -- it "☯ lam" $ do
  --   lam [] x `shouldBe` x
  --   lam [x'] y `shouldBe` Lam x' y
  --   lam [x', y'] z `shouldBe` Lam x' (Lam y' z)

  -- it "☯ unpack" $ do
  --   unpack ([], AnyP, a) `shouldBe` []
  --   unpack ([], VarP "x", a) `shouldBe` [("x", a)]
  --   unpack ([], AndP x' x', a) `shouldBe` [("x", Let ([], AndP x' x', a) x)]
  --   unpack ([], AndP x' y', a) `shouldBe` [("x", Let ([], AndP x' y', a) x), ("y", Let ([], AndP x' y', a) y)]
  --   unpack ([], OrP x' x', a) `shouldBe` [("x", Let ([], OrP x' x', a) x)]
  --   unpack ([], OrP x' y', a) `shouldBe` [("x", Let ([], OrP x' y', a) x), ("y", Let ([], OrP x' y', a) y)]
  --   unpack ([], AnnP x' x', a) `shouldBe` [("x", Let ([], AnnP x' x', a) x)]
  --   unpack ([], AnnP x' y', a) `shouldBe` [("x", Let ([], AnnP x' y', a) x), ("y", Let ([], AnnP x' y', a) y)]
  --   unpack ([], AppP x' x', a) `shouldBe` [("x", Let ([], AppP x' x', a) x)]
  --   unpack ([], AppP x' y', a) `shouldBe` [("x", Let ([], AppP x' y', a) x), ("y", Let ([], AppP x' y', a) y)]
  --   unpack ([], IfP x' y, a) `shouldBe` [("x", If y a)]
  --   unpack ([], AsP x' "y", a) `shouldBe` [("y", a), ("x", a)]
  --   unpack ([], EqP x, a) `shouldBe` []

  -- it "☯ compile" $ do
  --   let env = [("x", Int 1), ("y", Ann y IntT), ("a", a), ("b", b)]
  --   compile env (Err "e") `shouldBe` C.Err "e"
  --   compile env TypT `shouldBe` C.TypT
  --   compile env NilT `shouldBe` C.NilT
  --   compile env Nil `shouldBe` C.Nil
  --   compile env IntT `shouldBe` C.IntT
  --   compile env (Int 1) `shouldBe` C.Int 1
  --   compile env NumT `shouldBe` C.NumT
  --   compile env (Num 1) `shouldBe` C.Num 1
  --   compile env (Ctr "T" "A") `shouldBe` C.Ctr "T" "A"
  --   compile env (Var "a") `shouldBe` C.Var "a"
  --   compile env (Var "x") `shouldBe` C.Int 1
  --   compile env (Var "y") `shouldBe` C.Ann (C.Var "y") C.IntT
  --   compile env (Var "z") `shouldBe` C.Err "undefined variable: z"
  --   compile env (For "x" x) `shouldBe` C.For "x" (C.Var "x")
  --   compile env (For "y" x) `shouldBe` C.For "y" (C.Int 1)
  --   compile env (FunT a b) `shouldBe` C.FunT (C.Var "a") (C.Var "b")
  --   compile env (Lam x' x) `shouldBe` C.For "x" (C.Lam (C.Var "x") (C.Var "x"))
  --   compile env (Lam (AndP x' y') x) `shouldBe` C.for ["x", "y"] (C.Lam (C.And (C.Var "x") (C.Var "y")) (C.Var "x"))
  --   compile env (App a b) `shouldBe` C.App (C.Var "a") (C.Var "b")
  --   compile env (And a b) `shouldBe` C.And (C.Var "a") (C.Var "b")
  --   compile env (Or a b) `shouldBe` C.Or (C.Var "a") (C.Var "b")
  --   compile env (If a b) `shouldBe` C.If (C.Var "a") (C.Var "b")
  --   compile env (Ann a b) `shouldBe` C.Ann (C.Var "a") (C.For "b" (C.Var "b"))
  --   compile env (SumT "T" [("A", a)]) `shouldBe` C.SumT "T" [("A", C.Var "a")]
  --   compile env (Eq a b) `shouldBe` C.Eq (C.Var "a") (C.Var "b")
  --   compile env (Lt a b) `shouldBe` C.Op2 C.Lt (C.Var "a") (C.Var "b")
  --   compile env (Add a b) `shouldBe` C.Op2 C.Add (C.Var "a") (C.Var "b")
  --   compile env (Sub a b) `shouldBe` C.Op2 C.Sub (C.Var "a") (C.Var "b")
  --   compile env (Mul a b) `shouldBe` C.Op2 C.Mul (C.Var "a") (C.Var "b")
  --   compile env (Let ([], x', Int 2) x) `shouldBe` C.Int 1
  --   compile env (Let ([], z', Int 2) z) `shouldBe` C.Int 2
  --   compile env (TypeOf x) `shouldBe` C.IntT
  --   compile env (Match []) `shouldBe` C.Nil
  --   compile env (Match [([], Int 1), ([], Int 2)]) `shouldBe` C.Or (C.Int 1) (C.Int 2)
  --   compile env (Match [([x'], x), ([y'], x)]) `shouldBe` C.Or (C.For "x" (C.Lam (C.Var "x") (C.Var "x"))) (C.For "y" (C.Lam (C.Var "y") (C.Int 1)))

  -- it "☯ compilePattern" $ do
  --   let env = [("x", Int 1), ("y", Ann y IntT), ("a", a), ("b", b)]
  --   compilePattern env AnyP `shouldBe` ([""], C.Var "")
  --   compilePattern env (VarP "x") `shouldBe` (["x"], C.Var "x")
  --   compilePattern env (AndP a' b') `shouldBe` (["a", "b"], C.And (C.Var "a") (C.Var "b"))
  --   compilePattern env (OrP a' b') `shouldBe` (["a", "b"], C.Or (C.Var "a") (C.Var "b"))
  --   compilePattern env (AnnP a' b') `shouldBe` (["a", "b"], C.Ann (C.Var "a") (C.Var "b"))
  --   compilePattern env (AppP a' b') `shouldBe` (["a", "b"], C.App (C.Var "a") (C.Var "b"))
  --   compilePattern env (IfP a' x) `shouldBe` (["a"], C.If (C.Int 1) (C.Var "a"))
  --   compilePattern env (AsP a' "x") `shouldBe` (["x", "a"], C.Eq (C.Var "x") (C.Var "a"))
  --   compilePattern env (EqP x) `shouldBe` ([], C.Int 1)

  it "☯ TODO" $ do
    True `shouldBe` True
