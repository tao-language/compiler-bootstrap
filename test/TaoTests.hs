module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec (SpecWith, describe, it, shouldBe)

taoTests :: SpecWith ()
taoTests = describe "--==☯ Tao ☯==--" $ do
  let (a, b) = (Var "a", Var "b")
  let (a', b') = (VarP "a", VarP "b")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (VarP "x", VarP "y", VarP "z")

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

  it "☯ unpack" $ do
    let ctx :: Context
        ctx =
          [ ("A", UnionAlt "T" [] (Var "T")),
            ("B", UnionAlt "T" [("i", IntT), ("n", NumT)] (Var "T"))
          ]

    unpack ctx ([], AnyP, a) `shouldBe` Right []
    -- unpack ([], AsP AnyP "x", a) `shouldBe` [("x", Val a)]
    unpack ctx ([], VarP "x", a) `shouldBe` Right [("x", Val a)]
    unpack ctx ([], CtrP "A" [], a) `shouldBe` Right []
    unpack ctx ([], CtrP "B" [x'], a) `shouldBe` Left (CtrArgsMismatch "B" ["i", "n"] [VarP "x"])
    unpack ctx ([], CtrP "B" [x', y'], a) `shouldBe` Right [("x", Val (Get "B" a "i")), ("y", Val (Get "B" a "n"))]
    unpack ctx ([("x", IntT)], x', a) `shouldBe` Right [("x", Ann a IntT)]
    unpack ctx ([("x", IntT)], CtrP "B" [x', y'], a) `shouldBe` Right [("x", Ann (Get "B" a "i") IntT), ("y", Val (Get "B" a "n"))]

  it "☯ compile" $ do
    let ctx :: Context
        ctx =
          [ ("T", UnionType [] ["A", "B"]),
            ("A", UnionAlt "T" [] (Var "T")),
            ("B", UnionAlt "T" [("i", IntT), ("n", NumT)] (Var "T"))
          ]

    compile ctx Knd `shouldBe` Right C.Knd
    compile ctx IntT `shouldBe` Right C.IntT
    compile ctx NumT `shouldBe` Right C.NumT
    compile ctx (Int 1) `shouldBe` Right (C.Int 1)
    compile ctx (Num 1) `shouldBe` Right (C.Num 1)
    compile ctx (Var "x") `shouldBe` Right (C.Var "x")
    compile ctx (Lam "x" y) `shouldBe` Right (C.Lam "x" (C.Var "y"))
    compile ctx (For "x" y) `shouldBe` Right (C.For "x" (C.Var "y"))
    compile ctx (Fun x y) `shouldBe` Right (C.Fun (C.Var "x") (C.Var "y"))
    compile ctx (App x y) `shouldBe` Right (C.App (C.Var "x") (C.Var "y"))
    compile ctx (Typ "Bool" []) `shouldBe` Right (C.Typ "Bool" [])
    compile ctx (Typ "Maybe" [IntT]) `shouldBe` Right (C.Typ "Maybe" [C.IntT])
    compile ctx (Ctr "A" []) `shouldBe` compile [] (lam ["A", "B"] (app (Var "A") []))
    compile ctx (Ctr "B" [x, y]) `shouldBe` compile [] (lam ["A", "B"] (app (Var "B") [x, y]))
    compile ctx (Get "A" x "a") `shouldBe` Left (UndefinedCtrField "A" "a")
    compile ctx (Get "B" x "i") `shouldBe` compile [] (App x (lam ["i", "n"] (Var "i")))
    compile ctx (Get "B" x "n") `shouldBe` compile [] (App x (lam ["i", "n"] (Var "n")))
    compile ctx (Let [([], AnyP, y)] z) `shouldBe` Right (C.Var "z")
    compile ctx (Let [([], VarP "x", y)] z) `shouldBe` Right (C.Let [("x", C.Var "y")] (C.Var "z"))
    compile ctx (Let [([], CtrP "A" [], y)] z) `shouldBe` Right (C.Var "z")
    compile ctx (Let [([], CtrP "B" [AnyP, AnyP], y)] z) `shouldBe` Right (C.Var "z")
    compile ctx (Let [([], CtrP "B" [VarP "a", AnyP], y)] z) `shouldBe` Right (C.Let [("a", C.App (C.Var "y") (C.lam ["i", "n"] (C.Var "i")))] (C.Var "z"))
    compile ctx (Case x []) `shouldBe` Left EmptyCase
    compile ctx (Case x [(AnyP, y)]) `shouldBe` Right (C.Var "y")
    compile ctx (Case x [(VarP "a", y)]) `shouldBe` Right (C.Let [("a", C.Var "x")] (C.Var "y"))
    compile ctx (Case x [(CtrP "A" [], y)]) `shouldBe` Left (MissingCase "B")
    compile ctx (Case x [(CtrP "B" [VarP "a", AnyP], z), (CtrP "A" [], y)]) `shouldBe` Right (C.app (C.Var "x") [C.Var "y", C.Lam "*" $ C.Let [("a", C.App (C.Var "*") (C.lam ["i", "n"] (C.Var "i")))] $ C.Lam "*" (C.Var "z")])
  -- compile ctx (Match ) `shouldBe` Right (C.Var "z")
  -- Match ![([Pattern], Expr)] !Expr
  -- TypeOf !Expr
  -- Eq !Expr !Expr
  -- Lt !Expr !Expr
  -- Add !Expr !Expr
  -- Sub !Expr !Expr
  -- Mul !Expr !Expr
  --   compile ctx (Ctr "T" "A") `shouldBe` C.Ctr "T" "A"
  --   compile ctx (Var "a") `shouldBe` C.Var "a"
  --   compile ctx (Var "x") `shouldBe` C.Int 1
  --   compile ctx (Var "y") `shouldBe` C.Ann (C.Var "y") C.IntT
  --   compile ctx (Var "z") `shouldBe` C.Err "undefined variable: z"
  --   compile ctx (For "x" x) `shouldBe` C.For "x" (C.Var "x")
  --   compile ctx (For "y" x) `shouldBe` C.For "y" (C.Int 1)
  --   compile ctx (FunT a b) `shouldBe` C.FunT (C.Var "a") (C.Var "b")
  --   compile ctx (Lam x' x) `shouldBe` C.For "x" (C.Lam (C.Var "x") (C.Var "x"))
  --   compile ctx (Lam (AndP x' y') x) `shouldBe` C.for ["x", "y"] (C.Lam (C.And (C.Var "x") (C.Var "y")) (C.Var "x"))
  --   compile ctx (App a b) `shouldBe` C.App (C.Var "a") (C.Var "b")
  --   compile ctx (And a b) `shouldBe` C.And (C.Var "a") (C.Var "b")
  --   compile ctx (Or a b) `shouldBe` C.Or (C.Var "a") (C.Var "b")
  --   compile ctx (If a b) `shouldBe` C.If (C.Var "a") (C.Var "b")
  --   compile ctx (Ann a b) `shouldBe` C.Ann (C.Var "a") (C.For "b" (C.Var "b"))
  --   compile ctx (SumT "T" [("A", a)]) `shouldBe` C.SumT "T" [("A", C.Var "a")]
  --   compile ctx (Eq a b) `shouldBe` C.Eq (C.Var "a") (C.Var "b")
  --   compile ctx (Lt a b) `shouldBe` C.Op2 C.Lt (C.Var "a") (C.Var "b")
  --   compile ctx (Add a b) `shouldBe` C.Op2 C.Add (C.Var "a") (C.Var "b")
  --   compile ctx (Sub a b) `shouldBe` C.Op2 C.Sub (C.Var "a") (C.Var "b")
  --   compile ctx (Mul a b) `shouldBe` C.Op2 C.Mul (C.Var "a") (C.Var "b")
  --   compile ctx (Let ([], x', Int 2) x) `shouldBe` C.Int 1
  --   compile ctx (Let ([], z', Int 2) z) `shouldBe` C.Int 2
  --   compile ctx (TypeOf x) `shouldBe` C.IntT
  --   compile ctx (Match []) `shouldBe` C.Nil
  --   compile ctx (Match [([], Int 1), ([], Int 2)]) `shouldBe` C.Or (C.Int 1) (C.Int 2)
  --   compile ctx (Match [([x'], x), ([y'], x)]) `shouldBe` C.Or (C.For "x" (C.Lam (C.Var "x") (C.Var "x"))) (C.For "y" (C.Lam (C.Var "y") (C.Int 1)))

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
