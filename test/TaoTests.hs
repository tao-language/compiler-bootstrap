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

  -- it "☯ unpack" $ do
  --   let ctx :: Context
  --       ctx =
  --         [ ("A", UnionAlt "T" [] (Var "T")),
  --           ("B", UnionAlt "T" [("i", IntT), ("n", NumT)] (Var "T"))
  --         ]

  --   -- unpack ctx ([], AnyP, a) `shouldBe` Right []
  --   -- unpack ([], AsP AnyP "x", a) `shouldBe` [("x", Val a)]
  --   unpack ctx ([], VarP "x", a) `shouldBe` Right [("x", Val a)]
  --   unpack ctx ([], CtrP "A" [], a) `shouldBe` Right []
  --   unpack ctx ([], CtrP "B" [x'], a) `shouldBe` Left (CtrArgsMismatch "B" ["i", "n"] [VarP "x"])
  --   unpack ctx ([], CtrP "B" [x', y'], a) `shouldBe` Right [("x", Val (Get "B" a "i")), ("y", Val (Get "B" a "n"))]
  --   unpack ctx ([("x", IntT)], x', a) `shouldBe` Right [("x", Ann a IntT)]
  --   unpack ctx ([("x", IntT)], CtrP "B" [x', y'], a) `shouldBe` Right [("x", Ann (Get "B" a "i") IntT), ("y", Val (Get "B" a "n"))]

  -- it "☯ expandCase" $ do
  --   let ctx :: Context
  --       ctx =
  --         [ ("T", UnionType [] ["A", "B"]),
  --           ("A", UnionAlt "T" [] (Var "T")),
  --           ("B", UnionAlt "T" [("i", IntT), ("n", NumT)] (Var "T"))
  --         ]

  --   {--
  --   \a -> case a
  --     Just (Just x) = x
  --     Just x = 1
  --     _ = 0

  --   \a -> a (\m -> m (\x = x) 1) 0

  --   %case
  --     #Just [#Just [x]] -> x
  --     #Just [x] -> 1
  --     _ -> 0

  --   %case
  --     #Just [x] -> %case
  --     _ -> 0

  --   --}

  --   let a = Var "a"
  --   let (i0, i1, i2) = (Int 0, Int 1, Int 2)
  --   expandCase ctx a [] i0 `shouldBe` i0
  --   expandCase ctx a [("A", [], i1)] i0 `shouldBe` app a [i1, lam ["", ""] i0]
  --   -- expandCase ctx a [("B", [AnyP], i2)] i0 `shouldBe` app a [i1, lam ["", ""] i0]
  --   -- expandCase ctx a [("B", [AnyP, AnyP], i2)] i0 `shouldBe` app a [i1, lam ["", ""] i0]
  --   -- expandCase ctx a [("B", [AnyP, AnyP, AnyP], i2)] i0 `shouldBe` app a [i1, lam ["", ""] i0]
  --   True `shouldBe` True

  -- it "☯ expandMatch" $ do
  --   let (i0, i1, i2) = (Int 0, Int 1, Int 2)
  --   let (a, b, c) = (Var "a", Var "b", Var "c")
  --   let (x, y, z) = (VarP "x", VarP "y", VarP "z")

  --   expandMatch []  [([], i1)] i0 `shouldBe` i1
  --   expandMatch [a] [([VarP "y"], i1)] i0 `shouldBe` Let [(VarP "y", a)] i1
  --   expandMatch [a] [([VarP "y"], i1)] i0 `shouldBe` Let [(VarP "y", a)] i1
  --   expandMatch [a] [([CtrP "A" []], i1)] i0 `shouldBe` Case a [("A", Let [(CtrP "A" [], a)] i1)] i0
  --   expandMatch [a] [([CtrP "A" []], i1), ([VarP "y"], i2)] i0 `shouldBe` Case a [("A", Let [(CtrP "A" [], a)] i1)] (Let [(VarP "y", a)] i2)
  --   expandMatch [a] [([VarP "y"], i1), ([CtrP "A" []], i2)] i0 `shouldBe` Case a [("A", Let [(VarP "y", a)] i1)] (Let [(VarP "y", a)] i1)

  it "☯ compile" $ do
    let ops = []
    let ctx :: Context
        ctx =
          [ ("T", UnionType [] ["A", "B"]),
            ("A", UnionAlt "T" [] (Var "T")),
            ("B", UnionAlt "T" [("i", IntT), ("n", NumT)] (Var "T")),
            ("U", UnionType [] ["C"]),
            ("C", UnionAlt "U" [("i", IntT), ("n", NumT)] (Var "U"))
          ]

    let compile' = compile ops ctx
    compile' Knd `shouldBe` Right C.Knd
    compile' IntT `shouldBe` Right C.IntT
    compile' NumT `shouldBe` Right C.NumT
    compile' (Int 1) `shouldBe` Right (C.Int 1)
    compile' (Num 1) `shouldBe` Right (C.Num 1)
    compile' (Var "x") `shouldBe` Right (C.Var "x")
    compile' (For "x" y) `shouldBe` Right (C.For "x" (C.Var "y"))
    compile' (Fun x y) `shouldBe` Right (C.Fun (C.Var "x") (C.Var "y"))
    compile' (App x y) `shouldBe` Right (C.App (C.Var "x") (C.Var "y"))
    compile' (Typ "Bool" []) `shouldBe` Right (C.Typ "Bool" [])
    compile' (Typ "Maybe" [IntT]) `shouldBe` Right (C.Typ "Maybe" [C.IntT])
    compile' (Ctr "A" []) `shouldBe` Right (C.lam ["A", "B"] (C.Var "A"))
    compile' (Ctr "B" [x, y]) `shouldBe` Right (C.lam ["A", "B"] (C.app (C.Var "B") [C.Var "x", C.Var "y"]))
    compile' (Get "A" x "a") `shouldBe` Left (UndefinedCtrField "A" "a")
    compile' (Get "B" x "i") `shouldBe` Right (C.App (C.Var "x") (C.lam ["i", "n"] (C.Var "i")))
    compile' (Get "B" x "n") `shouldBe` Right (C.App (C.Var "x") (C.lam ["i", "n"] (C.Var "n")))
    compile' (Match []) `shouldBe` Left MissingCases
    compile' (Match [Case [] (Int 1)]) `shouldBe` Right (C.Int 1)
    compile' (Match [Case [VarP "x"] (Int 1)]) `shouldBe` Right (C.Lam "x" $ C.Int 1)
    compile' (Match [Case [VarP "x"] (Int 1), Case [] (Int 2)]) `shouldBe` Left (MatchMissingArgs (Int 2))
    compile' (Match [Case [CtrP "A" []] (Int 1)]) `shouldBe` Left MissingCases
    compile' (Match [Case [CtrP "A" []] (Int 1), Case [VarP "x"] (Int 2)]) `shouldBe` Right (C.Lam "x" $ C.app (C.Var "x") [C.Int 1, C.lam ["_", "_"] $ C.Int 2])
    compile' (Match [Case [CtrP "B" [VarP "a", VarP "b"]] (Int 1), Case [VarP "x"] (Int 2)]) `shouldBe` Right (C.Lam "x" $ C.app (C.Var "x") [C.Int 2, C.lam ["a", "b"] $ C.Int 1])
    -- TypeOf !Expr
    -- Eq !Expr !Expr
    -- Lt !Expr !Expr
    -- Add !Expr !Expr
    -- Sub !Expr !Expr
    -- Mul !Expr !Expr
    True `shouldBe` True
  --   compile' (Ctr "T" "A") `shouldBe` C.Ctr "T" "A"
  --   compile' (Var "a") `shouldBe` C.Var "a"
  --   compile' (Var "x") `shouldBe` C.Int 1
  --   compile' (Var "y") `shouldBe` C.Ann (C.Var "y") C.IntT
  --   compile' (Var "z") `shouldBe` C.Err "undefined variable: z"
  --   compile' (For "x" x) `shouldBe` C.For "x" (C.Var "x")
  --   compile' (For "y" x) `shouldBe` C.For "y" (C.Int 1)
  --   compile' (FunT a b) `shouldBe` C.FunT (C.Var "a") (C.Var "b")
  --   compile' (Lam x' x) `shouldBe` C.For "x" (C.Lam (C.Var "x") (C.Var "x"))
  --   compile' (Lam (AndP x' y') x) `shouldBe` C.for ["x", "y"] (C.Lam (C.And (C.Var "x") (C.Var "y")) (C.Var "x"))
  --   compile' (App a b) `shouldBe` C.App (C.Var "a") (C.Var "b")
  --   compile' (And a b) `shouldBe` C.And (C.Var "a") (C.Var "b")
  --   compile' (Or a b) `shouldBe` C.Or (C.Var "a") (C.Var "b")
  --   compile' (If a b) `shouldBe` C.If (C.Var "a") (C.Var "b")
  --   compile' (Ann a b) `shouldBe` C.Ann (C.Var "a") (C.For "b" (C.Var "b"))
  --   compile' (SumT "T" [("A", a)]) `shouldBe` C.SumT "T" [("A", C.Var "a")]
  --   compile' (Eq a b) `shouldBe` C.Eq (C.Var "a") (C.Var "b")
  --   compile' (Lt a b) `shouldBe` C.Op2 C.Lt (C.Var "a") (C.Var "b")
  --   compile' (Add a b) `shouldBe` C.Op2 C.Add (C.Var "a") (C.Var "b")
  --   compile' (Sub a b) `shouldBe` C.Op2 C.Sub (C.Var "a") (C.Var "b")
  --   compile' (Mul a b) `shouldBe` C.Op2 C.Mul (C.Var "a") (C.Var "b")
  --   compile' (Let ([], x', Int 2) x) `shouldBe` C.Int 1
  --   compile' (Let ([], z', Int 2) z) `shouldBe` C.Int 2
  --   compile' (TypeOf x) `shouldBe` C.IntT
  --   compile' (Match []) `shouldBe` C.Nil
  --   compile' (Match [([], Int 1), ([], Int 2)]) `shouldBe` C.Or (C.Int 1) (C.Int 2)
  --   compile' (Match [([x'], x), ([y'], x)]) `shouldBe` C.Or (C.For "x" (C.Lam (C.Var "x") (C.Var "x"))) (C.For "y" (C.Lam (C.Var "y") (C.Int 1)))

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
