module Tao2Tests where

-- import qualified Core2 as C
-- import Tao2
import Test.Hspec

tao2Tests :: SpecWith ()
tao2Tests = describe "--== Tao language ==--" $ do
  -- let a = Var "a"
  -- let (x, y, z) = (Var "x", Var "y", Var "z")

  -- it "☯ compile" $ do
  --   let unit = Var "Unit"
  --   let bool = Var "Bool"
  --   let maybe = Var "Maybe"
  --   let env =
  --         [ ("x", Int 1),
  --           ("y", Var "y"),
  --           ("f", Lam "x" (Num 0.0)),
  --           ("Unit", SumT "Unit" [] [("A", unit)]),
  --           ("A", Ctr "Unit" "A"),
  --           ("Bool", SumT "Bool" [] [("True", bool), ("False", bool)]),
  --           ("True", Ctr "Bool" "True"),
  --           ("False", Ctr "Bool" "False"),
  --           ("Maybe", SumT "Maybe" ["a"] [("Just", FunT a (App maybe a)), ("Nothing", App maybe a)]),
  --           ("Just", Ctr "Maybe" "Just"),
  --           ("Nothing", Ctr "Maybe" "Nothing")
  --         ]
  --   compile env Err `shouldBe` C.Err
  --   compile env (Int 1) `shouldBe` C.Int 1
  --   compile env (Num 1.1) `shouldBe` C.Num 1.1
  --   compile env (Var "x") `shouldBe` C.Int 1
  --   compile env (Var "y") `shouldBe` C.Var "y"
  --   compile env (Var "z") `shouldBe` C.Err
  --   compile env (Ann x y) `shouldBe` C.Ann (C.Int 1) (C.Var "y")
  --   compile env (Lam "x" x) `shouldBe` C.Lam "x" (C.Var "x")
  --   compile env (Lam "x" y) `shouldBe` C.Lam "x" (C.Var "y")
  --   compile env (App y x) `shouldBe` C.App (C.Var "y") (C.Int 1)
  --   compile env (If y x z) `shouldBe` C.app (C.Var "y") [C.Int 1, C.Err]
  --   compile env (Let [] x) `shouldBe` C.Int 1
  --   compile env (Let [("x", Int 2)] x) `shouldBe` C.Int 1
  --   compile env (Let [("z", Int 2)] z) `shouldBe` C.Int 2
  --   compile env (SumT "Never" [] []) `shouldBe` C.ForT "Never" (C.Var "Never")
  --   compile env (SumT "Unit" [] [("A", Var "Unit")]) `shouldBe` C.ForT "Unit" (C.FunT (C.Var "Unit") (C.Var "Unit"))
  --   compile env (SumT "Maybe" ["a"] [("Just", FunT a (App maybe a)), ("Nothing", App maybe a)]) `shouldBe` C.Lam "a" (C.ForT "Maybe" (C.funT [C.FunT (C.Var "a") (C.Var "Maybe"), C.Var "Maybe"] (C.Var "Maybe")))
  --   compile env (Ctr "X" "A") `shouldBe` C.Err
  --   compile env (Ctr "Unit" "X") `shouldBe` C.Err
  --   compile env (Ctr "Unit" "A") `shouldBe` compile env (Ann (Lam "A" (Var "A")) unit)
  --   compile env (Ctr "Bool" "True") `shouldBe` compile env (Ann (lam ["True", "False"] (Var "True")) bool)
  --   compile env (Ctr "Maybe" "Just") `shouldBe` compile (("a", a) : env) (Ann (lam ["a", "Just", "Nothing"] (App (Var "Just") a)) (ForT "a" $ FunT a (App maybe a)))
  --   compile env (TypeOf x) `shouldBe` C.IntT
  --   compile env (TypeOf y) `shouldBe` C.Var "yT"
  --   compile env (Case y []) `shouldBe` C.Err
  --   compile env (Case y [(AnyP, x)]) `shouldBe` C.Int 1
  --   compile env (Case y [(IntP 0, x)]) `shouldBe` compile env (If (eq y (Int 0)) x Err)
  --   compile env (Case y [(NumP 0.0, x)]) `shouldBe` compile env (If (eq y (Num 0.0)) x Err)
  --   compile env (Case y [(VarP "x", x)]) `shouldBe` C.let' ("x", C.Var "y") (C.Var "x")
  --   -- compile env (Case y [(AnnP AnyP IntT, x)]) `shouldBe` C.let' ("x", C.Var "y") (C.Var "x")
  --   compile env TypT `shouldBe` C.TypT
  --   compile env IntT `shouldBe` C.IntT
  --   compile env NumT `shouldBe` C.NumT
  --   compile env (ForT "x" y) `shouldBe` C.ForT "x" (C.Var "y")
  --   compile env (FunT y z) `shouldBe` C.FunT (C.Var "y") C.Err
  --   compile env Add `shouldBe` C.Op C.Add
  --   compile env Eq `shouldBe` C.Op C.Eq

  -- it "☯ decompile" $ do
  --   decompile C.Err `shouldBe` Err
  --   decompile (C.Int 1) `shouldBe` Int 1
  --   decompile (C.Num 1.1) `shouldBe` Num 1.1
  --   decompile (C.Var "x") `shouldBe` Var "x"
  --   decompile (C.Ann (C.Var "x") (C.Var "y")) `shouldBe` Ann x y
  --   decompile (C.Lam "x" (C.Var "y")) `shouldBe` Lam "x" y
  --   decompile (C.App (C.Var "x") (C.Var "y")) `shouldBe` App x y
  --   decompile C.TypT `shouldBe` TypT
  --   decompile C.IntT `shouldBe` IntT
  --   decompile C.NumT `shouldBe` NumT
  --   decompile (C.ForT "x" (C.Var "y")) `shouldBe` ForT "x" y
  --   decompile (C.FunT (C.Var "x") (C.Var "y")) `shouldBe` FunT x y
  --   decompile (C.Op C.Add) `shouldBe` Add
  --   decompile (C.Op C.Eq) `shouldBe` Eq

  -- it "☯ occurs" $ do
  --   occurs "x" (Int 1) `shouldBe` False
  --   occurs "x" (Num 1.0) `shouldBe` False
  --   occurs "x" (Var "x") `shouldBe` True
  --   occurs "x" (Var "y") `shouldBe` False
  --   occurs "x" (Lam "x" x) `shouldBe` False
  --   occurs "x" (Lam "y" x) `shouldBe` True
  --   occurs "x" (App x y) `shouldBe` True
  --   occurs "x" (App y x) `shouldBe` True
  --   occurs "x" (App y y) `shouldBe` False

  -- it "☯ unify" $ do
  --   let env = []
  --   unify env AnyT IntT `shouldBe` Just (IntT, env)
  --   unify env IntT AnyT `shouldBe` Just (IntT, env)

  -- it "☯ subtype" $ do
  --   subtype IntT IntT `shouldBe` True
  --   subtype NumT IntT `shouldBe` False
  --   subtype IntT NumT `shouldBe` False
  --   subtype NumT NumT `shouldBe` True
  --   subtype (FunT []) (FunT []) `shouldBe` True
  --   subtype (FunT []) (FunT [(IntT, NumT)]) `shouldBe` False
  --   subtype (FunT [(IntT, NumT)]) (FunT []) `shouldBe` True
  --   subtype (FunT [(IntT, NumT)]) (FunT [(IntT, NumT)]) `shouldBe` True
  --   subtype (FunT [(IntT, IntT)]) (FunT [(IntT, NumT)]) `shouldBe` False
  --   subtype (FunT [(NumT, NumT)]) (FunT [(IntT, NumT)]) `shouldBe` False
  --   subtype (FunT [(IntT, NumT), (NumT, IntT)]) (FunT [(IntT, NumT)]) `shouldBe` True
  --   subtype (FunT [(IntT, NumT)]) (FunT [(IntT, NumT), (NumT, IntT)]) `shouldBe` False

  -- it "☯ select" $ do
  --   select id IntT ([] :: [Type]) `shouldBe` Nothing
  --   select fst IntT [(IntT, NumT), (NumT, IntT)] `shouldBe` Just (IntT, NumT)
  --   select fst IntT [(NumT, IntT), (IntT, NumT)] `shouldBe` Just (IntT, NumT)

  -- it "☯ infer" $ do
  --   -- let env = [("x", Int 1), ("f", Lam [("x", Num 0.0)] [Br ("x", IntT) x, Br ("y", NumT) x])]
  --   let env = [("x", Int 1), ("f", Lam [("x", Num 0.0)] ("x", IntT) x)]
  --   infer env (Any IntT) `shouldBe` (IntT, env)
  --   infer env (Int 1) `shouldBe` (IntT, env)
  --   infer env (Num 1.0) `shouldBe` (NumT, env)
  --   infer env (Var "x") `shouldBe` (IntT, env)
  --   infer env (Var "y") `shouldBe` (AnyT, env)
  --   -- infer env (Lam [] []) `shouldBe` Nothing
  --   -- infer env (Lam [] [Br ("x", NumT) x]) `shouldBe` Just (FunT [(NumT, NumT)])
  --   -- infer env (Lam [] [Br ("y", NumT) x]) `shouldBe` Just (FunT [(NumT, IntT)])
  --   infer env (App x (Num 2.0)) `shouldBe` (IntT, env)
  --   infer env (App f (Int 2)) `shouldBe` (IntT, ("x", Any IntT) : env ++ [("x", Num 0.0)])
  --   infer env (App f (Num 2.0)) `shouldBe` (IntT, ("x", Any IntT) : env ++ [("x", Num 0.0)])

  -- it "☯ reduce" $ do
  --   -- let env = [("x", Int 1), ("f", Lam [("x", Num 0.0)] [Br ("x", IntT) x, Br ("y", NumT) x])]
  --   let env = [("x", Int 1), ("f", Lam [("x", Num 0.0)] ("x", IntT) x)]
  --   let env' = [("y", Int 0)]
  --   reduce env (Int 1) `shouldBe` Int 1
  --   reduce env (Num 1.0) `shouldBe` Num 1.0
  --   reduce env (Var "x") `shouldBe` Int 1
  --   reduce env (Var "y") `shouldBe` Var "y"
  --   -- reduce env (Lam env' []) `shouldBe` Lam (env ++ env') []
  --   -- reduce env (Lam env' [Br ("x", NumT) x]) `shouldBe` Lam (env ++ env') [Br ("x", NumT) x]
  --   -- reduce env (Lam env' [Br ("y", NumT) x]) `shouldBe` Lam (env ++ env') [Br ("y", NumT) x]
  --   reduce env (App x x) `shouldBe` App (Int 1) (Int 1)
  --   reduce env (App f x) `shouldBe` Int 1
  it "☯ TODO" $ do
    True `shouldBe` True
