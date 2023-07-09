module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec (SpecWith, describe, it, shouldBe)

taoTests :: SpecWith ()
taoTests = describe "--==☯ Tao ☯==--" $ do
  let a = Var "a"
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (VarP "x", VarP "y", VarP "z")

  it "☯ for" $ do
    for [] x `shouldBe` x
    for ["x"] y `shouldBe` For "x" y
    for ["x", "y"] z `shouldBe` For "x" (For "y" z)

  it "☯ fun" $ do
    fun [] x `shouldBe` x
    fun [x] y `shouldBe` Fun x y
    fun [x, y] z `shouldBe` Fun x (Fun y z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  -- it "☯ lam" $ do
  --   lam [] x `shouldBe` x
  --   lam [x'] y `shouldBe` Lam x' y
  --   lam [x', y'] z `shouldBe` Lam x' (Lam y' z)

  it "☯ toCore" $ do
    toCore (Int 1) `shouldBe` Right (C.Int 1)
    toCore (Num 1) `shouldBe` Right (C.Num 1)
    toCore (Var "x") `shouldBe` Right (C.Var "x")
    toCore (For "x" y) `shouldBe` Right (C.For "x" (C.Var "y"))
    toCore (Fun x y) `shouldBe` Right (C.Fun (C.Var "x") (C.Var "y"))
    toCore (App x y) `shouldBe` Right (C.App (C.Var "x") (C.Var "y"))
    toCore (Ann x y) `shouldBe` Right (C.Ann (C.Var "x") (C.Var "y"))
    toCore (Let [Untyped "x" y] z) `shouldBe` Right (C.Let [("x", C.Var "y")] (C.Var "z"))
    toCore (Ctr "A" []) `shouldBe` Right (C.Ctr "A" [])
    toCore (Ctr "B" [x, y]) `shouldBe` Right (C.Ctr "B" [C.Var "x", C.Var "y"])
    toCore (Case x [("A", y)] z) `shouldBe` Right (C.Case (C.Var "x") [("A", C.Var "y")] (C.Var "z"))
    toCore (CaseI x [(1, y)] z) `shouldBe` Right (C.CaseI (C.Var "x") [(1, C.Var "y")] (C.Var "z"))
    toCore (Match []) `shouldBe` Left (TypeError C.EmptyCase)
    toCore (Match [Br [] (Int 1)]) `shouldBe` Right (C.Int 1)
    toCore (Match [Br [VarP "x"] (Int 1)]) `shouldBe` Right (C.Lam "x" $ C.Int 1)
    toCore (Match [Br [VarP "x"] (Int 1), Br [] (Int 2)]) `shouldBe` Left (TypeError C.MatchNumPatternsMismatch)

-- it "☯ unpack" $ do
--   let (a, n) = (Var "a", Var "n")
--   unpack (Def [] AnyP a) `shouldBe` []
--   unpack (Def [] (VarP "x") a) `shouldBe` [("x", App (Lam "x" x) a)]
--   unpack (Def [] (CtrP "A" []) a) `shouldBe` []
--   unpack (Def [] (CtrP "B" [x', AnyP]) a) `shouldBe` [("x", App (Match [Br [CtrP "B" [x', AnyP]] x]) a)]
--   unpack (Def [("x", IntT)] x' a) `shouldBe` [("x", Ann (App (Lam "x" x) a) IntT)]

--   -- let boolT = Var "Bool"
--   -- unpack (DefT "Bool" [] [("True", ([],boolT)), ("False", ([],boolT))]) `shouldBe` [("Bool", Typ "Bool" Knd [("True", Var "Bool"), ("False", Var "Bool")]), (), ()]

--   let maybeT a = App (Var "Maybe") a
--   let maybeDef = Typ "Maybe" [("a", Knd)] ["Just", "Nothing"]
--   let justDef = Ann (Lam "x" $ Ctr "Just" [x]) (For "a" $ Fun a (maybeT a))
--   let nothingDef = Ann (Ctr "Nothing" []) (For "a" $ maybeT a)
--   unpack (DefT "Maybe" [("a", Knd)] [("Just", ([("x", a)], maybeT a)), ("Nothing", ([], maybeT a))]) `shouldBe` [("Maybe", maybeDef), ("Just", justDef), ("Nothing", nothingDef)]

--   -- let vecT n a = app (Var "Vec") [n, a]
--   True `shouldBe` True

-- it "☯ findPatternsType" $ do
--   let env =
--         [ ("T", Typ "T" [] ["A"]),
--           ("A", Ann (Ctr "A" []) (Var "T"))
--         ]

--   let findPatternsType' = findPatternsType [] env
--   findPatternsType' [] `shouldBe` Right Nothing
--   findPatternsType' [[CtrP "A" []]] `shouldBe` Right (Just "T")

-- it "☯ toCoreEnv" $ do
--   let env =
--         [ ("T", Typ "T" [] ["A", "B"]),
--           ("A", Ann (Ctr "A" []) (Var "T")),
--           ("B", Ann (Lam "x" $ Ctr "B" [Var "x"]) (Fun IntT (Var "T")))
--         ]

--   let toCoreEnv' env = toCoreEnv [] env env
--   toCoreEnv' [] `shouldBe` Right []
--   toCoreEnv' [("T", Typ "T" [] ["A"])] `shouldBe` Right [("T", C.Typ "T" [] ["A"])]
--   -- toCoreEnv' [("B", Ann (Lam (VarP "x") $ Ctr "B" [Var "x"]) (Fun IntT (Var "T")))] `shouldBe` Right [("T", C.Typ "T" [] ["A"])]
--   -- toCoreEnv' [("B", (Lam (VarP "x") $ Ctr "B" [Var "x"]))] `shouldBe` Right [("T", C.Typ "T" [] ["A"])]
--   toCoreEnv' [("B", Ctr "B" [Var "x"])] `shouldBe` Right [("B", C.Ctr "B" [C.Var "x"])]

-- -- it "☯ expandUnionAlt" $ do
-- --   let env =
-- --         [ ("T", Typ "T" [] ["A", "B"]),
-- --           ("A", Ann (Ctr "A" []) (Var "T")),
-- --           ("B", Ann (Lam (VarP "x") $ Ctr "B" [Var "x"]) (Fun IntT (Var "T")))
-- --         ]

-- --   let expandUnionAlt' = expandUnionAlt [] env
-- --   expandUnionAlt' "A" `shouldBe` Right ([], Typ "T" [] ["A", "B"])
-- -- -- expandUnionAlt' "A" `shouldBe` Right ([IntT], Typ "T" [] ["A", "B"])
