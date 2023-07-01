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

  it "☯ unpack" $ do
    let (a, n) = (Var "a", Var "n")
    unpack (Def [] AnyP a) `shouldBe` []
    unpack (Def [] (VarP "x") a) `shouldBe` [("x", App (Lam "x" x) a)]
    unpack (Def [] (CtrP "A" []) a) `shouldBe` []
    unpack (Def [] (CtrP "B" [x', AnyP]) a) `shouldBe` [("x", App (Match [Br [CtrP "B" [x', AnyP]] x]) a)]
    unpack (Def [("x", IntT)] x' a) `shouldBe` [("x", Ann (App (Lam "x" x) a) IntT)]

    -- let boolT = Var "Bool"
    -- unpack (DefT "Bool" [] [("True", ([],boolT)), ("False", ([],boolT))]) `shouldBe` [("Bool", Typ "Bool" Knd [("True", Var "Bool"), ("False", Var "Bool")]), (), ()]

    let maybeT a = App (Var "Maybe") a
    let maybeDef = Typ "Maybe" [("a", Knd)] ["Just", "Nothing"]
    let justDef = Ann (Lam "x" $ Ctr "Just" [x]) (For "a" $ Fun a (maybeT a))
    let nothingDef = Ann (Ctr "Nothing" []) (For "a" $ maybeT a)
    unpack (DefT "Maybe" [("a", Knd)] [("Just", ([("x", a)], maybeT a)), ("Nothing", ([], maybeT a))]) `shouldBe` [("Maybe", maybeDef), ("Just", justDef), ("Nothing", nothingDef)]

    -- let vecT n a = app (Var "Vec") [n, a]
    True `shouldBe` True

  it "☯ findPatternsType" $ do
    let env =
          [ ("T", Typ "T" [] ["A"]),
            ("A", Ann (Ctr "A" []) (Var "T"))
          ]

    let findPatternsType' = findPatternsType [] env
    findPatternsType' [] `shouldBe` Right Nothing
    findPatternsType' [[CtrP "A" []]] `shouldBe` Right (Just "T")

  it "☯ compileEnv" $ do
    let env =
          [ ("T", Typ "T" [] ["A", "B"]),
            ("A", Ann (Ctr "A" []) (Var "T")),
            ("B", Ann (Lam "x" $ Ctr "B" [Var "x"]) (Fun IntT (Var "T")))
          ]

    let compileEnv' env = compileEnv [] env env
    compileEnv' [] `shouldBe` Right []
    compileEnv' [("T", Typ "T" [] ["A"])] `shouldBe` Right [("T", C.Typ "T" [] ["A"])]
    -- compileEnv' [("B", Ann (Lam (VarP "x") $ Ctr "B" [Var "x"]) (Fun IntT (Var "T")))] `shouldBe` Right [("T", C.Typ "T" [] ["A"])]
    -- compileEnv' [("B", (Lam (VarP "x") $ Ctr "B" [Var "x"]))] `shouldBe` Right [("T", C.Typ "T" [] ["A"])]
    compileEnv' [("B", Ctr "B" [Var "x"])] `shouldBe` Right [("B", C.Ctr "B" [C.Var "x"])]

  -- it "☯ expandUnionAlt" $ do
  --   let env =
  --         [ ("T", Typ "T" [] ["A", "B"]),
  --           ("A", Ann (Ctr "A" []) (Var "T")),
  --           ("B", Ann (Lam (VarP "x") $ Ctr "B" [Var "x"]) (Fun IntT (Var "T")))
  --         ]

  --   let expandUnionAlt' = expandUnionAlt [] env
  --   expandUnionAlt' "A" `shouldBe` Right ([], Typ "T" [] ["A", "B"])
  -- -- expandUnionAlt' "A" `shouldBe` Right ([IntT], Typ "T" [] ["A", "B"])

  it "☯ compile" $ do
    let ops = []
    let env :: Env
        env =
          [ ("T", Typ "T" [] ["A", "B"]),
            ("A", Ann (Ctr "A" []) (Var "T")),
            ("B", Ann (lam ["i", "n"] $ Ctr "B" [Var "i", Var "n"]) (fun [IntT, NumT] (Var "T"))),
            ("U", Typ "U" [] ["C"]),
            ("C", Ann (lam ["i", "n"] $ Ctr "C" [Var "i", Var "n"]) (fun [IntT, NumT] (Var "U")))
          ]

    let compile' = compile ops env
    compile' Knd `shouldBe` Right C.Knd
    compile' IntT `shouldBe` Right C.IntT
    compile' NumT `shouldBe` Right C.NumT
    compile' (Int 1) `shouldBe` Right (C.Int 1)
    compile' (Num 1) `shouldBe` Right (C.Num 1)
    compile' (Var "x") `shouldBe` Right (C.Var "x")
    compile' (For "x" y) `shouldBe` Right (C.For "x" (C.Var "y"))
    compile' (Fun x y) `shouldBe` Right (C.Fun (C.Var "x") (C.Var "y"))
    compile' (App x y) `shouldBe` Right (C.App (C.Var "x") (C.Var "y"))
    -- TODO: Ctr
    -- compile' (Typ "Bool" []) `shouldBe` Right (C.Typ "Bool" [])
    -- compile' (Typ "Maybe" [IntT]) `shouldBe` Right (C.Typ "Maybe" [C.IntT])
    -- compile' (Typ "T" "A" []) `shouldBe` Right (C.Typ "A" [] ["A", "B"])
    -- compile' (Typ "T" "B" [("a", x), ("b", y)]) `shouldBe` Right (C.Typ "B" [("a", C.Var "x"), ("b", C.Var "y")] ["A", "B"])
    -- compile' (Get "A" x "a") `shouldBe` Left (UndefinedCtrField "A" "a")
    -- compile' (Get "B" x "i") `shouldBe` Right (C.App (C.Var "x") (C.lam ["i", "n"] (C.Var "i")))
    -- compile' (Get "B" x "n") `shouldBe` Right (C.App (C.Var "x") (C.lam ["i", "n"] (C.Var "n")))
    compile' (Match []) `shouldBe` Left EmptyMatch
    compile' (Match [Br [] (Int 1)]) `shouldBe` Right (C.Int 1)
    compile' (Match [Br [VarP "x"] (Int 1)]) `shouldBe` Right (C.Lam "x" $ C.Int 1)
    compile' (Match [Br [VarP "x"] (Int 1), Br [] (Int 2)]) `shouldBe` Left (MatchMissingArgs (Int 2))
    -- compile' (Match [Br [CtrP "A" []] (Int 1)]) `shouldBe` Left MissingBrs
    -- compile' (Match [Br [CtrP "A" []] (Int 1), Br [x'] (Int 2)]) `shouldBe` Right (C.Lam "x" $ C.app (C.Var "x") [C.Int 1, C.lam ["_", "_"] $ C.Int 2])
    -- compile' (Match [Br [CtrP "B" [x', y']] (Int 1), Br [z'] (Int 2)]) `shouldBe` Right (C.Lam "z" $ C.app (C.Var "z") [C.Int 2, C.lam ["x", "y"] $ C.Int 1])
    True `shouldBe` True
