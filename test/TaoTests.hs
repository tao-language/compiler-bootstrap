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

  it "☯ lam" $ do
    lam [] x `shouldBe` x
    lam [x'] y `shouldBe` Lam x' y
    lam [x', y'] z `shouldBe` Lam x' (Lam y' z)

  it "☯ unpack" $ do
    let (a, n) = (Var "a", Var "n")
    unpack (Def [] AnyP a) `shouldBe` []
    unpack (Def [] (VarP "x") a) `shouldBe` [("x", App (Match [Case [x'] x]) a)]
    unpack (Def [] (CtrP "A" []) a) `shouldBe` []
    unpack (Def [] (CtrP "B" [x', AnyP]) a) `shouldBe` [("x", App (Match [Case [CtrP "B" [x', AnyP]] x]) a)]
    unpack (Def [("x", IntT)] x' a) `shouldBe` [("x", Ann (App (Match [Case [x'] x]) a) IntT)]

    -- let boolT = Var "Bool"
    -- unpack (DefT "Bool" [] [("True", ([],boolT)), ("False", ([],boolT))]) `shouldBe` [("Bool", Typ "Bool" Knd [("True", Var "Bool"), ("False", Var "Bool")]), (), ()]

    let maybeT a = App (Var "Maybe") a
    let maybeDef = SumT [("a", Knd)] ["Just", "Nothing"]
    let justDef = Ann (Lam (VarP "x") $ Typ "Maybe" "Just" [("x", x)]) (For "a" $ Fun a (maybeT a))
    let nothingDef = Ann (Typ "Maybe" "Nothing" []) (For "a" $ maybeT a)
    unpack (DefT "Maybe" [("a", Knd)] [("Just", ([("x", a)], maybeT a)), ("Nothing", ([], maybeT a))]) `shouldBe` [("Maybe", maybeDef), ("Just", justDef), ("Nothing", nothingDef)]

    -- let vecT n a = app (Var "Vec") [n, a]
    True `shouldBe` True

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
    -- compile' (Typ "Bool" []) `shouldBe` Right (C.Typ "Bool" [])
    -- compile' (Typ "Maybe" [IntT]) `shouldBe` Right (C.Typ "Maybe" [C.IntT])
    -- compile' (Typ "T" "A" []) `shouldBe` Right (C.Typ "A" [] ["A", "B"])
    -- compile' (Typ "T" "B" [("a", x), ("b", y)]) `shouldBe` Right (C.Typ "B" [("a", C.Var "x"), ("b", C.Var "y")] ["A", "B"])
    compile' (Get "A" x "a") `shouldBe` Left (UndefinedCtrField "A" "a")
    compile' (Get "B" x "i") `shouldBe` Right (C.App (C.Var "x") (C.lam ["i", "n"] (C.Var "i")))
    compile' (Get "B" x "n") `shouldBe` Right (C.App (C.Var "x") (C.lam ["i", "n"] (C.Var "n")))
    compile' (Match []) `shouldBe` Left MissingCases
    compile' (Match [Case [] (Int 1)]) `shouldBe` Right (C.Int 1)
    compile' (Match [Case [VarP "x"] (Int 1)]) `shouldBe` Right (C.Lam "x" $ C.Int 1)
    compile' (Match [Case [VarP "x"] (Int 1), Case [] (Int 2)]) `shouldBe` Left (MatchMissingArgs (Int 2))
    compile' (Match [Case [CtrP "A" []] (Int 1)]) `shouldBe` Left MissingCases
    compile' (Match [Case [CtrP "A" []] (Int 1), Case [x'] (Int 2)]) `shouldBe` Right (C.Lam "x" $ C.app (C.Var "x") [C.Int 1, C.lam ["_", "_"] $ C.Int 2])
    compile' (Match [Case [CtrP "B" [x', y']] (Int 1), Case [z'] (Int 2)]) `shouldBe` Right (C.Lam "z" $ C.app (C.Var "z") [C.Int 2, C.lam ["x", "y"] $ C.Int 1])
