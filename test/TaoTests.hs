module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec (SpecWith, describe, it, shouldBe)

taoTests :: SpecWith ()
taoTests = describe "--==☯ Tao ☯==--" $ do
  let a = Var "a"
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y') = (VarP "x", VarP "y")

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
    lam [x'] y `shouldBe` Match [Case [x'] y]
    lam [x', y'] z `shouldBe` Match [Case [x', y'] z]

  it "☯ unpack" $ do
    let ctx :: Context
        ctx =
          [ ("A", UnionAlt "T" [] (Var "T")),
            ("B", UnionAlt "T" [("i", IntT), ("n", NumT)] (Var "T"))
          ]

    unpack ctx (AnyP, a) `shouldBe` Right []
    unpack ctx (VarP "x", a) `shouldBe` Right [("x", a)]
    unpack ctx (CtrP "A" [], a) `shouldBe` Right []
    unpack ctx (CtrP "B" [x'], a) `shouldBe` Left (CtrArgsMismatch "B" ["i", "n"] [VarP "x"])
    unpack ctx (CtrP "B" [x', y'], a) `shouldBe` Right [("x", Get "B" a "i"), ("y", Get "B" a "n")]

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
