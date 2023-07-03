module CoreTests where

import Core
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--==☯️ Core language ☯️==--" $ do
  let ops :: Ops
      ops =
        [ ("+", add),
          ("-", sub),
          ("*", mul),
          ("==", eq)
        ]

      add :: Operator
      add [Int a, Int b] = Just (Int (a + b))
      add [Op "+" [a, Int b1], Int b2] = Just (Op "+" [a, Int (b1 + b2)])
      add [Op "+" [Int b1, a], Int b2] = Just (Op "+" [a, Int (b1 + b2)])
      add [Int b1, Op "+" [a, Int b2]] = Just (Op "+" [a, Int (b1 + b2)])
      add [Int b1, Op "+" [Int b2, a]] = Just (Op "+" [a, Int (b1 + b2)])
      add _ = Nothing

      sub :: Operator
      sub [Int a, Int b] = Just (Int (a - b))
      sub _ = Nothing

      mul :: Operator
      mul [Int a, Int b] = Just (Int (a * b))
      mul _ = Nothing

      eq :: Operator
      eq [Int a, Int b] | a == b = Just (Var "True")
      eq [Int _, Int _] = Just (Var "False")
      eq _ = Nothing

  it "☯ eval" $ do
    let (x, y) = (Var "x", Var "y")
    let (a, b) = (Var "a", Var "b")
    let env :: Env
        env =
          [ ("x", Int 1),
            ("a", IntT),
            ("b", NumT)
          ]

    let eval' = eval ops env
    eval' Typ `shouldBe` Typ
    eval' IntT `shouldBe` IntT
    eval' NumT `shouldBe` NumT
    eval' (Int 1) `shouldBe` Int 1
    eval' (Num 1.1) `shouldBe` Num 1.1
    eval' (Var "A") `shouldBe` Var "A"
    eval' (Var "x") `shouldBe` Int 1
    eval' (Var "y") `shouldBe` Var "y"
    eval' (For "x" x) `shouldBe` For "x" x
    eval' (For "y" x) `shouldBe` Int 1
    eval' (Lam "x" x) `shouldBe` Lam "x" x
    eval' (Lam "y" x) `shouldBe` Lam "y" (Int 1)
    eval' (Fun a b) `shouldBe` Fun IntT NumT
    eval' (App (Var "A") x) `shouldBe` App (Var "A") (Int 1)
    eval' (App (Lam "y" y) x) `shouldBe` Int 1
    eval' (Op "+" [x, y]) `shouldBe` Op "+" [Int 1, y]
    eval' (Op "+" [x, Int 2]) `shouldBe` Int 3
    eval' (Op "-" [x, Int 2]) `shouldBe` Int (-1)
    eval' (Op "*" [x, Int 2]) `shouldBe` Int 2
    eval' (Op "==" [x, Int 1]) `shouldBe` Var "True"
    eval' (Op "==" [x, Int 2]) `shouldBe` Var "False"

  -- it "☯ occurs" $ do
  -- it "☯ unify" $ do

  it "☯ infer" $ do
    let a = Var "a"
    let (x, y) = (Var "x", Var "y")
    let xT = Var "xT"
    let (f, g) = (Var "f", Var "g")
    let ctx :: Context
        ctx =
          [ ("inferred", Value $ Int 1),
            ("mismatch", Value $ Ann (Int 1) NumT),
            ("match", Value $ Ann (Int 1) IntT),
            ("typed", Value $ Ann (Var "typed") IntT),
            ("free", Value $ Var "free"),
            ("x", Value $ Int 1),
            ("y", Value $ Num 1.1),
            ("f", Value $ Ann f (Fun IntT NumT)),
            ("g", Value $ Ann g (For "a" $ Fun a a)),
            ("op0", Value $ Ann (Var "op0") IntT),
            ("op1", Value $ Ann (Var "op1") (Fun IntT NumT))
          ]

    let infer' = infer ops ctx
    infer' Typ `shouldBe` Right (Typ, ctx)
    infer' IntT `shouldBe` Right (Typ, ctx)
    infer' (Int 1) `shouldBe` Right (IntT, ctx)
    infer' NumT `shouldBe` Right (Typ, ctx)
    infer' (Num 1) `shouldBe` Right (NumT, ctx)
    infer' (Var "undefined") `shouldBe` Left (UndefinedVar "undefined")
    infer' (Var "inferred") `shouldBe` Right (IntT, ctx)
    infer' (Var "mismatch") `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (Var "match") `shouldBe` Right (IntT, ctx)
    infer' (Var "typed") `shouldBe` Right (IntT, ctx)
    infer' (Var "free") `shouldBe` Right (Typ, ctx)
    infer' (Var "x") `shouldBe` Right (IntT, ctx)
    infer' (Var "y") `shouldBe` Right (NumT, ctx)
    infer' (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer' (Var "f") `shouldBe` Right (Fun IntT NumT, ctx)
    infer' (Var "g") `shouldBe` Right (For "a" $ Fun a a, ctx)
    infer' (For "x" (Int 1)) `shouldBe` Right (IntT, ctx)
    infer' (For "x" x) `shouldBe` Right (For "xT" xT, ctx)
    infer' (Lam "x" x) `shouldBe` Right (For "xT" $ Fun xT xT, ctx)
    infer' (Fun (Int 1) (Num 1.1)) `shouldBe` Left (TypeMismatch IntT Typ)
    infer' (Fun IntT (Num 1.1)) `shouldBe` Left (TypeMismatch NumT Typ)
    infer' (Fun IntT NumT) `shouldBe` Right (Typ, ctx)
    infer' (App x y) `shouldBe` Left (TypeMismatch (Fun NumT (Var "t")) IntT)
    infer' (App f y) `shouldBe` Left (TypeMismatch NumT IntT)
    infer' (App f x) `shouldBe` Right (NumT, ctx)
    infer' (App g x) `shouldBe` Right (IntT, ctx)
    infer' (Op "op0" []) `shouldBe` Right (IntT, ctx)
    infer' (Op "op0" [Num 1.1]) `shouldBe` Left (TypeMismatch (Fun NumT (Var "t")) IntT)
    infer' (Op "op1" [Num 1.1]) `shouldBe` Left (TypeMismatch NumT IntT)
    infer' (Op "op1" [Int 1]) `shouldBe` Right (NumT, ctx)

  let boolT = Ctr "Bool" []
  let boolctx :: Context
      boolctx =
        [ ("Bool", UnionType [] ["True", "False"]),
          ("False", UnionAlt [] ("Bool", [])),
          ("True", UnionAlt [] ("Bool", []))
        ]

  it "☯ Bool" $ do
    let case' a = Case a [("True", Int 1)] (Int 0)
    let ctx = boolctx

    let eval' = eval ops (envOf ctx)
    eval' (case' (Ctr "False" [])) `shouldBe` Int 0
    eval' (case' (Ctr "True" [])) `shouldBe` Int 1

    let infer' = infer ops ctx
    infer' (Var "Bool") `shouldBe` Right (Typ, ctx)
    infer' (Var "False") `shouldBe` Right (boolT, ctx)
    infer' (Var "True") `shouldBe` Right (boolT, ctx)
    infer' (case' (Var "False")) `shouldBe` Right (IntT, ctx)
    infer' (case' (Var "True")) `shouldBe` Right (IntT, ctx)

  it "☯ Maybe" $ do
    let a = Var "a"
    let maybeT a = Ctr "Maybe" [a]
    let case' a = Case a [("Just", Lam "x" (Var "x"))] (Int 0)
    let ctx :: Context
        ctx =
          [ ("Maybe", UnionType [("a", Typ)] ["Just", "Nothing"]),
            ("Nothing", UnionAlt [] ("Maybe", [Var "a"])),
            ("Just", UnionAlt [("x", Var "a")] ("Maybe", [Var "a"]))
          ]

    let eval' = eval ops (envOf ctx)
    eval' (case' (Ctr "Nothing" [])) `shouldBe` Int 0
    eval' (case' (Ctr "Just" [Int 1])) `shouldBe` Int 1

    let infer' = infer ops ctx
    infer' (app (Var "Maybe") []) `shouldBe` Right (Fun Typ Typ, ctx)
    infer' (app (Var "Maybe") [IntT]) `shouldBe` Right (Typ, ctx)
    infer' (app (Var "Nothing") []) `shouldBe` Right (For "a" $ maybeT a, ctx)
    infer' (app (Var "Just") []) `shouldBe` Right (For "a" $ Fun a (maybeT a), ctx)
    infer' (app (Var "Just") [Int 1]) `shouldBe` Right (maybeT IntT, ctx)
    infer' (case' (Ctr "Nothing" [])) `shouldBe` Right (IntT, ctx)
    infer' (case' (Ctr "Just" [Int 1])) `shouldBe` Right (IntT, ctx)
    infer' (case' (Ctr "Just" [Num 1.1])) `shouldBe` Left (TypeMismatch NumT IntT)

  it "☯ Nat" $ do
    let natT = Ctr "Nat" []
    let case' a = Case a [("Succ", Lam "x" (Int 1))] (Int 0)
    let ctx :: Context
        ctx =
          [ ("Nat", UnionType [] ["Zero", "Succ"]),
            ("Zero", UnionAlt [] ("Nat", [])),
            ("Succ", UnionAlt [("n", Var "Nat")] ("Nat", []))
          ]

    let eval' = eval ops (envOf ctx)
    eval' (case' (Ctr "Zero" [])) `shouldBe` Int 0
    eval' (case' (Ctr "Succ" [Var "Zero"])) `shouldBe` Int 1

    let infer' = infer ops ctx
    infer' (Var "Nat") `shouldBe` Right (Typ, ctx)
    infer' (Var "Zero") `shouldBe` Right (natT, ctx)
    infer' (Var "Succ") `shouldBe` Right (Fun natT natT, ctx)
    infer' (App (Var "Succ") (Var "Zero")) `shouldBe` Right (natT, ctx)
    infer' (Ctr "Succ" []) `shouldBe` Right (Fun natT natT, ctx)
    infer' (Ctr "Succ" [Var "Zero"]) `shouldBe` Right (natT, ctx)
    infer' (case' (Ctr "Zero" [])) `shouldBe` Right (IntT, ctx)
    infer' (case' (Ctr "Succ" [Var "Zero"])) `shouldBe` Right (IntT, ctx)

  it "☯ Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let vecT n a = Ctr "Vec" [n, a]
    let case' a = Case a [("Cons", lam ["x", "xs"] (Var "x"))] (Int 0)
    let ctx :: Context
        ctx =
          [ ("Vec", UnionType [("n", IntT), ("a", Typ)] ["Nil", "Cons"]),
            ("Nil", UnionAlt [] ("Vec", [Int 0, a])),
            ("Cons", UnionAlt [("x", a), ("xs", vecT n a)] ("Vec", [Op "+" [n, Int 1], a]))
          ]

    let eval' = eval ops (envOf ctx)
    eval' (case' (Var "Nil")) `shouldBe` Int 0
    eval' (case' (Ctr "Cons" [Int 1, Var "Nil"])) `shouldBe` Int 1
    eval' (case' (Ctr "Cons" [Int 2, Var "Nil"])) `shouldBe` Int 2

    let infer' = infer ops ctx
    infer' (app (Var "Vec") []) `shouldBe` Right (fun [IntT, Typ] Typ, ctx)
    infer' (app (Var "Vec") [Int 0]) `shouldBe` Right (Fun Typ Typ, ctx)
    infer' (app (Var "Vec") [Int 0, NumT]) `shouldBe` Right (Typ, ctx)
    infer' (Var "Nil") `shouldBe` Right (For "a" $ vecT (Int 0) a, ctx)
    infer' (Var "Cons") `shouldBe` Right (for ["n", "a"] $ fun [a, vecT n a] (vecT (Op "+" [n, Int 1]) a), ctx)
    infer' (Ctr "Cons" []) `shouldBe` Right (for ["n", "a"] $ fun [a, vecT n a] (vecT (Op "+" [n, Int 1]) a), ctx)
    infer' (Ctr "Cons" [Int 42]) `shouldBe` Right (For "n" $ fun [vecT n IntT] (vecT (Op "+" [n, Int 1]) IntT), ctx)
    infer' (Ctr "Cons" [Int 42, Var "Nil"]) `shouldBe` Right (vecT (Int 1) IntT, ctx)
    infer' (case' (Var "Nil")) `shouldBe` Right (IntT, ctx)
    infer' (case' (Ctr "Cons" [Int 42, Var "Nil"])) `shouldBe` Right (IntT, ctx)

  it "☯ factorial" $ do
    let i1 = Int 1
    let (f, n) = (Var "f", Var "n")
    let mul a b = app (Var "*") [a, b]
    let sub a b = app (Var "-") [a, b]

    let ctx :: Context
        ctx =
          ("f", Value $ Fix "f" $ Lam "n" (CaseI (Var "n") [(0, i1)] (n `mul` App f (n `sub` i1)))) :
          ("+", Value $ Ann (op2 "+") (fun [IntT, IntT] IntT)) :
          ("-", Value $ Ann (op2 "-") (fun [IntT, IntT] IntT)) :
          ("*", Value $ Ann (op2 "*") (fun [IntT, IntT] IntT)) :
          ("==", Value $ Ann (op2 "==") (fun [IntT, IntT] (Var "Bool"))) :
          boolctx
          where
            op2 op = lam ["x", "y"] (Op op [Var "x", Var "y"])

    let eval' = eval ops (envOf ctx)
    -- eval' (Var "f") `shouldBe` Fix "f" (Lam "n" $ app (Op "==" [n, i0]) [Op "*" [n, App f (Op "-" [n, i1])], Int 1])
    -- eval' (App f n) `shouldBe` app (Op "==" [n, i0]) [Int 0, Op "*" [n, App f (Op "-" [n, i1])]]
    eval' (App f (Int 0)) `shouldBe` Int 1
    eval' (App f (Int 1)) `shouldBe` Int 1
    eval' (App f (Int 2)) `shouldBe` Int 2
    eval' (App f (Int 3)) `shouldBe` Int 6
    eval' (App f (Int 4)) `shouldBe` Int 24
    eval' (App f (Int 5)) `shouldBe` Int 120

    let infer' = infer ops ctx
    infer' (Var "f") `shouldBe` Right (Fun IntT IntT, ctx)
    infer' (App f (Int 0)) `shouldBe` Right (IntT, ctx)

  it "☯ match" $ do
    let (x, x1) = (Var "x", Var "x1")
    let (x', y') = (VarP "x", VarP "y")
    let (i1, i2) = (Int 1, Int 2)
    match [] `shouldBe` Left EmptyCase
    match [Br [] i1] `shouldBe` Right i1
    match [Br [] i1, Br [] i2] `shouldBe` Right i1
    match [Br [VarP "x"] i1, Br [y'] i2] `shouldBe` Right (Lam "x" i1)
    match [Br [IntP 0] i1, Br [y'] i2] `shouldBe` Right (Lam "y" (CaseI (Var "y") [(0, i1)] i2))
    match [Br [CtrP "A" []] i1, Br [y'] i2] `shouldBe` Right (Lam "y" $ Case (Var "y") [("A", i1)] i2)
    match [Br [CtrP "B" [x']] i1, Br [y'] i2] `shouldBe` Right (Lam "y" $ Case (Var "y") [("B", Lam "x" i1)] i2)

    -- Name shadowing.
    match [Br [y'] x, Br [x'] x] `shouldBe` Right (Lam "y" x)
    match [Br [x'] x, Br [y'] x] `shouldBe` Right (Lam "x1" $ Let [("x", x1)] x)
