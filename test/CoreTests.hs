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
    eval' Knd `shouldBe` Knd
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
    let env :: Env
        env =
          [ ("inferred", Int 1),
            ("mismatch", Ann (Int 1) NumT),
            ("match", Ann (Int 1) IntT),
            ("typed", Ann (Var "typed") IntT),
            ("free", Var "free"),
            ("x", Int 1),
            ("y", Num 1.1),
            ("f", Ann f (Fun IntT NumT)),
            ("g", Ann g (For "a" $ Fun a a)),
            ("op0", Ann (Var "op0") IntT),
            ("op1", Ann (Var "op1") (Fun IntT NumT))
          ]

    let infer' = infer ops env
    infer' Knd `shouldBe` Right (Knd, env)
    infer' IntT `shouldBe` Right (Knd, env)
    infer' (Int 1) `shouldBe` Right (IntT, env)
    infer' NumT `shouldBe` Right (Knd, env)
    infer' (Num 1) `shouldBe` Right (NumT, env)
    infer' (Var "undefined") `shouldBe` Left (UndefinedVar "undefined")
    infer' (Var "inferred") `shouldBe` Right (IntT, env)
    infer' (Var "mismatch") `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (Var "match") `shouldBe` Right (IntT, env)
    infer' (Var "typed") `shouldBe` Right (IntT, env)
    infer' (Var "free") `shouldBe` Right (Knd, env)
    infer' (Var "x") `shouldBe` Right (IntT, env)
    infer' (Var "y") `shouldBe` Right (NumT, env)
    infer' (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer' (Var "f") `shouldBe` Right (Fun IntT NumT, env)
    infer' (Var "g") `shouldBe` Right (For "a" $ Fun a a, env)
    infer' (For "x" (Int 1)) `shouldBe` Right (IntT, env)
    infer' (For "x" x) `shouldBe` Right (For "xT" xT, env)
    infer' (Lam "x" x) `shouldBe` Right (For "xT" $ Fun xT xT, env)
    infer' (Fun (Int 1) (Num 1.1)) `shouldBe` Left (TypeMismatch IntT Knd)
    infer' (Fun IntT (Num 1.1)) `shouldBe` Left (TypeMismatch NumT Knd)
    infer' (Fun IntT NumT) `shouldBe` Right (Knd, env)
    infer' (App x y) `shouldBe` Left (TypeMismatch (Fun NumT (Var "t")) IntT)
    infer' (App f y) `shouldBe` Left (TypeMismatch NumT IntT)
    infer' (App f x) `shouldBe` Right (NumT, env)
    infer' (App g x) `shouldBe` Right (IntT, env)
    infer' (Op "op0" []) `shouldBe` Right (IntT, env)
    infer' (Op "op0" [Num 1.1]) `shouldBe` Left (TypeMismatch (Fun NumT (Var "t")) IntT)
    infer' (Op "op1" [Num 1.1]) `shouldBe` Left (TypeMismatch NumT IntT)
    infer' (Op "op1" [Int 1]) `shouldBe` Right (NumT, env)

  let boolT = Typ "Bool" [] ["True", "False"]
  let boolenv :: Env
      boolenv =
        [ ("Bool", Ann boolT Knd),
          ("False", Ann (Ctr "False" []) (Var "Bool")),
          ("True", Ann (Ctr "True" []) (Var "Bool"))
        ]

  it "☯ Bool" $ do
    let case' a = Case a [("True", Int 1)] (Int 0)
    let env = boolenv

    let eval' = eval ops env
    eval' (case' (Ctr "False" [])) `shouldBe` Int 0
    eval' (case' (Ctr "True" [])) `shouldBe` Int 1

    let infer' = infer ops env
    infer' (Var "Bool") `shouldBe` Right (Knd, env)
    infer' (Var "False") `shouldBe` Right (boolT, env)
    infer' (Var "True") `shouldBe` Right (boolT, env)
    infer' (case' (Var "False")) `shouldBe` Right (IntT, env)
    infer' (case' (Var "True")) `shouldBe` Right (IntT, env)

  it "☯ Maybe" $ do
    let a = Var "a"
    let maybeT a = Typ "Maybe" [("a", a)] ["Just", "Nothing"]
    let case' a = Case a [("Just", Lam "x" (Var "x"))] (Int 0)
    let env :: Env
        env =
          [ ("Maybe", Ann (Lam "a" $ maybeT a) (Fun Knd Knd)),
            ("Nothing", Ann (Ctr "Nothing" []) (For "a" $ App (Var "Maybe") a)),
            ("Just", Ann (Lam "x" (Ctr "Just" [Var "x"])) (For "a" $ Fun a (App (Var "Maybe") a)))
          ]

    let eval' = eval ops env
    eval' (case' (Ctr "Nothing" [])) `shouldBe` Int 0
    eval' (case' (Ctr "Just" [Int 1])) `shouldBe` Int 1

    let infer' = infer ops env
    infer' (Var "Maybe") `shouldBe` Right (Fun Knd Knd, env)
    infer' (Var "Nothing") `shouldBe` Right (For "a" $ maybeT a, env)
    infer' (Var "Just") `shouldBe` Right (For "a" $ Fun a (maybeT a), env)
    infer' (app (Var "Maybe") [IntT]) `shouldBe` Right (Knd, env)
    infer' (app (Var "Just") [Int 1]) `shouldBe` Right (maybeT IntT, env)
    infer' (case' (Ctr "Nothing" [])) `shouldBe` Right (IntT, env)
    infer' (case' (Ctr "Just" [Int 1])) `shouldBe` Right (IntT, env)
    infer' (case' (Ctr "Just" [Num 1.1])) `shouldBe` Left (TypeMismatch NumT IntT)

  it "☯ Nat" $ do
    let natT = Typ "Nat" [] ["Zero", "Succ"]
    let case' a = Case a [("Succ", Lam "x" (Int 1))] (Int 0)
    let env :: Env
        env =
          [ ("Nat", Ann natT Knd),
            ("Zero", Ann (Ctr "Zero" []) (Var "Nat")),
            ("Succ", Ann (Lam "n" (Ctr "Succ" [Var "n"])) (Fun (Var "Nat") (Var "Nat")))
          ]

    let eval' = eval ops env
    eval' (case' (Ctr "Zero" [])) `shouldBe` Int 0
    eval' (case' (Ctr "Succ" [Var "Zero"])) `shouldBe` Int 1

    let infer' = infer ops env
    infer' (Var "Nat") `shouldBe` Right (Knd, env)
    infer' (Var "Zero") `shouldBe` Right (natT, env)
    infer' (Var "Succ") `shouldBe` Right (Fun natT natT, env)
    infer' (App (Var "Succ") (Var "Zero")) `shouldBe` Right (natT, env)
    infer' (Ctr "Succ" []) `shouldBe` Right (Fun natT natT, env)
    infer' (Ctr "Succ" [Var "Zero"]) `shouldBe` Right (natT, env)
    infer' (case' (Ctr "Zero" [])) `shouldBe` Right (IntT, env)
    infer' (case' (Ctr "Succ" [Var "Zero"])) `shouldBe` Right (IntT, env)

  it "☯ Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let vecT n a = Typ "Vec" [("n", n), ("a", a)] ["Cons", "Nil"]
    let case' a = Case a [("Cons", lam ["x", "xs"] (Var "x"))] (Int 0)
    let env :: Env
        env =
          [ ("Vec", Ann (lam ["n", "a"] (vecT n a)) (fun [IntT, Knd] Knd)),
            ("Nil", Ann (Ctr "Nil" []) (For "a" $ app (Var "Vec") [Int 0, a])),
            ("Cons", Ann (lam ["x", "xs"] (Ctr "Cons" [Var "x", Var "xs"])) (for ["n", "a"] $ fun [a, app (Var "Vec") [n, a]] $ app (Var "Vec") [Op "+" [n, Int 1], a]))
          ]

    let eval' = eval ops env
    eval' (case' (Var "Nil")) `shouldBe` Int 0
    eval' (case' (Ctr "Cons" [Int 1, Var "Nil"])) `shouldBe` Int 1
    eval' (case' (Ctr "Cons" [Int 2, Var "Nil"])) `shouldBe` Int 2

    let infer' = infer ops env
    infer' (app (Var "Vec") []) `shouldBe` Right (fun [IntT, Knd] Knd, env)
    infer' (app (Var "Vec") [Int 0]) `shouldBe` Right (Fun Knd Knd, env)
    infer' (app (Var "Vec") [Int 0, NumT]) `shouldBe` Right (Knd, env)
    infer' (Var "Nil") `shouldBe` Right (For "a" $ vecT (Int 0) a, env)
    infer' (Var "Cons") `shouldBe` Right (for ["n", "a"] $ fun [a, vecT n a] (vecT (Op "+" [n, Int 1]) a), env)
    infer' (Ctr "Cons" []) `shouldBe` Right (for ["n", "a"] $ fun [a, vecT n a] (vecT (Op "+" [n, Int 1]) a), env)
    infer' (Ctr "Cons" [Int 42]) `shouldBe` Right (For "n" $ fun [vecT n IntT] (vecT (Op "+" [n, Int 1]) IntT), env)
    infer' (Ctr "Cons" [Int 42, Var "Nil"]) `shouldBe` Right (vecT (Int 1) IntT, env)
    infer' (case' (Var "Nil")) `shouldBe` Right (IntT, env)
    infer' (case' (Ctr "Cons" [Int 42, Var "Nil"])) `shouldBe` Right (IntT, env)

  it "☯ factorial" $ do
    let i1 = Int 1
    let (f, n) = (Var "f", Var "n")
    let mul a b = app (Var "*") [a, b]
    let sub a b = app (Var "-") [a, b]

    let env :: Env
        env =
          ("f", Fix "f" $ Lam "n" (CaseI (Var "n") [(0, i1)] (n `mul` App f (n `sub` i1)))) :
          ("+", Ann (op2 "+") (fun [IntT, IntT] IntT)) :
          ("-", Ann (op2 "-") (fun [IntT, IntT] IntT)) :
          ("*", Ann (op2 "*") (fun [IntT, IntT] IntT)) :
          ("==", Ann (op2 "==") (fun [IntT, IntT] (Var "Bool"))) :
          boolenv
          where
            op2 op = lam ["x", "y"] (Op op [Var "x", Var "y"])

    let eval' = eval ops env
    -- eval' (Var "f") `shouldBe` Fix "f" (Lam "n" $ app (Op "==" [n, i0]) [Op "*" [n, App f (Op "-" [n, i1])], Int 1])
    -- eval' (App f n) `shouldBe` app (Op "==" [n, i0]) [Int 0, Op "*" [n, App f (Op "-" [n, i1])]]
    eval' (App f (Int 0)) `shouldBe` Int 1
    eval' (App f (Int 1)) `shouldBe` Int 1
    eval' (App f (Int 2)) `shouldBe` Int 2
    eval' (App f (Int 3)) `shouldBe` Int 6
    eval' (App f (Int 4)) `shouldBe` Int 24
    eval' (App f (Int 5)) `shouldBe` Int 120

    let infer' = infer ops env
    infer' (Var "f") `shouldBe` Right (Fun IntT IntT, env)
    infer' (App f (Int 0)) `shouldBe` Right (IntT, env)

  it "☯ match" $ do
    let (x, x1) = (Var "x", Var "x1")
    let (x', y') = (VarP "x", VarP "y")
    let (i1, i2) = (Int 1, Int 2)
    match [] `shouldBe` Left EmptyCase
    match [Br [] i1] `shouldBe` Right i1
    match [Br [] i1, Br [] i2] `shouldBe` Right i1
    match [Br [AnyP] i1, Br [AnyP] i2] `shouldBe` Right (Lam "_" i1)
    match [Br [VarP "x"] i1, Br [AnyP] i2] `shouldBe` Right (Lam "x" i1)
    match [Br [IntP 0] i1, Br [AnyP] i2] `shouldBe` Right (Lam "_" (CaseI (Var "_") [(0, i1)] i2))
    match [Br [CtrP "A" []] i1, Br [AnyP] i2] `shouldBe` Right (Lam "_" $ Case (Var "_") [("A", i1)] i2)
    match [Br [CtrP "B" [x'], y'] i1, Br [AnyP, AnyP] i2] `shouldBe` Right (Lam "_" $ Case (Var "_") [("B", lam ["x", "y"] i1)] (Lam "_" i2))

    -- Name shadowing.
    match [Br [AnyP] x, Br [VarP "x"] x] `shouldBe` Right (Lam "x1" x)
    match [Br [VarP "x"] x, Br [AnyP] x] `shouldBe` Right (Lam "x1" $ Let [("x", x1)] x)

-- -- match [Br [x'] i1, Br [x'] i2] `shouldBe` lam ["x"] i1
-- -- match [Br [x'] i1, Br [] i2] `shouldBe` error "different number of patterns"