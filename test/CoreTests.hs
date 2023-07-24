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

  it "☯ or" $ do
    let (x, y, z) = (Var "x", Var "y", Var "z")
    or' [] `shouldBe` Err
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

  it "☯ eval" $ do
    let (x, y) = (Var "x", Var "y")
    let (x', y') = (VarP "x", VarP "y")
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
    -- eval' (For "x" x) `shouldBe` For "x" x
    -- eval' (For "y" x) `shouldBe` Int 1
    eval' (Lam x' x) `shouldBe` Lam x' x
    eval' (Lam y' x) `shouldBe` Lam y' (Int 1)
    eval' (Fun a b) `shouldBe` Fun IntT NumT
    eval' (App (Var "A") x) `shouldBe` App (Var "A") (Int 1)
    eval' (App (Lam y' y) x) `shouldBe` Int 1
    eval' (Op "+" [x, y]) `shouldBe` Op "+" [Int 1, y]
    eval' (Op "+" [x, Int 2]) `shouldBe` Int 3
    eval' (Op "-" [x, Int 2]) `shouldBe` Int (-1)
    eval' (Op "*" [x, Int 2]) `shouldBe` Int 2
    eval' (Op "==" [x, Int 1]) `shouldBe` Var "True"
    eval' (Op "==" [x, Int 2]) `shouldBe` Var "False"

  -- it "☯ occurs" $ do
  it "☯ subtype" $ do
    let (x, y) = (Var "x", Var "y")
    subtype Knd Knd `shouldBe` Right (Knd, [])
    subtype IntT Knd `shouldBe` Left (TypeMismatch IntT Knd)
    subtype IntT IntT `shouldBe` Right (IntT, [])
    subtype NumT NumT `shouldBe` Right (NumT, [])
    subtype (Int 1) (Int 1) `shouldBe` Right (Int 1, [])
    subtype (Num 1.1) (Num 1.1) `shouldBe` Right (Num 1.1, [])
    subtype (Var "x") (Var "x") `shouldBe` Right (Var "x", [])
    subtype (Var "x") IntT `shouldBe` Right (IntT, [("x", IntT)])
    subtype IntT (Var "x") `shouldBe` Right (IntT, [("x", IntT)])
    -- TODO: Fun
    -- TODO: App
    -- TODO: Ctr
    subtype IntT (Or x y) `shouldBe` Right (IntT, [("x", IntT), ("y", IntT)])
    subtype IntT (Or x NumT) `shouldBe` Right (IntT, [("x", IntT)])
    subtype IntT (Or NumT y) `shouldBe` Right (IntT, [("y", IntT)])
    subtype (Or x y) IntT `shouldBe` Right (IntT, [("x", IntT), ("y", IntT)])
    subtype (Or x NumT) IntT `shouldBe` Left (TypeMismatch NumT IntT)
    subtype (Or NumT y) IntT `shouldBe` Left (TypeMismatch NumT IntT)
    -- TODO: Op
    True `shouldBe` True

  it "☯ infer" $ do
    let a = Var "a"
    let (x, y) = (Var "x", Var "y")
    let (x', y') = (VarP "x", VarP "y")
    let (xT, yT) = (Var "xT", Var "yT")
    let (f, g) = (Var "f", Var "g")
    let typ n = Typ "T" [("n", n)] [("A", App (Var "T") (Int 0)), ("B", Fun (Var "n") (App (Var "T") (Var "n")))]
    let env :: Env
        env =
          [ ("inferred", Int 1),
            ("mismatch", Ann (Int 1) (For [] NumT)),
            ("match", Ann (Int 1) (For [] IntT)),
            ("typed", Ann (Var "typed") (For [] IntT)),
            ("free", Var "free"),
            ("x", Int 1),
            ("y", Num 1.1),
            ("f", Ann f (For [] $ Fun IntT NumT)),
            ("g", Ann g (For ["a"] $ Fun a a)),
            ("op0", Ann (Var "op0") (For [] IntT)),
            ("op1", Ann (Var "op1") (For [] $ Fun IntT NumT)),
            ("T", Lam (VarP "n") (typ (Var "n")))
          ]

    let infer' = infer ops env
    infer' Err `shouldBe` Left RuntimeError
    infer' Knd `shouldBe` Right (Knd, [])
    infer' IntT `shouldBe` Right (Knd, [])
    infer' NumT `shouldBe` Right (Knd, [])
    infer' (Int 1) `shouldBe` Right (IntT, [])
    infer' (Num 1) `shouldBe` Right (NumT, [])
    infer' (Var "undefined") `shouldBe` Left (UndefinedVar "undefined")
    infer' (Var "inferred") `shouldBe` Right (IntT, [])
    infer' (Var "mismatch") `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (Var "match") `shouldBe` Right (IntT, [])
    infer' (Var "typed") `shouldBe` Right (IntT, [])
    infer' (Var "free") `shouldBe` Right (Knd, [])
    infer' (Var "x") `shouldBe` Right (IntT, [])
    infer' (Var "y") `shouldBe` Right (NumT, [])
    infer' (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer' (Var "f") `shouldBe` Right (Fun IntT NumT, [])
    infer' (Var "g") `shouldBe` Right (Fun a a, [])
    infer' (Ctr "T" "A" []) `shouldBe` Right (typ (Int 0), [])
    infer' (Ctr "T" "B" [Int 1]) `shouldBe` Right (typ IntT, [("n", IntT)])
    -- TODO: Typ
    infer' (Lam (IntP 1) y) `shouldBe` Right (Fun (Int 1) NumT, [])
    infer' (Lam (VarP "x") y) `shouldBe` Right (Fun xT NumT, [])
    infer' (Lam (VarP "y") y) `shouldBe` Right (Fun yT yT, [])
    infer' (Lam (CtrP "T" "A" []) y) `shouldBe` Right (Fun (Ctr "T" "A" []) NumT, [])
    infer' (Lam (CtrP "T" "B" [y']) y) `shouldBe` Right (Fun (Ctr "T" "B" [yT]) yT, [("n", yT)])
    infer' (Fun IntT NumT) `shouldBe` Right (Knd, [])
    infer' (App x y) `shouldBe` Left (NotAFunction IntT)
    infer' (App f y) `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (App f x) `shouldBe` Right (NumT, [])
    infer' (App g x) `shouldBe` Right (IntT, [("a", IntT)])
    -- TODO: Ann
    infer' (Ann (Lam (CtrP "T" "B" [y']) y) (For [] $ Fun (typ IntT) IntT)) `shouldBe` Right (Fun (typ IntT) IntT, [("n", IntT), ("yT", IntT)])
    infer' (Ann (Lam (CtrP "T" "B" [y']) y) (For [] $ Fun (typ NumT) IntT)) `shouldBe` Left (TypeMismatch IntT NumT)
    -- TODO: Or
    -- TODO: Let
    -- TODO: Fix
    infer' (Op "op0" []) `shouldBe` Right (IntT, [])
    infer' (Op "op0" [Num 1.1]) `shouldBe` Left (NotAFunction IntT)
    infer' (Op "op1" [Num 1.1]) `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (Op "op1" [Int 1]) `shouldBe` Right (NumT, [])

  let boolT = Typ "Bool" [] [("True", Var "Bool"), ("False", Var "Bool")]
  let boolenv :: Env
      boolenv =
        [ ("Bool", boolT),
          ("False", Ctr "Bool" "False" []),
          ("True", Ctr "Bool" "True" [])
        ]

  it "☯ Bool" $ do
    let case' =
          or'
            [ Lam (CtrP "Bool" "True" []) (Int 1),
              Lam (CtrP "Bool" "False" []) (Int 0)
            ]
    let env = boolenv

    let eval' = eval ops env
    eval' (App case' (Ctr "Bool" "False" [])) `shouldBe` Int 0
    eval' (App case' (Ctr "Bool" "True" [])) `shouldBe` Int 1

    let infer' = infer ops env
    infer' (Var "Bool") `shouldBe` Right (Knd, [])
    infer' (Var "False") `shouldBe` Right (boolT, [])
    infer' (Var "True") `shouldBe` Right (boolT, [])
    infer' case' `shouldBe` Right (Fun (Ctr "Bool" "True" []) IntT `Or` Fun (Ctr "Bool" "False" []) IntT, [])
    infer' (Ann case' (For [] $ Fun boolT IntT)) `shouldBe` Right (Fun boolT IntT, [])
    infer' (App case' (Var "False")) `shouldBe` Right (IntT, [])
    infer' (App case' (Var "True")) `shouldBe` Right (IntT, [])

  it "☯ Maybe" $ do
    let a = Var "a"
    let xT = Var "xT"
    let maybeT x = Typ "Maybe" [("a", x)] [("Just", Fun a (App (Var "Maybe") a)), ("Nothing", App (Var "Maybe") a)]
    let case' =
          or'
            [ Lam (CtrP "Maybe" "Just" [VarP "x"]) (Var "x"),
              Lam (CtrP "Maybe" "Nothing" []) (Int 0)
            ]
    let env :: Env
        env =
          [ ("Maybe", Ann (Lam (VarP "a") (maybeT a)) (For [] $ Fun Knd Knd)),
            ("Just", Lam (VarP "x") (Ctr "Maybe" "Just" [Var "x"])),
            ("Nothing", Ctr "Maybe" "Nothing" [])
          ]

    let eval' = eval ops env
    eval' (App case' (Ctr "Maybe" "Nothing" [])) `shouldBe` Int 0
    eval' (App case' (Ctr "Maybe" "Just" [Int 1])) `shouldBe` Int 1

    let infer' = infer ops env
    infer' (app (Var "Maybe") []) `shouldBe` Right (Fun Knd Knd, [("aT", Knd)])
    infer' (app (Var "Maybe") [IntT]) `shouldBe` Right (Knd, [("aT", Knd)])
    infer' (app (Var "Nothing") []) `shouldBe` Right (maybeT a, [])
    infer' (app (Var "Just") []) `shouldBe` Right (Fun a (maybeT a), [("xT", a)])
    infer' (app (Var "Just") [Int 1]) `shouldBe` Right (maybeT IntT, [("xT", IntT), ("a", IntT)])
    infer' case' `shouldBe` Right (Fun (Ctr "Maybe" "Just" [xT]) xT `Or` Fun (Ctr "Maybe" "Nothing" []) IntT, [("a", xT)])
    infer' (Ann case' (For [] $ Fun (maybeT IntT) IntT)) `shouldBe` Right (Fun (maybeT IntT) IntT, [("a", IntT), ("xT", IntT)])
    infer' (Ann case' (For [] $ Fun (maybeT NumT) IntT)) `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (App case' (Ctr "Maybe" "Nothing" [])) `shouldBe` Right (IntT, [("a", IntT), ("xT", IntT)])
    infer' (App case' (Ctr "Maybe" "Just" [Int 1])) `shouldBe` Right (IntT, [("a", IntT), ("a", IntT), ("xT", IntT)])
    infer' (App case' (Ctr "Maybe" "Just" [Num 1.1])) `shouldBe` Left (TypeMismatch NumT IntT)

  it "☯ Nat" $ do
    let natT = Typ "Nat" [] [("Succ", Fun (Var "Nat") (Var "Nat")), ("Zero", Var "Nat")]
    let case' =
          or'
            [ Lam (CtrP "Nat" "Succ" [VarP "n"]) (Int 1),
              Lam (CtrP "Nat" "Zero" []) (Int 0)
            ]
    let env :: Env
        env =
          [ ("Nat", natT),
            ("Succ", Lam (VarP "n") (Ctr "Nat" "Succ" [Var "n"])),
            ("Zero", Ctr "Nat" "Zero" [])
          ]

    let eval' = eval ops env
    eval' (App case' (Ctr "Nat" "Zero" [])) `shouldBe` Int 0
    eval' (App case' (Ctr "Nat" "Succ" [Var "Zero"])) `shouldBe` Int 1

    let infer' = infer ops env
    infer' (Var "Nat") `shouldBe` Right (Knd, [])
    infer' (Var "Zero") `shouldBe` Right (natT, [])
    infer' (Var "Succ") `shouldBe` Right (Fun natT natT, [("nT", natT)])
    infer' (App (Var "Succ") (Var "Zero")) `shouldBe` Right (natT, [("nT", natT)])
    infer' (Ctr "Nat" "Succ" []) `shouldBe` Right (Fun natT natT, [])
    infer' (Ctr "Nat" "Succ" [Var "Zero"]) `shouldBe` Right (natT, [])
    infer' case' `shouldBe` Right (Fun (Ctr "Nat" "Succ" [Var "nT"]) IntT `Or` Fun (Ctr "Nat" "Zero" []) IntT, [("Nat", Var "nT")])
    infer' (App case' (Ctr "Nat" "Zero" [])) `shouldBe` Right (IntT, [("Nat", Var "nT")])
    infer' (App case' (Ctr "Nat" "Succ" [Var "Zero"])) `shouldBe` Right (IntT, [("Nat", Var "nT")])

  it "☯ Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let vecT x y = eval ops [] (Typ "Vec" [("n", x), ("a", y)] [("Cons", fun [a, app (Var "Vec") [n, a]] (app (Var "Vec") [Op "+" [n, Int 1], a])), ("Nil", app (Var "Vec") [Int 0, a])])
    let case' =
          or'
            [ Lam (CtrP "Vec" "Cons" [VarP "x", VarP "xs"]) (Var "x"),
              Lam (CtrP "Vec" "Nil" []) (Int 0)
            ]
    let env :: Env
        env =
          [ ("Vec", Ann (lam [VarP "n", VarP "a"] (vecT n a)) (For [] $ fun [IntT, Knd] Knd)),
            ("Cons", lam [VarP "x", VarP "xs"] (Ctr "Vec" "Cons" [Var "x", Var "xs"])),
            ("Nil", Ctr "Vec" "Nil" [])
          ]

    let eval' = eval ops env
    eval' (App case' (Var "Nil")) `shouldBe` Int 0
    eval' (App case' (Ctr "Vec" "Cons" [Int 1, Var "Nil"])) `shouldBe` Int 1
    eval' (App case' (Ctr "Vec" "Cons" [Int 2, Var "Nil"])) `shouldBe` Int 2

    let infer' = infer ops env
    infer' (app (Var "Vec") []) `shouldBe` Right (fun [IntT, Knd] Knd, [("nT", IntT), ("aT", Knd)])
    infer' (app (Var "Vec") [Int 0]) `shouldBe` Right (Fun Knd Knd, [("nT", IntT), ("aT", Knd)])
    infer' (app (Var "Vec") [Int 0, NumT]) `shouldBe` Right (Knd, [("nT", IntT), ("aT", Knd)])
    infer' (app (Var "Nil") []) `shouldBe` Right (vecT (Int 0) a, [])
    infer' (app (Var "Cons") []) `shouldBe` Right (fun [a, vecT n a] (vecT (Op "+" [n, Int 1]) a), [("xT", a), ("xsT", vecT n a)])
    infer' (app (Var "Cons") [Int 42]) `shouldBe` Right (fun [vecT n IntT] (vecT (Op "+" [n, Int 1]) IntT), [("xT", IntT), ("xsT", vecT n IntT), ("a", IntT)])
    infer' (app (Var "Cons") [Int 42, Var "Nil"]) `shouldBe` Right (vecT (Int 1) IntT, [("xT", IntT), ("xsT", vecT (Int 0) IntT), ("a", IntT), ("n", Int 0)])
    -- infer' (App case' (Var "Nil")) `shouldBe` Right (IntT, [])
    -- infer' (App case' (Ctr "Vec" "Cons" [Int 42, Var "Nil"])) `shouldBe` Right (IntT, [])
    True `shouldBe` True

  it "☯ factorial" $ do
    let i1 = Int 1
    let (f, n) = (Var "f", Var "n")
    let mul a b = app (Var "*") [a, b]
    let sub a b = app (Var "-") [a, b]

    let env :: Env
        env =
          ("f", Fix "f" $ Lam (IntP 0) (Int 1) `Or` Lam (VarP "n") (n `mul` App f (n `sub` i1))) :
          ("+", Ann (op2 "+") (For [] $ fun [IntT, IntT] IntT)) :
          ("-", Ann (op2 "-") (For [] $ fun [IntT, IntT] IntT)) :
          ("*", Ann (op2 "*") (For [] $ fun [IntT, IntT] IntT)) :
          ("==", Ann (op2 "==") (For [] $ fun [IntT, IntT] (Var "Bool"))) :
          boolenv
          where
            op2 op = lam [VarP "x", VarP "y"] (Op op [Var "x", Var "y"])

    let eval' = eval ops env
    -- eval' (Var "f") `shouldBe` Fix "f" (Lam' "n" $ app (Op "==" [n, i0]) [Op "*" [n, App f (Op "-" [n, i1])], Int 1])
    -- eval' (App f n) `shouldBe` app (Op "==" [n, i0]) [Int 0, Op "*" [n, App f (Op "-" [n, i1])]]
    eval' (App f (Int 0)) `shouldBe` Int 1
    eval' (App f (Int 1)) `shouldBe` Int 1
    eval' (App f (Int 2)) `shouldBe` Int 2
    eval' (App f (Int 3)) `shouldBe` Int 6
    eval' (App f (Int 4)) `shouldBe` Int 24
    eval' (App f (Int 5)) `shouldBe` Int 120

    let infer' a = fmap fst (infer ops env a)
    infer' (Var "f") `shouldBe` Right (Fun IntT IntT)
    infer' (App f (Int 0)) `shouldBe` Right IntT
