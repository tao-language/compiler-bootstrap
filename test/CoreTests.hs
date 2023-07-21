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
    eval' (For "x" x) `shouldBe` For "x" x
    eval' (For "y" x) `shouldBe` Int 1
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
    let env :: Env
        env =
          [ ("x", x),
            ("y", y)
          ]

    let subtype' = subtype ops env
    subtype' Knd Knd `shouldBe` Right (Knd, env)
    subtype' IntT Knd `shouldBe` Left (TypeMismatch IntT Knd)
    subtype' IntT IntT `shouldBe` Right (IntT, env)
    subtype' NumT NumT `shouldBe` Right (NumT, env)
    subtype' (Int 1) (Int 1) `shouldBe` Right (Int 1, env)
    subtype' (Num 1.1) (Num 1.1) `shouldBe` Right (Num 1.1, env)
    subtype' (Var "x") (Var "x") `shouldBe` Right (Var "x", env)
    subtype' (Var "x") IntT `shouldBe` Right (IntT, set "x" IntT env)
    subtype' IntT (Var "x") `shouldBe` Right (IntT, set "x" IntT env)
    -- TODO: For
    -- TODO: Fun
    -- TODO: App
    -- TODO: Ctr
    subtype' IntT (Or x y) `shouldBe` Right (IntT, set "x" IntT $ set "y" IntT env)
    subtype' IntT (Or x NumT) `shouldBe` Right (IntT, set "x" IntT env)
    subtype' IntT (Or NumT y) `shouldBe` Right (IntT, set "y" IntT env)
    subtype' (Or x y) IntT `shouldBe` Right (IntT, set "x" IntT $ set "y" IntT env)
    subtype' (Or x NumT) IntT `shouldBe` Left (TypeMismatch NumT IntT)
    subtype' (Or NumT y) IntT `shouldBe` Left (TypeMismatch NumT IntT)
    -- TODO: Op
    True `shouldBe` True

  it "☯ infer" $ do
    let a = Var "a"
    let (x, y) = (Var "x", Var "y")
    let (x', y') = (VarP "x", VarP "y")
    let (xT, yT) = (Var "xT", Var "yT")
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
    infer' Err `shouldBe` Left RuntimeError
    infer' Knd `shouldBe` Right (Knd, env)
    infer' IntT `shouldBe` Right (Knd, env)
    infer' NumT `shouldBe` Right (Knd, env)
    infer' (Int 1) `shouldBe` Right (IntT, env)
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
    -- TODO: Ctr
    infer' (Lam (IntP 1) y) `shouldBe` Right (Fun (Int 1) NumT, env)
    infer' (Lam (VarP "y") y) `shouldBe` Right (For "yT" $ Fun yT yT, env)
    -- infer' (Lam (CtrP "T" "A" []) y) `shouldBe` Right (Fun (Ctr "T" "A" []) NumT, env)
    -- infer' (Lam (CtrP "T" "B" [IntP 1]) y) `shouldBe` Right (Fun (Ctr "T" "B" [Int 1]) NumT, env)
    -- infer' (Lam (CtrP "T" "B" [VarP "y"]) y) `shouldBe` Right (For "yT" $ Fun (Ctr "T" "B" [yT]) yT, env)
    -- infer' (Lam (CtrP "T" "C" [x', y']) y) `shouldBe` Right (for ["xT", "yT"] $ Fun (Ctr "T" "C" [xT, yT]) yT, env)
    infer' (For "x" (Int 1)) `shouldBe` Right (IntT, env)
    infer' (For "x" x) `shouldBe` Right (For "xT" xT, env)
    infer' (Fun IntT NumT) `shouldBe` Right (Knd, env)
    infer' (App x y) `shouldBe` Left (TypeMismatch IntT (Fun NumT (Var "t")))
    infer' (App f y) `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (App f x) `shouldBe` Right (NumT, env)
    infer' (App g x) `shouldBe` Right (IntT, env)
    -- TODO: Ann
    -- TODO: Or
    -- TODO: Let
    -- TODO: Fix
    infer' (Op "op0" []) `shouldBe` Right (IntT, env)
    infer' (Op "op0" [Num 1.1]) `shouldBe` Left (TypeMismatch IntT (Fun NumT (Var "t")))
    infer' (Op "op1" [Num 1.1]) `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (Op "op1" [Int 1]) `shouldBe` Right (NumT, env)

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
    infer' (Var "Bool") `shouldBe` Right (Knd, env)
    infer' (Var "False") `shouldBe` Right (boolT, env)
    infer' (Var "True") `shouldBe` Right (boolT, env)
    infer' case' `shouldBe` Right (Fun (Ctr "Bool" "True" []) IntT `Or` Fun (Ctr "Bool" "False" []) IntT, env)
    infer' (Ann case' (Fun boolT IntT)) `shouldBe` Right (Fun boolT IntT, env)
    infer' (App case' (Var "False")) `shouldBe` Right (IntT, env)
    infer' (App case' (Var "True")) `shouldBe` Right (IntT, env)

  it "☯ Maybe" $ do
    let a = Var "a"
    let maybeT a = Typ "Maybe" [a] [("Just", Fun a (App (Var "Maybe") a)), ("Nothing", App (Var "Maybe") a)]
    let case' =
          or'
            [ Lam (CtrP "Maybe" "Just" [VarP "x"]) (Var "x"),
              Lam (CtrP "Maybe" "Nothing" []) (Int 0)
            ]
    let env :: Env
        env =
          [ ("Maybe", Ann (Lam (VarP "a") (maybeT a)) (Fun Knd Knd)),
            ("Just", Lam (VarP "x") (Ctr "Maybe" "Just" [Var "x"])),
            ("Nothing", Ctr "Maybe" "Nothing" [])
          ]

    let eval' = eval ops env
    eval' (App case' (Ctr "Maybe" "Nothing" [])) `shouldBe` Int 0
    eval' (App case' (Ctr "Maybe" "Just" [Int 1])) `shouldBe` Int 1

    let infer' = infer ops env
    infer' (app (Var "Maybe") []) `shouldBe` Right (Fun Knd Knd, env)
    infer' (app (Var "Maybe") [IntT]) `shouldBe` Right (Knd, env)
    infer' (app (Var "Nothing") []) `shouldBe` Right (For "a" $ maybeT a, env)
    infer' (app (Var "Just") []) `shouldBe` Right (For "a" $ Fun a (maybeT a), env)
    infer' (app (Var "Just") [Int 1]) `shouldBe` Right (maybeT IntT, env)
    infer' case' `shouldBe` Right (For "a" (Fun (Ctr "Maybe" "Just" [a]) a) `Or` Fun (Ctr "Maybe" "Nothing" []) IntT, env)
    infer' (Ann case' (Fun (maybeT IntT) IntT)) `shouldBe` Right (Fun (maybeT IntT) IntT, env)
    infer' (Ann case' (Fun (maybeT NumT) IntT)) `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (App case' (Ctr "Maybe" "Nothing" [])) `shouldBe` Right (IntT, env)
    infer' (App case' (Ctr "Maybe" "Just" [Int 1])) `shouldBe` Right (IntT, env)
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
    infer' (Var "Nat") `shouldBe` Right (Knd, env)
    infer' (Var "Zero") `shouldBe` Right (natT, env)
    infer' (Var "Succ") `shouldBe` Right (Fun natT natT, env)
    infer' (App (Var "Succ") (Var "Zero")) `shouldBe` Right (natT, env)
    infer' (Ctr "Nat" "Succ" []) `shouldBe` Right (Fun natT natT, env)
    infer' (Ctr "Nat" "Succ" [Var "Zero"]) `shouldBe` Right (natT, env)
    infer' case' `shouldBe` Right (Fun (Ctr "Nat" "Succ" [natT]) IntT `Or` Fun (Ctr "Nat" "Zero" []) IntT, env)
    infer' (App case' (Ctr "Nat" "Zero" [])) `shouldBe` Right (IntT, env)
    infer' (App case' (Ctr "Nat" "Succ" [Var "Zero"])) `shouldBe` Right (IntT, env)

  it "☯ Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let vecT n a = eval ops [] (Typ "Vec" [n, a] [("Cons", fun [a, app (Var "Vec") [n, a]] (app (Var "Vec") [Op "+" [n, Int 1], a])), ("Nil", app (Var "Vec") [Int 0, a])])
    let case' =
          or'
            [ Lam (CtrP "Vec" "Cons" [VarP "x", VarP "xs"]) (Var "x"),
              Lam (CtrP "Vec" "Nil" []) (Int 0)
            ]
    let env :: Env
        env =
          [ ("Vec", Ann (lam [VarP "n", VarP "a"] (vecT n a)) (fun [IntT, Knd] Knd)),
            ("Cons", lam [VarP "x", VarP "xs"] (Ctr "Vec" "Cons" [Var "x", Var "xs"])),
            ("Nil", Ctr "Vec" "Nil" [])
          ]

    let eval' = eval ops env
    eval' (App case' (Var "Nil")) `shouldBe` Int 0
    eval' (App case' (Ctr "Vec" "Cons" [Int 1, Var "Nil"])) `shouldBe` Int 1
    eval' (App case' (Ctr "Vec" "Cons" [Int 2, Var "Nil"])) `shouldBe` Int 2

    let infer' = infer ops env
    infer' (app (Var "Vec") []) `shouldBe` Right (fun [IntT, Knd] Knd, env)
    infer' (app (Var "Vec") [Int 0]) `shouldBe` Right (Fun Knd Knd, env)
    infer' (app (Var "Vec") [Int 0, NumT]) `shouldBe` Right (Knd, env)
    infer' (app (Var "Nil") []) `shouldBe` Right (For "a" $ vecT (Int 0) a, env)
    -- infer' (app (Var "Cons") []) `shouldBe` Right (for ["n", "a"] $ fun [a, vecT n a] (vecT (Op "+" [n, Int 1]) a), env)
    -- infer' (app (Var "Cons") [Int 42]) `shouldBe` Right (For "n" $ fun [vecT n IntT] (vecT (Op "+" [n, Int 1]) IntT), env)
    -- infer' (app (Var "Cons") [Int 42, Var "Nil"]) `shouldBe` Right (vecT (Int 1) IntT, env)
    -- infer' (case' (Var "Nil")) `shouldBe` Right (IntT, env)
    -- infer' (case' (Ctr "Vec" "Cons" [Int 42, Var "Nil"])) `shouldBe` Right (IntT, env)
    True `shouldBe` True

  it "☯ factorial" $ do
    let i1 = Int 1
    let (f, n) = (Var "f", Var "n")
    let mul a b = app (Var "*") [a, b]
    let sub a b = app (Var "-") [a, b]

    let env :: Env
        env =
          ("f", Fix "f" $ Lam (IntP 0) (Int 1) `Or` Lam (VarP "n") (n `mul` App f (n `sub` i1))) :
          ("+", Ann (op2 "+") (fun [IntT, IntT] IntT)) :
          ("-", Ann (op2 "-") (fun [IntT, IntT] IntT)) :
          ("*", Ann (op2 "*") (fun [IntT, IntT] IntT)) :
          ("==", Ann (op2 "==") (fun [IntT, IntT] (Var "Bool"))) :
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

    let infer' = infer ops env
    infer' (Var "f") `shouldBe` Right (Fun IntT IntT, env)
    infer' (App f (Int 0)) `shouldBe` Right (IntT, env)
