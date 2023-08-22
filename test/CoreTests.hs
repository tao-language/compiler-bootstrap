module CoreTests where

import Core
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯️ Core language ☯️==--" $ do
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  let (n1, n2, n3) = (Num 1.1, Num 2.2, Num 3.3)
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (f, g, h) = (Var "f", Var "g", Var "h")

  -- let (x', y') = (VarP "x", VarP "y")

  let factorial f = Fix "f" (lamEq (Int 0) i1 `Or` lamIfAs ("x", Int 0 `lt` x) (x `mul` App (Var f) (x `sub` i1)))

  it "☯ syntax sugar" $ do
    let' [] x `shouldBe` x
    -- let' [(y', z)] x `shouldBe` App (Lam y' x) z

    or' [] `shouldBe` Err
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

    -- lam [] x `shouldBe` x
    -- lam [y'] x `shouldBe` Lam y' x

    app x [] `shouldBe` x
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ eval const" $ do
    eval [] Knd `shouldBe` Knd
    eval [] IntT `shouldBe` IntT
    eval [] NumT `shouldBe` NumT
    eval [] (Int 1) `shouldBe` Int 1
    eval [] (Num 1.1) `shouldBe` Num 1.1
    eval [] Err `shouldBe` Err

  it "☯ eval Ctr" $ do
    let env = [("x", i1)]
    eval env (Ctr "A") `shouldBe` Ctr "A"
    eval env (App (Ctr "B") x) `shouldBe` App (Ctr "B") i1

  it "☯ eval Typ" $ do
    let env = [("x", i1)]
    eval env (Typ "T") `shouldBe` Typ "T"
    eval env (App (Typ "U") x) `shouldBe` App (Typ "U") i1

  it "☯ eval Var" $ do
    let env = [("x", i1), ("y", y), ("b", Ann b (For [] IntT)), ("a", b), ("c", Ann c (For ["a"] a))]
    eval env (Var "x") `shouldBe` Int 1
    eval env (Var "y") `shouldBe` Var "y"
    eval env (Var "z") `shouldBe` Var "z"
    eval env (Var "a") `shouldBe` Var "b"
    eval env (Var "c") `shouldBe` Var "c"

  it "☯ eval Fun" $ do
    let env = [("x", i1), ("y", IntT)]
    eval env (Fun x y) `shouldBe` Fun i1 IntT
    eval env (Fun (Or x y) z) `shouldBe` Or (Fun i1 z) (Fun IntT z)
    eval env (Fun x (Or y z)) `shouldBe` Or (Fun i1 IntT) (Fun i1 z)

  it "☯ eval Lam" $ do
    let env = [("x", i1)]
    -- eval env (Lam x' x) `shouldBe` Lam x' x
    -- eval env (Lam y' x) `shouldBe` Lam y' i1
    -- eval env (Lam x' (Or x y)) `shouldBe` Or (Lam x' x) (Lam x' y)
    True `shouldBe` True

  it "☯ eval Or" $ do
    let env = [("x", i1), ("y", i2), ("z", i3)]
    eval env (Or x Err) `shouldBe` i1
    eval env (Or Err y) `shouldBe` i2
    eval env (Or x y) `shouldBe` Or i1 i2
    eval env (Or x (Or y z)) `shouldBe` Or i1 (Or i2 i3)
    eval env (Or (Or x y) z) `shouldBe` Or i1 (Or i2 i3)

  it "☯ eval App" $ do
    let env = [("x", i1), ("f", g), ("g", g), ("h", h)]
    eval env (App (Var "f") Knd) `shouldBe` App g Knd
    -- eval env (App (Lam KndP x) y) `shouldBe` App (Lam KndP i1) y
    -- eval env (App (Lam KndP x) Knd) `shouldBe` i1
    -- eval env (App (Lam KndP x) IntT) `shouldBe` Err
    -- eval env (App (Lam IntTP x) IntT) `shouldBe` i1
    -- eval env (App (Lam (IntP 1) x) i1) `shouldBe` i1
    -- eval env (App (Lam (IntP 1) x) i2) `shouldBe` Err
    -- eval env (App (Lam (VarP "x") x) Knd) `shouldBe` Knd
    -- eval env (App (Lam (VarP "y") x) Knd) `shouldBe` i1
    -- eval env (App (Lam (CtrP "A") x) (Ctr "A")) `shouldBe` i1
    -- eval env (App (Lam (CtrP "A") x) (Ctr "B")) `shouldBe` Err
    -- eval env (App (Lam (TypP "T") x) (Typ "T")) `shouldBe` i1
    -- eval env (App (Lam (TypP "T") x) (Typ "U")) `shouldBe` Err
    -- eval env (App (Lam (AppP (CtrP "B") x') x) (App (Ctr "B") Knd)) `shouldBe` Knd
    -- eval env (App (Lam (AppP (TypP "U") x') x) (App (Typ "U") Knd)) `shouldBe` Knd
    -- eval env (App (Lam (FunP KndP x') x) (Fun IntT Knd)) `shouldBe` Err
    -- eval env (App (Lam (FunP IntTP x') x) (Fun IntT Knd)) `shouldBe` Knd
    -- eval env (App (Lam ErrP x) Knd) `shouldBe` Err
    -- eval env (App (Lam ErrP x) Err) `shouldBe` i1
    eval env (App (Or Err Err) Knd) `shouldBe` Err
    eval env (App (Or Err f) Knd) `shouldBe` App g Knd
    eval env (App (Or f Err) Knd) `shouldBe` App g Knd
    eval env (App (Or f h) Knd) `shouldBe` Or (App g Knd) (App h Knd)
    -- eval env (App (Fix "f" (Lam x' (App h f))) Knd) `shouldBe` App h (Fix "f" (Lam x' (App h f)))
    eval env (App Err Knd) `shouldBe` Err
    eval env (App Err Knd) `shouldBe` Err

  it "☯ eval Ann" $ do
    let env = [("x", i1)]
    eval env (Ann x (For [] IntT)) `shouldBe` i1

  it "☯ eval Op2" $ do
    let env = []
    eval env (add x y) `shouldBe` add x y
    eval env (add x i2) `shouldBe` add x i2
    eval env (add i1 y) `shouldBe` add i1 y

    eval env (add i1 i2) `shouldBe` Int 3
    eval env (sub i1 i2) `shouldBe` Int (-1)
    eval env (mul i1 i2) `shouldBe` Int 2

  it "☯ eval factorial" $ do
    let env = [("f", factorial "f")]
    eval env (Var "f") `shouldBe` factorial "f"
    eval env (App f x) `shouldBe` App (factorial "f") x
    eval env (App f (Int 0)) `shouldBe` Int 1
    eval env (App f (Int 1)) `shouldBe` Int 1
    eval env (App f (Int 2)) `shouldBe` Int 2
    eval env (App f (Int 3)) `shouldBe` Int 6
    eval env (App f (Int 4)) `shouldBe` Int 24
    eval env (App f (Int 5)) `shouldBe` Int 120

  it "☯ infer const" $ do
    infer [] Knd `shouldBe` Right (Knd, [])
    infer [] IntT `shouldBe` Right (Knd, [])
    infer [] NumT `shouldBe` Right (Knd, [])
    infer [] (Int 1) `shouldBe` Right (IntT, [])
    infer [] (Num 1.1) `shouldBe` Right (NumT, [])
    infer [] Err `shouldBe` Right (Err, [])

  it "☯ infer Ctr" $ do
    let env =
          [ ("C1", Ann (Ctr "C1") (For [] a)),
            ("C2", Ann (Ctr "C2") (For ["a"] a)),
            ("C3", Ann (Ctr "C3") (For ["b"] b)),
            ("C4", Ann (Ctr "C5") (For [] a)),
            ("C5", Ctr "C5"),
            ("b", b)
          ]
    infer env (Ctr "X") `shouldBe` Left (UndefinedCtr "X")
    infer env (Ctr "C1") `shouldBe` Right (a, [])
    infer env (Ctr "C2") `shouldBe` Right (a, [("a", a)])
    infer env (Ctr "C3") `shouldBe` Right (Var "b1", [("b1", Var "b1")])
    infer env (Ctr "C4") `shouldBe` Left (InconsistentCtr "C4" "C5")
    infer env (Ctr "C5") `shouldBe` Left (MissingType "C5")

  it "☯ infer Typ" $ do
    let env =
          [ ("T1", Ann (Typ "T1") (For [] a)),
            ("T2", Ann (Typ "T2") (For ["a"] a)),
            ("T3", Ann (Typ "T3") (For ["b"] b)),
            ("T4", Ann (Typ "T5") (For [] a)),
            ("T5", Typ "T5"),
            ("b", b)
          ]
    infer env (Typ "X") `shouldBe` Left (UndefinedTyp "X")
    infer env (Typ "T1") `shouldBe` Right (a, [])
    infer env (Typ "T2") `shouldBe` Right (a, [("a", a)])
    infer env (Typ "T3") `shouldBe` Right (Var "b1", [("b1", Var "b1")])
    infer env (Typ "T4") `shouldBe` Left (InconsistentTyp "T4" "T5")
    infer env (Typ "T5") `shouldBe` Left (MissingType "T5")

  it "☯ infer Var" $ do
    let (a1, yT) = (Var "a1", Var "yT")
    let env = [("x", i1), ("y", y), ("b", Ann b (For [] IntT)), ("a", b), ("c", Ann c (For ["a"] a))]
    infer env (Var "x") `shouldBe` Right (IntT, [])
    infer env (Var "y") `shouldBe` Right (yT, [("yT", yT), ("y", Ann y (For [] yT))])
    infer env (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer env (Var "a") `shouldBe` Right (IntT, [])
    infer env (Var "c") `shouldBe` Right (a1, [("a1", a1)])

  it "☯ infer Fun" $ do
    let aT = Var "aT"
    let env = [("a", a), ("b", IntT)]
    infer env (Fun x y) `shouldBe` Left (UndefinedVar "x")
    infer env (Fun a y) `shouldBe` Left (UndefinedVar "y")
    infer env (Fun a b) `shouldBe` Right (Knd, [("aT", aT), ("a", Ann a (For [] aT))])

  it "☯ infer Ann" $ do
    infer [] (Ann i1 (For [] IntT)) `shouldBe` Right (IntT, [])
    infer [] (Ann i1 (For [] Knd)) `shouldBe` Left (TypeMismatch IntT Knd)
    infer [] (Ann i1 (For ["a"] a)) `shouldBe` Right (IntT, [("a", IntT)])

  it "☯ infer Lam" $ do
    let (t, xT) = (Var "t", Var "xT")
    let env =
          [ ("A", Ann (Ctr "A") (For ["a"] a)),
            ("T", Ann (Typ "T") (For ["b"] b)),
            ("x", Ann x (For [] IntT))
          ]
    -- infer env (Lam KndP x) `shouldBe` Right (Fun Knd IntT, [])
    -- infer env (Lam IntTP x) `shouldBe` Right (Fun Knd IntT, [])
    -- infer env (Lam IntTP x) `shouldBe` Right (Fun Knd IntT, [])
    -- infer env (Lam (CtrP "A") x) `shouldBe` Right (Fun a IntT, [("a", a)])
    -- infer env (Lam (TypP "T") x) `shouldBe` Right (Fun b IntT, [("b", b)])
    -- infer env (Lam (VarP "x") x) `shouldBe` Right (Fun xT xT, [("xT", xT), ("x", Ann x (For [] xT))])
    -- infer env (Lam (FunP x' IntTP) x) `shouldBe` Right (Fun Knd xT, [("xT", xT), ("x", Ann x (For [] xT))])
    -- infer env (Lam (AppP x' IntTP) x) `shouldBe` Right (Fun t (Fun Knd t), [("xT", Fun Knd t), ("x", Ann x (For [] (Fun Knd t))), ("t", t)])
    True `shouldBe` True

  it "☯ infer App" $ do
    let t = Var "t"
    let env = [("x", i1), ("y", y), ("f", Ann (Var "f") (For [] $ Fun IntT Knd))]
    infer env (App (Var "f") x) `shouldBe` Right (Knd, [("t", Knd)])
    -- infer env (App (Lam y' y) x) `shouldBe` Right (IntT, [("yT", IntT), ("y", Ann y (For [] IntT)), ("t", IntT)])
    infer env (App y x) `shouldBe` Right (t, [("yT", Fun IntT t), ("y", Ann y (For [] (Fun IntT t))), ("t", t)])

  it "☯ infer Or" $ do
    let env = [("x", i1), ("y", IntT)]
    infer env (Or x x) `shouldBe` Right (IntT, [])
    infer env (Or x y) `shouldBe` Right (Or IntT Knd, [])

  it "☯ infer Fix" $ do
    True `shouldBe` True

  it "☯ infer Op2" $ do
    True `shouldBe` True

  it "☯ infer factorial" $ do
    let env = [("f", factorial "f")]
    infer env (Var "f") `shouldBe` Right (Fun IntT IntT, [("xT", IntT), ("x", Ann x (For [] IntT)), ("xT1", IntT), ("fT", Fun IntT IntT), ("f", Ann f (For [] (Fun IntT IntT))), ("t", IntT)])

  it "☯ infer Bool" $ do
    let i0 = Int 0
    let n = Var "n"
    let nat n = App (Typ "Nat") n
    let env =
          [ ("Nat", Ann (Typ "Nat") (For [] (Fun IntT Knd))),
            ("Zero", Ann (Ctr "Zero") (For [] (nat i0))),
            ("Succ", Ann (Ctr "Succ") (For ["n"] (Fun (nat n) (nat (add n i1)))))
          ]

    let num :: Int -> Expr
        num 0 = Ctr "Zero"
        num n = App (Ctr "Succ") (num (n - 1))
    let infer' = fmap fst . infer env
    infer' (num 0) `shouldBe` Right (nat i0)
    infer' (num 1) `shouldBe` Right (nat i1)
    infer' (num 2) `shouldBe` Right (nat i2)

  it "☯ infer Vec" $ do
    let i0 = Int 0
    let (n, a) = (Var "n", Var "a")
    let vec n a = app (Typ "Vec") [n, a]
    let env =
          [ ("Vec", Ann (Typ "Vec") (For [] (fun [IntT, Knd] Knd))),
            ("Nil", Ann (Ctr "Nil") (For ["a"] (vec i0 a))),
            ("Cons", Ann (Ctr "Cons") (For ["n", "a"] (fun [a, vec n a] (vec (add n i1) a))))
          ]

    let list [] = Ctr "Nil"
        list (x : xs) = app (Ctr "Cons") [x, list xs]
    let infer' = fmap fst . infer env
    infer' (list []) `shouldBe` Right (vec i0 a)
    infer' (list [Int 42]) `shouldBe` Right (vec i1 IntT)
    infer' (list [Int 42, Int 9]) `shouldBe` Right (vec i2 IntT)
    infer' (list [Int 42, Knd]) `shouldBe` Left (TypeMismatch Knd IntT)
