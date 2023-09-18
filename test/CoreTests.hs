module CoreTests where

import Core
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯️ Core language ☯️==--" $ do
  let (i0, i1, i2) = (Int 0, Int 1, Int 2)
  let (n1, n2, n3) = (Num 1.1, Num 2.2, Num 3.3)
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (f, g, h) = (Var "f", Var "g", Var "h")

  let factorial f = Fix f (or' branches)
        where
          branches =
            [ Lam "x" (If (eq x i0) i1),
              Lam "x" (If (lt i0 x) (x `mul` App (Var f) (x `sub` i1)))
            ]

  it "☯ show" $ do
    let (ty, tz) = (For [] y, For [] z)
    show Err `shouldBe` "@error"
    show Typ `shouldBe` "@Type"
    show IntT `shouldBe` "@Int"
    show NumT `shouldBe` "@Num"
    show (Int 1) `shouldBe` "1"
    show (Num 1.1) `shouldBe` "1.1"
    -- show (Typ "T") `shouldBe` "$T"
    -- show (Ctr "T" "A") `shouldBe` "$T.A"
    show (Var "x") `shouldBe` "x"

    show (pow (pow x y) z) `shouldBe` "(x^y)^z"
    show (pow x (pow y z)) `shouldBe` "x^y^z"
    show (pow (App x y) z) `shouldBe` "(x y)^z"
    show (pow x (App y z)) `shouldBe` "x^(y z)"

    show (App x (pow y z)) `shouldBe` "x y^z"
    show (App (pow x y) z) `shouldBe` "x^y z"
    show (App (App x y) z) `shouldBe` "x y z"
    show (App x (App y z)) `shouldBe` "x (y z)"
    show (App (mul x y) z) `shouldBe` "(x * y) z"
    show (App x (mul y z)) `shouldBe` "x (y * z)"

    -- show (isInt (App x y)) `shouldBe` "@isInt (x y)"
    -- show (isInt (pow x y)) `shouldBe` "@isInt x^y"
    -- show (pow (isInt x) y) `shouldBe` "(@isInt x)^y"
    -- show (App (isInt x) y) `shouldBe` "@isInt x y"
    -- show (App x (isInt y)) `shouldBe` "x (@isInt y)"

    -- show (isNum (App x y)) `shouldBe` "@isNum (x y)"
    -- show (isNum (pow x y)) `shouldBe` "@isNum x^y"
    -- show (pow (isNum x) y) `shouldBe` "(@isNum x)^y"
    -- show (App (isNum x) y) `shouldBe` "@isNum x y"
    -- show (App x (isNum y)) `shouldBe` "x (@isNum y)"

    show (int2Num (App x y)) `shouldBe` "@int2Num (x y)"
    show (int2Num (pow x y)) `shouldBe` "@int2Num x^y"
    show (pow (int2Num x) y) `shouldBe` "(@int2Num x)^y"
    show (App (int2Num x) y) `shouldBe` "@int2Num x y"
    show (App x (int2Num y)) `shouldBe` "x (@int2Num y)"

    show (mul x (App y z)) `shouldBe` "x * y z"
    show (mul (App x y) z) `shouldBe` "x y * z"
    show (mul (mul x y) z) `shouldBe` "x * y * z"
    show (mul x (mul y z)) `shouldBe` "x * (y * z)"
    show (mul (add x y) z) `shouldBe` "(x + y) * z"
    show (mul x (add y z)) `shouldBe` "x * (y + z)"

    show (add x (mul y z)) `shouldBe` "x + y * z"
    show (add (mul x y) z) `shouldBe` "x * y + z"
    show (add (add x y) z) `shouldBe` "x + y + z"
    show (add x (add y z)) `shouldBe` "x + (y + z)"
    show (sub (add x y) z) `shouldBe` "x + y - z"
    show (sub x (add y z)) `shouldBe` "x - (y + z)"
    show (sub (sub x y) z) `shouldBe` "x - y - z"
    show (sub x (sub y z)) `shouldBe` "x - (y - z)"
    show (sub (Fun x y) z) `shouldBe` "(x -> y) - z"
    show (sub x (Fun y z)) `shouldBe` "x - (y -> z)"

    show (Fun x (add y z)) `shouldBe` "x -> y + z"
    show (Fun (add x y) z) `shouldBe` "x + y -> z"
    show (Fun (Fun x y) z) `shouldBe` "(x -> y) -> z"
    show (Fun x (Fun y z)) `shouldBe` "x -> y -> z"
    show (Fun x (lt y z)) `shouldBe` "x -> (y < z)"
    show (Fun (lt x y) z) `shouldBe` "(x < y) -> z"

    show (lt x (Fun y z)) `shouldBe` "x < y -> z"
    show (lt (Fun x y) z) `shouldBe` "x -> y < z"
    show (lt (lt x y) z) `shouldBe` "(x < y) < z"
    show (lt x (lt y z)) `shouldBe` "x < y < z"
    show (lt (eq x y) z) `shouldBe` "(x == y) < z"
    show (lt x (eq y z)) `shouldBe` "x < (y == z)"

    show (eq x (lt y z)) `shouldBe` "x == y < z"
    show (eq (lt x y) z) `shouldBe` "x < y == z"
    show (eq (eq x y) z) `shouldBe` "x == y == z"
    show (eq x (eq y z)) `shouldBe` "x == (y == z)"
    show (eq (Ann x ty) z) `shouldBe` "(x : y) == z"
    show (eq x (Ann y tz)) `shouldBe` "x == (y : z)"

    show (Ann x (For [] (eq y z))) `shouldBe` "x : y == z"
    show (Ann (eq x y) tz) `shouldBe` "x == y : z"
    show (Ann x (For [] (Ann y tz))) `shouldBe` "x : y : z"
    show (Ann (Ann x ty) tz) `shouldBe` "(x : y) : z"
    show (Ann (Or x y) tz) `shouldBe` "(x | y) : z"
    show (Ann x (For [] (Or y z))) `shouldBe` "x : (y | z)"

    show (Lam "x" (Ann y tz)) `shouldBe` "\\x. (y : z)"
    show (Lam "x" (eq y z)) `shouldBe` "\\x. y == z"
    show (Ann (Lam "x" y) tz) `shouldBe` "(\\x. y) : z"
    show (Or (Lam "x" y) z) `shouldBe` "\\x. y | z"
    show (Or x (Lam "y" z)) `shouldBe` "x | \\y. z"

    show (Fix "x" (Ann y tz)) `shouldBe` "@fix x. (y : z)"
    show (Fix "x" (eq y z)) `shouldBe` "@fix x. y == z"
    show (Ann (Fix "x" y) tz) `shouldBe` "(@fix x. y) : z"
    show (Or (Fix "x" y) z) `shouldBe` "@fix x. y | z"
    show (Or x (Fix "y" z)) `shouldBe` "x | @fix y. z"

    show (Or x (Ann y tz)) `shouldBe` "x | y : z"
    show (Or (Ann x ty) z) `shouldBe` "x : y | z"
    show (Or x (Or y z)) `shouldBe` "x | y | z"
    show (Or (Or x y) z) `shouldBe` "(x | y) | z"

    show (If x (Ann y tz)) `shouldBe` "x; y : z"
    show (If (Ann x ty) z) `shouldBe` "x : y; z"
    show (If x (If y z)) `shouldBe` "x; y; z"
    show (If (If x y) z) `shouldBe` "(x; y); z"

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
    eval [] Err `shouldBe` Err
    eval [] Typ `shouldBe` Typ
    eval [] IntT `shouldBe` IntT
    eval [] NumT `shouldBe` NumT
    eval [] (Int 1) `shouldBe` Int 1
    eval [] (Num 1.1) `shouldBe` Num 1.1
  -- eval [] (Typ "T") `shouldBe` Typ "T"
  -- eval [] (Ctr "T" "A") `shouldBe` Ctr "T" "A"

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
    let env = [("x", i0), ("y", i1), ("z", i2)]
    eval env (Or x Err) `shouldBe` i0
    eval env (Or Err y) `shouldBe` i1
    eval env (Or x y) `shouldBe` Or i0 i1
    eval env (Or x (Or y z)) `shouldBe` Or i0 (Or i1 i2)
    eval env (Or (Or x y) z) `shouldBe` Or i0 (Or i1 i2)

  it "☯ eval App" $ do
    let env = [("x", i1), ("f", g), ("g", g), ("h", h)]
    eval env (App (Var "f") Typ) `shouldBe` App g Typ
    -- eval env (App (Lam TypP x) y) `shouldBe` App (Lam TypP i1) y
    -- eval env (App (Lam TypP x) Typ) `shouldBe` i1
    -- eval env (App (Lam TypP x) IntT) `shouldBe` Err
    -- eval env (App (Lam IntTP x) IntT) `shouldBe` i1
    -- eval env (App (Lam (IntP 1) x) i1) `shouldBe` i1
    -- eval env (App (Lam (IntP 1) x) i2) `shouldBe` Err
    -- eval env (App (Lam (VarP "x") x) Typ) `shouldBe` Typ
    -- eval env (App (Lam (VarP "y") x) Typ) `shouldBe` i1
    -- eval env (App (Lam (CtrP "A") x) (Ctr "A")) `shouldBe` i1
    -- eval env (App (Lam (CtrP "A") x) (Ctr "B")) `shouldBe` Err
    -- eval env (App (Lam (TypP "T") x) (Typ "T")) `shouldBe` i1
    -- eval env (App (Lam (TypP "T") x) (Typ "U")) `shouldBe` Err
    -- eval env (App (Lam (AppP (CtrP "B") x') x) (App (Ctr "B") Typ)) `shouldBe` Typ
    -- eval env (App (Lam (AppP (TypP "U") x') x) (App (Typ "U") Typ)) `shouldBe` Typ
    -- eval env (App (Lam (FunP TypP x') x) (Fun IntT Typ)) `shouldBe` Err
    -- eval env (App (Lam (FunP IntTP x') x) (Fun IntT Typ)) `shouldBe` Typ
    -- eval env (App (Lam ErrP x) Typ) `shouldBe` Err
    -- eval env (App (Lam ErrP x) Err) `shouldBe` i1
    eval env (App (Or Err Err) Typ) `shouldBe` Err
    eval env (App (Or Err f) Typ) `shouldBe` App g Typ
    eval env (App (Or f Err) Typ) `shouldBe` App g Typ
    eval env (App (Or f h) Typ) `shouldBe` Or (App g Typ) (App h Typ)
    -- eval env (App (Fix "f" (Lam x' (App h f))) Typ) `shouldBe` App h (Fix "f" (Lam x' (App h f)))
    eval env (App Err Typ) `shouldBe` Err
    eval env (App Err Typ) `shouldBe` Err

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
    infer [] Err `shouldBe` Right (Err, [])
    infer [] Typ `shouldBe` Right (Typ, [])
    infer [] IntT `shouldBe` Right (Typ, [])
    infer [] NumT `shouldBe` Right (Typ, [])
    infer [] (Int 1) `shouldBe` Right (IntT, [])
    infer [] (Num 1.1) `shouldBe` Right (NumT, [])

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
    infer env (Fun a b) `shouldBe` Right (Typ, [("aT", aT), ("a", Ann a (For [] aT))])

  it "☯ infer Ann" $ do
    infer [] (Ann i1 (For [] IntT)) `shouldBe` Right (IntT, [])
    infer [] (Ann i1 (For [] Typ)) `shouldBe` Left (TypeMismatch IntT Typ)
    infer [] (Ann i1 (For ["a"] a)) `shouldBe` Right (IntT, [("a", IntT)])
  -- infer [] (Ann (Typ "T") (For [] IntT)) `shouldBe` Right (IntT, [])
  -- infer [] (Ann (Ctr "T" "A") (For [] IntT)) `shouldBe` Right (IntT, [])

  it "☯ infer Lam" $ do
    let (t, xT, _T) = (Var "t", Var "xT", Var "_T")
    let env =
          [ ("x", Ann x (For [] a)),
            ("y", Int 1),
            ("a", a)
          ]
    infer env (Lam "x" x) `shouldBe` Right (Fun xT xT, [("xT", xT), ("x", Ann x $ For [] xT)])
    -- PFun !Pattern !Pattern
    -- PApp !Pattern !Pattern
    -- PErr
    True `shouldBe` True

  it "☯ infer App" $ do
    let t = Var "t"
    let env =
          [ ("x", i1),
            ("y", y),
            ("f", Ann (Var "f") (For [] $ Fun IntT Typ))
          ]
    infer env (App (Var "f") x) `shouldBe` Right (Typ, [])
    -- infer env (App (Lam y' y) x) `shouldBe` Right (IntT, [("yT", IntT), ("y", Ann y (For [] IntT)), ("t", IntT)])
    infer env (App y x) `shouldBe` Right (t, [("yT", Fun IntT t), ("y", Ann y (For [] (Fun IntT t))), ("t", t)])

  it "☯ infer Or" $ do
    let env = [("x", i1), ("y", IntT)]
    infer env (Or x x) `shouldBe` Right (IntT, [])
    infer env (Or x y) `shouldBe` Right (Or IntT Typ, [])

  it "☯ infer Fix" $ do
    True `shouldBe` True

  it "☯ infer Op2" $ do
    True `shouldBe` True

  it "☯ infer factorial" $ do
    let env = [("f", factorial "f")]
    infer env (Var "f") `shouldBe` Right (Fun IntT IntT, [("xT", IntT), ("x", Ann x (For [] IntT)), ("xT1", IntT), ("fT", Fun IntT IntT), ("f", Ann f (For [] (Fun IntT IntT))), ("t", IntT)])

  -- it "☯ infer Bool" $ do
  --   let env = [("Bool", or' [Tag "True", Tag "False"])]

  --   eval env (Tag "True") `shouldBe` Tag "True"
  --   eval env (Tag "Bool") `shouldBe` Or (Tag "True") (Tag "False")

  --   let infer' = fmap fst . infer env
  --   infer' (Tag "True") `shouldBe` Right (Var "true")
  --   infer' (Tag "Bool") `shouldBe` Right (Or (Tag "True") (Tag "False"))
  --   infer' (Ann (Tag "True") (For [] $ Tag "Bool")) `shouldBe` Right (Tag "True")
  --   infer' (Ann (Tag "False") (For [] $ Tag "Bool")) `shouldBe` Right (Tag "False")
  --   infer' (Ann (Tag "X") (For [] $ Tag "Bool")) `shouldBe` Left (TypeMismatch (Tag "X") (Tag "False"))

  it "☯ infer Maybe" $ do
    let maybe = App (Tag "Maybe")
    let just = App (Tag "Just")
    let nothing = Tag "Nothing"
    let env = [("Maybe", Lam "a" $ or' [Ann (Tag "Nothing") (For ["n", "a"] $ maybe a), Ann (Tag "Just") (For ["n", "a"] $ Fun a (maybe a))])]

    unify nothing (Ann (Tag "Nothing") (For ["a"] $ maybe a)) `shouldBe` Right (maybe a, [("a", a)])
    unify (just IntT) (Ann (Tag "Just") (For ["a"] $ Fun a (maybe a))) `shouldBe` Right (maybe IntT, [("a", IntT)])

    let infer' = fmap fst . infer env
    infer' (Tag "Nothing") `shouldBe` Right (Tag "Nothing")
    infer' (Tag "Just") `shouldBe` Right (Tag "Just")
    infer' (just i1) `shouldBe` Right (just IntT)
    infer' (Ann nothing (For [] $ maybe IntT)) `shouldBe` Right (maybe IntT)
    infer' (Ann (just i1) (For [] $ maybe IntT)) `shouldBe` Right (maybe IntT)
    infer' (Ann (just i1) (For [] $ maybe NumT)) `shouldBe` Left (TypeMismatch IntT NumT)

  it "☯ infer Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let vec n a = app (Tag "Vec") [n, a]
    let nil = Tag "Nil"
    let cons x xs = app (Tag "Cons") [x, xs]
    let nilType = For ["a"] (vec i0 a)
    let consType = For ["n", "a"] (fun [a, vec n a] (vec (add n i1) a))
    let env = [("Vec", lam ["n", "a"] (or' [Ann (Tag "Nil") nilType, Ann (Tag "Cons") consType]))]

    let infer' = fmap fst . infer env
    infer' nil `shouldBe` Right nil
    infer' (cons (Num 1.1) nil) `shouldBe` Right (cons NumT nil)
    infer' (Ann nil (For [] $ vec i0 NumT)) `shouldBe` Right (vec i0 NumT)
    infer' (Ann nil (For [] $ vec i1 NumT)) `shouldBe` Left (TypeMismatch i0 i1)
    infer' (Ann (cons (Num 1.1) nil) (For [] $ vec i1 NumT)) `shouldBe` Right (vec i1 NumT)
    infer' (Ann (cons (Num 1.1) $ cons (Num 2.2) nil) (For [] $ vec i0 NumT)) `shouldBe` Left (TypeMismatch i2 i0)
    infer' (Ann (cons (Num 1.1) $ cons (Num 2.2) nil) (For [] $ vec i2 NumT)) `shouldBe` Right (vec i2 NumT)

  -- it "☯ infer Nat" $ do
  --   let n = Var "n"
  --   let nat = App (Typ "Nat")
  --   let env =
  --         [ ("Nat", Ann (Typ "Nat") $ For ["n"] $ Fun n (or' [Ctr "Nat" "Zero", App (Ctr "Nat" "Succ") n])),
  --           ("Zero", Ann (Ctr "Nat" "Zero") $ For [] $ nat i0),
  --           ("Succ", Ann (Ctr "Nat" "Succ") $ For ["n"] $ Fun (nat n) (nat (add n i1)))
  --         ]

  --   let num :: Int -> Expr
  --       num 0 = Ctr "Nat" "Zero"
  --       num n = App (Ctr "Nat" "Succ") (num (n - 1))
  --   let infer' = fmap fst . infer env
  --   infer' (num 0) `shouldBe` Right (nat i0)
  --   infer' (num 1) `shouldBe` Right (nat i1)
  --   infer' (num 2) `shouldBe` Right (nat i2)

  -- it "☯ infer Vec" $ do
  --   let (n, a) = (Var "n", Var "a")
  --   let vec n a = app (Typ "Vec") [n, a]
  --   let env =
  --         [ ("Vec", Ann (Typ "Vec") $ For ["n", "a"] $ fun [n, a] (or' [Ctr "Vec" "Nil", app (Ctr "Vec" "Cons") [IntT, Typ]])),
  --           ("Nil", Ann (Ctr "Vec" "Nil") $ For ["a"] $ vec i0 a),
  --           ("Cons", Ann (Ctr "Vec" "Cons") $ For ["n", "a"] $ fun [a, vec n a] (vec (add n i1) a))
  --         ]

  --   let list [] = Ctr "Vec" "Nil"
  --       list (x : xs) = app (Ctr "Vec" "Cons") [x, list xs]
  --   let infer' = fmap fst . infer env
  --   infer' (list []) `shouldBe` Right (vec i0 a)
  --   infer' (list [Int 42]) `shouldBe` Right (vec i1 IntT)
  --   infer' (list [Int 42, Int 9]) `shouldBe` Right (vec i2 IntT)
  --   infer' (list [Int 42, Typ]) `shouldBe` Left (TypeMismatch Typ IntT)

  it "☯ TODO" $ do
    True `shouldBe` True
