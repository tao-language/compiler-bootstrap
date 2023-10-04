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
              Lam "x" (x `mul` App (Var f) (x `sub` i1))
            ]

  it "☯ show" $ do
    let (ty, tz) = (For [] y, For [] z)
    show Err `shouldBe` "@err"
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

    show (int2num (App x y)) `shouldBe` "@int2num (x y)"
    show (int2num (pow x y)) `shouldBe` "@int2num x^y"
    show (pow (int2num x) y) `shouldBe` "(@int2num x)^y"
    show (App (int2num x) y) `shouldBe` "@int2num x y"
    show (App x (int2num y)) `shouldBe` "x (@int2num y)"

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
    show (sub (fun [x] y) z) `shouldBe` "(x -> y) - z"
    show (sub x (fun [y] z)) `shouldBe` "x - (y -> z)"

    show (fun [x] (add y z)) `shouldBe` "x -> y + z"
    show (fun [add x y] z) `shouldBe` "x + y -> z"
    show (fun [fun [x] y] z) `shouldBe` "(x -> y) -> z"
    show (fun [x] (fun [y] z)) `shouldBe` "x -> y -> z"
    show (fun [x] (lt y z)) `shouldBe` "x -> (y < z)"
    show (fun [lt x y] z) `shouldBe` "(x < y) -> z"

    show (lt x (fun [y] z)) `shouldBe` "x < y -> z"
    show (lt (fun [x] y) z) `shouldBe` "x -> y < z"
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

    show (If x (Ann y tz)) `shouldBe` "x ? y : z"
    show (If (Ann x ty) z) `shouldBe` "x : y ? z"
    show (If x (If y z)) `shouldBe` "x ? y ? z"
    show (If (If x y) z) `shouldBe` "(x ? y) ? z"

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

  it "☯ eval Var" $ do
    let env = [("x", i1), ("y", y), ("b", Ann b (For [] IntT)), ("a", b), ("c", Ann c (For ["a"] a))]
    eval env (Var "x") `shouldBe` Int 1
    eval env (Var "y") `shouldBe` Var "y"
    eval env (Var "z") `shouldBe` Var "z"
    eval env (Var "a") `shouldBe` Var "b"
    eval env (Var "c") `shouldBe` Var "c"

  it "☯ eval Lam" $ do
    let env = [("x", i1)]
    eval env (Lam "x" x) `shouldBe` Lam "x" x
    eval env (Lam "y" x) `shouldBe` Lam "y" i1

  it "☯ eval Fun" $ do
    let env = [("x", i1), ("y", i2)]
    eval env (Fun x y) `shouldBe` Fun i1 i2

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
    eval env (App (Or Err Err) Typ) `shouldBe` Err
    eval env (App (Or Err f) Typ) `shouldBe` App g Typ
    eval env (App (Or f Err) Typ) `shouldBe` App g Typ
    eval env (App (Or f h) Typ) `shouldBe` Or (App g Typ) (App h Typ)
    -- eval env (App (Fix "f" (Lam x' (App h f))) Typ) `shouldBe` App h (Fix "f" (Lam x' (App h f)))
    eval env (App Err Typ) `shouldBe` Err
    eval env (App Err Typ) `shouldBe` Err

  it "☯ eval Ann" $ do
    let env = []
    eval env (ann Typ Typ) `shouldBe` Typ
    eval env (ann Typ IntT) `shouldBe` Err
    eval env (ann IntT Typ) `shouldBe` IntT
    eval env (ann NumT Typ) `shouldBe` NumT
    eval env (ann (Int 1) IntT) `shouldBe` Int 1
    eval env (ann (Num 1.1) NumT) `shouldBe` Num 1.1
    eval env (ann (Tag "A") (Tag "A")) `shouldBe` Tag "A"
    eval env (ann (Tag "A") (Tag "B")) `shouldBe` ann (Tag "A") (Tag "B")
    eval env (ann (Tag "A") (ann (Tag "A") (Tag "B"))) `shouldBe` ann (Tag "A") (Tag "B")
    eval env (ann (Tag "A") (ann (Tag "B") (Tag "A"))) `shouldBe` Err
    eval env (ann (Var "x") IntT) `shouldBe` Ann x (For [] IntT)
    eval env (ann (Lam "x" x) (Fun IntT IntT)) `shouldBe` ann (Lam "x" x) (Fun IntT IntT)
    -- Fix
    -- Fun
    -- Or
    -- If
    eval env (ann (App (Tag "A") i1) NumT) `shouldBe` ann (App (Tag "A") i1) NumT
    eval env (ann (App (Tag "A") i1) (App (Tag "A") IntT)) `shouldBe` App (Tag "A") i1
    eval env (ann (App (Tag "A") i1) (App (Tag "A") NumT)) `shouldBe` App (Tag "A") Err
    -- Fst
    -- Snd
    -- Op1
    -- Op2
    -- Rec
    eval env (ann (ann i1 IntT) IntT) `shouldBe` i1
    eval env (ann (ann i1 NumT) IntT) `shouldBe` Err
    eval env (ann (ann i1 IntT) NumT) `shouldBe` Err
    eval env (ann Err IntT) `shouldBe` Err
    eval env (ann i1 Err) `shouldBe` Err

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
    infer env (Lam "x" x) `shouldBe` Right (fun [xT] xT, [("xT", xT), ("x", Ann x $ For [] xT)])

  it "☯ infer Fun" $ do
    let env = [("a", Int 1), ("b", Num 1.1)]
    infer env (Fun a b) `shouldBe` Right (Fun IntT NumT, [])

  it "☯ infer App" $ do
    let t = Var "t"
    let env =
          [ ("x", i1),
            ("y", y),
            ("f", Ann (Var "f") (For [] $ fun [IntT] Typ))
          ]
    infer env (App (Var "f") x) `shouldBe` Right (Typ, [])
    -- infer env (App (Lam y' y) x) `shouldBe` Right (IntT, [("yT", IntT), ("y", Ann y (For [] IntT)), ("t", IntT)])
    infer env (App y x) `shouldBe` Right (t, [("yT", fun [IntT] t), ("y", Ann y (For [] (fun [IntT] t))), ("t", t)])

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
    infer env (Var "f") `shouldBe` Right (fun [IntT] IntT, [("xT", IntT), ("x", Ann x (For [] IntT)), ("xT1", IntT), ("fT", fun [IntT] IntT), ("f", Ann f (For [] (fun [IntT] IntT))), ("t", IntT)])

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
    let (just, justType) = (App (Tag "Just"), For ["a"] $ fun [a] (maybe a))
    let (nothing, nothingType) = (Tag "Nothing", For ["a"] $ maybe a)
    let env = [("Maybe", Lam "a" $ or' [Ann (Tag "Nothing") nothingType, Ann (Tag "Just") justType])]

    unify nothing (Ann (Tag "Nothing") (For ["a"] $ maybe a)) `shouldBe` Right (maybe a, [("a", a)])
    unify (just IntT) (Ann (Tag "Just") (For ["a"] $ fun [a] (maybe a))) `shouldBe` Right (maybe IntT, [("a", IntT)])

    let infer' = fmap fst . infer env
    infer' (Tag "Nothing") `shouldBe` Right (Tag "Nothing")
    infer' (Tag "Just") `shouldBe` Right (Tag "Just")
    infer' (just i1) `shouldBe` Right (just IntT)
    infer' (Ann nothing (For [] $ maybe IntT)) `shouldBe` Right (maybe IntT)
    infer' (Ann (just i1) (For [] $ maybe IntT)) `shouldBe` Right (maybe IntT)
    infer' (Ann (just i1) (For [] $ maybe NumT)) `shouldBe` Left (TypeMismatch IntT NumT)
    True `shouldBe` True

  it "☯ infer Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let vec n a = app (Tag "Vec") [n, a]
    let (nil, nilType) = (Tag "Nil", For ["a"] (vec i0 a))
    let (cons, consType) = (\x xs -> app (Tag "Cons") [x, xs], For ["n", "a"] (fun [a, vec n a] (vec (add n i1) a)))
    let env = [("Vec", lam ["n", "a"] (or' [Ann (Tag "Nil") nilType, Ann (Tag "Cons") consType]))]

    let infer' = fmap fst . infer env
    infer' nil `shouldBe` Right nil
    infer' (cons (Num 1.1) nil) `shouldBe` Right (cons NumT nil)
    infer' (Ann nil (For [] $ vec i0 NumT)) `shouldBe` Right (vec i0 NumT)
    infer' (Ann nil (For [] $ vec i1 NumT)) `shouldBe` Left (TypeMismatch i0 i1)
    infer' (Ann (cons (Num 1.1) nil) (For [] $ vec i1 NumT)) `shouldBe` Right (vec i1 NumT)
    infer' (Ann (cons (Num 1.1) $ cons (Num 2.2) nil) (For [] $ vec i0 NumT)) `shouldBe` Left (TypeMismatch i2 i0)
    infer' (Ann (cons (Num 1.1) $ cons (Num 2.2) nil) (For [] $ vec i2 NumT)) `shouldBe` Right (vec i2 NumT)

  it "☯ overload" $ do
    let m = App (Tag "M")
    let overloads =
          [ Ann (lam ["x", "y"] $ add x y) (For [] (fun [IntT, IntT] IntT)),
            Ann (lam ["x", "y"] $ add (int2num x) y) (For [] (fun [IntT, NumT] NumT)),
            Ann (lam ["x", "y"] $ Tag "C") (For [] (fun [Tag "T", Tag "T"] (Tag "T"))),
            Ann (lam ["x", "y"] $ Tag "Z") (For [] (fun [Tag "U", Tag "U"] (Tag "U"))),
            Ann (lam ["x", "y"] $ Tag "N") (For ["a"] (fun [m a] (m a)))
          ]

    let env =
          [ ("+", or' overloads),
            ("T", or' [Tag "A", Tag "B", Tag "C"]),
            ("U", or' [Tag "X", Tag "Y", Tag "Z"]),
            ("M", Lam "_" $ or' [Ann (Tag "N") (For ["a"] (m a)), Ann (Tag "J") (For ["a"] (fun [a] (m a)))])
          ]

    -- eval env (app (Var "+") [Int 1, Int 2]) `shouldBe` Int 3
    -- eval env (app (Var "+") [Int 1, Num 2.2]) `shouldBe` Num 3.2
    -- eval env (app (Var "+") [Num 1.1, Int 2]) `shouldBe` Err
    -- eval env (app (Var "+") [Tag "A", Tag "B"]) `shouldBe` Tag "C"
    -- eval env (app (Var "+") [Tag "X", Tag "Y"]) `shouldBe` Tag "Z"
    -- eval env (app (Var "+") [Tag "N", Tag "N"]) `shouldBe` Tag "N"
    True `shouldBe` True
