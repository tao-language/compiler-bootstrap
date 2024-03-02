module CoreTests where

import Core
import Data.Bifunctor (Bifunctor (first))
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯️ Core language ☯️==--" $ do
  let err = Err NotImplementedError
  let (i0, i1, i2) = (Int 0, Int 1, Int 2)
  let (n1, n2, n3) = (Num 1.1, Num 2.2, Num 3.3)
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (f, g, h) = (Var "f", Var "g", Var "h")

  let factorial f = Fix f (or' branches)
        where
          branches =
            [ Fun i0 i1,
              lam [x] (x `mul` App (Var f) (x `sub` i1))
            ]

  it "☯ show" $ do
    let (ty, tz) = (for [] y, for [] z)
    show err `shouldBe` "$error NotImplementedError"
    show Knd `shouldBe` "$Type"
    show IntT `shouldBe` "$Int"
    show NumT `shouldBe` "$Num"
    show (Int 1) `shouldBe` "1"
    show (Num 1.1) `shouldBe` "1.1"
    -- show (Knd "T") `shouldBe` "$T"
    -- show (Ctr "T" "A") `shouldBe` "$T.A"
    show (Var "x") `shouldBe` "x"

    -- show (pow (pow x y) z) `shouldBe` "(x^y)^z"
    -- show (pow x (pow y z)) `shouldBe` "x^y^z"
    -- show (pow (App x y) z) `shouldBe` "(x y)^z"
    -- show (pow x (App y z)) `shouldBe` "x^(y z)"

    -- show (App x (pow y z)) `shouldBe` "x y^z"
    -- show (App (pow x y) z) `shouldBe` "x^y z"
    -- show (App (App x y) z) `shouldBe` "x y z"
    -- show (App x (App y z)) `shouldBe` "x (y z)"
    -- show (App (mul x y) z) `shouldBe` "(x * y) z"
    -- show (App x (mul y z)) `shouldBe` "x (y * z)"

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

    -- show (mul x (App y z)) `shouldBe` "x * y z"
    -- show (mul (App x y) z) `shouldBe` "x y * z"
    -- show (mul (mul x y) z) `shouldBe` "x * y * z"
    -- show (mul x (mul y z)) `shouldBe` "x * (y * z)"
    -- show (mul (add x y) z) `shouldBe` "(x + y) * z"
    -- show (mul x (add y z)) `shouldBe` "x * (y + z)"

    -- show (add x (mul y z)) `shouldBe` "x + y * z"
    -- show (add (mul x y) z) `shouldBe` "x * y + z"
    -- show (add (add x y) z) `shouldBe` "x + y + z"
    -- show (add x (add y z)) `shouldBe` "x + (y + z)"
    -- show (sub (add x y) z) `shouldBe` "x + y - z"
    -- show (sub x (add y z)) `shouldBe` "x - (y + z)"
    -- show (sub (sub x y) z) `shouldBe` "x - y - z"
    -- show (sub x (sub y z)) `shouldBe` "x - (y - z)"
    -- show (sub (fun [x] y) z) `shouldBe` "(x -> y) - z"
    -- show (sub x (fun [y] z)) `shouldBe` "x - (y -> z)"

    -- show (fun [x] (add y z)) `shouldBe` "x -> y + z"
    -- show (fun [add x y] z) `shouldBe` "x + y -> z"
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

    show (Ann x (for [] (eq y z))) `shouldBe` "x : y == z"
    show (Ann (eq x y) tz) `shouldBe` "x == y : z"
    show (Ann x (for [] (Ann y tz))) `shouldBe` "x : y : z"
    show (Ann (Ann x ty) tz) `shouldBe` "(x : y) : z"
    show (Ann (Or x y) tz) `shouldBe` "(x | y) : z"
    show (Ann x (for [] (Or y z))) `shouldBe` "x : (y | z)"

    show (For "x" (Ann y tz)) `shouldBe` "@x. (y : z)"
    show (For "x" (eq y z)) `shouldBe` "@x. y == z"
    show (Ann (For "x" y) tz) `shouldBe` "(@x. y) : z"
    show (Or (For "x" y) z) `shouldBe` "@x. y | z"
    show (Or x (For "y" z)) `shouldBe` "x | @y. z"

    show (Or x (Ann y tz)) `shouldBe` "x | y : z"
    show (Or (Ann x ty) z) `shouldBe` "x : y | z"
    show (Or x (Or y z)) `shouldBe` "x | y | z"
    show (Or (Or x y) z) `shouldBe` "(x | y) | z"

  -- show (If x (Ann y tz)) `shouldBe` "x ? y : z"
  -- show (If (Ann x ty) z) `shouldBe` "x : y ? z"
  -- show (If x (If y z)) `shouldBe` "x ? y ? z"
  -- show (If (If x y) z) `shouldBe` "(x ? y) ? z"

  it "☯ syntax sugar" $ do
    -- let' [] x `shouldBe` x
    -- let' [(y', z)] x `shouldBe` App (Fun y' x) z

    -- or' [] `shouldBe` err
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

    -- lam [] x `shouldBe` x
    -- lam [y'] x `shouldBe` Fun y' x

    app x [] `shouldBe` x
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ eval const" $ do
    eval [] Knd `shouldBe` Knd
    eval [] IntT `shouldBe` IntT
    eval [] NumT `shouldBe` NumT
    eval [] (Int 1) `shouldBe` Int 1
    eval [] (Num 1.1) `shouldBe` Num 1.1
    eval [] err `shouldBe` err

  it "☯ eval Var" $ do
    let env = [("x", i1), ("y", y), ("b", Ann b (for [] IntT)), ("a", b), ("c", Ann c (for ["a"] a))]
    eval env (Var "x") `shouldBe` Int 1
    eval env (Var "y") `shouldBe` Var "y"
    eval env (Var "z") `shouldBe` Var "z"
    eval env (Var "a") `shouldBe` Var "b"
    eval env (Var "c") `shouldBe` Var "c"

  it "☯ eval Fun" $ do
    let env = [("x", i1)]
    eval env (Fun x x) `shouldBe` Fun i1 i1
    eval env (For "x" $ Fun x x) `shouldBe` For "x" (Fun x x)

  it "☯ eval Fun" $ do
    let env = [("x", i1), ("y", i2)]
    eval env (Fun x y) `shouldBe` Fun i1 i2

  it "☯ eval Or" $ do
    let env = [("x", i0), ("y", i1), ("z", i2)]
    eval env (Or x err) `shouldBe` i0
    eval env (Or err y) `shouldBe` i1
    eval env (Or x y) `shouldBe` Or i0 i1
    eval env (Or x (Or y z)) `shouldBe` Or i0 (Or i1 i2)
    eval env (Or (Or x y) z) `shouldBe` Or i0 (Or i1 i2)

  it "☯ eval App" $ do
    let env = [("x", i1), ("f", g), ("g", g), ("h", h)]
    eval env (App (Var "f") Knd) `shouldBe` App g Knd
    eval env (App (Or err err) Knd) `shouldBe` err
    eval env (App (Or err f) Knd) `shouldBe` App g Knd
    eval env (App (Or f err) Knd) `shouldBe` App g Knd
    eval env (App (Or f h) Knd) `shouldBe` Or (App g Knd) (App h Knd)
    -- eval env (App (For "f" (Fun x' (App h f))) Knd) `shouldBe` App h (For "f" (Fun x' (App h f)))
    eval env (App err Knd) `shouldBe` err
    eval env (App err Knd) `shouldBe` err

  it "☯ eval Ann" $ do
    let env = []
    eval env (Ann Knd Knd) `shouldBe` Knd
    -- eval env (Ann Knd IntT) `shouldBe` err
    eval env (Ann IntT Knd) `shouldBe` IntT
    eval env (Ann NumT Knd) `shouldBe` NumT
    eval env (Ann (Int 1) IntT) `shouldBe` Int 1
    eval env (Ann (Num 1.1) NumT) `shouldBe` Num 1.1
    eval env (Ann (Tag "A") (Tag "A")) `shouldBe` Tag "A"
    -- eval env (Ann (Tag "A") (Tag "B")) `shouldBe` ann (Tag "A") (Tag "B")
    -- eval env (Ann (Tag "A") (ann (Tag "A") (Tag "B"))) `shouldBe` ann (Tag "A") (Tag "B")
    -- eval env (Ann (Tag "A") (ann (Tag "B") (Tag "A"))) `shouldBe` err
    -- eval env (Ann (Var "x") IntT) `shouldBe` Ann x (for [] IntT)
    -- eval env (Ann (Fun "x" x) (Fun IntT IntT)) `shouldBe` ann (Fun "x" x) (Fun IntT IntT)
    -- eval env (Ann (For "x" (Fun "y" x)) (Fun IntT NumT)) `shouldBe` For "x" (ann (Fun "y" x) (Fun IntT NumT))
    -- eval env (Ann (Fun IntT NumT) (Fun Knd Knd)) `shouldBe` err
    -- Fun
    -- Or
    -- If
    -- eval env (Ann (App (Tag "A") i1) NumT) `shouldBe` ann (App (Tag "A") i1) NumT
    -- eval env (Ann (App (Tag "A") i1) (App (Tag "A") IntT)) `shouldBe` App (Tag "A") i1
    -- eval env (Ann (App (Tag "A") i1) (App (Tag "A") NumT)) `shouldBe` App (Tag "A") err
    -- Fst
    -- Snd
    -- Op1
    -- Op2
    -- eval env (ann (ann i1 IntT) IntT) `shouldBe` i1
    -- eval env (ann (ann i1 NumT) IntT) `shouldBe` err
    -- eval env (ann (ann i1 IntT) NumT) `shouldBe` err
    -- eval env (ann err IntT) `shouldBe` err
    -- eval env (ann i1 err) `shouldBe` err
    -- eval env (Ann (Fun "_" a) (for ["a"] $ Fun a Knd)) `shouldBe` IntT
    True `shouldBe` True

  it "☯ eval Op2" $ do
    let env = []
    eval env (add x y) `shouldBe` add x y
    eval env (add x i2) `shouldBe` add x i2
    eval env (add i1 y) `shouldBe` add i1 y

    eval env (add i1 i2) `shouldBe` Int 3
    eval env (sub i1 i2) `shouldBe` Int (-1)
    eval env (mul i1 i2) `shouldBe` Int 2

  it "☯ eval let'" $ do
    let env = [("x", i1)]
    eval env (let' (x, x) x) `shouldBe` i1
    eval env (let' (x, y) x) `shouldBe` y
    eval env (let' (x, y) z) `shouldBe` z

  it "☯ eval lets" $ do
    eval [] (lets [(x, i1), (y, x)] x) `shouldBe` i1
    eval [] (lets [(x, i1), (y, x)] y) `shouldBe` i1
    eval [] (lets [(x, y), (y, i1)] x) `shouldBe` y
    eval [] (lets [(x, y), (y, i1)] y) `shouldBe` i1

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

  it "☯ unify" $ do
    let maybe = App (Tag "Maybe")
    -- unify Knd Knd `shouldBe` Right []
    -- IntT
    -- NumT
    -- Int !Int
    -- Num !Double
    -- Tag !String
    -- Var !String
    -- Ann !Expr !Type
    -- unify (Tag "Nothing") (Ann (Tag "Nothing") (for ["a"] $ maybe a)) `shouldBe` Right []
    -- unify (App (Tag "Just") IntT) (Ann (Tag "Just") (for ["a"] $ Fun a (maybe a))) `shouldBe` Right [("a", IntT)]
    -- Fun !String !Expr
    -- For !String !Expr
    -- Fun !Expr !Expr
    -- Or !Expr !Expr
    -- If !Expr !Expr
    -- App !Expr !Expr
    -- Fst !Expr
    -- Snd !Expr
    -- Op1 !UnaryOp !Expr
    -- Op2 !BinaryOp !Expr !Expr
    -- Err !Error
    True `shouldBe` True

  it "☯ infer const" $ do
    infer [] Knd `shouldBe` (Knd, [])
    infer [] IntT `shouldBe` (Knd, [])
    infer [] NumT `shouldBe` (Knd, [])
    infer [] (Int 1) `shouldBe` (IntT, [])
    infer [] (Num 1.1) `shouldBe` (NumT, [])
    infer [] err `shouldBe` (err, [])

  it "☯ infer Var" $ do
    let (a1, yT) = (Var "a1", Var "yT")
    let env = [("x", i1), ("y", y), ("b", Ann b (for [] IntT)), ("a", b), ("c", Ann c (for ["a"] a))]
    infer env (Var "x") `shouldBe` (IntT, [])
    infer env (Var "y") `shouldBe` (yT, [("yT", yT), ("y", Ann y (for [] yT))])
    infer env (Var "z") `shouldBe` (Err $ UndefinedVar "z", [])
    infer env (Var "a") `shouldBe` (IntT, [])
    infer env (Var "c") `shouldBe` (a1, [("a1", a1)])

  it "☯ infer Ann" $ do
    let env = []
    infer env (Ann i1 IntT) `shouldBe` (IntT, [])
    infer env (Ann i1 Knd) `shouldBe` (Err $ TypeMismatch IntT Knd, [])
    infer env (Ann i1 (for ["a"] a)) `shouldBe` (IntT, [("a", IntT)])

  it "☯ infer Fun" $ do
    let (t, xT, _T) = (Var "t", Var "xT", Var "_T")
    let env =
          [ ("x", Ann x a),
            ("y", Int 1),
            ("a", a)
          ]
    infer env (Fun x x) `shouldBe` (Fun a a, [])

  it "☯ infer Fun" $ do
    let env = [("a", Int 1), ("b", Num 1.1)]
    infer env (Fun a b) `shouldBe` (Fun IntT NumT, [])

  it "☯ infer App" $ do
    let t = Var "t"
    let env =
          [ ("x", i1),
            ("y", y),
            ("f", Ann (Var "f") (for [] $ fun [IntT] Knd))
          ]
    infer env (App (Var "f") x) `shouldBe` (Knd, [("t", Knd)])
    infer env (App (For "y" $ Fun y y) x) `shouldBe` (IntT, [("t", IntT), ("yT", IntT), ("y", Ann y (for [] IntT))])
    infer env (App y x) `shouldBe` (t, [("t", t), ("yT", fun [IntT] t), ("y", Ann y (for [] (fun [IntT] t)))])

  it "☯ infer Or" $ do
    let env = [("x", i1), ("y", IntT)]
    infer env (Or x x) `shouldBe` (IntT, [])
    infer env (Or x y) `shouldBe` (Or IntT Knd, [])

  it "☯ infer For" $ do
    True `shouldBe` True

  it "☯ infer Op2" $ do
    True `shouldBe` True

  it "☯ infer factorial" $ do
    let env = [("f", factorial "f")]
    infer env (Var "f") `shouldBe` (fun [IntT] IntT, [("xT", IntT), ("x", Ann x (for [] IntT)), ("t", IntT), ("fT", fun [IntT] IntT), ("f", Ann f (for [] (fun [IntT] IntT)))])

  it "☯ infer Union" $ do
    let env = [("T", or' [Tag "A", Tag "B"])]
    infer env (Tag "T") `shouldBe` (or' [Tag "A", Tag "B"], [])
    infer env (Ann (Tag "A") (Tag "A")) `shouldBe` (Tag "A", [])
    infer env (Ann (Tag "A") (Tag "T")) `shouldBe` (Tag "A", [])
    infer env (Ann (Tag "B") (Tag "T")) `shouldBe` (Tag "B", [])
    infer env (Ann (Tag "C") (Tag "T")) `shouldBe` (Err $ TypeMismatch (Tag "C") (Tag "B"), [])

  it "☯ infer Bool" $ do
    let (bool, true, false) = (Tag "Bool", Tag "True", Tag "False")
    let boolType = Typ "Bool" ["True", "False"]
    let env =
          [ ("Bool", Ann boolType Knd),
            ("True", Ann true bool),
            ("False", Ann false bool)
          ]

    let infer' = fst . infer env
    infer' (Tag "Bool") `shouldBe` Knd
    infer' (Tag "True") `shouldBe` boolType
    infer' (Ann true bool) `shouldBe` boolType
    infer' (Ann false (Tag "X")) `shouldBe` Err (TypeMismatch bool (Tag "X"))
    infer' (Ann (Tag "X") bool) `shouldBe` Err (TypeMismatch (Tag "X") bool)

  it "☯ infer Maybe" $ do
    let (maybe, just, nothing) = (Tag "Maybe", Tag "Just", Tag "Nothing")
    let maybeType = Typ "Maybe" ["Just", "Nothing"]
    let env =
          [ ("Maybe", Ann maybeType (for ["a"] $ Fun a Knd)),
            ("Just", Ann (Tag "Just") (for ["a"] $ Fun a (App maybe a))),
            ("Nothing", Ann (Tag "Nothing") (for ["a"] $ App maybe a))
          ]

    let infer' = fst . infer env
    infer' (Tag "Maybe") `shouldBe` Fun a Knd
    infer' (Tag "Nothing") `shouldBe` App maybeType a
    infer' (Tag "Just") `shouldBe` Fun a (App maybeType a)
    infer' (App just i1) `shouldBe` App maybeType IntT
    infer' (Ann nothing (App maybe IntT)) `shouldBe` App maybeType IntT
    infer' (Ann (App just i1) (App maybe IntT)) `shouldBe` App maybeType IntT
    infer' (Ann (App just i1) (App maybe NumT)) `shouldBe` App maybeType (Err (TypeMismatch IntT NumT))
    infer' (Ann (Tag "X") (App maybe IntT)) `shouldBe` Err (TypeMismatch (Tag "X") (App maybeType IntT))

  it "☯ infer Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let (vec, cons, nil) = (Tag "Vec", Tag "Cons", Tag "Nil")
    let vecType = Typ "Vec" ["Cons", "Nil"]
    let env =
          [ ("Vec", Ann vecType (fun [IntT, Knd] Knd)),
            ("Cons", Ann cons (for ["n", "a"] $ fun [a, app vec [n, a]] $ app vec [add n i1, a])),
            ("Nil", Ann nil (for ["a"] $ app vec [i0, a]))
          ]

    let infer' = fst . infer env
    infer' vec `shouldBe` fun [IntT, Knd] Knd
    infer' nil `shouldBe` app vecType [i0, a]
    infer' cons `shouldBe` fun [a, app vecType [n, a]] (app vecType [add n i1, a])
    infer' (app cons [Num 1.1, nil]) `shouldBe` app vecType [i1, NumT]
    infer' (app cons [Num 1.1, app cons [Num 2.2, nil]]) `shouldBe` app vecType [i2, NumT]
    infer' (Ann nil (app vec [i0, NumT])) `shouldBe` app vecType [i0, NumT]
    infer' (Ann nil (app vec [i1, NumT])) `shouldBe` app vecType [Err (TypeMismatch i0 i1), NumT]
    infer' (Ann (app cons [Num 1.1, nil]) (app vec [i1, NumT])) `shouldBe` app vecType [i1, NumT]
    infer' (Ann (app cons [Num 1.1, app cons [Num 2.2, nil]]) (app vec [i0, NumT])) `shouldBe` app vecType [Err (TypeMismatch i2 i0), NumT]
    infer' (Ann (app cons [Num 1.1, app cons [Num 2.2, nil]]) (app vec [i2, IntT])) `shouldBe` app vecType [i2, Err (TypeMismatch NumT IntT)]
    infer' (Ann (app cons [Num 1.1, app cons [Num 2.2, nil]]) (app vec [i2, NumT])) `shouldBe` app vecType [i2, NumT]

  it "☯ overload" $ do
    -- let m = App (Tag "M")
    -- let overloads =
    --       [ ann (lam [_x, _y] $ add x y) (fun [IntT, IntT] IntT),
    --         ann (lam [_x, _y] $ add (int2num x) y) (fun [IntT, NumT] NumT),
    --         ann (lam [_x, _y] $ Tag "C") (fun [Tag "T", Tag "T"] (Tag "T")),
    --         ann (lam [_x, _y] $ Tag "Z") (fun [Tag "U", Tag "U"] (Tag "U")),
    --         Ann (lam [_x, _y] $ Tag "N") (for ["a"] $ fun [m a, m a] (m a))
    --       ]

    -- let typeU = Typ "U" [] [("X", for [] (Tag "U")), ("Y", for [] (Tag "U")), ("Z", for [] (Tag "U"))]
    -- let typeM x = Typ "M" [x] [("N", for ["a"] $ App (Tag "M") a), ("J", for ["a"] $ Fun a (App (Tag "M") a))]
    -- let env =
    --       [ ("+", or' overloads),
    --         ("T", or' [Tag "A", Tag "B", Tag "C"]),
    --         ("U", typeU),
    --         ("M", Fun _x $ typeM x)
    --       ]

    -- let eval' = eval env
    -- eval' (app (Var "+") [Int 1, Int 2]) `shouldBe` Int 3
    -- eval' (app (Var "+") [Int 1, Num 2.2]) `shouldBe` Num 3.2
    -- -- eval' (app (Var "+") [Num 1.1, Int 2]) `shouldBe` err
    -- eval' (app (Var "+") [Tag "A", Tag "B"]) `shouldBe` Tag "C"
    -- eval' (app (Var "+") [Tag "X", Tag "Y"]) `shouldBe` ann (Tag "Z") typeU
    -- eval' (app (Var "+") [Tag "N", Tag "N"]) `shouldBe` Ann (Tag "N") (for ["a"] $ typeM a)
    -- eval' (app (Var "+") [App (Tag "J") i1, Tag "N"]) `shouldBe` ann (Tag "N") (typeM IntT)
    True `shouldBe` True
