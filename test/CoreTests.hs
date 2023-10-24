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
  let (_x, _y, _z) = (PVar "x", PVar "y", PVar "z")

  let factorial f = Fix f (or' branches)
        where
          branches =
            [ Lam (PInt 0) i1,
              Lam (PVar "x") (x `mul` App (Var f) (x `sub` i1))
            ]

  it "☯ show" $ do
    let (ty, tz) = (For [] y, For [] z)
    -- show (Err ) `shouldBe` "@error []"
    show Knd `shouldBe` "@Type"
    show IntT `shouldBe` "@Int"
    show NumT `shouldBe` "@Num"
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

    show (Ann x (For [] (eq y z))) `shouldBe` "x : y == z"
    show (Ann (eq x y) tz) `shouldBe` "x == y : z"
    show (Ann x (For [] (Ann y tz))) `shouldBe` "x : y : z"
    show (Ann (Ann x ty) tz) `shouldBe` "(x : y) : z"
    show (Ann (Or x y) tz) `shouldBe` "(x | y) : z"
    show (Ann x (For [] (Or y z))) `shouldBe` "x : (y | z)"

    show (Lam _x (Ann y tz)) `shouldBe` "\\x. (y : z)"
    show (Lam _x (eq y z)) `shouldBe` "\\x. y == z"
    show (Ann (Lam _x y) tz) `shouldBe` "(\\x. y) : z"
    show (Or (Lam _x y) z) `shouldBe` "\\x. y | z"
    show (Or x (Lam _y z)) `shouldBe` "x | \\y. z"

    show (Fix "x" (Ann y tz)) `shouldBe` "@fix x. (y : z)"
    show (Fix "x" (eq y z)) `shouldBe` "@fix x. y == z"
    show (Ann (Fix "x" y) tz) `shouldBe` "(@fix x. y) : z"
    show (Or (Fix "x" y) z) `shouldBe` "@fix x. y | z"
    show (Or x (Fix "y" z)) `shouldBe` "x | @fix y. z"

    show (Or x (Ann y tz)) `shouldBe` "x | y : z"
    show (Or (Ann x ty) z) `shouldBe` "x : y | z"
    show (Or x (Or y z)) `shouldBe` "x | y | z"
    show (Or (Or x y) z) `shouldBe` "(x | y) | z"

  -- show (If x (Ann y tz)) `shouldBe` "x ? y : z"
  -- show (If (Ann x ty) z) `shouldBe` "x : y ? z"
  -- show (If x (If y z)) `shouldBe` "x ? y ? z"
  -- show (If (If x y) z) `shouldBe` "(x ? y) ? z"

  it "☯ syntax sugar" $ do
    let' [] x `shouldBe` x
    -- let' [(y', z)] x `shouldBe` App (Lam y' x) z

    -- or' [] `shouldBe` err
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
    eval [] (Err (UndefinedVar "x")) `shouldBe` Err (UndefinedVar "x")

  it "☯ eval Var" $ do
    let env = [("x", i1), ("y", y), ("b", Ann b (For [] IntT)), ("a", b), ("c", Ann c (For ["a"] a))]
    eval env (Var "x") `shouldBe` Int 1
    eval env (Var "y") `shouldBe` Var "y"
    eval env (Var "z") `shouldBe` Var "z"
    eval env (Var "a") `shouldBe` Var "b"
    eval env (Var "c") `shouldBe` Var "c"

  it "☯ eval Lam" $ do
    let env = [("x", i1)]
    eval env (Lam _x x) `shouldBe` Lam _x x
    eval env (Lam _y x) `shouldBe` Lam _y i1

  it "☯ eval Fun" $ do
    let env = [("x", i1), ("y", i2)]
    eval env (Fun x y) `shouldBe` Fun i1 i2

  it "☯ eval Or" $ do
    let err = Err (UndefinedVar "error")
    let env = [("x", i0), ("y", i1), ("z", i2)]
    eval env (Or x err) `shouldBe` i0
    eval env (Or err y) `shouldBe` i1
    eval env (Or x y) `shouldBe` Or i0 i1
    eval env (Or x (Or y z)) `shouldBe` Or i0 (Or i1 i2)
    eval env (Or (Or x y) z) `shouldBe` Or i0 (Or i1 i2)

  it "☯ eval App" $ do
    let err = Err (UndefinedVar "error")
    let env = [("x", i1), ("f", g), ("g", g), ("h", h)]
    eval env (App (Var "f") Knd) `shouldBe` App g Knd
    eval env (App (Or err err) Knd) `shouldBe` err
    eval env (App (Or err f) Knd) `shouldBe` App g Knd
    eval env (App (Or f err) Knd) `shouldBe` App g Knd
    eval env (App (Or f h) Knd) `shouldBe` Or (App g Knd) (App h Knd)
    -- eval env (App (Fix "f" (Lam x' (App h f))) Knd) `shouldBe` App h (Fix "f" (Lam x' (App h f)))
    eval env (App err Knd) `shouldBe` err
    eval env (App err Knd) `shouldBe` err

  it "☯ eval Ann" $ do
    let env = []
    eval env (ann Knd Knd) `shouldBe` Knd
    -- eval env (ann Knd IntT) `shouldBe` err
    eval env (ann IntT Knd) `shouldBe` IntT
    eval env (ann NumT Knd) `shouldBe` NumT
    eval env (ann (Int 1) IntT) `shouldBe` Int 1
    eval env (ann (Num 1.1) NumT) `shouldBe` Num 1.1
    eval env (ann (Tag "A") (Tag "A")) `shouldBe` Tag "A"
    -- eval env (ann (Tag "A") (Tag "B")) `shouldBe` ann (Tag "A") (Tag "B")
    -- eval env (ann (Tag "A") (ann (Tag "A") (Tag "B"))) `shouldBe` ann (Tag "A") (Tag "B")
    -- eval env (ann (Tag "A") (ann (Tag "B") (Tag "A"))) `shouldBe` err
    -- eval env (ann (Var "x") IntT) `shouldBe` Ann x (For [] IntT)
    -- eval env (ann (Lam "x" x) (Fun IntT IntT)) `shouldBe` ann (Lam "x" x) (Fun IntT IntT)
    -- eval env (ann (Fix "x" (Lam "y" x)) (Fun IntT NumT)) `shouldBe` Fix "x" (ann (Lam "y" x) (Fun IntT NumT))
    -- eval env (ann (Fun IntT NumT) (Fun Knd Knd)) `shouldBe` err
    -- Fun
    -- Or
    -- If
    -- eval env (ann (App (Tag "A") i1) NumT) `shouldBe` ann (App (Tag "A") i1) NumT
    -- eval env (ann (App (Tag "A") i1) (App (Tag "A") IntT)) `shouldBe` App (Tag "A") i1
    -- eval env (ann (App (Tag "A") i1) (App (Tag "A") NumT)) `shouldBe` App (Tag "A") err
    -- Fst
    -- Snd
    -- Op1
    -- Op2
    -- Rec
    -- eval env (ann (ann i1 IntT) IntT) `shouldBe` i1
    -- eval env (ann (ann i1 NumT) IntT) `shouldBe` err
    -- eval env (ann (ann i1 IntT) NumT) `shouldBe` err
    -- eval env (ann err IntT) `shouldBe` err
    -- eval env (ann i1 err) `shouldBe` err
    -- eval env (Ann (Lam "_" a) (For ["a"] $ Fun a Knd)) `shouldBe` IntT
    True `shouldBe` True

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
    -- unify (Tag "Nothing") (Ann (Tag "Nothing") (For ["a"] $ maybe a)) `shouldBe` Right []
    -- unify (App (Tag "Just") IntT) (Ann (Tag "Just") (For ["a"] $ Fun a (maybe a))) `shouldBe` Right [("a", IntT)]
    -- Lam !String !Expr
    -- Fix !String !Expr
    -- Fun !Expr !Expr
    -- Or !Expr !Expr
    -- If !Expr !Expr
    -- App !Expr !Expr
    -- Fst !Expr
    -- Snd !Expr
    -- Op1 !UnaryOp !Expr
    -- Op2 !BinaryOp !Expr !Expr
    -- Rec ![(String, Expr)]
    -- Err ![Error]
    True `shouldBe` True

  it "☯ infer const" $ do
    infer [] Knd `shouldBe` Right (Knd, [])
    infer [] IntT `shouldBe` Right (Knd, [])
    infer [] NumT `shouldBe` Right (Knd, [])
    infer [] (Int 1) `shouldBe` Right (IntT, [])
    infer [] (Num 1.1) `shouldBe` Right (NumT, [])
    infer [] (Err (UndefinedVar "x")) `shouldBe` Right (Err (UndefinedVar "x"), [])

  it "☯ infer Var" $ do
    let (a1, yT) = (Var "a1", Var "yT")
    let env = [("x", i1), ("y", y), ("b", Ann b (For [] IntT)), ("a", b), ("c", Ann c (For ["a"] a))]
    infer env (Var "x") `shouldBe` Right (IntT, [])
    infer env (Var "y") `shouldBe` Right (yT, [("yT", yT), ("y", Ann y (For [] yT))])
    infer env (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer env (Var "a") `shouldBe` Right (IntT, [])
    infer env (Var "c") `shouldBe` Right (a1, [("a1", a1)])

  it "☯ infer Ann" $ do
    let env = []
    infer env (ann i1 IntT) `shouldBe` Right (IntT, [])
    infer env (ann i1 Knd) `shouldBe` Left (TypeMismatch IntT Knd)
    infer env (Ann i1 (For ["a"] a)) `shouldBe` Right (IntT, [("a", IntT)])

  it "☯ infer Lam" $ do
    let (t, xT, _T) = (Var "t", Var "xT", Var "_T")
    let env =
          [ ("x", Ann x (For [] a)),
            ("y", Int 1),
            ("a", a)
          ]
    infer env (Lam _x x) `shouldBe` Right (fun [xT] xT, [("xT", xT), ("x", Ann x $ For [] xT)])

  it "☯ infer Fun" $ do
    let env = [("a", Int 1), ("b", Num 1.1)]
    infer env (Fun a b) `shouldBe` Right (Fun IntT NumT, [])

  it "☯ infer App" $ do
    let t = Var "t"
    let env =
          [ ("x", i1),
            ("y", y),
            ("f", Ann (Var "f") (For [] $ fun [IntT] Knd))
          ]
    infer env (App (Var "f") x) `shouldBe` Right (Knd, [("t", Knd)])
    infer env (App (Lam _y y) x) `shouldBe` Right (IntT, [("t", IntT), ("yT", IntT), ("y", Ann y (For [] IntT))])
    infer env (App y x) `shouldBe` Right (t, [("t", t), ("yT", fun [IntT] t), ("y", Ann y (For [] (fun [IntT] t)))])

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
    infer env (Var "f") `shouldBe` Right (fun [IntT] IntT, [("xT", IntT), ("x", Ann x (For [] IntT)), ("t", IntT), ("fT", fun [IntT] IntT), ("f", Ann f (For [] (fun [IntT] IntT)))])

  it "☯ infer Union" $ do
    let env = [("T", or' [Tag "A", Tag "B"])]
    infer env (Tag "T") `shouldBe` Right (or' [Tag "A", Tag "B"], [])
    infer env (ann (Tag "A") (Tag "A")) `shouldBe` Right (Tag "A", [])
    infer env (ann (Tag "A") (Tag "T")) `shouldBe` Right (Tag "A", [])
    infer env (ann (Tag "B") (Tag "T")) `shouldBe` Right (Tag "B", [])
    infer env (ann (Tag "C") (Tag "T")) `shouldBe` Left (TypeMismatch (Tag "C") (Tag "B"))

  it "☯ infer Bool" $ do
    let boolType = Typ "Bool" [] [("True", For [] $ Tag "Bool"), ("False", For [] $ Tag "Bool")]
    let env = [("Bool", boolType)]

    let infer' = fmap fst . infer env
    infer' (Tag "True") `shouldBe` Right (Tag "True")
    infer' (Tag "Bool") `shouldBe` Right Knd
    infer' (ann (Tag "True") (Tag "Bool")) `shouldBe` Right boolType
    infer' (ann (Tag "False") (Tag "X")) `shouldBe` Left (TypeMismatch (Tag "False") (Tag "X"))
    infer' (ann (Tag "X") (Tag "Bool")) `shouldBe` Left (TypeMismatch (Tag "X") (Tag "Bool"))

  it "☯ infer Maybe" $ do
    let maybe = App (Tag "Maybe")
    let (nothing, nothingType) = (Tag "Nothing", For ["a"] $ maybe a)
    let (just, justType) = (App (Tag "Just"), For ["a"] $ Fun a (maybe a))
    let maybeType a = Typ "Maybe" [a] [("Nothing", nothingType), ("Just", justType)]
    let env = [("Maybe", Lam (PVar "a") $ maybeType a)]

    -- unify nothing (Ann (Tag "Nothing") nothingType) `shouldBe` Right (maybe a, [("a", a)])
    -- unify nothing (ann (maybe IntT) (Ann (Tag "Nothing") nothingType)) `shouldBe` Right (maybe IntT, [])
    -- unify (just IntT) (Ann (Tag "Just") justType) `shouldBe` Right (maybe IntT, [("a", IntT)])

    let infer' = fmap fst . infer env
    infer' (Tag "Nothing") `shouldBe` Right (Tag "Nothing")
    infer' (Tag "Just") `shouldBe` Right (Tag "Just")
    infer' (just i1) `shouldBe` Right (just IntT)
    infer' (ann nothing (maybe IntT)) `shouldBe` Right (maybeType IntT)
    infer' (ann (just i1) (maybe IntT)) `shouldBe` Right (maybeType IntT)
    infer' (ann (just i1) (maybe NumT)) `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (ann (Tag "X") (maybe IntT)) `shouldBe` Left (TypeMismatch (Tag "X") (maybe IntT))

  it "☯ infer Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let vec n a = app (Tag "Vec") [n, a]
    let (nil, nilType) = (Tag "Nil", For ["a"] (vec i0 a))
    let (cons, consType) = (\x xs -> app (Tag "Cons") [x, xs], For ["n", "a"] (fun [a, vec n a] (vec (add n i1) a)))
    let vecType n a = Typ "Vec" [n, a] [("Nil", nilType), ("Cons", consType)]
    let env = [("Vec", lam [PVar "n", PVar "a"] $ vecType n a)]

    let infer' = fmap fst . infer env
    infer' nil `shouldBe` Right nil
    infer' (cons (Num 1.1) nil) `shouldBe` Right (cons NumT nil)
    infer' (ann nil (vec i0 NumT)) `shouldBe` Right (vecType i0 NumT)
    infer' (ann nil (vec i1 NumT)) `shouldBe` Left (TypeMismatch i0 i1)
    infer' (ann (cons (Num 1.1) nil) (vec i1 NumT)) `shouldBe` Right (vecType i1 NumT)
    infer' (ann (cons (Num 1.1) $ cons (Num 2.2) nil) (vec i0 NumT)) `shouldBe` Left (TypeMismatch i2 i0)
    infer' (ann (cons (Num 1.1) $ cons (Num 2.2) nil) (vec i2 NumT)) `shouldBe` Right (vecType i2 NumT)

  it "☯ overload" $ do
    let m = App (Tag "M")
    let overloads =
          [ ann (lam [_x, _y] $ add x y) (fun [IntT, IntT] IntT),
            ann (lam [_x, _y] $ add (int2num x) y) (fun [IntT, NumT] NumT),
            ann (lam [_x, _y] $ Tag "C") (fun [Tag "T", Tag "T"] (Tag "T")),
            ann (lam [_x, _y] $ Tag "Z") (fun [Tag "U", Tag "U"] (Tag "U")),
            Ann (lam [_x, _y] $ Tag "N") (For ["a"] $ fun [m a, m a] (m a))
          ]

    let typeU = Typ "U" [] [("X", For [] (Tag "U")), ("Y", For [] (Tag "U")), ("Z", For [] (Tag "U"))]
    let typeM x = Typ "M" [x] [("N", For ["a"] $ App (Tag "M") a), ("J", For ["a"] $ Fun a (App (Tag "M") a))]
    let env =
          [ ("+", or' overloads),
            ("T", or' [Tag "A", Tag "B", Tag "C"]),
            ("U", typeU),
            ("M", Lam _x $ typeM x)
          ]

    let eval' = eval env
    eval' (app (Var "+") [Int 1, Int 2]) `shouldBe` Int 3
    eval' (app (Var "+") [Int 1, Num 2.2]) `shouldBe` Num 3.2
    -- eval' (app (Var "+") [Num 1.1, Int 2]) `shouldBe` err
    eval' (app (Var "+") [Tag "A", Tag "B"]) `shouldBe` Tag "C"
    eval' (app (Var "+") [Tag "X", Tag "Y"]) `shouldBe` ann (Tag "Z") typeU
    eval' (app (Var "+") [Tag "N", Tag "N"]) `shouldBe` Ann (Tag "N") (For ["a"] $ typeM a)
    eval' (app (Var "+") [App (Tag "J") i1, Tag "N"]) `shouldBe` ann (Tag "N") (typeM IntT)
