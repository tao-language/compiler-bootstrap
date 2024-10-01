module CoreTests where

import Core
import Data.Bifunctor (Bifunctor (first))
import Data.Char (toLower)
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯️ Core language ☯️==--" $ do
  let (i0, i1, i2) = (Int 0, Int 1, Int 2)
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (f, g, h) = (Var "f", Var "g", Var "h")

  let factorial f = Fix f (case0 `Or` caseN f)
        where
          case0 = Fun (Int 0) i1
          caseN f = lam [x] (x `mul` App (Var f) (x `sub` i1))

  it "☯ show" $ do
    show Err `shouldBe` "!error"
    show Knd `shouldBe` "!Kind"
    show IntT `shouldBe` "!Int"
    show NumT `shouldBe` "!Num"
    show (Int 1) `shouldBe` "1"
    show (Num 1.1) `shouldBe` "1.1"
    -- show (Typ "T") `shouldBe` "$T"
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

    show (int2num (App x y)) `shouldBe` "$i2n (x y)"
    show (int2num (pow x y)) `shouldBe` "$i2n x^y"
    show (pow (int2num x) y) `shouldBe` "($i2n x)^y"
    show (App (int2num x) y) `shouldBe` "$i2n x y"
    show (App x (int2num y)) `shouldBe` "x ($i2n y)"

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
    show (eq (Ann x y) z) `shouldBe` "(x : y) == z"
    show (eq x (Ann y z)) `shouldBe` "x == (y : z)"

    show (Ann x (eq y z)) `shouldBe` "x : y == z"
    show (Ann (eq x y) z) `shouldBe` "x == y : z"
    show (Ann x (Ann y z)) `shouldBe` "x : y : z"
    show (Ann (Ann x y) z) `shouldBe` "(x : y) : z"
    show (Ann (Or x y) z) `shouldBe` "(x | y) : z"
    show (Ann x (Or y z)) `shouldBe` "x : (y | z)"

    show (For "x" (Ann y z)) `shouldBe` "@x. (y : z)"
    show (For "x" (eq y z)) `shouldBe` "@x. y == z"
    show (Ann (For "x" y) z) `shouldBe` "(@x. y) : z"
    show (Or (For "x" y) z) `shouldBe` "@x. y | z"
    show (Or x (For "y" z)) `shouldBe` "x | @y. z"

    show (Or x (Ann y z)) `shouldBe` "x | y : z"
    show (Or (Ann x y) z) `shouldBe` "x : y | z"
    show (Or x (Or y z)) `shouldBe` "x | y | z"
    show (Or (Or x y) z) `shouldBe` "(x | y) | z"

  -- show (If x (Ann y z)) `shouldBe` "x ? y : z"
  -- show (If (Ann x y) z) `shouldBe` "x : y ? z"
  -- show (If x (If y z)) `shouldBe` "x ? y ? z"
  -- show (If (If x y) z) `shouldBe` "(x ? y) ? z"

  it "☯ syntax sugar" $ do
    -- let' [] x `shouldBe` x
    -- let' [(y', z)] x `shouldBe` App (Fun y' x) z

    -- lam [] x `shouldBe` x
    -- lam [y'] x `shouldBe` Fun y' x

    and' [] `shouldBe` Err
    and' [x] `shouldBe` x
    and' [x, y] `shouldBe` x `And` y

    tag "A" [] `shouldBe` Tag "A"
    tag "A" [x] `shouldBe` Tag "A" `And` x
    tag "A" [x, y] `shouldBe` Tag "A" `And` (x `And` y)

    app x [] `shouldBe` x
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ eval const" $ do
    eval [] Knd `shouldBe` Knd
    eval [] IntT `shouldBe` IntT
    eval [] NumT `shouldBe` NumT
    eval [] (Int 1) `shouldBe` Int 1
    eval [] (Num 1.1) `shouldBe` Num 1.1
    eval [] Err `shouldBe` Err

  it "☯ eval Var" $ do
    let env = [("x", i1), ("y", y), ("b", Ann b IntT), ("a", b), ("c", Ann c (for ["a"] a))]
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
    let env = [("x", i0), ("y", i1)]
    eval env (Or x y) `shouldBe` Or i0 i1

  it "☯ eval App" $ do
    let env = [("x", i1), ("f", g), ("g", g), ("h", h)]
    eval env (App (Var "f") IntT) `shouldBe` App g IntT
    eval env (App (Or Err f) IntT) `shouldBe` App g IntT
    eval env (App (Or f Err) IntT) `shouldBe` Or (App g IntT) (App Err IntT)
    eval env (App (Or f h) IntT) `shouldBe` Or (App g IntT) (App h IntT)
    eval env (App (Tag "A") IntT) `shouldBe` tag "A" [IntT]
    eval env (App (And (Tag "A") IntT) NumT) `shouldBe` tag "A" [IntT, NumT]
    eval env (App (lam [IntT] x) IntT) `shouldBe` Int 1
    eval env (App (lam [NumT] x) IntT) `shouldBe` Err
    eval env (App (lam [NumT] x) NumT) `shouldBe` Int 1
    eval env (App (lam [Var "x"] x) IntT) `shouldBe` IntT
    eval env (App (lam [tag "A" []] x) (tag "A" [])) `shouldBe` Int 1
    eval env (App (lam [tag "A" [x]] x) (tag "A" [IntT])) `shouldBe` IntT
    eval env (app (lam [IntT, NumT] x) [IntT, NumT]) `shouldBe` Int 1
    eval env (App Err IntT) `shouldBe` Err
    eval env (App Err IntT) `shouldBe` Err

  it "☯ eval Ann" $ do
    let env = [("x", i1)]
    eval env (Ann x IntT) `shouldBe` Int 1

  it "☯ eval Op" $ do
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
    unify (Ann (Tag "A") (Tag "T")) (Tag "T") `shouldBe` Right (Tag "T", [])

  it "☯ infer const" $ do
    infer [] Knd `shouldBe` Right (Knd, [])
    infer [] IntT `shouldBe` Right (IntT `Or` Knd, [])
    infer [] NumT `shouldBe` Right (NumT `Or` Knd, [])
    infer [] (Int 1) `shouldBe` Right (intT 1, [])
    infer [] (Num 1.1) `shouldBe` Right (numT 1.1, [])
    infer [] Err `shouldBe` Right (Err, [])

  it "☯ infer Var" $ do
    let (a1, yT) = (Var "a1", Var "yT")
    let env = [("x", i1), ("y", y), ("b", Ann b IntT), ("a", b), ("c", Ann c (for ["a"] a))]
    infer env (Var "x") `shouldBe` Right (intT 1, [])
    infer env (Var "y") `shouldBe` Right (yT, [("yT", yT), ("y", Ann y yT)])
    infer env (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer env (Var "a") `shouldBe` Right (IntT, [])
    infer env (Var "c") `shouldBe` Right (a1, [("a1", a1)])

  it "☯ infer Ann" $ do
    let env = []
    infer env (Ann i1 IntT) `shouldBe` Right (IntT, [])
    infer env (Ann i1 NumT) `shouldBe` Left (TypeCheck i1 NumT)
    infer env (Ann i1 (for ["a"] a)) `shouldBe` Right (intT 1, [("a", intT 1)])

  it "☯ infer Ann Tag" $ do
    let env = [("T", Tag "A" `Or` Tag "B")]
    -- infer env (Tag "T" []) `shouldBe` Right (Tag "A" [] `Or` Tag "B" [], [])
    -- infer env (Ann (Tag "A" []) (Tag "A" [])) `shouldBe` Right (Tag "A" [], [])
    infer env (Ann (Tag "A") (Tag "T")) `shouldBe` Right (Tag "T", [])
    -- infer env (Ann (Tag "B []) (Tag "T" [])) `shouldBe` Right (Tag "T" [], [])
    -- infer env (Ann (Tag "C" []) (Tag "T" [])) `shouldBe` Left (TypeMismatch (Ann (Tag "C" []) (Tag "T" [])) (Tag "A" [] `Or` Tag "B" []))
    True `shouldBe` True

  it "☯ infer Fun" $ do
    let (t, xT, _T) = (Var "t", Var "xT", Var "_T")
    let env =
          [ ("x", Ann x a),
            ("y", Int 1),
            ("a", a)
          ]
    infer env (Fun x x) `shouldBe` Right (Fun a a, [])

  it "☯ infer Fun" $ do
    let env = [("a", Ann a IntT), ("b", Ann b NumT)]
    infer env (Fun a b) `shouldBe` Right (Fun IntT NumT, [])

  it "☯ infer App" $ do
    let env =
          [ ("x", i1),
            ("y", y),
            ("f", Ann (Var "f") (Fun IntT NumT))
          ]
    infer env (App (Var "f") x) `shouldBe` Right (NumT, [])
    infer env (App (Fun y y) x) `shouldBe` Right (intT 1, [("yT", intT 1), ("y", Ann y (intT 1))])
    infer env (App y x) `shouldBe` Right (Var "yT1", [("yT1", Var "yT1"), ("yT", Fun (intT 1) (Var "yT1")), ("y", Ann y (Fun (intT 1) (Var "yT1")))])

  it "☯ infer Or" $ do
    let env = [("x", Int 42), ("y", Num 3.14)]
    infer env (Or x x) `shouldBe` Right (IntT, [])
    infer env (Or x y) `shouldBe` Right (intT 42 `Or` numT 3.14, [])

  it "☯ infer For" $ do
    True `shouldBe` True

  it "☯ infer Op2" $ do
    True `shouldBe` True

  it "☯ infer factorial" $ do
    let env = [("f", factorial "f")]
    infer env (Var "f") `shouldBe` Right (Fix "f" $ Fun (intT 0) (intT 1), [("xT", intT 0), ("x", Ann x (intT 0)), ("*T", intT 1), ("*", Ann (Op "*" []) (intT 1))])
    infer env (Ann (Var "f") (Fun IntT IntT)) `shouldBe` Right (Fun IntT IntT, [("x", Ann x IntT)])

  -- it "☯ infer Bool" $ do
  --   let (bool, true, false) = (Tag "Bool", Tag "True", Tag "False")
  --   let env = [("Bool", true `Or` false)]

  --   let infer' a = fmap fst (infer env a)
  --   infer' (Tag "True") `shouldBe` Right true
  --   infer' (Ann true bool) `shouldBe` Right bool
  --   infer' (Ann false (Tag "X")) `shouldBe` Left (TypeMismatch (Ann false (Tag "X")) (Tag "X"))
  --   infer' (Ann (Tag "X") bool) `shouldBe` Left (TypeMismatch (Ann (Tag "X") bool) (true `Or` false))

  -- it "☯ infer Maybe" $ do
  --   let (maybe, just, nothing) = (App (Tag "Maybe"), \a -> tag "Just" [a], Tag "Nothing")
  --   let env = [("Maybe", lam [PVar "a"] (nothing `Or` just a))]

  --   let infer' a = fmap fst (infer env a)
  --   infer' (Tag "Nothing") `shouldBe` Right (Tag "Nothing")
  --   infer' (Tag "Just") `shouldBe` Right (Tag "Just")
  --   infer' (just i1) `shouldBe` Right (just (Or (Int 1) IntT))
  --   infer' (Ann nothing (maybe IntT)) `shouldBe` Right (maybe IntT)
  --   infer' (Ann (just i1) (maybe IntT)) `shouldBe` Right (maybe IntT)
  --   infer' (Ann (just i1) (maybe NumT)) `shouldBe` Left (TypeMismatch (just (Int 1 `Or` IntT)) (nothing `Or` just NumT))
  --   infer' (Ann (Tag "X") (maybe IntT)) `shouldBe` Left (TypeMismatch (Ann (Tag "X") (maybe IntT)) (nothing `Or` just IntT))

  -- it "☯ infer Vec" $ do
  --   let (n, a) = (Var "n", Var "a")
  --   let (vec, cons, nil) = (\n a -> app (Tag "Vec") [n, a], \x xs -> tag "Cons" [x, xs], Tag "Nil")
  --   let vecDef a = Ann (Tag "Nil") (vec i0 a) `Or` Ann (Tag "Cons") (For "n" $ fun [a, vec n a] (vec (n `add` i1) a))
  --   let env = [("Vec", lam [PVar "n", PVar "a"] (vecDef a))]

  --   let infer' a = fmap fst (infer env a)
  --   -- infer' (Tag "Nil") `shouldBe` Right (Tag "Nil")
  --   -- infer' (Tag "Cons") `shouldBe` Right (Tag "Cons")
  --   -- infer' (cons (Num 1.1) nil) `shouldBe` Right (cons (Num 1.1 `Or` NumT) nil)
  --   infer' (Ann nil (vec i0 NumT)) `shouldBe` Right (vec i0 NumT)
  --   infer' (Ann nil (vec i1 NumT)) `shouldBe` Left (TypeMismatch (Ann nil (vec i1 NumT)) (vecDef NumT))
  --   infer' (Ann (cons (Num 1.1) nil) (vec i1 NumT)) `shouldBe` Right (vec i1 NumT)
  --   -- infer' (Ann (cons [Num 1.1, cons [Num 2.2, nil]]) (vec [i0, NumT])) `shouldBe` Left (TypeMismatch i2 i0)
  --   -- infer' (Ann (cons [Num 1.1, cons [Num 2.2, nil]]) (vec [i2, IntT])) `shouldBe` Left (TypeMismatch NumT IntT)
  --   -- infer' (Ann (cons [Num 1.1, cons [Num 2.2, nil]]) (vec [i2, NumT])) `shouldBe` Right (vec [i2, NumT])
  --   True `shouldBe` True

  -- it "☯ checkTypes" $ do
  --   let env =
  --         [ ("f", Ann f (Fun IntT NumT)),
  --           ("x", Ann (Int 42) NumT),
  --           ("y", App f (Int 42)),
  --           ("z", App f (Tag "A"))
  --         ]
  --   checkTypes env `shouldBe` [TypeMismatch (Int 42 `Or` IntT) NumT, TypeMismatch (Tag "A") IntT]

  it "☯ rename simple" $ do
    let env = [("A", x), ("B", y)]
    let f t xs x = case map toLower x of
          y | y `elem` xs -> f t xs (y ++ "_")
          y -> y
    rename f [] env env `shouldBe` [("a", x), ("b", y)]

  it "☯ rename name clashes" $ do
    let env = [("a_", x), ("A", y), ("a", z)]
    let f t xs x = case map toLower x of
          y | y `elem` xs -> f t xs (y ++ "_")
          y -> y
    rename f [] env env `shouldBe` [("a_", x), ("a__", y), ("a", z)]
