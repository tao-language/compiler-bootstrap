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

  let add a b = Call "+" [a, b]
  let ops =
        [ ( "+",
            \eval args -> case eval <$> args of
              [Int x, Int y] -> Int (x + y)
              args -> Call "+" args
          ),
          ( "-",
            \eval args -> case eval <$> args of
              [Int x, Int y] -> Int (x - y)
              args -> Call "-" args
          ),
          ( "*",
            \eval args -> case eval <$> args of
              [Int x, Int y] -> Int (x * y)
              args -> Call "*" args
          )
        ]

  let factorial f = Fix f (case0 `Or` caseN f)
        where
          case0 = Fun (Int 0) i1
          caseN f = For "x" (Fun x (x `mul` App (Var f) (x `sub` i1)))
          sub x y = Call "-" [x, y]
          mul x y = Call "*" [x, y]

  it "☯ show" $ do
    show Err `shouldBe` "!error"
    show IntT `shouldBe` "!IntT"
    show NumT `shouldBe` "!NumT"
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

  -- show (int2num (App x y)) `shouldBe` "$i2n (x y)"
  -- show (int2num (pow x y)) `shouldBe` "$i2n x^y"
  -- show (pow (int2num x) y) `shouldBe` "($i2n x)^y"
  -- show (App (int2num x) y) `shouldBe` "$i2n x y"
  -- show (App x (int2num y)) `shouldBe` "x ($i2n y)"

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
  -- show (fun [fun [x] y] z) `shouldBe` "(x -> y) -> z"
  -- show (fun [x] (fun [y] z)) `shouldBe` "x -> y -> z"
  -- show (fun [x] (lt y z)) `shouldBe` "x -> (y < z)"
  -- show (fun [lt x y] z) `shouldBe` "(x < y) -> z"

  -- show (lt x (fun [y] z)) `shouldBe` "x < y -> z"
  -- show (lt (fun [x] y) z) `shouldBe` "x -> y < z"
  -- show (lt (lt x y) z) `shouldBe` "(x < y) < z"
  -- show (lt x (lt y z)) `shouldBe` "x < y < z"
  -- show (lt (eq x y) z) `shouldBe` "(x == y) < z"
  -- show (lt x (eq y z)) `shouldBe` "x < (y == z)"

  -- show (eq x (lt y z)) `shouldBe` "x == y < z"
  -- show (eq (lt x y) z) `shouldBe` "x < y == z"
  -- show (eq (eq x y) z) `shouldBe` "x == y == z"
  -- show (eq x (eq y z)) `shouldBe` "x == (y == z)"
  -- show (eq (Ann x y) z) `shouldBe` "(x : y) == z"
  -- show (eq x (Ann y z)) `shouldBe` "x == (y : z)"

  -- show (Ann x (eq y z)) `shouldBe` "x : y == z"
  -- show (Ann (eq x y) z) `shouldBe` "x == y : z"
  -- show (Ann x (Ann y z)) `shouldBe` "x : y : z"
  -- show (Ann (Ann x y) z) `shouldBe` "(x : y) : z"
  -- show (Ann (Or x y) z) `shouldBe` "(x | y) : z"
  -- show (Ann x (Or y z)) `shouldBe` "x : (y | z)"

  -- show (For "x" (Ann y z)) `shouldBe` "@x. (y : z)"
  -- show (For "x" (eq y z)) `shouldBe` "@x. y == z"
  -- show (Ann (For "x" y) z) `shouldBe` "(@x. y) : z"
  -- show (Or (For "x" y) z) `shouldBe` "@x. y | z"
  -- show (Or x (For "y" z)) `shouldBe` "x | @y. z"

  -- show (Or x (Ann y z)) `shouldBe` "x | y : z"
  -- show (Or (Ann x y) z) `shouldBe` "x : y | z"
  -- show (Or x (Or y z)) `shouldBe` "x | y | z"
  -- show (Or (Or x y) z) `shouldBe` "(x | y) | z"

  -- show (If x (Ann y z)) `shouldBe` "x ? y : z"
  -- show (If (Ann x y) z) `shouldBe` "x : y ? z"
  -- show (If x (If y z)) `shouldBe` "x ? y ? z"
  -- show (If (If x y) z) `shouldBe` "(x ? y) ? z"

  it "☯ syntax sugar" $ do
    -- let' [] x `shouldBe` x
    -- let' [(y', z)] x `shouldBe` App (Fun y' x) z

    -- lam [] x `shouldBe` x
    -- lam [y'] x `shouldBe` Fun y' x

    and' [] `shouldBe` Unit
    and' [x] `shouldBe` x
    and' [x, y] `shouldBe` x `And` y

    tag "A" [] `shouldBe` Tag "A"
    tag "A" [x] `shouldBe` Tag "A" `And` x
    tag "A" [x, y] `shouldBe` Tag "A" `And` (x `And` y)

    app x [] `shouldBe` x
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ reduce" $ do
    let env =
          [ ("x", Int 42),
            ("y", Num 3.14),
            ("z", Var "z"),
            ("f", For "y" (Fun y y))
          ]

    let reduce' x = reduce ops (Let env x)
    reduce' IntT `shouldBe` IntT
    reduce' NumT `shouldBe` NumT
    reduce' (Int 1) `shouldBe` Int 1
    reduce' (Num 1.1) `shouldBe` Num 1.1
    reduce' (Tag "x") `shouldBe` Tag "x"
    reduce' (Var "x") `shouldBe` Int 42
    reduce' (Var "y") `shouldBe` Num 3.14
    reduce' (Var "z") `shouldBe` Var "z"
    reduce' (Var "w") `shouldBe` Var "w"
    -- reduce' (For "x" x) `shouldBe` For "x" x
    -- reduce' (For "x" y) `shouldBe` For "x" (Num 3.14)
    -- reduce' (Fix "x" x) `shouldBe` Fix "x" x
    -- reduce' (Fix "x" y) `shouldBe` Fix "x" (Num 3.14)
    reduce' (Ann x NumT) `shouldBe` Ann (Int 42) NumT
    reduce' (And x y) `shouldBe` And (Let env x) (Let env y)
    reduce' (Or x y) `shouldBe` Or (Let env x) (Let env y)
    reduce' (Fun x y) `shouldBe` Fun (Let env x) (Let env y)
    reduce' (App IntT y) `shouldBe` Err
    reduce' (App NumT y) `shouldBe` Err
    reduce' (App (Int 1) y) `shouldBe` Err
    reduce' (App (Num 1.1) y) `shouldBe` Err
    reduce' (App (Tag "x") y) `shouldBe` Err
    reduce' (App (Var "x") y) `shouldBe` Err
    reduce' (App (Var "z") y) `shouldBe` App z (Num 3.14)
    reduce' (App (App (Var "z") y) x) `shouldBe` App (App z (Num 3.14)) (Int 42)
    -- reduce' (App (For "x" x) y) `shouldBe` App x (Num 3.14)
    -- reduce' (App (Fix "x" x) y) `shouldBe` App (Fix "x" x) x
    reduce' (App (Fun IntT NumT) IntT) `shouldBe` NumT
    reduce' (App (Fun NumT IntT) IntT) `shouldBe` Err
    reduce' (App (Fun NumT IntT) NumT) `shouldBe` IntT
    reduce' (App (Fun (Int 42) z) (Int 42)) `shouldBe` z
    reduce' (App (Fun (Int 42) z) (Int 0)) `shouldBe` Err
    reduce' (App (Fun (Num 3.14) z) (Num 3.14)) `shouldBe` z
    reduce' (App (Fun (Num 3.14) z) (Num 0.0)) `shouldBe` Err
    reduce' (App (Fun (Tag "A") z) (Tag "A")) `shouldBe` z
    reduce' (App (Fun (Tag "A") z) (Tag "B")) `shouldBe` Err
    reduce' (App (Fun (Var "x") z) (Int 42)) `shouldBe` z
    reduce' (App (Fun (Var "x") z) (Int 0)) `shouldBe` Err
    reduce' (App (Fun (Var "x") z) x) `shouldBe` z
    reduce' (App (Fun (Var "x") z) y) `shouldBe` Err
    -- TODO: reduce App Fun App
    reduce' (App (Fun (And IntT NumT) z) (And IntT NumT)) `shouldBe` z
    reduce' (App (Fun (And IntT NumT) z) (And IntT IntT)) `shouldBe` Err
    reduce' (App (Fun (And IntT NumT) z) (And NumT NumT)) `shouldBe` Err
    reduce' (App (Fun (Or IntT NumT) z) IntT) `shouldBe` z
    reduce' (App (Fun (Or IntT NumT) z) NumT) `shouldBe` z
    reduce' (App (Fun (Or IntT IntT) z) x) `shouldBe` Err
    reduce' (App (Fun (Ann x Err) z) x) `shouldBe` z
    reduce' (App (Fun (Ann x Err) z) y) `shouldBe` Err
    reduce' (App (Fun (Call "f" []) z) (Call "f" [])) `shouldBe` z
    reduce' (App (Fun Err IntT) Err) `shouldBe` IntT
    reduce' (App (For "y" (Fun y y)) x) `shouldBe` Int 42
    reduce' (App (Var "f") x) `shouldBe` Int 42
    reduce' (App (Or (Var "f") Err) x) `shouldBe` Int 42
    reduce' (App (Or Err (Var "f")) x) `shouldBe` Int 42
    reduce' (App (Or Err Err) x) `shouldBe` Err
    reduce' (Call "f" [x, y]) `shouldBe` Call "f" [Let env x, Let env y]
    reduce' Err `shouldBe` Err

  it "☯ eval" $ do
    let env =
          [ ("x", Int 42),
            ("y", Num 3.14),
            ("f", For "z" (Fun z z))
          ]

    let eval' x = eval ops (Let env x)
    eval' (Fun x y) `shouldBe` Fun (Int 42) (Num 3.14)
    eval' (And x y) `shouldBe` And (Int 42) (Num 3.14)
    eval' (Or x y) `shouldBe` Or (Int 42) (Num 3.14)
    eval' (Call "f" [x, y]) `shouldBe` Call "f" [Int 42, Num 3.14]
    -- eval' (For "x" (And x y)) `shouldBe` For "x" (And x (Num 3.14))
    -- eval' (Fix "x" (And x y)) `shouldBe` Fix "x" (And x (Num 3.14))
    eval' (App z (And x y)) `shouldBe` App z (And (Int 42) (Num 3.14))

  it "☯ eval factorial" $ do
    let env = [("f", factorial "f")]
    let eval' x = eval ops (Let env x)

    eval' (Var "f") `shouldBe` factorial "f"
    eval' (App f x) `shouldBe` App (factorial "f") x
    eval' (App f (Int 0)) `shouldBe` Int 1
    eval' (App f (Int 1)) `shouldBe` Int 1
    eval' (App f (Int 2)) `shouldBe` Int 2
    eval' (App f (Int 3)) `shouldBe` Int 6
    eval' (App f (Int 4)) `shouldBe` Int 24
    eval' (App f (Int 5)) `shouldBe` Int 120

  -- it "☯ eval fibonacci" $ do
  --   let fib f = Fix f (case0 `Or` case1 `Or` caseN f)
  --         where
  --           case0 = Fun i0 i0
  --           case1 = Fun i1 i1
  --           caseN f = For "x" (Fun x (App (Var f) (x `sub` i1) `add` App (Var f) (x `sub` i2)))
  --           add x y = Call "+" [x, y]
  --           sub x y = Call "-" [x, y]
  --   let env = [("f", fib "f")]
  --   let eval' x = eval ops (Let env x)
  --   eval' (App f (Int 0)) `shouldBe` Int 0
  --   eval' (App f (Int 1)) `shouldBe` Int 1
  --   eval' (App f (Int 2)) `shouldBe` Int 1
  --   eval' (App f (Int 3)) `shouldBe` Int 2
  --   eval' (App f (Int 4)) `shouldBe` Int 3
  --   eval' (App f (Int 5)) `shouldBe` Int 5

  it "☯ eval type alias" $ do
    let env = [("T0", Fun (Int 0) NumT), ("T1", lam [x] (Fun (Int 1) x))]
    let eval' x = eval ops (Let env x)
    eval' (App (Tag "A") (Tag "A")) `shouldBe` Tag "A"
    eval' (App (And (Tag "A") IntT) (And (Tag "A") IntT)) `shouldBe` And (Tag "A") IntT
    eval' (App (Tag "T0") (Int 0)) `shouldBe` NumT
    eval' (App (And (Tag "T1") NumT) (Int 1)) `shouldBe` NumT

  it "☯ unify" $ do
    True `shouldBe` True

  it "☯ infer const" $ do
    infer [] [] IntT `shouldBe` ((IntT, IntT), [], [])
    infer [] [] NumT `shouldBe` ((NumT, NumT), [], [])
    infer [] [] (Int 1) `shouldBe` ((Int 1, IntT), [], [])
    infer [] [] (Num 1.1) `shouldBe` ((Num 1.1, NumT), [], [])
    infer [] [] Err `shouldBe` ((Err, Err), [], [])

  it "☯ infer Var" $ do
    let (a1, yT) = (Var "a1", Var "yT")
    let env = [("x", i1), ("y", y), ("b", Ann b IntT), ("a", b), ("c", Ann c (for ["a"] a))]
    infer [] env (Var "x") `shouldBe` ((x, IntT), [], [])
    infer [] env (Var "y") `shouldBe` ((y, yT), [("yT", yT), ("y", Ann y yT)], [])
    infer [] env (Var "z") `shouldBe` ((z, Err), [], [UndefinedVar "z"])
    infer [] env (Var "a") `shouldBe` ((a, IntT), [], [])
    infer [] env (Var "c") `shouldBe` ((c, a1), [("a1", a1)], [])

  it "☯ infer Ann" $ do
    let env = []
    infer [] env (Ann i1 IntT) `shouldBe` ((i1, IntT), [], [])
    infer [] env (Ann i1 NumT) `shouldBe` ((i1, Err), [], [TypeMismatch IntT NumT])
    infer [] env (Ann i1 (For "a" a)) `shouldBe` ((i1, IntT), [("a", IntT)], [])

  it "☯ infer Ann Tag" $ do
    let env = [("T", Tag "A" `Or` Tag "B")]
    -- infer [] env (Tag "T" []) `shouldBe` Right (Tag "A" [] `Or` Tag "B" [], [])
    -- infer [] env (Ann (Tag "A" []) (Tag "A" [])) `shouldBe` Right (Tag "A" [], [])
    -- infer [] env (Ann (Tag "A") (Tag "T")) `shouldBe` Right (Tag "T", [])
    -- infer [] env (Ann (Tag "B []) (Tag "T" [])) `shouldBe` Right (Tag "T" [], [])
    -- infer [] env (Ann (Tag "C" []) (Tag "T" [])) `shouldBe` Left (TypeMismatch (Ann (Tag "C" []) (Tag "T" [])) (Tag "A" [] `Or` Tag "B" []))
    True `shouldBe` True

  it "☯ infer Fun" $ do
    let (t, xT, _T) = (Var "t", Var "xT", Var "_T")
    let env =
          [ ("x", Ann x a),
            ("y", Int 1),
            ("a", a)
          ]
    infer [] env (Fun x x) `shouldBe` ((Fun (Ann x a) x, Fun a a), [], [])

  it "☯ infer Fun" $ do
    let env = [("a", Ann a IntT), ("b", Ann b NumT)]
    infer [] env (Fun a b) `shouldBe` ((Fun (Ann a IntT) b, Fun IntT NumT), [], [])

  it "☯ infer App" $ do
    let env =
          [ ("x", i1),
            ("y", y),
            ("f", Ann f (Fun IntT NumT))
          ]
    infer [] env (App f x) `shouldBe` ((App f (Ann x IntT), NumT), [], [])
    infer [] env (App (Fun y y) x) `shouldBe` ((App (Fun (Ann y (Var "yT")) y) (Ann x IntT), IntT), [("yT", IntT), ("y", Ann y IntT)], [])
    infer [] env (App y x) `shouldBe` ((App y (Ann x IntT), Var "yT1"), [("yT1", Var "yT1"), ("yT", Fun IntT (Var "yT1")), ("y", Ann y (Fun IntT (Var "yT1")))], [])

  it "☯ infer Or" $ do
    let env = [("x", Int 42), ("y", Num 3.14)]
    infer [] env (Or x x) `shouldBe` ((Or x x, IntT), [], [])
    infer [] env (Or x y) `shouldBe` ((Or x y, IntT `Or` NumT), [], [])

  it "☯ infer For" $ do
    True `shouldBe` True

  it "☯ infer Op2" $ do
    True `shouldBe` True

  it "☯ infer factorial" $ do
    let env = [("f", Ann (factorial "f") (Fun IntT IntT))]
    let infer' a = let ((a', t), _, _) = infer ops env a in (a', t)
    infer' (Var "f") `shouldBe` (f, Fun IntT IntT)
    infer' (Ann f (Fun IntT IntT)) `shouldBe` (f, Fun IntT IntT)

  -- it "☯ infer Bool" $ do
  --   let (bool, true, false) = (Tag "Bool", Tag "True", Tag "False")
  --   let env = [("Bool", true `Or` false)]

  --   let infer' a = fmap fst (infer ops env a)
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

  it "☯ infer Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let nil = Tag "Nil"
    let cons x xs = tag "Cons" [x, xs]
    let vec n a = tag "Vec" [n, a]
    let vecDef a =
          or'
            [ For "n" (Fun (cons a (vec n a)) (vec (n `add` i1) a)),
              Fun nil (vec i0 a)
            ]
    let env = [("Vec", lam [And n a] (vecDef a))]

    let infer' = infer ops env
    infer' (Tag "Nil") `shouldBe` ((Tag "Nil", Tag "Nil"), [], [])
    infer' (cons (Num 1.1) nil) `shouldBe` ((cons (Num 1.1) nil, cons NumT nil), [], [])
    infer' (Ann nil (vec i0 NumT)) `shouldBe` ((nil, vec i0 NumT), env, [])
    infer' (Ann nil (vec i1 NumT)) `shouldBe` ((nil, vec Err NumT), env, [TypeMismatch i0 i1])
    infer' (Ann (cons (Num 1.1) nil) (vec i1 NumT)) `shouldBe` ((cons (Num 1.1) nil, vec i1 NumT), env, [])
    infer' (Ann (cons (Num 1.1) (cons (Num 2.2) nil)) (vec i0 NumT)) `shouldBe` ((cons (Num 1.1) (cons (Num 2.2) nil), vec Err NumT), env, [TypeMismatch i2 i0])

-- it "☯ checkTypes" $ do
--   let env =
--         [ ("f", Ann f (Fun IntT NumT)),
--           ("x", Ann (Int 42) NumT),
--           ("y", App f (Int 42)),
--           ("z", App f (Tag "A"))
--         ]
--   checkTypes env `shouldBe` [TypeMismatch (Int 42 `Or` IntT) NumT, TypeMismatch (Tag "A") IntT]

-- it "☯ rename simple" $ do
--   let env = [("A", x), ("B", y)]
--   let f t xs x = case map toLower x of
--         y | y `elem` xs -> f t xs (y ++ "_")
--         y -> y
--   rename f [] env env `shouldBe` [("a", x), ("b", y)]

-- it "☯ rename name clashes" $ do
--   let env = [("a_", x), ("A", y), ("a", z)]
--   let f t xs x = case map toLower x of
--         y | y `elem` xs -> f t xs (y ++ "_")
--         y -> y
--   rename f [] env env `shouldBe` [("a_", x), ("a__", y), ("a", z)]

-- it "☯ load Module" $ do
--   let mod =
--         Module
--           { values = [("x", Int 1), ("y", Int 2)],
--             types = [],
--             tests = []
--           }
--   load "examples/core-package/core-module" `shouldReturn` mod
