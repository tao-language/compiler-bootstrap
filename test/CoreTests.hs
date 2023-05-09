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
      add eval args = case eval <$> args of
        [Int a, Int b] -> Just (Int (a + b))
        _else -> Nothing

      sub :: Operator
      sub eval args = case eval <$> args of
        [Int a, Int b] -> Just (Int (a - b))
        _else -> Nothing

      mul :: Operator
      mul eval args = case eval <$> args of
        [Int a, Int b] -> Just (Int (a * b))
        _else -> Nothing

      eq :: Operator
      eq eval args = case eval <$> args of
        [Int a, Int b] | a == b -> Just (Var "True")
        [Int _, Int _] -> Just (Var "False")
        _else -> Nothing

  let boolT = Ctr "Bool" [] ["False", "True"]
  let boolenv :: Env
      boolenv =
        [ ("Bool", Ann boolT Knd),
          ("False", Ann (Ctr "False" [] ["False", "True"]) (Var "Bool")),
          ("True", Ann (Ctr "True" [] ["False", "True"]) (Var "Bool"))
        ]

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
    eval' (For "y" x) `shouldBe` For "y" (Int 1)
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

  it "☯ Bool" $ do
    let env = boolenv

    let eval' = eval ops env
    eval' (app (Var "False") [Int 0, Int 1]) `shouldBe` Int 0
    eval' (app (Var "True") [Int 0, Int 1]) `shouldBe` Int 1

    let expand = expandType ops env
    expand ["False", "True"] "Bool" [] `shouldBe` Right (For "Bool" $ fun [Var "Bool", Var "Bool"] (Var "Bool"))

    let infer' = infer ops env
    infer' (Var "Bool") `shouldBe` Right (Knd, env)
    infer' (Var "False") `shouldBe` Right (boolT, env)
    -- infer' (Var "True") `shouldBe` Right (boolT, env)
    -- infer' (app (Var "False") [Int 0]) `shouldBe` Right (Fun IntT IntT, env)
    -- infer' (app (Var "True") [Int 0, Int 1]) `shouldBe` Right (IntT, env)
    True `shouldBe` True

  it "☯ Maybe" $ do
    let a = Var "a"
    let maybeT a = Ctr "Maybe" [("a", a)] ["Nothing", "Just"]
    let env :: Env
        env =
          [ ("Maybe", Ann (Lam "a" $ maybeT a) (Fun Knd Knd)),
            ("Nothing", Ann (Ctr "Nothing" [] ["Nothing", "Just"]) (For "a" $ App (Var "Maybe") a)),
            ("Just", Ann (Lam "x" $ Ctr "Just" [("x", Var "x")] ["Nothing", "Just"]) (For "a" $ Fun a (App (Var "Maybe") a)))
          ]

    let eval' = eval ops env
    eval' (app (Var "Maybe") [IntT]) `shouldBe` maybeT IntT
    eval' (app (Var "Nothing") [Int 0, Lam "x" $ Var "x"]) `shouldBe` Int 0
    eval' (app (Var "Just") [Int 1, Int 0, Lam "x" $ Var "x"]) `shouldBe` Int 1

    let expand = expandType ops env
    expand ["Nothing", "Just"] "Maybe" [("a", a)] `shouldBe` Right (for ["Maybe", "a"] $ fun [Var "Maybe", Fun a (Var "Maybe")] (Var "Maybe"))
    expand ["Nothing", "Just"] "Maybe" [("a", IntT)] `shouldBe` Right (for ["Maybe"] $ fun [Var "Maybe", Fun IntT (Var "Maybe")] (Var "Maybe"))

    let infer' = infer ops env
    infer' (Var "Maybe") `shouldBe` Right (Fun Knd Knd, env)
    infer' (Var "Nothing") `shouldBe` Right (For "a" $ maybeT a, env)
    infer' (Var "Just") `shouldBe` Right (For "a" $ Fun a (maybeT a), env)
    infer' (app (Var "Maybe") [IntT]) `shouldBe` Right (Knd, env)
    infer' (app (Var "Just") [Int 1]) `shouldBe` Right (maybeT IntT, env)
    infer' (app (Var "Just") [Int 1, Int 0]) `shouldBe` Right (Fun (Fun IntT IntT) IntT, env)
    infer' (app (Var "Just") [Int 1, Int 0, Lam "y" $ Var "y"]) `shouldBe` Right (IntT, env)
    infer' (app (Var "Just") [Num 1.1, Int 0, Lam "y" $ Var "y"]) `shouldBe` Left (TypeMismatch NumT IntT)

  it "☯ Nat" $ do
    let natT = Ctr "Nat" [] ["Zero", "Succ"]
    let env :: Env
        env =
          [ ("Nat", Ann natT Knd),
            ("Zero", Ann (Ctr "Zero" [] ["Zero", "Succ"]) (Var "Nat")),
            ("Succ", Ann (Lam "n" $ Ctr "Succ" [("n", Var "n")] ["Zero", "Succ"]) (Fun (Var "Nat") (Var "Nat")))
          ]

    let eval' = eval ops env
    eval' (app (Var "Zero") [Int 0, Lam "n" $ Int 1]) `shouldBe` Int 0
    eval' (app (Var "Succ") [Var "Zero", Int 0, Lam "n" $ Int 1]) `shouldBe` Int 1

    let expand = expandType ops env
    expand ["Zero", "Succ"] "Nat" [] `shouldBe` Right (for ["Nat"] $ fun [Var "Nat", Fun (Var "Nat") (Var "Nat")] (Var "Nat"))

    let infer' = infer ops env
    infer' (Var "Nat") `shouldBe` Right (Knd, env)
    infer' (Var "Zero") `shouldBe` Right (natT, env)
    infer' (Var "Succ") `shouldBe` Right (Fun natT natT, env)
    infer' (App (Var "Succ") (Var "Zero")) `shouldBe` Right (natT, env)

  it "☯ Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let vecT n' a' = Ctr "Vec" [("n", n'), ("a", a')] ["Nil", "Cons"]
    let env :: Env
        env =
          [ ("Vec", Ann (lam ["n", "a"] (vecT n a)) (fun [IntT, Knd] Knd)),
            ("Nil", Ann (Ctr "Nil" [] ["Nil", "Cons"]) (For "a" $ app (Var "Vec") [Int 0, a])),
            ("Cons", Ann (lam ["x", "xs"] $ Ctr "Cons" [("x", Var "x"), ("xs", Var "xs")] ["Nil", "Cons"]) (for ["n", "a"] $ fun [a, app (Var "Vec") [n, a]] $ app (Var "Vec") [Op "+" [n, Int 1], a]))
          ]

    let eval' = eval ops env
    eval' (app (Var "Nil") [Int 0, lam ["x", "xs"] $ Var "x"]) `shouldBe` Int 0
    eval' (app (Var "Cons") [Int 1, Var "Nil", Int 0, lam ["x", "xs"] $ Var "x"]) `shouldBe` Int 1

    let expand = expandType ops env
    expand ["Nil", "Cons"] "Vec" [("n", n), ("a", a)] `shouldBe` Right (for ["Vec", "n", "a"] $ fun [Var "Vec", fun [a, app (Var "Vec") [n, a]] (Var "Vec")] (Var "Vec"))
    expand ["Nil", "Cons"] "Vec" [("n", Int 1), ("a", NumT)] `shouldBe` Right (for ["Vec"] $ fun [Var "Vec", fun [NumT, app (Var "Vec") [Int 1, NumT]] (Var "Vec")] (Var "Vec"))

    let infer' = infer ops env
    infer' (Var "Vec") `shouldBe` Right (fun [IntT, Knd] Knd, env)
    infer' (app (Var "Vec") [Int 0]) `shouldBe` Right (fun [Knd] Knd, env)
    infer' (app (Var "Vec") [Int 0, NumT]) `shouldBe` Right (Knd, env)
    infer' (app (Var "Nil") []) `shouldBe` Right (For "a" $ vecT (Int 0) a, env)
    infer' (app (Var "Cons") []) `shouldBe` Right (for ["n", "a"] $ fun [a, vecT n a] (vecT (Op "+" [n, Int 1]) a), env)
    infer' (app (Var "Cons") [Num 1.1]) `shouldBe` Right (For "n" $ fun [vecT (Var "n") NumT] (vecT (Op "+" [Var "n", Int 1]) NumT), env)
    infer' (app (Var "Cons") [Num 1.1, Var "Nil"]) `shouldBe` Right (vecT (Int 1) NumT, env)
    infer' (app (Var "Nil") [Int 0, lam ["y", "ys"] $ Var "y"]) `shouldBe` Right (IntT, env)
    infer' (app (Var "Cons") [Int 1, Var "Nil", Int 0, lam ["y", "ys"] $ Var "y"]) `shouldBe` Right (IntT, env)
    infer' (app (Var "Cons") [Num 1.1, Var "Nil", Int 0, lam ["y", "ys"] $ Var "y"]) `shouldBe` Left (TypeMismatch NumT IntT)

  it "☯ factorial" $ do
    let (i0, i1) = (Int 0, Int 1)
    let (f, n) = (Var "f", Var "n")
    let eq a b = app (Var "==") [a, b]
    let mul a b = app (Var "*") [a, b]
    let sub a b = app (Var "-") [a, b]

    let env :: Env
        env =
          ("f", Fix "f" $ Lam "n" $ app (eq n i0) [n `mul` App f (n `sub` i1), Int 1]) :
          ("+", Ann (op2 "+") (fun [IntT, IntT] IntT)) :
          ("-", Ann (op2 "-") (fun [IntT, IntT] IntT)) :
          ("*", Ann (op2 "*") (fun [IntT, IntT] IntT)) :
          ("==", Ann (op2 "==") (fun [IntT, IntT] (Var "Bool"))) :
          boolenv
          where
            op2 op = lam ["x", "y"] (Op op [Var "x", Var "y"])

    let eval' = eval ops env
    eval' (Var "f") `shouldBe` Fix "f" (Lam "n" $ app (Op "==" [n, i0]) [Op "*" [n, App f (Op "-" [n, i1])], Int 1])
    -- eval' (App f n) `shouldBe` app (Op "==" [n, i0]) [Int 0, Op "*" [n, App f (Op "-" [n, i1])]]
    eval' (App f (Int 0)) `shouldBe` Int 1
    eval' (App f (Int 1)) `shouldBe` Int 1
    eval' (App f (Int 2)) `shouldBe` Int 2
    eval' (App f (Int 3)) `shouldBe` Int 6
    eval' (App f (Int 4)) `shouldBe` Int 24
    eval' (App f (Int 5)) `shouldBe` Int 120

    let infer' = infer ops env
    infer' (Lam "n" $ n `sub` i1) `shouldBe` Right (Fun IntT IntT, env)
    infer' (Var "f") `shouldBe` Right (Fun IntT IntT, env)
    infer' (App f (Int 0)) `shouldBe` Right (IntT, env)
