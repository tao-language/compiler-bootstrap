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

      add :: [Term] -> Maybe Term
      add [Int a, Int b] = Just (Int (a + b))
      add _ = Nothing

      sub :: [Term] -> Maybe Term
      sub [Int a, Int b] = Just (Int (a - b))
      sub _ = Nothing

      mul :: [Term] -> Maybe Term
      mul [Int a, Int b] = Just (Int (a * b))
      mul _ = Nothing

      eq :: [Term] -> Maybe Term
      eq [Int a, Int b] | a == b = Just (Var "True")
      eq [Int _, Int _] = Just (Var "False")
      eq _ = Nothing

  let boolT = Ctr "Bool" 0 (For "a" $ fun [Var "a", Var "a"] (Var "a"))
  let false = Ctr "False" 0 $ lam ["F", "T"] $ Var "F"
  let true = Ctr "True" 0 $ lam ["F", "T"] $ Var "T"
  let boolCtx :: Context
      boolCtx =
        [ ("Bool", Ann boolT Typ),
          ("False", Ann false (Var "Bool")),
          ("True", Ann true (Var "Bool"))
        ]

  let opsCtx :: Context
      opsCtx =
        [ ("+", Ann (op2 "+") (fun [IntT, IntT] IntT)),
          ("-", Ann (op2 "-") (fun [IntT, IntT] IntT)),
          ("*", Ann (op2 "*") (fun [IntT, IntT] IntT)),
          ("==", Ann (op2 "==") (fun [IntT, IntT] (Var "Bool")))
        ]
        where
          op2 op = lam ["x", "y"] (Op op [Var "x", Var "y"])

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
    eval' Typ `shouldBe` Typ
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
    let ctx :: Context
        ctx =
          [ ("inferred", Val (Int 1)),
            ("mismatch", Ann (Int 1) NumT),
            ("match", Ann (Int 1) IntT),
            ("typed", Ann (Var "typed") IntT),
            ("free", Val (Var "free")),
            ("x", Val (Int 1)),
            ("y", Val (Num 1.1)),
            ("f", Ann f (Fun IntT NumT)),
            ("g", Ann g (For "a" $ Fun a a)),
            ("op0", Ann (Var "op0") IntT),
            ("op1", Ann (Var "op1") (Fun IntT NumT))
          ]

    let infer' = infer ops ctx
    infer' Typ `shouldBe` Right (Typ, ctx)
    infer' IntT `shouldBe` Right (Typ, ctx)
    infer' (Int 1) `shouldBe` Right (IntT, ctx)
    infer' NumT `shouldBe` Right (Typ, ctx)
    infer' (Num 1) `shouldBe` Right (NumT, ctx)
    infer' (Var "undefined") `shouldBe` Left (UndefinedVar "undefined")
    infer' (Var "inferred") `shouldBe` Right (IntT, ctx)
    infer' (Var "mismatch") `shouldBe` Left (TypeMismatch IntT NumT)
    infer' (Var "match") `shouldBe` Right (IntT, ctx)
    infer' (Var "typed") `shouldBe` Right (IntT, ctx)
    infer' (Var "free") `shouldBe` Right (Typ, ctx)
    infer' (Var "x") `shouldBe` Right (IntT, ctx)
    infer' (Var "y") `shouldBe` Right (NumT, ctx)
    infer' (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer' (Var "f") `shouldBe` Right (Fun IntT NumT, ctx)
    infer' (Var "g") `shouldBe` Right (For "a" $ Fun a a, ctx)
    infer' (For "x" (Int 1)) `shouldBe` Right (IntT, ctx)
    infer' (For "x" x) `shouldBe` Right (For "xT" xT, ctx)
    infer' (Lam "x" x) `shouldBe` Right (For "xT" $ Fun xT xT, ctx)
    infer' (Fun (Int 1) (Num 1.1)) `shouldBe` Left (TypeMismatch IntT Typ)
    infer' (Fun IntT (Num 1.1)) `shouldBe` Left (TypeMismatch NumT Typ)
    infer' (Fun IntT NumT) `shouldBe` Right (Typ, ctx)
    infer' (App x y) `shouldBe` Left (TypeMismatch (Fun NumT (Var "t")) IntT)
    infer' (App f y) `shouldBe` Left (TypeMismatch NumT IntT)
    infer' (App f x) `shouldBe` Right (NumT, ctx)
    infer' (App g x) `shouldBe` Right (IntT, ctx)
    infer' (Op "op0" []) `shouldBe` Right (IntT, ctx)
    infer' (Op "op0" [Num 1.1]) `shouldBe` Left (TypeMismatch (Fun NumT (Var "t")) IntT)
    infer' (Op "op1" [Num 1.1]) `shouldBe` Left (TypeMismatch NumT IntT)
    infer' (Op "op1" [Int 1]) `shouldBe` Right (NumT, ctx)

  it "☯ Bool" $ do
    let ctx = boolCtx

    let eval' = apply ops ctx
    eval' (app (Var "False") [Int 0, Int 1]) `shouldBe` Int 0
    eval' (app (Var "True") [Int 0, Int 1]) `shouldBe` Int 1

    let infer' = infer ops ctx
    infer' (Var "Bool") `shouldBe` Right (Typ, ctx)
    infer' (Var "False") `shouldBe` Right (boolT, ctx)
    infer' (Var "True") `shouldBe` Right (boolT, ctx)
    infer' (app (Var "False") [Int 0]) `shouldBe` Right (Fun IntT IntT, ctx)
    infer' (app (Var "True") [Int 0, Int 1]) `shouldBe` Right (IntT, ctx)

  it "☯ Maybe" $ do
    let (a, b) = (Var "a", Var "b")
    let maybeDef = Lam "a" $ For "b" $ fun [b, Fun a b] b
    let nothingDef = lam ["N", "J"] $ Var "N"
    let justDef = lam ["x", "N", "J"] $ App (Var "J") (Var "x")
    let maybeT a = Ctr "Maybe" 0 (eval ops [] $ App maybeDef a)
    let nothing = Ctr "Nothing" 0 (lam ["N", "J"] $ Var "N")
    let just a = Ctr "Just" 0 (eval ops [] $ App justDef a)
    let ctx :: Context
        ctx =
          [ ("Maybe", Ann (Ctr "Maybe" 1 maybeDef) (Fun Typ Typ)),
            ("Nothing", Ann (Ctr "Nothing" 0 nothingDef) (For "a" $ App (Var "Maybe") a)),
            ("Just", Ann (Ctr "Just" 1 justDef) (For "a" $ Fun a (App (Var "Maybe") a)))
          ]

    let eval' = apply ops ctx
    eval' (Var "Nothing") `shouldBe` nothing
    eval' (app (Var "Just") [Int 1]) `shouldBe` just (Int 1)
    eval' (app (Var "Nothing") [Int 0, Lam "x" $ Var "x"]) `shouldBe` Int 0
    eval' (app (Var "Just") [Int 1, Int 0, Lam "x" $ Var "x"]) `shouldBe` Int 1

    let infer' = infer ops ctx
    infer' (Var "Maybe") `shouldBe` Right (Fun Typ Typ, ctx)
    infer' (Var "Nothing") `shouldBe` Right (For "a" $ maybeT a, ctx)
    infer' (Var "Just") `shouldBe` Right (For "a" $ Fun a (maybeT a), ctx)
    infer' (app (Var "Maybe") [IntT]) `shouldBe` Right (Typ, ctx)
    infer' (app (Var "Just") [Int 1]) `shouldBe` Right (maybeT IntT, ctx)
    infer' (app (Var "Just") [Int 1, Int 0, Lam "x" $ Var "x"]) `shouldBe` Right (IntT, ctx)
    infer' (app (Var "Just") [Num 1.1, Int 0, Lam "x" $ Var "x"]) `shouldBe` Left (TypeMismatch NumT IntT)

  it "☯ Nat" $ do
    let a = Var "a"
    let natDef = For "a" $ fun [a, Fun (Var "Nat") a] a
    let zeroDef = lam ["Z", "S"] (Var "Z")
    let succDef = lam ["n", "Z", "S"] (app (Var "S") [Var "n"])
    let ctx :: Context
        ctx =
          [ ("Nat", Ann (Ctr "Nat" 0 natDef) Typ),
            ("Zero", Ann (Ctr "Zero" 0 zeroDef) (Var "Nat")),
            ("Succ", Ann (Ctr "Succ" 1 succDef) (Fun (Var "Nat") (Var "Nat")))
          ]

    let eval' = apply ops ctx
    eval' (app (Var "Zero") [Int 0, Lam "n" $ Int 1]) `shouldBe` Int 0
    eval' (app (Var "Succ") [Var "Zero", Int 0, Lam "n" $ Int 1]) `shouldBe` Int 1

    let infer' = infer ops ctx
    infer' (Var "Nat") `shouldBe` Right (Typ, ctx)
    infer' (Var "Zero") `shouldBe` Right (Ctr "Nat" 0 natDef, ctx)
    infer' (Var "Succ") `shouldBe` Right (Fun (Ctr "Nat" 0 natDef) (Ctr "Nat" 0 natDef), ctx)
    infer' (App (Var "Succ") (Var "Zero")) `shouldBe` Right (Ctr "Nat" 0 natDef, ctx)

  it "☯ Vec" $ do
    let (a, b) = (Var "a", Var "b")
    let vecDef = lam ["n", "a"] (For "b" $ fun [b, fun [a, app (Var "Vec") [Var "n", a]] b] b)
    let vecT n a = Ctr "Vec" 0 (eval ops [] $ app vecDef [n, a])
    let nilDef = lam ["N", "C"] (Var "N")
    let consDef = lam ["x", "xs", "N", "C"] (app (Var "C") [Var "x", Var "xs"])
    let ctx :: Context
        ctx =
          [ ("Vec", Ann (Ctr "Vec" 2 vecDef) (fun [IntT, Typ] Typ)),
            ("Nil", Ann (Ctr "Nil" 0 nilDef) (for ["a"] $ app (Var "Vec") [Int 0, Var "a"])),
            ("Cons", Ann (Ctr "Cons" 2 consDef) (for ["n", "a"] $ fun [Var "a", app (Var "Vec") [Var "n", Var "a"]] (app (Var "Vec") [Op "+" [Var "n", Int 1], Var "a"])))
          ]

    let eval' = apply ops ctx
    eval' (app (Var "Nil") [Int 0, lam ["x", "xs"] $ Var "x"]) `shouldBe` Int 0
    eval' (app (Var "Cons") [Int 1, Var "Nil", Int 0, lam ["x", "xs"] $ Var "x"]) `shouldBe` Int 1

    let infer' = infer ops ctx
    infer' (Var "Vec") `shouldBe` Right (fun [IntT, Typ] Typ, ctx)
    infer' (app (Var "Vec") [Int 0]) `shouldBe` Right (fun [Typ] Typ, ctx)
    infer' (app (Var "Vec") [Int 0, NumT]) `shouldBe` Right (Typ, ctx)
    infer' (app (Var "Nil") []) `shouldBe` Right (For "a" $ vecT (Int 0) a, ctx)
    infer' (app (Var "Cons") []) `shouldBe` Right (for ["n", "a"] $ fun [a, vecT (Var "n") a] (vecT (Op "+" [Var "n", Int 1]) a), ctx)
    infer' (app (Var "Cons") [Num 1.1]) `shouldBe` Right (For "n" $ fun [vecT (Var "n") NumT] (vecT (Op "+" [Var "n", Int 1]) NumT), ctx)
    infer' (app (Var "Cons") [Num 1.1, Var "Nil"]) `shouldBe` Right (vecT (Int 1) NumT, ctx)
    infer' (app (Var "Nil") [Int 0, lam ["y", "ys"] $ Var "y"]) `shouldBe` Right (IntT, ctx)
    infer' (app (Var "Cons") [Int 1, Var "Nil", Int 0, lam ["y", "ys"] $ Var "y"]) `shouldBe` Right (IntT, ctx)
    infer' (app (Var "Cons") [Num 1.1, Var "Nil", Int 0, lam ["y", "ys"] $ Var "y"]) `shouldBe` Left (TypeMismatch NumT IntT)

  it "☯ factorial" $ do
    let (i0, i1) = (Int 0, Int 1)
    let (f, n) = (Var "f", Var "n")
    let eq a b = app (Var "==") [a, b]
    let mul a b = app (Var "*") [a, b]
    let sub a b = app (Var "-") [a, b]

    let ctx :: Context
        ctx =
          ("f", Val $ Ctr "f" 0 $ Lam "n" $ app (eq n i0) [n `mul` App f (n `sub` i1), Int 1]) :
          boolCtx ++ opsCtx

    let eval' = apply ops ctx
    eval' (Var "f") `shouldBe` Ctr "f" 0 (Lam "n" $ app (Op "==" [n, i0]) [Op "*" [n, App f (Op "-" [n, i1])], Int 1])
    -- eval' (App f n) `shouldBe` app (Op "==" [n, i0]) [Int 0, Op "*" [n, App f (Op "-" [n, i1])]]
    eval' (App f (Int 0)) `shouldBe` Int 1
    eval' (App f (Int 1)) `shouldBe` Int 1
    eval' (App f (Int 2)) `shouldBe` Int 2
    eval' (App f (Int 3)) `shouldBe` Int 6
    eval' (App f (Int 4)) `shouldBe` Int 24
    eval' (App f (Int 5)) `shouldBe` Int 120

    let infer' = infer ops ctx
    infer' (Lam "n" $ n `sub` i1) `shouldBe` Right (Fun IntT IntT, ctx)
    infer' (Var "f") `shouldBe` Right (Fun IntT IntT, ctx)
    infer' (App f (Int 0)) `shouldBe` Right (IntT, ctx)

  it "☯ TODO" $ do
    True `shouldBe` True