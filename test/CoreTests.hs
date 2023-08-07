module CoreTests where

import Core
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--==☯️ Core language ☯️==--" $ do
  it "☯ or" $ do
    let (x, y, z) = (Var "x", Var "y", Var "z")
    or' [] `shouldBe` Err
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

  it "☯ eval" $ do
    let (x, y) = (Var "x", Var "y")
    let (a, b) = (Var "a", Var "b")
    let env :: Env
        env =
          [ ("x", Int 1),
            ("a", IntT),
            ("b", NumT)
          ]

    eval env Knd `shouldBe` Knd
    eval env IntT `shouldBe` IntT
    eval env NumT `shouldBe` NumT
    eval env (Int 1) `shouldBe` Int 1
    eval env (Num 1.1) `shouldBe` Num 1.1
    eval env (Var "A") `shouldBe` Var "A"
    eval env (Var "x") `shouldBe` Int 1
    eval env (Var "y") `shouldBe` Var "y"
    eval env (Union [("A", x)]) `shouldBe` Union [("A", Int 1)]
    eval env (Typ "T" [x]) `shouldBe` Typ "T" [Int 1]
    eval env (Ctr "T" "A" [x]) `shouldBe` Ctr "T" "A" [Int 1]
    eval env (Lam x x) `shouldBe` Lam x x
    eval env (Lam y x) `shouldBe` Lam y (Int 1)
    eval env (Fun a b) `shouldBe` Fun IntT NumT
    eval env (App x x) `shouldBe` App (Int 1) (Int 1)
    eval env (App (Lam y y) x) `shouldBe` Int 1
    eval env (App (Lam y a) x) `shouldBe` IntT
    eval env (App (Lam (Int 1) a) x) `shouldBe` IntT
    eval env (App (Lam (Int 2) a) x) `shouldBe` Err
    eval env (App (Lam (Ctr "T" "A" []) a) (Ctr "T" "A" [])) `shouldBe` IntT
    eval env (App (Lam (Ctr "T" "A" []) a) (Ctr "T" "B" [])) `shouldBe` Err
    eval env (Ann x (For [] a)) `shouldBe` Int 1
    eval env (Or x x) `shouldBe` Or (Int 1) (Int 1)
    eval env (Fix "x" x) `shouldBe` Fix "x" x
    eval env (Fix "y" x) `shouldBe` Int 1
    eval env (add x y) `shouldBe` add (Int 1) y
    eval env (add x (Int 2)) `shouldBe` Int 3
    eval env (sub x (Int 2)) `shouldBe` Int (-1)
    eval env (mul x (Int 2)) `shouldBe` Int 2

  -- it "☯ occurs" $ do
  it "☯ subtype" $ do
    let (x, y) = (Var "x", Var "y")
    subtype Knd Knd `shouldBe` Right (Knd, [])
    subtype IntT Knd `shouldBe` Left (TypeMismatch IntT Knd)
    subtype IntT IntT `shouldBe` Right (IntT, [])
    subtype NumT NumT `shouldBe` Right (NumT, [])
    subtype (Int 1) (Int 1) `shouldBe` Right (Int 1, [])
    subtype (Num 1.1) (Num 1.1) `shouldBe` Right (Num 1.1, [])
    subtype (Var "x") (Var "x") `shouldBe` Right (Var "x", [])
    subtype (Var "x") IntT `shouldBe` Right (IntT, [("x", IntT)])
    subtype IntT (Var "x") `shouldBe` Right (IntT, [("x", IntT)])
    -- TODO: Fun
    -- TODO: App
    -- TODO: Ctr
    subtype IntT (Or x y) `shouldBe` Right (IntT, [("x", IntT), ("y", IntT)])
    subtype IntT (Or x NumT) `shouldBe` Right (IntT, [("x", IntT)])
    subtype IntT (Or NumT y) `shouldBe` Right (IntT, [("y", IntT)])
    subtype (Or x y) IntT `shouldBe` Right (IntT, [("x", IntT), ("y", IntT)])
    subtype (Or x NumT) IntT `shouldBe` Left (TypeMismatch NumT IntT)
    subtype (Or NumT y) IntT `shouldBe` Left (TypeMismatch NumT IntT)
    -- TODO: Op
    True `shouldBe` True

  it "☯ infer values" $ do
    let env = []
    infer env Err `shouldBe` Left RuntimeError
    infer env Knd `shouldBe` Right (Knd, [])
    infer env IntT `shouldBe` Right (Knd, [])
    infer env NumT `shouldBe` Right (Knd, [])
    infer env (Int 1) `shouldBe` Right (IntT, [])
    infer env (Num 1) `shouldBe` Right (NumT, [])

  it "☯ infer Var" $ do
    let env =
          [ ("inferred", Int 1),
            ("mismatch", Ann (Int 1) (For [] NumT)),
            ("match", Ann (Int 1) (For [] IntT)),
            ("typed", Ann (Var "typed") (For [] IntT)),
            ("free", Var "free")
          ]
    infer env (Var "undefined") `shouldBe` Left (UndefinedVar "undefined")
    infer env (Var "inferred") `shouldBe` Right (IntT, [])
    infer env (Var "mismatch") `shouldBe` Left (TypeMismatch IntT NumT)
    infer env (Var "match") `shouldBe` Right (IntT, [])
    infer env (Var "typed") `shouldBe` Right (IntT, [])
    infer env (Var "free") `shouldBe` Right (Knd, [])

  it "☯ infer Union" $ do
    let env = []
    infer env (Union []) `shouldBe` Right (Knd, [])
    infer env (Union [("A", IntT)]) `shouldBe` Right (Knd, [])

  it "☯ infer Typ" $ do
    let x = Var "x"
    let env =
          [ ("T0", Ann (Typ "T0" []) (For [] $ Union [("A", Var "T0")])),
            ("T1", Lam x (Ann (Typ "T1" [x]) (For [] $ Union []))),
            ("TA", Lam x (Ann (Typ "TA" [x]) (For [] $ Union [("A", App (Var "TA") (Int 0))]))),
            ("TB", Lam x (Ann (Typ "TB" [x]) (For [] $ Union [("B", App (Var "TB") x)]))),
            ("TC", Ann (Lam x (Typ "TC" [x])) (For [] $ Fun IntT (Union [])))
          ]
    infer env (Typ "T0" []) `shouldBe` Right (Union [("A", Typ "T0" [])], [])
    infer env (Typ "T0" [Int 1]) `shouldBe` Left (NumArgsMismatch "T0" 0 [Int 1])
    infer env (Typ "T1" []) `shouldBe` Left (NumArgsMismatch "T1" 1 [])
    infer env (Typ "T1" [Int 1]) `shouldBe` Right (Union [], [("xT", IntT)])
    infer env (Typ "TA" [Int 1]) `shouldBe` Right (Union [("A", Typ "TA" [Int 0])], [("xT", IntT)])
    infer env (Typ "TB" [Int 1]) `shouldBe` Right (Union [("B", Typ "TB" [Int 1])], [("xT", IntT)])
    -- infer env (Typ "TC" [Int 1]) `shouldBe` Right (Union [("A", Typ "TC" [Int 0]), ("B", Typ "TC" [Int 1])], [("xT", IntT)])
    -- infer env (Typ "TC" [Num 1.1]) `shouldBe` Right (Err, [])
    True `shouldBe` True

  -- it "☯ infer Ctr" $ do
  --   let env = []
  --   infer env (Ctr "T1" "A" []) `shouldBe` Right (Typ "T1" [Int 0], [])
  --   infer env (Ctr "T1" "B" [Ctr "T1" "A" []]) `shouldBe` Right (Typ "T1" [Int 0], [("n", Int 0)])
  --   infer env (Ctr "TX" "A" []) `shouldBe` Right (Err, [])

  it "☯ infer Lam" $ do
    let (x, y) = (Var "x", Var "y")
    let (xT, yT) = (Var "xT", Var "yT")
    let env =
          [ ("x", Int 1),
            ("y", Num 1.1)
          ]
    infer env (Lam (Int 1) y) `shouldBe` Right (Fun (Ann (Int 1) (For [] IntT)) NumT, [])
    infer env (Lam (Var "x") y) `shouldBe` Right (Fun (Ann x (For [] xT)) NumT, [])
    infer env (Lam (Var "x") x) `shouldBe` Right (Fun (Ann x (For [] xT)) xT, [])
    -- infer env (Lam (Ctr "T1" "A" []) y) `shouldBe` Right (Fun (typ (Int 0)) NumT, [])
    -- infer env (Lam (Ctr "T1" "B" [Ctr "T1" "A" []]) y) `shouldBe` Right (Fun (typ (Int 1)) NumT, [("n", Int 1)])
    -- infer env (Lam (Ctr "T1" "B" [y]) y) `shouldBe` Right (Fun (typ y) yT, [("n", yT)])
    True `shouldBe` True

  it "☯ infer Fun" $ do
    let env = []
    infer env (Fun IntT NumT) `shouldBe` Right (Knd, [])

  it "☯ infer App" $ do
    let env =
          [ ("x", Int 1),
            ("y", Num 1.1),
            ("f", Ann (Var "f") (For [] $ Fun IntT NumT)),
            ("g", Ann (Var "g") (For ["a"] $ Fun (Var "a") (Var "a")))
          ]
    infer env (App (Var "x") (Var "y")) `shouldBe` Left (NotAFunction IntT)
    infer env (App (Var "f") (Var "y")) `shouldBe` Left (TypeMismatch IntT NumT)
    infer env (App (Var "f") (Var "x")) `shouldBe` Right (NumT, [])
    infer env (App (Var "g") (Var "x")) `shouldBe` Right (IntT, [("a", IntT)])

  it "☯ infer Ann" $ do
    let env = []
    -- TODO: Typ
    -- infer env (Ann (Lam (Ctr "T1" "B" [y]) y) (For [] $ Fun (typ IntT) IntT)) `shouldBe` Right (Fun (typ IntT) IntT, [("n", IntT), ("yT", IntT)])
    -- infer env (Ann (Lam (Ctr "T1" "B" [y]) y) (For [] $ Fun (typ NumT) IntT)) `shouldBe` Left (TypeMismatch IntT NumT)
    True `shouldBe` True

  it "☯ infer Ann" $ do
    -- TODO: Or
    True `shouldBe` True

  it "☯ infer Let" $ do
    -- TODO: Let
    True `shouldBe` True

  it "☯ infer Fix" $ do
    -- TODO: Fix
    True `shouldBe` True

  it "☯ infer Op2" $ do
    -- TODO: Op2
    True `shouldBe` True

  it "☯ infer Call" $ do
    -- TODO: Call
    -- infer env (Op "op0" []) `shouldBe` Right (IntT, [])
    -- infer env (Op "op0" [Num 1.1]) `shouldBe` Left (NotAFunction IntT)
    -- infer env (Op "op1" [Num 1.1]) `shouldBe` Left (TypeMismatch IntT NumT)
    -- infer env (Op "op1" [Int 1]) `shouldBe` Right (NumT, [])
    True `shouldBe` True

  let boolT = Typ "Bool" []
  let boolenv :: Env
      boolenv =
        [ ("Bool", Ann boolT (For [] $ Union [("True", Var "Bool"), ("False", Var "Bool")])),
          ("False", Ctr "Bool" "False" []),
          ("True", Ctr "Bool" "True" [])
        ]

  -- it "☯ Bool" $ do
  --   let case' =
  --         or'
  --           [ Lam (Ctr "Bool" "True" []) (Int 1),
  --             Lam (Ctr "Bool" "False" []) (Int 0)
  --           ]
  --   let env = boolenv

  --   let eval' = eval env
  --   eval' (App case' (Ctr "Bool" "False" [])) `shouldBe` Int 0
  --   eval' (App case' (Ctr "Bool" "True" [])) `shouldBe` Int 1

  --   let infer' = infer env
  --   infer' (Var "Bool") `shouldBe` Right (Union [("True", boolT), ("False", boolT)], [])
  --   infer' (Var "False") `shouldBe` Right (boolT, [])
  --   -- infer' (Var "True") `shouldBe` Right (boolT, [])
  --   -- infer' case' `shouldBe` Right (Fun (Ctr "Bool" "True" []) IntT `Or` Fun (Ctr "Bool" "False" []) IntT, [])
  --   -- infer' (Ann case' (For [] $ Fun boolT IntT)) `shouldBe` Right (Fun boolT IntT, [])
  --   -- infer' (App case' (Var "False")) `shouldBe` Right (IntT, [])
  --   -- infer' (App case' (Var "True")) `shouldBe` Right (IntT, [])
  --   True `shouldBe` True

  -- it "☯ Maybe" $ do
  --   let a = Var "a"
  --   let xT = Var "xT"
  --   let maybeT x = Typ "Maybe" [("a", x)] [("Just", Fun a (App (Var "Maybe") a)), ("Nothing", App (Var "Maybe") a)]
  --   let case' =
  --         or'
  --           [ Lam (Ctr "Maybe" "Just" [Var "x"]) (Var "x"),
  --             Lam (Ctr "Maybe" "Nothing" []) (Int 0)
  --           ]
  --   let env :: Env
  --       env =
  --         [ ("Maybe", Ann (Lam (Var "a") (maybeT a)) (For [] $ Fun Knd Knd)),
  --           ("Just", Lam (Var "x") (Ctr "Maybe" "Just" [Var "x"])),
  --           ("Nothing", Ctr "Maybe" "Nothing" [])
  --         ]

  --   let eval' = eval env
  --   eval' (App case' (Ctr "Maybe" "Nothing" [])) `shouldBe` Int 0
  --   eval' (App case' (Ctr "Maybe" "Just" [Int 1])) `shouldBe` Int 1

  --   let infer' = infer env
  --   infer' (app (Var "Maybe") []) `shouldBe` Right (Fun Knd Knd, [("aT", Knd)])
  --   infer' (app (Var "Maybe") [IntT]) `shouldBe` Right (Knd, [("aT", Knd)])
  --   infer' (app (Var "Nothing") []) `shouldBe` Right (maybeT a, [])
  --   infer' (app (Var "Just") []) `shouldBe` Right (Fun a (maybeT a), [("xT", a)])
  --   infer' (app (Var "Just") [Int 1]) `shouldBe` Right (maybeT IntT, [("xT", IntT), ("a", IntT)])
  --   infer' case' `shouldBe` Right (Fun (Ctr "Maybe" "Just" [xT]) xT `Or` Fun (Ctr "Maybe" "Nothing" []) IntT, [("a", xT)])
  --   infer' (Ann case' (For [] $ Fun (maybeT IntT) IntT)) `shouldBe` Right (Fun (maybeT IntT) IntT, [("a", IntT), ("xT", IntT)])
  --   infer' (Ann case' (For [] $ Fun (maybeT NumT) IntT)) `shouldBe` Left (TypeMismatch IntT NumT)
  --   infer' (App case' (Ctr "Maybe" "Nothing" [])) `shouldBe` Right (IntT, [("a", IntT), ("xT", IntT)])
  --   infer' (App case' (Ctr "Maybe" "Just" [Int 1])) `shouldBe` Right (IntT, [("a", IntT), ("a", IntT), ("xT", IntT)])
  --   infer' (App case' (Ctr "Maybe" "Just" [Num 1.1])) `shouldBe` Left (TypeMismatch NumT IntT)

  -- it "☯ Nat" $ do
  --   let natT = Typ "Nat" [] [("Succ", Fun (Var "Nat") (Var "Nat")), ("Zero", Var "Nat")]
  --   let case' =
  --         or'
  --           [ Lam (Ctr "Nat" "Succ" [Var "n"]) (Int 1),
  --             Lam (Ctr "Nat" "Zero" []) (Int 0)
  --           ]
  --   let env :: Env
  --       env =
  --         [ ("Nat", natT),
  --           ("Succ", Lam (Var "n") (Ctr "Nat" "Succ" [Var "n"])),
  --           ("Zero", Ctr "Nat" "Zero" [])
  --         ]

  --   let eval' = eval env
  --   eval' (App case' (Ctr "Nat" "Zero" [])) `shouldBe` Int 0
  --   eval' (App case' (Ctr "Nat" "Succ" [Var "Zero"])) `shouldBe` Int 1

  --   let infer' = infer env
  --   infer' (Var "Nat") `shouldBe` Right (Knd, [])
  --   infer' (Var "Zero") `shouldBe` Right (natT, [])
  --   infer' (Var "Succ") `shouldBe` Right (Fun natT natT, [("nT", natT)])
  --   infer' (App (Var "Succ") (Var "Zero")) `shouldBe` Right (natT, [("nT", natT)])
  --   infer' (Ctr "Nat" "Succ" []) `shouldBe` Right (Fun natT natT, [])
  --   infer' (Ctr "Nat" "Succ" [Var "Zero"]) `shouldBe` Right (natT, [])
  --   infer' case' `shouldBe` Right (Fun (Ctr "Nat" "Succ" [Var "nT"]) IntT `Or` Fun (Ctr "Nat" "Zero" []) IntT, [("Nat", Var "nT")])
  --   infer' (App case' (Ctr "Nat" "Zero" [])) `shouldBe` Right (IntT, [("Nat", Var "nT")])
  --   infer' (App case' (Ctr "Nat" "Succ" [Var "Zero"])) `shouldBe` Right (IntT, [("Nat", Var "nT")])

  -- it "☯ Vec" $ do
  --   let (n, a) = (Var "n", Var "a")
  --   let vecT x y = eval [] (Typ "Vec" [("n", x), ("a", y)] [("Cons", fun [a, app (Var "Vec") [n, a]] (app (Var "Vec") [Op "+" [n, Int 1], a])), ("Nil", app (Var "Vec") [Int 0, a])])
  --   let case' =
  --         or'
  --           [ Lam (Ctr "Vec" "Cons" [Var "x", Var "xs"]) (Var "x"),
  --             Lam (Ctr "Vec" "Nil" []) (Int 0)
  --           ]
  --   let env :: Env
  --       env =
  --         [ ("Vec", Ann (lam [Var "n", Var "a"] (vecT n a)) (For [] $ fun [IntT, Knd] Knd)),
  --           ("Cons", lam [Var "x", Var "xs"] (Ctr "Vec" "Cons" [Var "x", Var "xs"])),
  --           ("Nil", Ctr "Vec" "Nil" [])
  --         ]

  --   let eval' = eval env
  --   eval' (App case' (Var "Nil")) `shouldBe` Int 0
  --   eval' (App case' (Ctr "Vec" "Cons" [Int 1, Var "Nil"])) `shouldBe` Int 1
  --   eval' (App case' (Ctr "Vec" "Cons" [Int 2, Var "Nil"])) `shouldBe` Int 2

  --   let infer' = infer env
  --   -- infer' (app (Var "Vec") []) `shouldBe` Right (fun [IntT, Knd] Knd, [("nT", IntT), ("aT", Knd)])
  --   -- infer' (app (Var "Vec") [Int 0]) `shouldBe` Right (Fun Knd Knd, [("nT", IntT), ("aT", Knd)])
  --   -- infer' (app (Var "Vec") [Int 0, NumT]) `shouldBe` Right (Knd, [("nT", IntT), ("aT", Knd)])
  --   -- infer' (app (Var "Nil") []) `shouldBe` Right (vecT (Int 0) a, [])
  --   -- infer' (app (Var "Cons") []) `shouldBe` Right (fun [a, vecT n a] (vecT (Op "+" [n, Int 1]) a), [("xT", a), ("xsT", vecT n a)])
  --   -- infer' (app (Var "Cons") [Int 42]) `shouldBe` Right (fun [vecT n IntT] (vecT (Op "+" [n, Int 1]) IntT), [("xT", IntT), ("xsT", vecT n IntT), ("a", IntT)])
  --   -- infer' (app (Var "Cons") [Int 42, Var "Nil"]) `shouldBe` Right (vecT (Int 1) IntT, [("xT", IntT), ("xsT", vecT (Int 0) IntT), ("a", IntT), ("n", Int 0)])
  --   infer' (App case' (Var "Nil")) `shouldBe` Right (IntT, [])
  --   -- infer' (App case' (Ctr "Vec" "Cons" [Int 42, Var "Nil"])) `shouldBe` Right (IntT, [])
  --   True `shouldBe` True

  it "☯ factorial" $ do
    let (i0, i1) = (Int 0, Int 1)
    let (f, n, m) = (Var "f", Var "n", Var "m")
    let def = Fix "f" (Lam i0 i1 `Or` Lam n (n `mul` App f (n `sub` i1)))
    let env = ("f", def) : boolenv

    eval env (Var "f") `shouldBe` def
    eval env (App f m) `shouldBe` App def m
    eval env (App f (Int 0)) `shouldBe` Int 1
    eval env (App f (Int 1)) `shouldBe` Int 1
    eval env (App f (Int 2)) `shouldBe` Int 2
    eval env (App f (Int 3)) `shouldBe` Int 6
    eval env (App f (Int 4)) `shouldBe` Int 24
    eval env (App f (Int 5)) `shouldBe` Int 120

    let infer' a = fmap fst (infer env a)
    infer' (Var "f") `shouldBe` Right (Fun IntT IntT)
    infer' (App f (Int 0)) `shouldBe` Right IntT
