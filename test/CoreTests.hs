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
    eval env (Fun (x, a) b) `shouldBe` Fun (x, IntT) NumT
    eval env (App x x) `shouldBe` App (Int 1) (Int 1)
    eval env (App (Lam y y) x) `shouldBe` Int 1
    eval env (App (Lam y a) x) `shouldBe` IntT
    eval env (App (Lam (Int 1) a) x) `shouldBe` IntT
    eval env (App (Lam (Int 2) a) x) `shouldBe` Err
    eval env (App (Lam (Ctr "T" "A" []) a) (Ctr "T" "A" [])) `shouldBe` IntT
    eval env (App (Lam (Ctr "T" "A" []) a) (Ctr "T" "B" [])) `shouldBe` Err
    eval env (Ann x a) `shouldBe` Int 1
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
            ("mismatch", Ann (Int 1) NumT),
            ("match", Ann (Int 1) IntT),
            ("typed", Ann (Var "typed") IntT),
            ("free", Var "free")
          ]
    infer env (Var "undefined") `shouldBe` Left (UndefinedVar "undefined")
    infer env (Var "inferred") `shouldBe` Right (IntT, [])
    infer env (Var "mismatch") `shouldBe` Left (TypeMismatch IntT NumT)
    infer env (Var "match") `shouldBe` Right (IntT, [])
    infer env (Var "typed") `shouldBe` Right (IntT, [])
    infer env (Var "free") `shouldBe` Right (Var "freeT", [("free", Ann (Var "free") (Var "freeT"))])

  it "☯ infer Union" $ do
    let env = []
    infer env (Union []) `shouldBe` Right (Knd, [])
    infer env (Union [("A", IntT)]) `shouldBe` Right (Knd, [])

  it "☯ infer Typ" $ do
    let x = Var "x"
    let env =
          [ ("T0", Ann (Typ "T0" []) (Union [("A", Var "T0")])),
            ("T1", Lam x (Ann (Typ "T1" [x]) (Union []))),
            ("TA", Lam x (Ann (Typ "TA" [x]) (Union [("A", App (Var "TA") (Int 0))]))),
            ("TB", Lam x (Ann (Typ "TB" [x]) (Union [("B", App (Var "TB") x)]))),
            ("TC", Ann (Lam x (Typ "TC" [x])) (Fun (x, IntT) (Union [])))
          ]
    infer env (Typ "T0" []) `shouldBe` Right (Union [("A", Typ "T0" [])], [])
    infer env (Typ "T0" [Int 1]) `shouldBe` Left (NumArgsMismatch "T0" 0 [Int 1])
    infer env (Typ "T1" []) `shouldBe` Left (NumArgsMismatch "T1" 1 [])
    infer env (Typ "T1" [Int 1]) `shouldBe` Right (Union [], [("xT", IntT)])
    infer env (Typ "TA" [Int 1]) `shouldBe` Right (Union [("A", Typ "TA" [Int 0])], [("xT", IntT)])
    infer env (Typ "TB" [Int 1]) `shouldBe` Right (Union [("B", Typ "TB" [Int 1])], [("xT", IntT)])
    infer env (Typ "TC" [Int 1]) `shouldBe` Right (Union [], [])
    infer env (Typ "TC" [Num 1.1]) `shouldBe` Left (TypeMismatch IntT NumT)

  it "☯ infer Ctr" $ do
    let (x, y) = (Var "x", Var "y")
    let env =
          [ ("T1", Lam x (Ann (Typ "T1" [x]) (Union [("A", Typ "T1" [Int 0])]))),
            ("T2", Lam x (Ann (Typ "T2" [x]) (Union [("A", For "y" $ Fun (x, y) (Typ "T2" [y]))])))
          ]
    infer env (Ctr "X" "A" []) `shouldBe` Left (UndefinedVar "X")
    infer env (Ctr "T1" "A" []) `shouldBe` Right (Typ "T1" [Int 0], [])
    infer env (Ctr "T2" "A" [Ctr "T1" "A" []]) `shouldBe` Right (Typ "T2" [Typ "T1" [Int 0]], [("y", Typ "T1" [Int 0])])

  it "☯ infer Lam" $ do
    let (x, y) = (Var "x", Var "y")
    let (xT, yT) = (Var "xT", Var "yT")
    let env =
          [ ("x", Int 1),
            ("y", Num 1.1)
          ]
    infer env (Lam (Int 1) y) `shouldBe` Right (Fun (Int 1, IntT) NumT, [])
    infer env (Lam (Var "x") y) `shouldBe` Right (Fun (x, xT) NumT, [])
    infer env (Lam (Var "x") x) `shouldBe` Right (Fun (x, xT) xT, [])
    -- infer env (Lam (Ctr "T1" "A" []) y) `shouldBe` Right (Fun (typ (Int 0)) NumT, [])
    -- infer env (Lam (Ctr "T1" "B" [Ctr "T1" "A" []]) y) `shouldBe` Right (Fun (typ (Int 1)) NumT, [("n", Int 1)])
    -- infer env (Lam (Ctr "T1" "B" [y]) y) `shouldBe` Right (Fun (typ y) yT, [("n", yT)])
    True `shouldBe` True

  it "☯ infer Fun" $ do
    let x = Var "x"
    let env = [("x", Int 1)]
    infer env (Fun (x, IntT) NumT) `shouldBe` Right (Knd, [])

  it "☯ infer App" $ do
    let (x, a) = (Var "x", Var "a")
    let env =
          [ ("x", Int 1),
            ("y", Num 1.1),
            ("f", Ann (Var "f") (Fun (x, IntT) NumT)),
            ("g", Ann (Var "g") (For "a" $ Fun (x, a) a))
          ]
    infer env (App (Var "x") (Var "y")) `shouldBe` Left (NotAFunction IntT)
    infer env (App (Var "f") (Var "y")) `shouldBe` Left (TypeMismatch IntT NumT)
    infer env (App (Var "f") (Var "x")) `shouldBe` Right (NumT, [])
    infer env (App (Var "g") (Var "x")) `shouldBe` Right (IntT, [("a", IntT)])

  it "☯ infer Ann" $ do
    let env = []
    -- TODO: Typ
    -- infer env (Ann (Lam (Ctr "T1" "B" [y]) y) (Fun (typ IntT) IntT)) `shouldBe` Right (Fun (typ IntT) IntT, [("n", IntT), ("yT", IntT)])
    -- infer env (Ann (Lam (Ctr "T1" "B" [y]) y) (Fun (typ NumT) IntT)) `shouldBe` Left (TypeMismatch IntT NumT)
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

  let boolenv :: Env
      boolenv =
        [ ("Bool", Ann (Typ "Bool" []) (Union [("True", Var "Bool"), ("False", Var "Bool")])),
          ("False", Ctr "Bool" "False" []),
          ("True", Ctr "Bool" "True" [])
        ]

  it "☯ Bool" $ do
    let x = Var "x"
    let case' =
          or'
            [ Lam (Ctr "Bool" "True" []) (Int 1),
              Lam (Ctr "Bool" "False" []) (Int 0)
            ]
    let env = boolenv

    eval env (App case' (Ctr "Bool" "False" [])) `shouldBe` Int 0
    eval env (App case' (Ctr "Bool" "True" [])) `shouldBe` Int 1

    infer env (Var "Bool") `shouldBe` Right (Union [("True", Typ "Bool" []), ("False", Typ "Bool" [])], [])
    infer env (Var "False") `shouldBe` Right (Typ "Bool" [], [])
    infer env (Var "True") `shouldBe` Right (Typ "Bool" [], [])
    infer env case' `shouldBe` Right (Fun (Ctr "Bool" "True" [] `Or` Ctr "Bool" "False" [], Typ "Bool" []) IntT, [])
    infer env (Ann case' (Fun (x, Typ "Bool" []) IntT)) `shouldBe` Right (Fun (Ctr "Bool" "True" [] `Or` Ctr "Bool" "False" [], Typ "Bool" []) IntT, [])
    infer env (App case' (Var "False")) `shouldBe` Right (IntT, [])
    infer env (App case' (Var "True")) `shouldBe` Right (IntT, [])

  it "☯ Maybe" $ do
    let (x, a) = (Var "x", Var "a")
    let (xT, aT) = (Var "xT", Var "aT")
    let case' =
          or'
            [ Lam (Ctr "Maybe" "Just" [Var "x"]) (Var "x"),
              Lam (Ctr "Maybe" "Nothing" []) (Int 0)
            ]
    let alts a =
          [ ("Just", Fun (x, a) (Typ "Maybe" [a])),
            ("Nothing", Typ "Maybe" [a])
          ]
    let env =
          [ ("Maybe", Lam a (Ann (Typ "Maybe" [a]) (Union $ alts a))),
            ("Just", Lam x (Ctr "Maybe" "Just" [x])),
            ("Nothing", Ctr "Maybe" "Nothing" [])
          ]

    eval env (App case' (Ctr "Maybe" "Nothing" [])) `shouldBe` Int 0
    eval env (App case' (Ctr "Maybe" "Just" [Int 1])) `shouldBe` Int 1

    infer env (app (Var "Maybe") []) `shouldBe` Right (Fun (a, aT) (Union $ alts a), [])
    infer env (app (Var "Maybe") [IntT]) `shouldBe` Right (Union (alts IntT), [("aT", Knd)])
    infer env (app (Var "Nothing") []) `shouldBe` Right (Typ "Maybe" [a], [])
    infer env (app (Var "Just") []) `shouldBe` Right (Fun (x, a) (Typ "Maybe" [a]), [("xT", a)])
    infer env (app (Var "Just") [Int 1]) `shouldBe` Right (Typ "Maybe" [IntT], [("xT", IntT), ("a", IntT)])
    -- infer env case' `shouldBe` Right (Fun (Ctr "Maybe" "Just" [x] `Or` Ctr "Maybe" "Nothing" [], Typ "Maybe" [IntT]) IntT, [("xT", IntT)])
    -- infer env (Ann case' (Fun (x, Typ "Maybe" [IntT]) IntT)) `shouldBe` Right (Fun (x, Typ "Maybe" [IntT]) IntT, [("xT", IntT), ("xT", IntT), ("a", IntT)])
    -- infer env (Ann case' (Fun (x, Typ "Maybe" [NumT]) IntT)) `shouldBe` Left (TypeMismatch IntT NumT)
    -- infer env (App case' (Ctr "Maybe" "Nothing" [])) `shouldBe` Right (IntT, [("a", IntT), ("xT", IntT)])
    -- infer env (App case' (Ctr "Maybe" "Just" [Int 1])) `shouldBe` Right (IntT, [("a", IntT), ("a", IntT), ("xT", IntT)])
    -- infer env (App case' (Ctr "Maybe" "Just" [Num 1.1])) `shouldBe` Left (TypeMismatch NumT IntT)
    True `shouldBe` True

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

  --   let eval env = eval env
  --   eval env (App case' (Ctr "Nat" "Zero" [])) `shouldBe` Int 0
  --   eval env (App case' (Ctr "Nat" "Succ" [Var "Zero"])) `shouldBe` Int 1

  --   let infer env = infer env
  --   infer env (Var "Nat") `shouldBe` Right (Knd, [])
  --   infer env (Var "Zero") `shouldBe` Right (natT, [])
  --   infer env (Var "Succ") `shouldBe` Right (Fun natT natT, [("nT", natT)])
  --   infer env (App (Var "Succ") (Var "Zero")) `shouldBe` Right (natT, [("nT", natT)])
  --   infer env (Ctr "Nat" "Succ" []) `shouldBe` Right (Fun natT natT, [])
  --   infer env (Ctr "Nat" "Succ" [Var "Zero"]) `shouldBe` Right (natT, [])
  --   infer env case' `shouldBe` Right (Fun (Ctr "Nat" "Succ" [Var "nT"]) IntT `Or` Fun (Ctr "Nat" "Zero" []) IntT, [("Nat", Var "nT")])
  --   infer env (App case' (Ctr "Nat" "Zero" [])) `shouldBe` Right (IntT, [("Nat", Var "nT")])
  --   infer env (App case' (Ctr "Nat" "Succ" [Var "Zero"])) `shouldBe` Right (IntT, [("Nat", Var "nT")])

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
  --         [ ("Vec", Ann (lam [Var "n", Var "a"] (vecT n a)) (fun [IntT, Knd] Knd)),
  --           ("Cons", lam [Var "x", Var "xs"] (Ctr "Vec" "Cons" [Var "x", Var "xs"])),
  --           ("Nil", Ctr "Vec" "Nil" [])
  --         ]

  --   let eval env = eval env
  --   eval env (App case' (Var "Nil")) `shouldBe` Int 0
  --   eval env (App case' (Ctr "Vec" "Cons" [Int 1, Var "Nil"])) `shouldBe` Int 1
  --   eval env (App case' (Ctr "Vec" "Cons" [Int 2, Var "Nil"])) `shouldBe` Int 2

  --   let infer env = infer env
  --   -- infer env (app (Var "Vec") []) `shouldBe` Right (fun [IntT, Knd] Knd, [("nT", IntT), ("aT", Knd)])
  --   -- infer env (app (Var "Vec") [Int 0]) `shouldBe` Right (Fun Knd Knd, [("nT", IntT), ("aT", Knd)])
  --   -- infer env (app (Var "Vec") [Int 0, NumT]) `shouldBe` Right (Knd, [("nT", IntT), ("aT", Knd)])
  --   -- infer env (app (Var "Nil") []) `shouldBe` Right (vecT (Int 0) a, [])
  --   -- infer env (app (Var "Cons") []) `shouldBe` Right (fun [a, vecT n a] (vecT (Op "+" [n, Int 1]) a), [("xT", a), ("xsT", vecT n a)])
  --   -- infer env (app (Var "Cons") [Int 42]) `shouldBe` Right (fun [vecT n IntT] (vecT (Op "+" [n, Int 1]) IntT), [("xT", IntT), ("xsT", vecT n IntT), ("a", IntT)])
  --   -- infer env (app (Var "Cons") [Int 42, Var "Nil"]) `shouldBe` Right (vecT (Int 1) IntT, [("xT", IntT), ("xsT", vecT (Int 0) IntT), ("a", IntT), ("n", Int 0)])
  --   infer env (App case' (Var "Nil")) `shouldBe` Right (IntT, [])
  --   -- infer env (App case' (Ctr "Vec" "Cons" [Int 42, Var "Nil"])) `shouldBe` Right (IntT, [])
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
    infer' (Var "f") `shouldBe` Right (Fun (Or i0 n, IntT) IntT)
    infer' (App f (Int 0)) `shouldBe` Right IntT
