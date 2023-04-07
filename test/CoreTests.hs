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

  let boolCtx :: Context
      boolCtx =
        [ ("Bool", Union ["False", "True"] Knd),
          ("False", Alt ("Bool", []) (Var "Bool")),
          ("True", Alt ("Bool", []) (Var "Bool"))
        ]

  let maybeCtx :: Context
      maybeCtx =
        [ ("Maybe", Union ["Nothing", "Just"] (Fun Knd Knd)),
          ("Nothing", Alt ("Maybe", []) (For "a" $ App (Var "Maybe") (Var "a"))),
          ("Just", Alt ("Maybe", ["x"]) (For "a" $ Fun (Var "a") (App (Var "Maybe") (Var "a"))))
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
    eval' Knd `shouldBe` Knd
    eval' (Typ "T") `shouldBe` Typ "T"
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

  it "☯ inferType" $ do
    let a = Var "a"
    let (x, y) = (Var "x", Var "y")
    let xT = Var "xT"
    let (f, g, h) = (Var "f", Var "g", Var "h")
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
            ("h", Val (Var "h")),
            ("op0", Ann (Var "op0") IntT),
            ("op1", Ann (Var "op1") (Fun IntT NumT))
          ]

    let infer = inferType ops ctx
    infer Knd `shouldBe` Right (Knd, ctx)
    infer IntT `shouldBe` Right (Knd, ctx)
    infer (Int 1) `shouldBe` Right (IntT, ctx)
    infer NumT `shouldBe` Right (Knd, ctx)
    infer (Num 1) `shouldBe` Right (NumT, ctx)
    infer (Var "undefined") `shouldBe` Left (UndefinedVar "undefined")
    infer (Var "inferred") `shouldBe` Right (IntT, ctx)
    infer (Var "mismatch") `shouldBe` Left (Mismatch IntT NumT)
    infer (Var "match") `shouldBe` Right (IntT, ctx)
    infer (Var "typed") `shouldBe` Right (IntT, ctx)
    infer (Var "free") `shouldBe` Right (Var "freeT", ("freeT", Val (Var "freeT")) : set "free" (Ann (Var "free") (Var "freeT")) ctx)
    infer (Var "x") `shouldBe` Right (IntT, ctx)
    infer (Var "y") `shouldBe` Right (NumT, ctx)
    infer (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer (Var "f") `shouldBe` Right (Fun IntT NumT, ctx)
    infer (Var "g") `shouldBe` Right (For "a" $ Fun a a, ctx)
    infer (For "x" (Int 1)) `shouldBe` Right (IntT, ctx)
    infer (For "x" x) `shouldBe` Right (For "xT" xT, ctx)
    infer (Lam "x" x) `shouldBe` Right (For "xT" $ Fun xT xT, ctx)
    infer (Fun (Int 1) (Num 1.1)) `shouldBe` Left (Mismatch IntT Knd)
    infer (Fun IntT (Num 1.1)) `shouldBe` Left (Mismatch NumT Knd)
    infer (Fun IntT NumT) `shouldBe` Right (Knd, ctx)
    infer (App x y) `shouldBe` Left (NotAFunction x IntT)
    infer (App f y) `shouldBe` Left (Mismatch NumT IntT)
    infer (App f x) `shouldBe` Right (NumT, ctx)
    infer (App g x) `shouldBe` Right (IntT, ctx)
    infer (App h x) `shouldBe` Right (For "hT1" (Var "hT1"), ("hT", Val (Var "hT")) : set "h" (Ann (Var "h") (Var "hT")) ctx)
    infer (Op "op0" []) `shouldBe` Right (IntT, ctx)
    infer (Op "op0" [Num 1.1]) `shouldBe` Left (NotAFunction (Var "op0") IntT)
    infer (Op "op1" [Num 1.1]) `shouldBe` Left (Mismatch NumT IntT)
    infer (Op "op1" [Int 1]) `shouldBe` Right (NumT, ctx)

  it "☯ Bool" $ do
    let f = Var "f"
    let caseOf = App (Case [("False", Int 0), ("True", Int 1)])
    let ctx :: Context
        ctx =
          ("f", Val (Lam "x" $ caseOf (Var "x"))) :
          boolCtx

    let eval' = solve ops ctx
    eval' (App f $ Var "False") `shouldBe` Int 0
    eval' (App f $ Var "True") `shouldBe` Int 1
    eval' (caseOf (Var "False")) `shouldBe` Int 0
    eval' (caseOf (Var "True")) `shouldBe` Int 1

    let infer = inferType ops ctx
    infer (Var "Bool") `shouldBe` Right (Knd, ctx)
    infer (Var "False") `shouldBe` Right (Typ "Bool", ctx)
    infer (Var "True") `shouldBe` Right (Typ "Bool", ctx)
    infer (Case [("False", Int 0), ("True", Int 1)]) `shouldBe` Right (Fun (Typ "Bool") IntT, ctx)
    infer (caseOf (Num 1.1)) `shouldBe` Left (Mismatch NumT (Typ "Bool"))
    infer (caseOf (Var "True")) `shouldBe` Right (IntT, ctx)

  it "☯ Maybe" $ do
    let (f, a) = (Var "f", Var "a")
    let caseOf = App (Case [("Nothing", Int 0), ("Just", Lam "x" $ Var "x")])
    let ctx :: Context
        ctx =
          ("f", Val (Lam "x" $ caseOf (Var "x"))) :
          maybeCtx

    let eval' = solve ops ctx
    eval' (App f $ Var "Nothing") `shouldBe` Int 0
    eval' (App f $ App (Var "Just") (Int 1)) `shouldBe` Int 1
    eval' (caseOf (Var "Nothing")) `shouldBe` Int 0
    eval' (caseOf (App (Var "Just") (Int 1))) `shouldBe` Int 1

    let infer = inferType ops ctx
    infer (Var "Maybe") `shouldBe` Right (Fun Knd Knd, ctx)
    infer (Var "Nothing") `shouldBe` Right (For "a" $ App (Typ "Maybe") a, ctx)
    infer (Var "Just") `shouldBe` Right (For "a" $ Fun a (App (Typ "Maybe") a), ctx)
    infer (App (Var "Maybe") IntT) `shouldBe` Right (Knd, ctx)
    infer (App (Var "Just") (Int 1)) `shouldBe` Right (App (Typ "Maybe") IntT, ctx)
    infer (Case [("Nothing", Int 0)]) `shouldBe` Right (For "a" $ Fun (App (Typ "Maybe") a) IntT, ctx)
    infer (Case [("Just", Lam "y" $ Var "y")]) `shouldBe` Right (For "a" $ Fun (App (Typ "Maybe") a) a, ctx)
    infer (Case [("Nothing", Int 0), ("Just", Lam "x" $ Var "x")]) `shouldBe` Right (Fun (App (Typ "Maybe") IntT) IntT, ctx)
    infer (caseOf (App (Var "Just") (Int 2))) `shouldBe` Right (IntT, ctx)
    infer (caseOf (App (Var "Just") (Num 2.2))) `shouldBe` Left (Mismatch NumT IntT)

  it "☯ factorial" $ do
    let (i0, i1) = (Int 0, Int 1)
    let (f, n) = (Var "f", Var "n")
    let eq a b = app (Var "==") [a, b]
    let mul a b = app (Var "*") [a, b]
    let sub a b = app (Var "-") [a, b]

    let ctx :: Context
        ctx =
          ("f", Val (Fix "f" $ Lam "n" $ App (Case [("True", Int 1), ("False", n `mul` App f (n `sub` i1))]) (eq n i0))) :
          boolCtx ++ opsCtx

    let eval' = solve ops ctx
    eval' (Var "f") `shouldBe` Fix "f" (Lam "n" $ App (Case [("True", Int 1), ("False", Op "*" [n, App f (Op "-" [n, i1])])]) (Op "==" [n, i0]))
    -- eval' (App f n) `shouldBe` app (Op "==" [n, i0]) [Int 0, Op "*" [n, App f (Op "-" [n, i1])]]
    eval' (App f (Int 0)) `shouldBe` Int 1
    eval' (App f (Int 1)) `shouldBe` Int 1
    eval' (App f (Int 2)) `shouldBe` Int 2
    eval' (App f (Int 3)) `shouldBe` Int 6
    eval' (App f (Int 4)) `shouldBe` Int 24
    eval' (App f (Int 5)) `shouldBe` Int 120

    let infer = inferType ops ctx
    infer (Var "f") `shouldBe` Right (Fun IntT IntT, ctx)
    infer (App f (Int 0)) `shouldBe` Right (IntT, ctx)
