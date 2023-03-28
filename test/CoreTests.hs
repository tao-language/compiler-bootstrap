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

      add :: [Expr] -> Maybe Expr
      add [Int a, Int b] = Just (Int (a + b))
      add _ = Nothing

      sub :: [Expr] -> Maybe Expr
      sub [Int a, Int b] = Just (Int (a - b))
      sub _ = Nothing

      mul :: [Expr] -> Maybe Expr
      mul [Int a, Int b] = Just (Int (a * b))
      mul _ = Nothing

      eq :: [Expr] -> Maybe Expr
      eq [Int a, Int b] | a == b = Just (Ctr "True")
      eq [Int _, Int _] = Just (Ctr "False")
      eq _ = Nothing

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
    eval' (Ctr "A") `shouldBe` Ctr "A"
    eval' (Var "x") `shouldBe` Int 1
    eval' (Var "y") `shouldBe` Var "y"
    eval' (Let [("x", Int 0)] x) `shouldBe` Int 1
    eval' (Let [("y", Int 0)] y) `shouldBe` Int 0
    eval' (For "x" x) `shouldBe` For "x" x
    eval' (For "y" x) `shouldBe` For "y" (Int 1)
    eval' (Lam "x" x) `shouldBe` Lam "x" x
    eval' (Lam "y" x) `shouldBe` Lam "y" (Int 1)
    eval' (Case [("A", x)]) `shouldBe` Case [("A", Int 1)]
    eval' (Fun a b) `shouldBe` Fun IntT NumT
    eval' (App (Ctr "A") x) `shouldBe` App (Ctr "A") (Int 1)
    eval' (App (Lam "y" y) x) `shouldBe` Int 1
    eval' (App (Case [("A", x)]) y) `shouldBe` App (Case [("A", Int 1)]) y
    eval' (App (Case [("A", x)]) (Ctr "A")) `shouldBe` Int 1
    eval' (App (Case [("A", x)]) (Ctr "B")) `shouldBe` App (Case [("A", Int 1)]) (Ctr "B")
    eval' (App (Case [("B", Lam "y" y)]) (App (Ctr "B") x)) `shouldBe` Int 1
    eval' (App (Case [("A", Int 1), ("B", Int 2)]) (Ctr "A")) `shouldBe` Int 1
    eval' (App (Case [("A", Int 1), ("B", Int 2)]) (Ctr "B")) `shouldBe` Int 2
    eval' (Op "+" [x, y]) `shouldBe` Op "+" [Int 1, y]
    eval' (Op "+" [x, Int 2]) `shouldBe` Int 3
    eval' (Op "-" [x, Int 2]) `shouldBe` Int (-1)
    eval' (Op "*" [x, Int 2]) `shouldBe` Int 2
    eval' (Op "==" [x, Int 1]) `shouldBe` Ctr "True"
    eval' (Op "==" [x, Int 2]) `shouldBe` Ctr "False"

  -- it "☯ occurs" $ do
  -- it "☯ unify" $ do

  it "☯ instantiate" $ do
    let (a, a1, b) = (Var "a", Var "a1", Var "b")
    let ctx :: Context
        ctx = [("a", Val IntT)]
    let inst = instantiate ops ctx
    inst a `shouldBe` (IntT, ctx)
    inst (For "a" a) `shouldBe` (a1, ("a1", Val a1) : ctx)
    inst (For "b" b) `shouldBe` (b, ("b", Val b) : ctx)

  it "☯ inferType" $ do
    let a = Var "a"
    let (x, y) = (Var "x", Var "y")
    let xT = Var "xT"
    let (f, g) = (Var "f", Var "g")
    let ctx :: Context
        ctx =
          [ ("Invalid", Val Typ),
            ("Bool", Ann (Ctr "Bool") Typ),
            ("True", Ann (Ctr "True") (Var "Bool")),
            ("False", Ann (Ctr "False") (Var "Bool")),
            ("Maybe", Ann (Ctr "Maybe") (Fun Typ Typ)),
            ("Just", Ann (Ctr "Just") (For "a" $ Fun a (App (Var "Maybe") a))),
            ("Nothing", Ann (Ctr "Nothing") (For "a" $ App (Var "Maybe") a)),
            ("inferred", Val (Int 1)),
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

    let infer = inferType ops ctx
    infer Typ `shouldBe` Right (Typ, ctx)
    infer IntT `shouldBe` Right (Typ, ctx)
    infer (Int 1) `shouldBe` Right (IntT, ctx)
    infer NumT `shouldBe` Right (Typ, ctx)
    infer (Num 1) `shouldBe` Right (NumT, ctx)
    infer (Ctr "Undefined") `shouldBe` Left (UndefinedCtr "Undefined")
    infer (Ctr "Invalid") `shouldBe` Left (InvalidCtr "Invalid" (Val Typ))
    infer (Ctr "Bool") `shouldBe` Right (Typ, ctx)
    infer (Ctr "True") `shouldBe` Right (Ctr "Bool", ctx)
    infer (Var "undefined") `shouldBe` Left (UndefinedVar "undefined")
    infer (Var "inferred") `shouldBe` Right (IntT, ctx)
    infer (Var "mismatch") `shouldBe` Left (Mismatch IntT NumT)
    infer (Var "match") `shouldBe` Right (IntT, ctx)
    infer (Var "typed") `shouldBe` Right (IntT, ctx)
    -- infer (Var "free") `shouldBe` Right (Var "freeT", ("free", Ann (Var "free") (For "freeT" (Var "freeT"))) : ctx)
    infer (Var "x") `shouldBe` Right (IntT, ctx)
    infer (Var "y") `shouldBe` Right (NumT, ctx)
    infer (Var "f") `shouldBe` Right (Fun IntT NumT, ctx)
    infer (Var "g") `shouldBe` Right (For "a" $ Fun a a, ctx)
    -- TODO: Let
    infer (For "x" (Int 1)) `shouldBe` Right (IntT, ctx)
    infer (For "x" x) `shouldBe` Right (For "xT" xT, ctx)
    infer (Lam "x" x) `shouldBe` Right (For "xT" $ Fun xT xT, ctx)
    infer (Case [("True", Int 1)]) `shouldBe` Right (Fun (Ctr "Bool") IntT, ctx)
    infer (Case [("Nothing", Int 0)]) `shouldBe` Right (For "a" $ Fun (App (Ctr "Maybe") a) IntT, ctx)
    infer (Case [("Just", Lam "x" x)]) `shouldBe` Right (For "a" $ Fun (App (Ctr "Maybe") a) a, ctx)
    infer (Fun (Int 1) (Num 1.1)) `shouldBe` Left (Mismatch IntT Typ)
    infer (Fun IntT (Num 1.1)) `shouldBe` Left (Mismatch NumT Typ)
    infer (Fun IntT NumT) `shouldBe` Right (Typ, ctx)
    infer (App x y) `shouldBe` Left (NotAFunction x IntT)
    infer (App f y) `shouldBe` Left (Mismatch NumT IntT)
    infer (App f x) `shouldBe` Right (NumT, ctx)
    infer (App g x) `shouldBe` Right (IntT, ("a", Val IntT) : ctx)
    infer (Op "op0" []) `shouldBe` Right (IntT, ctx)
    infer (Op "op0" [Num 1.1]) `shouldBe` Left (NotAFunction (Var "op0") IntT)
    infer (Op "op1" [Num 1.1]) `shouldBe` Left (Mismatch NumT IntT)
    infer (Op "op1" [Int 1]) `shouldBe` Right (NumT, ctx)

  it "☯ Bool" $ do
    let f = Var "f"
    let ctx :: Context
        ctx =
          [ ("Bool", Ann (Ctr "Bool") Typ),
            ("False", Ann (Ctr "False") (Var "Bool")),
            ("True", Ann (Ctr "True") (Var "Bool")),
            ("f", Val (Case [("False", Int 0), ("True", Int 1)]))
          ]

    let infer = inferType ops ctx
    infer (Var "Bool") `shouldBe` Right (Typ, ctx)
    infer (Var "False") `shouldBe` Right (Ctr "Bool", ctx)
    infer (Var "True") `shouldBe` Right (Ctr "Bool", ctx)

    let eval' = eval ops (ctxEnv ctx)
    eval' (App f $ Var "False") `shouldBe` Int 0
    eval' (App f $ Var "True") `shouldBe` Int 1

  it "☯ Maybe" $ do
    let (f, a) = (Var "f", Var "a")
    let ctx :: Context
        ctx =
          [ ("Maybe", Ann (Ctr "Maybe") (Fun Typ Typ)),
            ("Just", Ann (Ctr "Just") (For "a" $ Fun a (App (Var "Maybe") a))),
            ("Nothing", Ann (Ctr "Nothing") (For "a" $ App (Var "Maybe") a)),
            ("f", Val (Case [("Nothing", Int 0), ("Just", Lam "x" $ Var "x")]))
          ]

    let infer = inferType ops ctx
    infer (Var "Maybe") `shouldBe` Right (Fun Typ Typ, ctx)
    infer (Var "Nothing") `shouldBe` Right (For "a" $ App (Ctr "Maybe") a, ctx)
    infer (Var "Just") `shouldBe` Right (For "a" $ Fun a (App (Ctr "Maybe") a), ctx)
    infer (App (Var "Maybe") IntT) `shouldBe` Right (Typ, ctx)
    infer (App (Var "Just") (Int 1)) `shouldBe` Right (App (Ctr "Maybe") IntT, ("a", Val IntT) : ctx)
    infer (App (Var "Nothing") IntT) `shouldBe` Left (NotAFunction (Var "Nothing") (App (Ctr "Maybe") a))

    let eval' = eval ops (ctxEnv ctx)
    eval' (App f $ Var "Nothing") `shouldBe` Int 0
    eval' (App f $ App (Var "Just") (Int 1)) `shouldBe` Int 1

  it "☯ factorial" $ do
    let op2 op = lam ["x", "y"] (Op op [Var "x", Var "y"])
    let (i0, i1) = (Int 0, Int 1)
    let (f, n) = (Var "f", Var "n")
    let eq a b = app (Var "==") [a, b]
    let mul a b = app (Var "*") [a, b]
    let sub a b = app (Var "-") [a, b]

    let ctx :: Context
        ctx =
          [ ("+", Ann (op2 "+") (fun [IntT, IntT] IntT)),
            ("-", Ann (op2 "-") (fun [IntT, IntT] IntT)),
            ("*", Ann (op2 "*") (fun [IntT, IntT] IntT)),
            ("==", Ann (op2 "==") (fun [IntT, IntT] (Var "Bool"))),
            ("Bool", Ann (Ctr "Bool") Typ),
            ("False", Ann (Ctr "False") (Var "Bool")),
            ("True", Ann (Ctr "True") (Var "Bool")),
            ("f", Val $ Lam "n" $ App (Case [("True", i1), ("False", n `mul` App f (n `sub` i1))]) (eq n i0))
          ]

    -- let infer = inferType ops ctx
    -- infer (Var "f") `shouldBe` Right (Typ, ctx)

    let eval' = eval ops (ctxEnv ctx)
    eval' (App f (Int 0)) `shouldBe` Int 1
    eval' (App f (Int 1)) `shouldBe` Int 1
    eval' (App f (Int 2)) `shouldBe` Int 2
    eval' (App f (Int 3)) `shouldBe` Int 6
    eval' (App f (Int 4)) `shouldBe` Int 24
    eval' (App f (Int 5)) `shouldBe` Int 120
