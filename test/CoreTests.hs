module CoreTests where

import Core
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--==☯️ Core language ☯️==--" $ do
  let ops :: Ops
      ops =
        [ ("+", add),
          ("-", sub),
          ("*", mul)
        ]

      add :: [Expr] -> Maybe Expr
      add [Lit (Int a), Lit (Int b)] = Just (int (a + b))
      add _ = Nothing

      sub :: [Expr] -> Maybe Expr
      sub [Lit (Int a), Lit (Int b)] = Just (int (a - b))
      sub _ = Nothing

      mul :: [Expr] -> Maybe Expr
      mul [Lit (Int a), Lit (Int b)] = Just (int (a * b))
      mul _ = Nothing

  it "☯ instantiate" $ do
    let (a, a1) = (Var "a", Var "a1")
    let ctx :: Context
        ctx = [("a", Val intT)]
    let inst = instantiate ops ctx
    inst (For [] a) `shouldBe` Right (intT, ctx)
    inst (For ["a"] a) `shouldBe` Right (a1, ("a1", Val a1) : ctx)

  it "☯ inferType" $ do
    let a = Var "a"
    let (x, y) = (Var "x", Var "y")
    let (xT, x1) = (Var "xT", Var "x1")
    let (f, g) = (Var "f", Var "g")
    let ctx :: Context
        ctx =
          [ ("Invalid", Val Typ),
            ("Bool", Ann (ctr "Bool") (For [] Typ)),
            ("True", Ann (ctr "True") (For [] $ Var "Bool")),
            ("False", Ann (ctr "False") (For [] $ Var "Bool")),
            ("Maybe", Ann (ctr "Maybe") (For [] $ Fun Typ Typ)),
            ("Just", Ann (ctr "Just") (For ["a"] $ Fun a (App (Var "Maybe") a))),
            ("Nothing", Ann (ctr "Nothing") (For ["a"] $ App (Var "Maybe") a)),
            ("inferred", Val (int 1)),
            ("mismatch", Ann (int 1) (For [] numT)),
            ("match", Ann (int 1) (For [] intT)),
            ("typed", Ann (Var "typed") (For [] intT)),
            ("free", Val (Var "free")),
            ("x", Val (int 1)),
            ("y", Val (num 1.1)),
            ("f", Ann f (For [] $ Fun intT numT)),
            ("g", Ann g (For ["x"] $ Fun x x)),
            ("op0", Ann (Var "op0") (For [] intT)),
            ("op1", Ann (Var "op1") (For [] $ Fun intT numT))
          ]

    let infer = inferType ops ctx
    infer Typ `shouldBe` Right (Typ, ctx)
    infer (Lit IntT) `shouldBe` Right (Typ, ctx)
    infer (Lit (Int 1)) `shouldBe` Right (intT, ctx)
    infer (Lit NumT) `shouldBe` Right (Typ, ctx)
    infer (Lit (Num 1)) `shouldBe` Right (numT, ctx)
    infer (Lit (Ctr "Undefined")) `shouldBe` Left (UndefinedCtr "Undefined")
    infer (Lit (Ctr "Invalid")) `shouldBe` Left (InvalidCtr "Invalid" (Val Typ))
    infer (Lit (Ctr "Bool")) `shouldBe` Right (Typ, ctx)
    infer (Lit (Ctr "True")) `shouldBe` Right (ctr "Bool", ctx)
    infer (Var "undefined") `shouldBe` Left (UndefinedVar "undefined")
    infer (Var "inferred") `shouldBe` Right (intT, ctx)
    infer (Var "mismatch") `shouldBe` Left (Mismatch intT numT)
    infer (Var "match") `shouldBe` Right (intT, ctx)
    infer (Var "typed") `shouldBe` Right (intT, ctx)
    infer (Var "free") `shouldBe` Right (Var "freeT", ("free", Ann (Var "free") (For ["freeT"] (Var "freeT"))) : ctx)
    infer (Var "x") `shouldBe` Right (intT, ctx)
    infer (Var "y") `shouldBe` Right (numT, ctx)
    infer (Var "f") `shouldBe` Right (Fun intT numT, ctx)
    infer (Var "g") `shouldBe` Right (Fun x1 x1, ("x1", Val x1) : ctx)
    infer (Lam "x" x) `shouldBe` Right (Fun xT xT, ("xT", Val xT) : ("x", Ann x (For ["xT"] xT)) : ctx)
    infer (Case []) `shouldBe` Left EmptyCase
    infer (Case [("True", int 1)]) `shouldBe` Right (Fun (ctr "Bool") intT, ctx)
    infer (Case [("True", int 1), ("False", int 2)]) `shouldBe` Right (Fun (ctr "Bool") intT, ctx)
    infer (Case [("True", int 1), ("False", num 1.1)]) `shouldBe` Left (Mismatch intT numT)
    infer (Case [("Just", Lam "x" x)]) `shouldBe` Right (Fun (App (ctr "Maybe") a) a, ("xT", Val a) : ("x", Ann x (For ["xT"] xT)) : ("a", Val a) : ctx)
    infer (Case [("Just", Lam "x" x), ("Nothing", int 0)]) `shouldBe` Right (Fun (App (ctr "Maybe") intT) intT, ("a1", Val intT) : ("xT", Val intT) : ("x", Ann x (For ["xT"] xT)) : ("a", Val intT) : ctx)
    infer (Fun (int 1) (num 1.1)) `shouldBe` Left (Mismatch intT Typ)
    infer (Fun intT (num 1.1)) `shouldBe` Left (Mismatch numT Typ)
    infer (Fun intT numT) `shouldBe` Right (Typ, ctx)
    infer (App x y) `shouldBe` Left (NotAFunction x intT)
    infer (App f y) `shouldBe` Left (Mismatch numT intT)
    infer (App f x) `shouldBe` Right (numT, ctx)
    infer (App g x) `shouldBe` Right (intT, ("x1", Val intT) : ctx)
    infer (Op "op0" []) `shouldBe` Right (intT, ctx)
    infer (Op "op0" [num 1.1]) `shouldBe` Left (NotAFunction (Var "op0") intT)
    infer (Op "op1" [num 1.1]) `shouldBe` Left (Mismatch numT intT)
    infer (Op "op1" [int 1]) `shouldBe` Right (numT, ctx)

  it "☯ Bool" $ do
    let ctx :: Context
        ctx =
          [ -- Bool = True | False
            ("Bool", Ann (ctr "Bool") (For [] Typ)),
            ("True", Ann (ctr "True") (For [] (Var "Bool"))),
            ("False", Ann (ctr "False") (For [] (Var "Bool")))
            -- f True = 1
            -- f False = 0
            -- ("f", Val (Case [("True", int 1), ("False", int 0)]))
          ]

    let infer = inferType ops ctx
    infer (Var "Bool") `shouldBe` Right (Typ, ctx)
    infer (Var "True") `shouldBe` Right (ctr "Bool", ctx)
    infer (Var "False") `shouldBe` Right (ctr "Bool", ctx)

    let eval' = eval ops (ctxEnv ctx)
    eval' (Var "Bool") `shouldBe` ctr "Bool"
    eval' (Var "True") `shouldBe` ctr "True"
    eval' (Var "False") `shouldBe` ctr "False"

  it "☯ Maybe" $ do
    {- Maybe a = Just a | Nothing

    Maybe : (a : Typ) -> Type
    Maybe a = #Maybe a

    Just : (a : Typ) -> (x : a) -> Maybe a
    Just a x = #Just x

    Nothing : (a : Typ) -> Maybe a
    Nothing a = #Nothing

    f Nothing = 0
    f (Just x) = x

    f : Maybe Int -> Int
    f = @case {Just -> \x -> x | Nothing -> 0}
    -}

    -- let a = Var "a"
    -- let env =
    --       [ ("Maybe", Lam "a" (App (ctr "Maybe") a))
    --       ]
    -- let ctx =
    --       [ ("Maybe", Fun ("a", Typ) Typ),
    --         ("Just", Fun ("a", Typ) $ App (ctr "Maybe") a),
    --         ("Nothing", Fun ("a", Typ) $ App (ctr "Maybe") a),
    --         ("f", Fun ("", App (ctr "Maybe") intT) intT)
    --       ]

    -- let infer = inferType ops env ctx
    -- infer (Var "Maybe") `shouldBe` Right (Fun ("a", Typ) Typ)
    -- infer (Var "Just") `shouldBe` Right (Fun ("a", Typ) $ App (ctr "Maybe") a)
    -- infer (Var "Nothing") `shouldBe` Right (Fun ("a", Typ) $ App (ctr "Maybe") a)
    -- infer (App (Var "Maybe") intT) `shouldBe` Right Typ
    -- infer (App (Var "Just") intT) `shouldBe` Right (App (ctr "Maybe") intT)
    -- infer (App (Var "Nothing") intT) `shouldBe` Right (App (ctr "Maybe") intT)
    True `shouldBe` True

  it "☯ factorial" $ do
    -- fact = fix (Nat->Nat) (\(f:Nat->Nat)(n:Nat).ifz n then succ 0 else mul n (f (pred n)))
    -- fact (succ (succ (succ 0)))

    -- prim "fix" =
    --   ( 2,
    --     Pi "A" (S "*") (Pi "_" (Pi "_" (V "A") (V "A")) (V "A")),
    --     \env [x, y] -> reduce env $ App y $ Prim "fix" [x, y]
    --   )
    True `shouldBe` True
