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
      add [Int a, Int b] = Just (Int (a + b))
      add _ = Nothing

      sub :: [Expr] -> Maybe Expr
      sub [Int a, Int b] = Just (Int (a - b))
      sub _ = Nothing

      mul :: [Expr] -> Maybe Expr
      mul [Int a, Int b] = Just (Int (a * b))
      mul _ = Nothing

  -- it "☯ eval" $ do
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
    infer (For "x" IntT) `shouldBe` Right (Typ, ctx)
    infer (For "x" x) `shouldBe` Right (For "xT" xT, ctx)
    infer (Lam "x" x) `shouldBe` Right (For "xT" $ Fun xT xT, ctx)
    infer (Case []) `shouldBe` Left EmptyCase
    infer (Case [("True", Int 1)]) `shouldBe` Right (Fun (Ctr "Bool") IntT, ctx)
    infer (Case [("True", Int 1), ("False", Int 2)]) `shouldBe` Right (Fun (Ctr "Bool") IntT, ctx)
    infer (Case [("True", Int 1), ("False", Num 1.1)]) `shouldBe` Left (Mismatch IntT NumT)
    -- infer (Case [("Just", Lam "x" x)]) `shouldBe` Right (For "a" $ Fun (App (Ctr "Maybe") a) a, ctx)
    -- infer (Case [("Just", Lam "x" x), ("Nothing", Int 0)]) `shouldBe` Right (Fun (App (Ctr "Maybe") IntT) IntT, ctx)
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
    let ctx :: Context
        ctx =
          [ -- Bool = True | False
            ("Bool", Ann (Ctr "Bool") Typ),
            ("True", Ann (Ctr "True") (Var "Bool")),
            ("False", Ann (Ctr "False") (Var "Bool"))
            -- f True = 1
            -- f False = 0
            -- ("f", Val (Case [("True", Int 1), ("False", Int 0)]))
          ]

    let infer = inferType ops ctx
    infer (Var "Bool") `shouldBe` Right (Typ, ctx)
    infer (Var "True") `shouldBe` Right (Ctr "Bool", ctx)
    infer (Var "False") `shouldBe` Right (Ctr "Bool", ctx)

    let eval' = eval ops (ctxEnv ctx)
    eval' (Var "Bool") `shouldBe` Ctr "Bool"
    eval' (Var "True") `shouldBe` Ctr "True"
    eval' (Var "False") `shouldBe` Ctr "False"

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
    --       [ ("Maybe", Lam "a" (App (Ctr "Maybe") a))
    --       ]
    -- let ctx =
    --       [ ("Maybe", Fun ("a", Typ) Typ),
    --         ("Just", Fun ("a", Typ) $ App (Ctr "Maybe") a),
    --         ("Nothing", Fun ("a", Typ) $ App (Ctr "Maybe") a),
    --         ("f", Fun ("", App (Ctr "Maybe") IntT) IntT)
    --       ]

    -- let infer = inferType ops env ctx
    -- infer (Var "Maybe") `shouldBe` Right (Fun ("a", Typ) Typ)
    -- infer (Var "Just") `shouldBe` Right (Fun ("a", Typ) $ App (Ctr "Maybe") a)
    -- infer (Var "Nothing") `shouldBe` Right (Fun ("a", Typ) $ App (Ctr "Maybe") a)
    -- infer (App (Var "Maybe") IntT) `shouldBe` Right Typ
    -- infer (App (Var "Just") IntT) `shouldBe` Right (App (Ctr "Maybe") IntT)
    -- infer (App (Var "Nothing") IntT) `shouldBe` Right (App (Ctr "Maybe") IntT)
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
