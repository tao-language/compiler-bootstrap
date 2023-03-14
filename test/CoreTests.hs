module CoreTests where

import Core
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--==☯️ Core language ☯️==--" $ do
  let (a, b, c) = (ctr "A", ctr "B", ctr "C")
  let (x, y, z) = (Var "x", Var "y", Var "z")

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

  it "☯ beta" $ do
    let y1 = Var "y1"
    beta ("x", a) (ctr "B") `shouldBe` b
    beta ("x", a) (Var "x") `shouldBe` a
    beta ("x", a) (Var "y") `shouldBe` Var "y"
    beta ("x", a) (Lam "x" Typ x) `shouldBe` Lam "x" Typ x
    beta ("x", a) (Lam "y" x y) `shouldBe` Lam "y" a y
    beta ("x", a) (Lam "y" y x) `shouldBe` Lam "y" y a
    beta ("x", y) (Lam "y" x y) `shouldBe` Lam "y1" y y1
    beta ("x", y) (Lam "y" y x) `shouldBe` Lam "y1" y y
    -- beta ("x", a) (Fun "x" Typ x) `shouldBe` Fun "x" Typ x
    -- beta ("x", a) (Fun "y" x y) `shouldBe` Fun "y" a y
    -- beta ("x", a) (Fun "y" y x) `shouldBe` Fun "y" y a
    -- beta ("x", y) (Fun "y" x y) `shouldBe` Fun "y1" y y1
    -- beta ("x", y) (Fun "y" y x) `shouldBe` Fun "y1" y y
    beta ("x", a) (App x y) `shouldBe` App a y
    beta ("x", a) (App y x) `shouldBe` App y a
    -- TODO: Fix
    beta ("x", a) (Op "+" [x, y]) `shouldBe` Op "+" [a, y]
    beta ("x", a) (Op "+" [y, x]) `shouldBe` Op "+" [y, a]

  it "☯ reduce" $ do
    let env = [("x", a), ("y", b), ("z", c)]
    let reduce' = reduce ops env
    reduce' Knd `shouldBe` Knd
    reduce' Typ `shouldBe` Typ
    reduce' intT `shouldBe` intT
    reduce' (int 1) `shouldBe` int 1
    reduce' (ctr "A") `shouldBe` a
    reduce' (Var "x") `shouldBe` a
    reduce' (Var "y") `shouldBe` b
    reduce' (Var "z") `shouldBe` c
    reduce' (Var "w") `shouldBe` Var "w"
    reduce' (Lam "x" x y) `shouldBe` Lam "x" x y
    reduce' (Lam "x" y x) `shouldBe` Lam "x" y x
    -- reduce' (Fun "x" x y) `shouldBe` Fun "x" x y
    -- reduce' (Fun "x" y x) `shouldBe` Fun "x" y x
    reduce' (Or x y) `shouldBe` Or x y
    reduce' (App Err z) `shouldBe` Err
    reduce' (App (ctr "A") z) `shouldBe` App a z
    reduce' (App (Var "x") z) `shouldBe` App a z
    reduce' (App (Lam "x" x y) z) `shouldBe` b
    reduce' (App (Lam "x" y x) z) `shouldBe` c
    reduce' (App (Lam "y" y x) z) `shouldBe` a
    -- reduce' (App (Fun "x" x y) z) `shouldBe` App (Fun "x" x y) z
    reduce' (App (Case (Ctr "A") z) x) `shouldBe` c
    reduce' (App (Case (Ctr "A") z) y) `shouldBe` Err
    reduce' (App (Or (Lam "x" y x) Err) z) `shouldBe` c
    reduce' (App (Or Err (Lam "x" y x)) z) `shouldBe` c
    reduce' (App (Op "+" [x]) y) `shouldBe` Op "+" [a, b]
    reduce' (Fix (Lam "f" y x)) `shouldBe` a
    reduce' (Op "+" [x, y]) `shouldBe` Op "+" [a, b]
  -- fix f == f (fix f)

  it "☯ eval" $ do
    let env = [("x", a), ("y", b), ("z", c)]
    let eval' = eval ops env
    eval' Knd `shouldBe` Knd
    eval' Typ `shouldBe` Typ
    eval' intT `shouldBe` intT
    eval' (int 1) `shouldBe` int 1
    eval' (ctr "A") `shouldBe` a
    eval' (Var "x") `shouldBe` a
    eval' (Var "y") `shouldBe` b
    eval' (Var "z") `shouldBe` c
    eval' (Var "w") `shouldBe` Var "w"
    eval' (Lam "x" x y) `shouldBe` Lam "x" a b
    eval' (Lam "x" y x) `shouldBe` Lam "x" b x
    -- eval' (Fun "x" x y) `shouldBe` Fun "x" a b
    -- eval' (Fun "x" y x) `shouldBe` Fun "x" b x
    eval' (App (ctr "A") z) `shouldBe` App a c
    eval' (App (Var "x") z) `shouldBe` App a c
    eval' (App (Lam "x" x y) z) `shouldBe` b
    eval' (App (Lam "x" y x) z) `shouldBe` c
    eval' (App (Lam "y" y x) z) `shouldBe` a
    -- eval' (App (Fun "x" x y) z) `shouldBe` App (Fun "x" a b) c
    eval' (App (Op "+" [x]) y) `shouldBe` Op "+" [a, b]
    eval' (Op "+" [x, y]) `shouldBe` Op "+" [a, b]

  it "☯ instantiate" $ do
    let env = [("x", int 1)]
    let ctx = [("x", intT)]
    let instantiate' = instantiate ops env ctx
    instantiate' Typ `shouldBe` (Typ, env, ctx)
    instantiate' (Var "x") `shouldBe` (int 1, env, ctx)
    instantiate' (For "x" Typ x) `shouldBe` (x, ("x", x) : env, ("x", Typ) : ctx)

  it "☯ infer" $ do
    let bool = ctr "Bool"
    let (true, false) = (ctr "True", ctr "False")
    let (maybe, a) = (App (ctr "Maybe"), Var "a")
    let (just, nothing) = (App (ctr "Just"), ctr "Nothing")
    let env =
          [ ("Bool", bool),
            ("True", true),
            ("False", false),
            ("Maybe", Lam "a" Typ (maybe a)),
            ("Just", Lam "x" (For "a" Typ a) (just x)),
            ("Nothing", nothing)
          ]
    let ctx =
          [ ("Bool", Typ),
            ("True", bool),
            ("False", bool),
            ("Maybe", For "a" Typ $ Fun a Typ),
            ("Just", For "a" Typ $ Fun a (maybe a)),
            ("Nothing", For "a" Typ $ maybe a)
          ]

    let infer' = infer ops env ctx
    infer' Knd `shouldBe` Right (Knd, env, ctx)
    infer' Typ `shouldBe` Right (Knd, env, ctx)
    infer' intT `shouldBe` Right (Typ, env, ctx)
    infer' (int 1) `shouldBe` Right (intT, env, ctx)
    infer' (ctr "Bool") `shouldBe` Right (Typ, env, ctx)
    infer' (ctr "True") `shouldBe` Right (bool, env, ctx)
    infer' (ctr "False") `shouldBe` Right (bool, env, ctx)
    infer' (ctr "Maybe") `shouldBe` Right (For "a" Typ $ Fun a Typ, env, ctx)
    infer' (ctr "Just") `shouldBe` Right (For "a" Typ $ Fun a (maybe a), env, ctx)
    infer' (ctr "Nothing") `shouldBe` Right (For "a" Typ $ maybe a, env, ctx)
    infer' (Var "Bool") `shouldBe` Right (Typ, env, ctx)
    infer' (Var "True") `shouldBe` Right (bool, env, ctx)
    infer' (Var "False") `shouldBe` Right (bool, env, ctx)
    infer' (Var "x") `shouldBe` Left (UndefinedVar "x")
    infer' (Fun true true) `shouldBe` Right (bool, env, ctx) -- Left "Fun can only be of Typ or Knd, got: Bool Bool"
    infer' (Fun bool bool) `shouldBe` Right (Typ, env, ctx)
    infer' (Fun bool Typ) `shouldBe` Right (Knd, env, ctx)
    infer' (Fun Typ bool) `shouldBe` Right (Typ, env, ctx)
    infer' (Fun Typ Typ) `shouldBe` Right (Knd, env, ctx)
    infer' (Fun Knd Knd) `shouldBe` Right (Knd, env, ctx)
    infer' (For "x" true x) `shouldBe` Right (true, env, ctx)
    infer' (For "x" bool x) `shouldBe` Right (bool, env, ctx)
    infer' (For "x" Typ x) `shouldBe` Right (Typ, env, ctx)
    infer' (For "x" Knd x) `shouldBe` Right (Knd, env, ctx)
    infer' (Lam "x" true x) `shouldBe` Right (Fun true true, env, ctx) -- Left "Fun can only be of Typ or Knd, got: Bool Bool"
    infer' (Lam "x" bool x) `shouldBe` Right (Fun bool bool, env, ctx)
    infer' (Lam "x" Typ x) `shouldBe` Right (Fun Typ Typ, env, ctx)
    infer' (Lam "x" Knd x) `shouldBe` Right (Fun Knd Knd, env, ctx)
    infer' (just true) `shouldBe` Right (maybe bool, ("a", bool) : env, ("a", Typ) : ctx)
    infer' (Case IntT true) `shouldBe` Right (Fun Typ bool, env, ctx)
    infer' (Case (Int 1) true) `shouldBe` Right (Fun intT bool, env, ctx)
    infer' (Case (Ctr "Bool") (int 1)) `shouldBe` Right (Fun Typ intT, env, ctx)
    infer' (Case (Ctr "True") (int 1)) `shouldBe` Right (Fun bool intT, env, ctx)
    infer' (Case (Ctr "Just") (int 1)) `shouldBe` Right (Fun (For "a" Typ $ Fun a (maybe a)) intT, env, ctx)
    -- TODO: infer' Or
    infer' (App true false) `shouldBe` Left (NotAFunction true bool)
    infer' (App (Lam "x" true $ int 0) true) `shouldBe` Right (intT, env, ctx)
    infer' (App (Lam "x" true $ int 0) false) `shouldBe` Left (UnifyError true false)
    infer' (App (Lam "x" bool $ int 0) true) `shouldBe` Right (intT, env, ctx)
    infer' (App (Lam "x" bool $ int 0) false) `shouldBe` Right (intT, env, ctx)
    infer' (App (Lam "x" Typ $ int 0) true) `shouldBe` Left (UnifyError Typ bool)
    infer' (App (Lam "x" Typ $ int 0) bool) `shouldBe` Right (intT, env, ctx)
    -- TODO: infer' Fix
    -- TODO: infer' Op
    True `shouldBe` True

  it "☯ arithmetic" $ do
    let env = []
    let eval' = eval ops env
    eval' (Op "+" [int 1, int 2]) `shouldBe` int 3
    eval' (Op "-" [int 1, int 2]) `shouldBe` int (-1)
    eval' (Op "*" [int 1, int 2]) `shouldBe` int 2

  -- it "☯ Bool" $ do
  --   -- Type Bool = True | False
  --   -- f True = 1
  --   -- f False = 0

  --   let f = Var "f"
  --   let bool = Var "Bool"
  --   let true = Var "True"
  --   let false = Var "False"
  --   let ctx = [("Bool", Typ), ("True", bool), ("False", bool)]
  --   let env =
  --         [ ("f", Case (Ctr "True") (int 1) `Or` Case (Ctr "False") (int 0)),
  --           ("Bool", ctr "Bool"),
  --           ("True", ctr "True"),
  --           ("False", ctr "False")
  --         ]

  --   let infer' = infer ops env ctx
  --   infer' bool `shouldBe` Right Typ
  --   infer' true `shouldBe` Right bool
  --   infer' false `shouldBe` Right bool

  --   let eval' = eval ops env
  --   eval' (App f true) `shouldBe` int 1
  --   eval' (App f false) `shouldBe` int 0
  --   eval' (App f (int 0)) `shouldBe` Err
  --   True `shouldBe` True

  it "☯ factorial" $ do
    -- fact = fix (Nat->Nat) (\(f:Nat->Nat)(n:Nat).ifz n then succ 0 else mul n (f (pred n)))
    -- fact (succ (succ (succ 0)))

    -- prim "fix" =
    --   ( 2,
    --     Pi "A" (S "*") (Pi "_" (Pi "_" (V "A") (V "A")) (V "A")),
    --     \env [x, y] -> reduce env $ App y $ Prim "fix" [x, y]
    --   )
    True `shouldBe` True
