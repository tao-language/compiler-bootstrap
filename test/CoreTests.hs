module CoreTests where

import Core
import Flow ((|>))
import Test.Hspec

coreTests :: SpecWith ()
coreTests = describe "--==☯ Core language ☯==--" $ do
  let k = Var "k"
  let (f, g) = (Var "f", Var "g")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let a = VarT "a"
  let (xT, yT, zT) = (VarT "xT", VarT "yT", VarT "zT")

  let true = Ctr ("Bool", "True") []
  let false = Ctr ("Bool", "False") []
  let boolT = SumT [("True", (0, TypT "Bool" [])), ("False", (0, TypT "Bool" []))]

  let eqOp (And (Int a) (Int b)) = Just (if a == b then true else false)
      eqOp _ = Nothing
  let addOp (And (Int a) (Int b)) = Just (Int (a + b))
      addOp _ = Nothing
  let subOp (And (Int a) (Int b)) = Just (Int (a - b))
      subOp _ = Nothing
  let mulOp (And (Int a) (Int b)) = Just (Int (a * b))
      mulOp _ = Nothing

  let eq a b = Op "==" (And a b)
  let add a b = Op "+" (And a b)
  let sub a b = Op "-" (And a b)
  let mul a b = Op "*" (And a b)

  let ops :: Ops
      ops =
        [ ("==", eqOp),
          ("+", addOp),
          ("-", subOp),
          ("*", mulOp)
        ]

  let ctxOps :: Context
      ctxOps =
        [ ("==", ForAll ["a"] (FunT (AndT a a) (TypT "Bool" []))),
          ("+", ForAll ["a"] (FunT (AndT a a) a)),
          ("-", ForAll ["a"] (FunT (AndT a a) a)),
          ("*", ForAll ["a"] (FunT (AndT a a) a))
        ]

  it "☯ lam" $ do
    lam [] x `shouldBe` x
    lam ["x"] y `shouldBe` Lam "x" y
    lam ["x", "y"] z `shouldBe` Lam "x" (Lam "y" z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ or'" $ do
    or' [] `shouldBe` Nil
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

  it "☯ unify" $ do
    let env = [("x", Var "x"), ("y", Var "y"), ("a", Var "a")]
    -- unify env (Err "e") (Err "e") `shouldBe` Just env
    -- unify env (Err "e") (Err "f") `shouldBe` Nothing
    -- unify env (Err "e") Nil `shouldBe` Nothing
    -- unify env Nil Nil `shouldBe` Just env
    -- unify env (Int 1) (Int 1) `shouldBe` Just env
    -- unify env (Int 1) (Int 2) `shouldBe` Nothing
    -- unify env (Num 1.1) (Num 1.1) `shouldBe` Just env
    -- unify env (Num 1.1) (Num 2.2) `shouldBe` Nothing
    -- unify env (Ctr "T" "A") (Ctr "X" "A") `shouldBe` Nothing
    -- unify env (Ctr "T" "A") (Ctr "T" "X") `shouldBe` Nothing
    -- unify env (Ctr "T" "A") (Ctr "T" "A") `shouldBe` Just env
    -- unify env (Var "x") (Var "y") `shouldBe` Just (set ("x", y) env)
    -- unify env (Var "x") Nil `shouldBe` Just (set ("x", Nil) env)
    -- unify env Nil (Var "x") `shouldBe` Just (set ("x", Nil) env)
    -- unify env (For "x" x) Nil `shouldBe` Just (("x", Nil) : env)
    -- unify env (For "x" TypT) Nil `shouldBe` Nothing
    -- unify env Nil (For "x" x) `shouldBe` Just (("x", Nil) : env)
    -- unify env Nil (For "x" TypT) `shouldBe` Nothing
    -- unify env (App x Nil) (App (Err "e") y) `shouldBe` Just (set ("x", Err "e") env |> set ("y", Nil))
    -- unify env (App (Err "e") y) (App x Nil) `shouldBe` Just (set ("x", Err "e") env |> set ("y", Nil))
    -- unify env (Or x (Err "e")) Nil `shouldBe` Just (set ("x", Nil) env)
    -- unify env (Or (Err "e") x) Nil `shouldBe` Just (set ("x", Nil) env)
    -- unify env Nil (Or x (Err "e")) `shouldBe` Just (set ("x", Nil) env)
    -- unify env Nil (Or (Err "e") x) `shouldBe` Just (set ("x", Nil) env)
    -- unify env (Ann x IntT) (Ann y a) `shouldBe` Just (set ("x", y) env |> set ("a", IntT))
    -- unify env (Ann x IntT) Nil `shouldBe` Just (set ("x", Nil) env)
    -- unify env Nil (Ann x IntT) `shouldBe` Just (set ("x", Nil) env)
    True `shouldBe` True

  it "☯ newName" $ do
    newName [] "x" `shouldBe` "x"
    newName ["x"] "x" `shouldBe` "x'"

  it "☯ occurs" $ do
    -- occurs "x" Nil `shouldBe` False
    -- occurs "x" (Int 1) `shouldBe` False
    -- occurs "x" (Num 1.1) `shouldBe` False
    -- occurs "x" (Ctr "x" "x") `shouldBe` False
    -- occurs "x" (Var "x") `shouldBe` True
    -- occurs "x" (Var "y") `shouldBe` False
    -- -- TODO: Let
    -- occurs "x" (Lam "x" x) `shouldBe` False
    -- occurs "x" (Lam "y" x) `shouldBe` True
    -- occurs "x" (App x y) `shouldBe` True
    -- occurs "x" (App y x) `shouldBe` True
    -- occurs "x" (App y y) `shouldBe` False
    -- occurs "x" (And x y) `shouldBe` True
    -- occurs "x" (And y x) `shouldBe` True
    -- occurs "x" (And y y) `shouldBe` False
    -- occurs "x" (Or x y) `shouldBe` True
    -- occurs "x" (Or y x) `shouldBe` True
    -- occurs "x" (Or y y) `shouldBe` False
    -- occurs "x" (Fst x) `shouldBe` True
    -- occurs "x" (Snd x) `shouldBe` True
    -- occurs "x" (Op2 Add x y) `shouldBe` True
    -- occurs "x" (Op2 Add y x) `shouldBe` True
    -- occurs "x" (Op2 Add y y) `shouldBe` False
    -- occurs "x" (Err Fail) `shouldBe` False
    occurs "x" NilT `shouldBe` False

  it "☯ reduce" $ do
    let ctrA = Ctr ("T", "A") []
    let ctrB x = Ctr ("T", "B") [x]
    let env =
          [ ("x", Int 1),
            ("y", Var "y"),
            ("f", Lam "x" (Var "x"))
          ]

    reduce ops env Nil `shouldBe` Nil
    reduce ops env (Int 1) `shouldBe` Int 1
    reduce ops env (Num 1.1) `shouldBe` Num 1.1
    reduce ops env (Ctr ("T", "A") []) `shouldBe` ctrA
    reduce ops env (Ctr ("T", "B") [Nil]) `shouldBe` ctrB (Let env Nil)
    reduce ops env (Var "x") `shouldBe` Int 1
    reduce ops env (Var "y") `shouldBe` y
    reduce ops env (Var "z") `shouldBe` Err (UndefinedVar "z")
    -- Let
    reduce ops env (Lam "x" x) `shouldBe` Lam "x" (Let env x)
    reduce ops env (App f x) `shouldBe` Int 1
    reduce ops env (App (Lam "x" x) x) `shouldBe` Int 1
    reduce ops env (App (Case ("T", "A") [] x) ctrA) `shouldBe` Int 1
    reduce ops env (App (Case ("T", "A") [] x) (ctrB Nil)) `shouldBe` Err Fail
    reduce ops env (App (Case ("T", "B") ["x"] x) (ctrB Nil)) `shouldBe` Nil
    reduce ops env (App (Err Fail) x) `shouldBe` Err Fail
    reduce ops env (And x y) `shouldBe` And (Let env x) (Let env y)
    reduce ops env (Or x y) `shouldBe` Or (Let env x) (Let env y)
    reduce ops env (Fst Nil) `shouldBe` Err (NoFstOf Nil)
    reduce ops env (Fst y) `shouldBe` Fst y
    reduce ops env (Fst (And x y)) `shouldBe` Int 1
    reduce ops env (Fst (Or x y)) `shouldBe` Int 1
    reduce ops env (Snd Nil) `shouldBe` Err (NoSndOf Nil)
    reduce ops env (Snd y) `shouldBe` Snd y
    reduce ops env (Snd (And y x)) `shouldBe` Int 1
    reduce ops env (Snd (Or y x)) `shouldBe` Int 1
    reduce ops env (eq (Int 1) (Int 1)) `shouldBe` true
    reduce ops env (eq (Int 1) (Int 2)) `shouldBe` false
    reduce ops env (eq x y) `shouldBe` eq (Int 1) y
    reduce ops env (add (Int 1) (Int 1)) `shouldBe` Int 2
    reduce ops env (add x y) `shouldBe` add (Int 1) y
    reduce ops env (sub (Int 1) (Int 1)) `shouldBe` Int 0
    reduce ops env (sub x y) `shouldBe` sub (Int 1) y
    reduce ops env (mul (Int 1) (Int 1)) `shouldBe` Int 1
    reduce ops env (mul x y) `shouldBe` mul (Int 1) y
    reduce ops env (Err Fail) `shouldBe` Err Fail

  it "☯ infer" $ do
    -- TODO: check output ctx
    let infer' ctx env a = fmap fst (infer ctx env a)
    let ctx =
          ("T", ForAll ["a"] (SumT [("A", (0, TypT "T" [a])), ("B", (1, FunT a (TypT "T" [a])))])) :
          ("y", ForAll [] NumT) :
          ctxOps
    let env =
          [ ("x", Int 1),
            ("y", Num 1.1),
            ("z", Var "z"),
            ("f", Lam "x" (Var "x"))
          ]

    infer' ctx env Nil `shouldBe` Right NilT
    infer' ctx env (Int 1) `shouldBe` Right IntT
    infer' ctx env (Num 1.1) `shouldBe` Right NumT
    infer' ctx env (Var "x") `shouldBe` Right IntT
    infer' ctx env (Var "y") `shouldBe` Right NumT
    infer' ctx env (Var "z") `shouldBe` Right zT
    infer' ctx env (Var "w") `shouldBe` Left (RuntimeError $ UndefinedVar "w")
    infer' ctx env (Let [("x", Nil)] (Var "x")) `shouldBe` Right IntT
    infer' ctx env (Let [("w", Nil)] (Var "w")) `shouldBe` Right NilT
    infer' ctx env (Ctr ("X", "A") []) `shouldBe` Left (UndefinedType "X")
    infer' ctx env (Ctr ("T", "X") []) `shouldBe` Left (UndefinedAlt ("T", "X"))
    infer' ctx env (Ctr ("T", "A") []) `shouldBe` Right (TypT "T" [a])
    infer' ctx env (Ctr ("T", "A") [Nil]) `shouldBe` Left (ArgsMismatch 0 [Nil])
    infer' ctx env (Ctr ("T", "B") [Nil]) `shouldBe` Right (TypT "T" [NilT])
    infer' ctx env (Ctr ("T", "B") []) `shouldBe` Left (ArgsMismatch 1 [])
    infer' ctx env (Ctr ("T", "B") [z]) `shouldBe` Right (TypT "T" [zT])
    infer' ctx env (Lam "x" x) `shouldBe` Right (FunT xT xT)
    infer' ctx env (Lam "x" Nil) `shouldBe` Right (FunT xT NilT)
    infer' ctx env (Case ("T", "A") [] x) `shouldBe` Right (FunT (TypT "T" [a]) IntT)
    infer' ctx env (Case ("T", "A") ["x"] x) `shouldBe` Left (ArgsMismatch 0 [x])
    infer' ctx env (Case ("T", "B") [] x) `shouldBe` Left (ArgsMismatch 1 [])
    infer' ctx env (Case ("T", "B") ["x"] x) `shouldBe` Right (FunT (TypT "T" [a]) a)
    infer' ctx env (App Nil x) `shouldBe` Left (TypeMismatch (FunT IntT (VarT "_app")) NilT)
    infer' ctx env (App f Nil) `shouldBe` Right NilT
    infer' ctx env (And x y) `shouldBe` Right (AndT IntT NumT)
    infer' ctx env (Or x y) `shouldBe` Left (TypeMismatch IntT NumT)
    infer' ctx env (Or x x) `shouldBe` Right IntT
    -- infer' ctx env (Or ctrA (ctrB (Int 1))) `shouldBe` Right (ctrType IntT)
    -- TODO: all cases of Or
    infer' ctx env (Fst Nil) `shouldBe` Left (RuntimeError $ NoFstOf Nil)
    infer' ctx env (Fst (And x y)) `shouldBe` Right IntT
    -- TODO: Fst (something with OrT)
    infer' ctx env (Snd Nil) `shouldBe` Left (RuntimeError $ NoSndOf Nil)
    infer' ctx env (Snd (And x y)) `shouldBe` Right NumT
    -- TODO: Snd (something with OrT)
    infer' ctx env (Fix "f" Nil) `shouldBe` Right (VarT "fT")
    infer' ctx env (Fix "f" f) `shouldBe` Right (VarT "fT")
    infer' ctx env (Fix "f" (App f x)) `shouldBe` Right (FunT IntT (VarT "_app"))
    infer' ctx env (Op "==" Nil) `shouldBe` Left (TypeMismatch NilT (AndT a a))
    infer' ctx env (Op "==" (And x x)) `shouldBe` Right (TypT "Bool" [])
    infer' ctx env (Op "+" (And x x)) `shouldBe` Right IntT
    infer' ctx env (Err Fail) `shouldBe` Left (RuntimeError Fail)

  it "☯ factorial" $ do
    -- f 0 = 1
    -- f n = n * f (n - 1)
    --
    -- f n = if n == 0 then 1 else n * f (n - 1)

    let (i0, i1) = (Int 0, Int 1)
    let (f, n) = (Var "f", Var "n")
    let ctx =
          ("Bool", ForAll [] boolT) : ctxOps
    let env =
          [ ("f", Fix "f" $ Lam "n" $ if' ("Bool", "True") (eq n i0) i1 (n `mul` App f (n `sub` i1)))
          ]

    let infer' ctx env a = fmap fst (infer ctx env a)
    infer' ctx env f `shouldBe` Right (FunT IntT IntT)
    infer' ctx env (App f Nil) `shouldBe` Left (TypeMismatch NilT IntT)
    infer' ctx env (App f (Int 0)) `shouldBe` Right IntT
    reduce ops env (App f (Int 0)) `shouldBe` Int 1
    reduce ops env (App f (Int 1)) `shouldBe` Int 1
    reduce ops env (App f (Int 2)) `shouldBe` Int 2
    reduce ops env (App f (Int 3)) `shouldBe` Int 6
    reduce ops env (App f (Int 4)) `shouldBe` Int 24
    reduce ops env (App f (Int 5)) `shouldBe` Int 120

  it "☯ Bool" $ do
    -- type Bool = True | False
    -- f True = 1
    -- f False = 0
    --
    -- True = #Bool.True ()
    -- False = #Bool.False ()
    -- f = @Case #Bool.True _ -> 1 | \_ -> 0

    let (i0, i1) = (Int 0, Int 1)
    let ctx = [("Bool", ForAll [] boolT)]
    let env =
          [ ("True", true),
            ("False", false),
            ("f", Case ("Bool", "True") [] i1 `Or` Lam "" i0)
          ]

    let infer' ctx env a = fmap fst (infer ctx env a)
    infer' ctx env (Var "True") `shouldBe` Right (TypT "Bool" [])
    infer' ctx env (Var "False") `shouldBe` Right (TypT "Bool" [])
    infer' ctx env (Var "f") `shouldBe` Right (FunT (TypT "Bool" []) IntT)
    infer' ctx env (App f Nil) `shouldBe` Left (TypeMismatch NilT (TypT "Bool" []))
    infer' ctx env (App f true) `shouldBe` Right IntT
    reduce ops env (App f true) `shouldBe` Int 1
    reduce ops env (App f false) `shouldBe` Int 0

  it "☯ Maybe" $ do
    -- type Maybe a = Just a | Nothing
    -- f (Just x) = x
    -- f Nothing = 0
    --
    -- type Maybe a = #Maybe.Just a | #Maybe.Nothing
    -- Just x = #Maybe.Just x
    -- Nothing = #Maybe.Nothing
    --
    -- f = @Case #Maybe.Just x -> x | \_ -> 0

    let i0 = Int 0
    let just x = Ctr ("Maybe", "Just") [x]
    let nothing = Ctr ("Maybe", "Nothing") []
    let ctx = [("Maybe", ForAll ["a"] $ SumT [("Just", (1, FunT a (TypT "Maybe" [a]))), ("Nothing", (0, TypT "Maybe" [a]))])]
    let env =
          [ ("Just", Lam "x" (just x)),
            ("Nothing", nothing),
            ("f", Case ("Maybe", "Just") ["x"] x `Or` Lam "" i0)
          ]

    let infer' ctx env a = fmap fst (infer ctx env a)
    infer' ctx env nothing `shouldBe` Right (TypT "Maybe" [a])
    infer' ctx env (Var "Just") `shouldBe` Right (FunT xT (TypT "Maybe" [xT]))
    infer' ctx env (just Nil) `shouldBe` Right (TypT "Maybe" [NilT])
    infer' ctx env f `shouldBe` Right (FunT (TypT "Maybe" [IntT]) IntT)
    infer' ctx env (App f Nil) `shouldBe` Left (TypeMismatch NilT (TypT "Maybe" [IntT]))
    infer' ctx env (App f nothing) `shouldBe` Right IntT
    reduce ops env (App f nothing) `shouldBe` Int 0
    reduce ops env (App f (just (Int 1))) `shouldBe` Int 1
    reduce ops env (App f (just (Int 2))) `shouldBe` Int 2

  it "☯ Nat" $ do
    -- type Nat n = Z : Nat 0 | S : Nat n -> Nat (n + 1)
    --
    -- Z : @ForAll n. Nat 0
    -- Z = #Nat.Z []
    --
    -- S : @ForAll n. Nat n -> Nat (n + 1)
    -- S x = #Nat.S [x]
    --
    -- infer Z =
    True `shouldBe` True

  it "☯ Vec" $ do
    -- type Vec n a = Cons a (Vec n a) : Vec (n+1) a | Nil : Vec 0 a
    -- sum (Cons x xs) = x + sum xs
    -- sum Nil = 0
    --
    -- type Vec n a = #Vec.Cons a (Vec n a) | #Vec.Nil
    -- Cons = \x xs -> #Vec.Cons (x, xs)
    -- Nil = #Vec.Cons
    --
    -- f = @Case Vec.Cons x xs -> x + sum xs | \_ -> 0

    let i0 = Int 0
    let (n, a) = (VarT "n", VarT "a")
    let (v, x, xs) = (Var "v", Var "x", Var "xs")
    let sum = Var "sum"
    -- let consT = CtrT ("Vec", "Cons") [a, vecT n a] (vecT (n + 1) a)
    -- let consT = CtrT ("Vec", "Cons") [a, vecT n a] (vecT (n + 1) a)
    -- let nilT = CtrT ("Vec", "Nil") [] (vecT 0 a)
    -- let vecT n a = consT n a `OrT` nilT
    let cons x xs = Ctr ("Vec", "Cons") [x, xs]
    let nil = Ctr ("Vec", "Nil") []
    -- let ctx = [("Vec", ForAll ["n", "a"] (vecT n a))]
    -- let env =
    --       [ ("Cons", lam ["x", "xs"] (Ctr ("Vec", "Cons") (And x xs))),
    --         ("Nil", Ctr ("Vec", "Nil") Nil),
    --         ("f", Case ("Vec", "Cons") "v" (Let [("x", Fst v), ("xs", Snd v)] (x `add` App sum xs)) `Or` Lam "" i0)
    --       ]

    let infer' ctx env a = fmap fst (infer ctx env a)
    -- infer' ctx env nil `shouldBe` Right (vecT (E $ Int 0) (T a))
    -- infer' ctx env (Var "Just") `shouldBe` Right (FunT (VarT "aT") (maybeT (VarT "aT")))
    -- infer' ctx env (just Nil) `shouldBe` Right (maybeT NilT)
    -- infer' ctx env f `shouldBe` Right (FunT (maybeT IntT) IntT)
    -- infer' ctx env (App f Nil) `shouldBe` Left (TypeMismatch (CtrT ("Maybe", "Just") IntT) NilT)
    -- infer' ctx env (App f nothing) `shouldBe` Right IntT
    -- reduce ops env (App f nothing) `shouldBe` Int 0
    -- reduce ops env (App f (just (Int 1))) `shouldBe` Int 1
    -- reduce ops env (App f (just (Int 2))) `shouldBe` Int 2
    True `shouldBe` True
