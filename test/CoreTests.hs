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
  -- let (aT, bT) = (Var "aT", Var "bT")
  let boolT = CtrT ("Bool", "True") NilT `OrT` CtrT ("Bool", "False") NilT

  let eqOp (And (Int a) (Int b)) | a == b = Just (Ctr ("Bool", "True") Nil)
      eqOp (And (Int _) (Int _)) = Just (Ctr ("Bool", "False") Nil)
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

  let ops =
        [ ("==", eqOp),
          ("+", addOp),
          ("-", subOp),
          ("*", mulOp)
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
    let env =
          [ ("x", Int 1),
            ("y", Var "y"),
            ("f", Lam "x" (Var "x"))
          ]
    reduce ops env Nil `shouldBe` Nil
    reduce ops env (Int 1) `shouldBe` Int 1
    reduce ops env (Num 1.1) `shouldBe` Num 1.1
    reduce ops env (Ctr ("T", "A") Nil) `shouldBe` Ctr ("T", "A") (Let env Nil)
    reduce ops env (Var "x") `shouldBe` Int 1
    reduce ops env (Var "y") `shouldBe` y
    reduce ops env (Var "z") `shouldBe` Err (UndefinedVar "z")
    -- Let
    reduce ops env (Lam "x" x) `shouldBe` Lam "x" (Let env x)
    reduce ops env (App f x) `shouldBe` Int 1
    reduce ops env (App (Lam "x" x) x) `shouldBe` Int 1
    reduce ops env (App (Case ("T", "A") "x" x) (Ctr ("T", "A") Nil)) `shouldBe` Nil
    reduce ops env (App (Case ("T", "A") "x" x) (Ctr ("T", "B") Nil)) `shouldBe` Err Fail
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
    reduce ops env (eq (Int 1) (Int 1)) `shouldBe` Ctr ("Bool", "True") Nil
    reduce ops env (eq (Int 1) (Int 2)) `shouldBe` Ctr ("Bool", "False") Nil
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
    let ctrA a = Ctr ("T", "A") a
    let ctrB a = Ctr ("T", "B") a
    let ctrTA a = CtrT ("T", "A") a
    let ctrTB a = CtrT ("T", "B") a
    let ctx =
          [ ("==", ForAll ["a"] (FunT (AndT a a) boolT)),
            ("+", ForAll ["a"] (FunT (AndT a a) a)),
            ("T", ForAll ["a"] (ctrTA NilT `OrT` ctrTB a)),
            ("y", ForAll [] NumT)
          ]
    let env =
          [ ("x", Int 1),
            ("y", Num 1.1),
            ("z", Var "z"),
            ("f", Lam "x" (Var "x"))
          ]

    infer' ctx env Nil `shouldBe` Right NilT
    infer' ctx env (Int 1) `shouldBe` Right IntT
    infer' ctx env (Num 1.1) `shouldBe` Right NumT
    infer' ctx env (Ctr ("X", "A") Nil) `shouldBe` Left (UndefinedType "X")
    infer' ctx env (Ctr ("T", "X") Nil) `shouldBe` Left (UndefinedAlt ("T", "X"))
    infer' ctx env (Ctr ("T", "A") Nil) `shouldBe` Right (ctrTA NilT `OrT` ctrTB a)
    infer' ctx env (Ctr ("T", "B") Nil) `shouldBe` Right (ctrTA NilT `OrT` ctrTB NilT)
    infer' ctx env (Ctr ("T", "B") z) `shouldBe` Right (ctrTA NilT `OrT` ctrTB zT)
    infer' ctx env (Var "x") `shouldBe` Right IntT
    infer' ctx env (Var "y") `shouldBe` Right NumT
    infer' ctx env (Var "z") `shouldBe` Right zT
    infer' ctx env (Var "w") `shouldBe` Left (RuntimeError $ UndefinedVar "w")
    infer' ctx env (Let [("x", Nil)] (Var "x")) `shouldBe` Right IntT
    infer' ctx env (Let [("w", Nil)] (Var "w")) `shouldBe` Right NilT
    infer' ctx env (Lam "x" x) `shouldBe` Right (FunT xT xT)
    infer' ctx env (Lam "x" Nil) `shouldBe` Right (FunT xT NilT)
    infer' ctx env (App Nil x) `shouldBe` Left (TypeMismatch NilT (FunT IntT (VarT "_app")))
    infer' ctx env (App f Nil) `shouldBe` Right NilT
    infer' ctx env (And x y) `shouldBe` Right (AndT IntT NumT)
    infer' ctx env (Or x y) `shouldBe` Left (TypeMismatch IntT NumT)
    infer' ctx env (Or x x) `shouldBe` Right IntT
    infer' ctx env (Or (ctrA Nil) (ctrB (Int 1))) `shouldBe` Right (OrT (ctrTA NilT) (ctrTB IntT))
    -- TODO: all cases of Or
    infer' ctx env (Fst Nil) `shouldBe` Left (RuntimeError $ NoFstOf Nil)
    infer' ctx env (Fst (And x y)) `shouldBe` Right IntT
    -- TODO: Fst (something with OrT)
    infer' ctx env (Snd Nil) `shouldBe` Left (RuntimeError $ NoSndOf Nil)
    infer' ctx env (Snd (And x y)) `shouldBe` Right NumT
    -- TODO: Snd (something with OrT)
    infer' ctx env (If Nil x) `shouldBe` Right IntT
    infer' ctx env (Case ("T", "A") "x" (Int 1)) `shouldBe` Right (FunT (ctrTA NilT `OrT` ctrTB a) IntT)
    infer' ctx env (Case ("T", "A") "x" (Var "x")) `shouldBe` Right (FunT (ctrTA NilT `OrT` ctrTB a) NilT)
    infer' ctx env (Case ("T", "B") "x" (Int 1)) `shouldBe` Right (FunT (ctrTA NilT `OrT` ctrTB a) IntT)
    infer' ctx env (Case ("T", "B") "x" (Var "x")) `shouldBe` Right (FunT (ctrTA NilT `OrT` ctrTB a) a)
    infer' ctx env (Fix "f" Nil) `shouldBe` Right (VarT "fT")
    infer' ctx env (Fix "f" f) `shouldBe` Right (VarT "fT")
    infer' ctx env (Fix "f" (App f x)) `shouldBe` Right (FunT IntT (VarT "_app"))
    infer' ctx env (Op "==" Nil) `shouldBe` Left (TypeMismatch NilT (AndT a a))
    infer' ctx env (Op "==" (And x x)) `shouldBe` Right boolT
    infer' ctx env (Op "+" (And x x)) `shouldBe` Right IntT
    infer' ctx env (Err Fail) `shouldBe` Left (RuntimeError Fail)

  it "☯ factorial" $ do
    -- f 0 = 1
    -- f n = n * f (n - 1)
    --
    -- f = \n -> if n == 0 then 1 else n * f (n - 1)

    let (i0, i1) = (Int 0, Int 1)
    let (f, n) = (Var "f", Var "n")
    let ctx =
          [ ("==", ForAll ["a"] (FunT (AndT a a) boolT)),
            ("*", ForAll ["a"] (FunT (AndT a a) a)),
            ("-", ForAll ["a"] (FunT (AndT a a) a)),
            ("Bool", ForAll [] boolT)
          ]
    let env =
          [ ("f", Fix "f" $ Lam "n" $ if' ("Bool", "True") (eq n i0) i1 (n `mul` App f (n `sub` i1)))
          ]

    let infer' ctx env a = fmap fst (infer ctx env a)
    infer' ctx env f `shouldBe` Right (FunT IntT IntT)
    infer' ctx env (App f Nil) `shouldBe` Left (TypeMismatch IntT NilT)
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
    let (true, false) = (Var "True", Var "False")
    let ctx = [("Bool", ForAll [] boolT)]
    let env =
          [ ("True", Ctr ("Bool", "True") Nil),
            ("False", Ctr ("Bool", "False") Nil),
            ("f", Case ("Bool", "True") "x" i1 `Or` Lam "" i0)
          ]

    let infer' ctx env a = fmap fst (infer ctx env a)
    infer' ctx env true `shouldBe` Right boolT
    infer' ctx env false `shouldBe` Right boolT
    infer' ctx env f `shouldBe` Right (FunT boolT IntT)
    infer' ctx env (App f Nil) `shouldBe` Left (TypeMismatch (CtrT ("Bool", "True") NilT) NilT)
    infer' ctx env (App f true) `shouldBe` Right IntT
    reduce ops env (App f true) `shouldBe` Int 1
    reduce ops env (App f false) `shouldBe` Int 0

  it "☯ Maybe" $ do
    -- type Maybe a = Just a | Nothing
    -- f (Just x) = x
    -- f Nothing = 0
    --
    -- type Maybe a = #Maybe.Just | #Maybe.Nothing
    -- Just = \x -> #Maybe.Just x
    -- Nothing = #Maybe.Nothing
    --
    -- f = @Case #Maybe.Just x -> x | \_ -> 0

    let i0 = Int 0
    let maybeT a = CtrT ("Maybe", "Just") a `OrT` CtrT ("Maybe", "Nothing") NilT
    let (just, nothing) = (App (Var "Just"), Var "Nothing")
    let ctx = [("Maybe", ForAll ["a"] (maybeT (VarT "a")))]
    let env =
          [ ("Just", Lam "a" (Ctr ("Maybe", "Just") (Var "a"))),
            ("Nothing", Ctr ("Maybe", "Nothing") Nil),
            ("f", Case ("Maybe", "Just") "x" x `Or` Lam "" i0)
          ]

    let infer' ctx env a = fmap fst (infer ctx env a)
    infer' ctx env nothing `shouldBe` Right (maybeT (VarT "a"))
    infer' ctx env (Var "Just") `shouldBe` Right (FunT (VarT "aT") (maybeT (VarT "aT")))
    infer' ctx env (just Nil) `shouldBe` Right (maybeT NilT)
    infer' ctx env f `shouldBe` Right (FunT (maybeT IntT) IntT)
    infer' ctx env (App f Nil) `shouldBe` Left (TypeMismatch (CtrT ("Maybe", "Just") IntT) NilT)
    infer' ctx env (App f nothing) `shouldBe` Right IntT
    reduce ops env (App f nothing) `shouldBe` Int 0
    reduce ops env (App f (just (Int 1))) `shouldBe` Int 1
    reduce ops env (App f (just (Int 2))) `shouldBe` Int 2

  it "☯ Vec" $ do
    -- type Vec n a = Cons a (Vec n a) : Vec (n+1) a | Nil : Vec 0 a
    -- sum (Cons x xs) = x + sum xs
    -- sum Nil = 0
    --
    -- type Vec n a = #Vec.Cons | #Vec.Nil
    -- Cons = \x xs -> #Vec.Cons (x, xs)
    -- Nil = #Vec.Cons
    --
    -- f = @Case Vec.Cons x xs -> x + sum xs | \_ -> 0

    -- let i0 = Int 0
    -- let (n, a) = (VarT "n", VarT "a")
    -- let (v, x, xs) = (Var "v", Var "x", Var "xs")
    -- let sum = Var "sum"
    -- let (consT, nilT) = (\n a -> CtrT ("Vec", "Cons") (AndT n a), CtrT ("Vec", "Nil") NilT)
    -- let vecT n a = consT n a `OrT` nilT
    -- let (cons, nil) = (App . App (Var "Cons"), Var "Nil")
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
