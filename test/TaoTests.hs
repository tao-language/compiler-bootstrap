module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

taoTests :: SpecWith ()
taoTests = describe "--== Tao representation ==--" $ do
  let (a, b) = (Var "a", Var "b")
  let (f, g) = (Var "f", Var "g")
  let (p, q) = (Var "p", Var "q")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PAs PAny "x", PAs PAny "y", PAs PAny "z")
  let (xT, yT) = (Var "xT", Var "yT")
  let neverT = SumT "Never" []
  let unitT = SumT "Unit" [("A", ([], Var "Unit"))]
  let monadT = SumT "Monad" [("M", (["x"], FunT a (App (Var "Monad") a)))]
  let prelude =
        [ ("Never", neverT),
          ("Unit", unitT),
          ("A", Ctr "Unit" "A"),
          ("Bool", boolTDef),
          ("True", true),
          ("False", false),
          ("Monad", Lam "a" monadT),
          ("M", Ctr "Monad" "M")
        ]

  it "☯ forT" $ do
    forT [] x `shouldBe` x
    forT ["x"] y `shouldBe` ForT "x" y
    forT ["x", "y"] z `shouldBe` ForT "x" (ForT "y" z)

  it "☯ funT" $ do
    funT [] x `shouldBe` x
    funT [x] y `shouldBe` FunT x y
    funT [x, y] z `shouldBe` FunT x (FunT y z)

  it "☯ lam" $ do
    lam [] x `shouldBe` x
    lam ["x"] y `shouldBe` Lam "x" y
    lam ["x", "y"] z `shouldBe` Lam "x" (Lam "y" z)

  it "☯ asLam" $ do
    asLam x `shouldBe` ([], x)
    asLam (Lam "x" y) `shouldBe` (["x"], y)
    asLam (Lam "x" (Lam "y" z)) `shouldBe` (["x", "y"], z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ asApp" $ do
    asApp x `shouldBe` (x, [])
    asApp (App x y) `shouldBe` (x, [y])
    asApp (App (App x y) z) `shouldBe` (x, [y, z])

  it "☯ built-in operators" $ do
    add x y `shouldBe` App (App (Op Add) x) y
    sub x y `shouldBe` App (App (Op Sub) x) y
    mul x y `shouldBe` App (App (Op Mul) x) y
    eq x y `shouldBe` App (App (Op Eq) x) y

  it "☯ readNameIdx" $ do
    readNameIdx "" "" `shouldBe` Nothing
    readNameIdx "" "x" `shouldBe` Nothing
    readNameIdx "" "42" `shouldBe` Just 42
    readNameIdx "x" "x42" `shouldBe` Just 42
    readNameIdx "x" "y42" `shouldBe` Nothing

  it "☯ findNameIdx" $ do
    findNameIdx [] "x" `shouldBe` Nothing
    findNameIdx ["x"] "x" `shouldBe` Just 0
    findNameIdx ["x1"] "x" `shouldBe` Just 1
    findNameIdx ["x", "x1"] "x" `shouldBe` Just 1
    findNameIdx ["x1", "x"] "x" `shouldBe` Just 1
    findNameIdx ["x1", "x2"] "x" `shouldBe` Just 2
    findNameIdx ["x2", "x1"] "x" `shouldBe` Just 2

  it "☯ newName" $ do
    newName [] "x" `shouldBe` "x"
    newName ["x"] "x" `shouldBe` "x1"
    newName ["x", "x1"] "x" `shouldBe` "x2"

  it "☯ substitute" $ do
    substitute "x" y x `shouldBe` y
    substitute "x" y z `shouldBe` z
    substitute "x" y (FunT x x) `shouldBe` FunT y y
    substitute "x" y (Lam "x" x) `shouldBe` Lam "x" x
    substitute "x" y (Lam "z" x) `shouldBe` Lam "z" y
    substitute "x" y (App x x) `shouldBe` App y y

  it "☯ instantiate" $ do
    let a1 = Var "a1"
    instantiate [] IntT `shouldBe` (IntT, [])
    instantiate [] (ForT "a" a) `shouldBe` (a, [("a", a)])
    instantiate [("a", IntT)] (ForT "a" a) `shouldBe` (a1, [("a1", a1), ("a", IntT)])
    instantiate [] (forT ["a", "b"] (FunT a b)) `shouldBe` (FunT a b, [("b", b), ("a", a)])

  it "☯ unify" $ do
    let env = [("x", Int 1), ("y", y)]
    unify env TypT TypT `shouldBe` Right env
    unify env IntT IntT `shouldBe` Right env
    unify env (Int 1) (Int 1) `shouldBe` Right env
    unify env (Int 1) (Int 2) `shouldBe` Left (TypeMismatch (Int 1) (Int 2))
    unify env (Var "y") (Var "y") `shouldBe` Right env
    unify env (Var "x") (Int 1) `shouldBe` Right env
    unify env (Var "x") (Int 2) `shouldBe` Left (TypeMismatch (Int 1) (Int 2))
    unify env (Var "z") (Int 1) `shouldBe` Right (("z", Int 1) : env)
    unify env (Int 1) (Var "x") `shouldBe` Right env
    unify env (Int 2) (Var "x") `shouldBe` Left (TypeMismatch (Int 2) (Int 1))
    unify env (Int 1) (Var "z") `shouldBe` Right (("z", Int 1) : env)
    unify env (App z x) (App y x) `shouldBe` Right (("z", y) : env)
    unify env (App y x) (App y z) `shouldBe` Right (("z", Int 1) : env)
    unify env (FunT z x) (FunT y x) `shouldBe` Right (("z", y) : env)
    unify env (FunT y x) (FunT y z) `shouldBe` Right (("z", Int 1) : env)

  it "☯ infer" $ do
    let env =
          ("x", Int 1) :
          ("y", y) :
          ("f", Ann f (ForT "a" $ funT [IntT, a] TypT)) :
          ("g", Lam "x" (Ann (App g (Int 1)) TypT)) :
          ("p", Rec [("y", Int 2), ("x", Int 1)]) :
          ("q", Ann q (RecT [("y", IntT), ("x", IntT)])) :
          prelude

    let infer' env expr = fmap fst (infer env expr)
    infer env Err `shouldBe` Right (Err, env)
    infer env TypT `shouldBe` Right (TypT, env)
    infer env IntT `shouldBe` Right (TypT, env)
    infer env (Int 1) `shouldBe` Right (IntT, env)
    infer env (TupT [IntT]) `shouldBe` Right (TypT, env)
    infer env (Tup [Int 1]) `shouldBe` Right (TupT [IntT], env)
    infer env (RecT [("x", IntT)]) `shouldBe` Right (TypT, env)
    infer env (Rec [("x", a)]) `shouldBe` Left (UndefinedVar "a")
    infer env (Rec [("x", Int 1)]) `shouldBe` Right (RecT [("x", IntT)], env)
    infer env (Var "p") `shouldBe` Right (RecT [("x", IntT), ("y", IntT)], env)
    infer env (Var "q") `shouldBe` Right (RecT [("x", IntT), ("y", IntT)], env)
    infer env (Get x "x") `shouldBe` Left (NotARecord x IntT)
    infer env (Get p "x") `shouldBe` Right (IntT, env)
    infer env (Get p "y") `shouldBe` Right (IntT, env)
    infer env (Get p "z") `shouldBe` Left (UndefinedField "z" [("x", IntT), ("y", IntT)])
    infer env (Get q "x") `shouldBe` Right (IntT, env)
    infer env (Set x []) `shouldBe` Left (NotARecord x IntT)
    infer env (Set p []) `shouldBe` Right (RecT [("x", IntT), ("y", IntT)], env)
    infer env (Set p [("x", Int 0)]) `shouldBe` Right (RecT [("x", IntT), ("y", IntT)], env)
    infer env (Set p [("x", IntT)]) `shouldBe` Right (RecT [("x", TypT), ("y", IntT)], env)
    infer env (Set p [("z", IntT)]) `shouldBe` Right (RecT [("x", IntT), ("y", IntT), ("z", TypT)], env)
    infer env (Set q [("z", IntT)]) `shouldBe` Right (RecT [("x", IntT), ("y", IntT), ("z", TypT)], env)
    infer env neverT `shouldBe` Right (TypT, env)
    infer env unitT `shouldBe` Right (TypT, env)
    infer env monadT `shouldBe` Right (TypT, env)
    infer env (Ctr "X" "A") `shouldBe` Left (UndefinedType "X")
    infer env (Ctr "x" "A") `shouldBe` Left (NotASumType "x" (Int 1))
    infer env (Ctr "Unit" "X") `shouldBe` Left (CtrNotInSumType "Unit" "X" ["A"])
    infer' env (Ctr "Unit" "A") `shouldBe` Right unitT
    infer' env (Ctr "Monad" "M") `shouldBe` Right (FunT a monadT)
    infer env (Var "x") `shouldBe` Right (IntT, env)
    infer env (Var "y") `shouldBe` Right (y, env)
    infer env (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer env (Var "f") `shouldBe` Right (ForT "a" (funT [IntT, a] TypT), env)
    infer' env (Var "g") `shouldBe` Right (FunT IntT TypT)
    infer env (FunT (Int 1) TypT) `shouldBe` Right (TypT, env)
    infer env (FunT z TypT) `shouldBe` Left (UndefinedVar "z")
    infer env (FunT TypT z) `shouldBe` Left (UndefinedVar "z")
    infer env (Lam "x" x) `shouldBe` Right (ForT "xT" (FunT xT xT), ("x", Ann x xT) : ("xT", xT) : env)
    infer env (Lam "x" (Ann x IntT)) `shouldBe` Right (FunT IntT IntT, ("xT", IntT) : ("x", Ann x xT) : ("xT", xT) : env)
    infer env (App x x) `shouldBe` Left (TypeMismatch (FunT IntT (Var "%1")) IntT)
    infer env (App f TypT) `shouldBe` Left (TypeMismatch TypT IntT)
    infer' env (App f (Int 1)) `shouldBe` Right (FunT a TypT)
    infer' env (App (Lam "x" x) (Int 1)) `shouldBe` Right IntT
    infer env (Ann x IntT) `shouldBe` Right (IntT, env)
    infer env (Ann x (Int 0)) `shouldBe` Left (TypeMismatch (Int 0) IntT)
    infer env (Ann x TypT) `shouldBe` Left (TypeMismatch TypT IntT)
    infer env (ForT "x" x) `shouldBe` Right (TypT, env)
    infer env (ForT "x" z) `shouldBe` Left (UndefinedVar "z")
    infer env (If (Int 0) (Int 1) (Int 2)) `shouldBe` Left (TypeMismatch IntT (funT [Var "Bool1", Var "Bool1"] (Var "Bool1")))
    infer env (If true (Int 1) TypT) `shouldBe` Left (TypeMismatch IntT TypT)
    infer' env (If true (Int 1) (Int 1)) `shouldBe` Right IntT
    infer env (Let [("x", IntT)] x) `shouldBe` Right (IntT, env ++ [("x", IntT)])
    infer env (Let [("z", Int 1)] z) `shouldBe` Right (IntT, env ++ [("z", Int 1)])
    infer' env (Match [([x'], x)]) `shouldBe` Right (ForT "xT" (FunT xT xT))
    infer env (TypeOf (Int 1)) `shouldBe` Right (TypT, env)
    infer env (Op (Call "f" (ForT "a" a))) `shouldBe` Right (ForT "a" a, env)
  -- -- TODO: Operators
  -- -- infer env Add `shouldBe` Right (ForT "a" a, env)

  it "☯ bindings" $ do
    bindings PAny `shouldBe` []
    bindings (PVar "x") `shouldBe` ["x"]
    bindings (PAs y' "x") `shouldBe` ["x", "y"]
    bindings (PCtr "A" []) `shouldBe` []
    bindings (PCtr "A" [x', y']) `shouldBe` ["x", "y"]
    bindings (PTup [x', y']) `shouldBe` ["x", "y"]
    bindings (PRec [("a", x'), ("b", y')]) `shouldBe` ["x", "y"]
    bindings (PAnn x' y') `shouldBe` ["x", "y"]
    bindings (PEq x) `shouldBe` []
    bindings (PIf x' y) `shouldBe` ["x"]

  it "☯ unpack" $ do
    unpack (PAny, x) `shouldBe` []
    unpack (PAs PAny "x", y) `shouldBe` [("x", App (Match [([x'], x)]) y)]

  it "☯ freeVars" $ do
    freeVars Err `shouldBe` []
    freeVars TypT `shouldBe` []
    freeVars IntT `shouldBe` []
    freeVars (Int 1) `shouldBe` []
    freeVars (Tup [x]) `shouldBe` ["x"]
    freeVars (Rec [("a", x)]) `shouldBe` ["x"]
    freeVars (Rec [("a", x)]) `shouldBe` ["x"]
    freeVars (Get x "a") `shouldBe` ["x"]
    freeVars (Set x [("a", y)]) `shouldBe` ["x", "y"]
    freeVars unitT `shouldBe` []
    freeVars monadT `shouldBe` ["a"]
    freeVars (Ctr "T" "A") `shouldBe` []
    freeVars (Var "x") `shouldBe` ["x"]
    freeVars (ForT "x" x) `shouldBe` []
    freeVars (ForT "x" y) `shouldBe` ["y"]
    freeVars (FunT x y) `shouldBe` ["x", "y"]
    freeVars (Lam "x" x) `shouldBe` []
    freeVars (Lam "x" y) `shouldBe` ["y"]
    freeVars (App x y) `shouldBe` ["x", "y"]
    freeVars (Ann x y) `shouldBe` ["x", "y"]
    freeVars (If x y z) `shouldBe` ["x", "y", "z"]
    freeVars (Let [("x", y)] x) `shouldBe` []
    freeVars (Let [("y", z)] x) `shouldBe` ["x"]
    freeVars (Match [([], x)]) `shouldBe` ["x"]
    freeVars (TypeOf x) `shouldBe` ["x"]
    freeVars (Op Add) `shouldBe` []
    freeVars (Op (Call "f" x)) `shouldBe` ["x"]

  -- TODO
  -- it "☯ freeVarsCase" $ do
  --   True `shouldBe` True

  it "☯ findName" $ do
    findName [] `shouldBe` "%1"
    findName [([], Var "%42")] `shouldBe` "%43"
    findName [([PAny], Var "%42")] `shouldBe` "%43"
    findName [([x'], Var "%42")] `shouldBe` "x"
    findName [([x'], Var "%42"), ([y'], Int 2)] `shouldBe` "%43"
    findName [([PAs PAny "x"], Var "%42")] `shouldBe` "x"
    findName [([PAny, x'], Var "%42")] `shouldBe` "%43"
    findName [([PAny], Var "%42"), ([x'], x)] `shouldBe` "x"

  it "☯ ctrType" $ do
    let env = ("x", Int 1) : prelude
    ctrType env "X" `shouldBe` Left (UndefinedCtr "X")
    ctrType env "x" `shouldBe` Left (NotACtr "x" (Int 1))
    ctrType env "A" `shouldBe` Right "Unit"
    ctrType env "True" `shouldBe` Right "Bool"
    ctrType env "M" `shouldBe` Right "Monad"

  it "☯ typeAlts" $ do
    let env = ("x", Int 1) : prelude
    typeAlts env "X" `shouldBe` Left (UndefinedType "X")
    typeAlts env "x" `shouldBe` Left (NotASumType "x" (Int 1))
    typeAlts env "Never" `shouldBe` Right []
    typeAlts env "Unit" `shouldBe` Right [("A", ([], Var "Unit"))]
    typeAlts env "Bool" `shouldBe` Right [("True", ([], Var "Bool")), ("False", ([], Var "Bool"))]
    typeAlts env "Monad" `shouldBe` Right [("M", (["x"], FunT a (App (Var "Monad") a)))]

  it "☯ findAlts" $ do
    let env = prelude
    findAlts env [] `shouldBe` Right []
    findAlts env [([], Int 1)] `shouldBe` Right []
    findAlts env [([PAny], Int 1)] `shouldBe` Right []
    findAlts env [([PAs PAny "x"], Int 1)] `shouldBe` Right []
    findAlts env [([PCtr "A" []], Int 1)] `shouldBe` Right [("A", ([], Var "Unit"))]
    findAlts env [([PAs (PCtr "A" []) "x"], Int 1)] `shouldBe` Right [("A", ([], Var "Unit"))]
    findAlts env [([PEq (Int 0)], Int 1)] `shouldBe` Right []

  it "☯ collapse" $ do
    let alt = ("()", (["y"], IntT))
    collapse "x" alt [([], Int 1)] `shouldBe` []
    collapse "x" alt [([], Int 1)] `shouldBe` []
    collapse "x" alt [([PAny, z'], Int 1)] `shouldBe` [([PAny, z'], Int 1)]
    collapse "x" alt [([PVar "x", z'], Int 1)] `shouldBe` [([PAny, z'], Int 1)]
    collapse "x" alt [([PAs PAny "x", z'], Int 1)] `shouldBe` [([PAny, z'], Int 1)]
    collapse "x" alt [([PAs PAny "y", z'], Int 1)] `shouldBe` [([PAny, z'], Let [("y", x)] (Int 1))]
    collapse "x" alt [([PCtr "()" [y'], z'], Int 1)] `shouldBe` [([y', z'], Int 1)]
    collapse "x" alt [([PCtr "A" [y'], z'], Int 1)] `shouldBe` []
    collapse "x" alt [([PTup [], z'], Int 1)] `shouldBe` [([z'], Int 1)]
    collapse "x" alt [([PTup [y'], z'], Int 1)] `shouldBe` [([y', z'], Int 1)]
    collapse "x" alt [([PRec [], z'], Int 1)] `shouldBe` [([z'], Int 1)]
    collapse "x" alt [([PRec [("a", y')], z'], Int 1)] `shouldBe` [([z'], Let [("y", App (Match [([y'], y)]) (Get x "a"))] (Int 1))]
    collapse "x" alt [([PAnn x' y', z'], x)] `shouldBe` [([PAny, z'], App (Match [([y'], x)]) (TypeOf x))]
    collapse "x" alt [([PEq (Int 0), z'], Int 1), ([y'], Int 2)] `shouldBe` [([PAny, z'], If (eq x (Int 0)) (Int 1) (Match [([PAny], Let [("y", x)] (Int 2))]))]
    collapse "x" alt [([PIf PAny true, z'], Int 1), ([y'], Int 2)] `shouldBe` [([PAny, z'], If true (Int 1) (Match [([PAny], Let [("y", x)] (Int 2))]))]

  it "☯ collapseCases" $ do
    let env = ("x", Int 1) : prelude
    collapseCases env [] `shouldBe` Left NotAllCasesCovered
    collapseCases env [([], x)] `shouldBe` Right x
    collapseCases env [([], x), ([], y)] `shouldBe` Right x
    collapseCases env [([x'], x)] `shouldBe` Right (Lam "x" (Match [([], x)]))
    collapseCases env [([PAny], x)] `shouldBe` Right (Lam "%1" (Match [([], x)]))
    collapseCases env [([PAs PAny "x"], x)] `shouldBe` Right (Lam "x" (Match [([], x)]))
    collapseCases env [([PCtr "A" []], x), ([y'], z)] `shouldBe` Right (Lam "y" (app y [Match [([], x), ([], z)]]))
    collapseCases env [([PCtr "True" []], x), ([y'], z)] `shouldBe` Right (Lam "y" (app y [Match [([], x), ([], z)], Match [([], z)]]))
    collapseCases env [([PCtr "M" [x']], x), ([y'], z)] `shouldBe` Right (Lam "y" (app y [Match [([x'], x), ([PAny], z)]]))
    collapseCases env [([PEq (Int 0)], x), ([y'], z)] `shouldBe` Right (Lam "y" (Match [([], If (eq y (Int 0)) x (Match [([], z)]))]))

  it "☯ compile" $ do
    let env =
          ("x", Int 1) :
          ("xT", IntT) :
          ("yT", TypT) :
          ("f", f) :
          ("g", Lam "y" (App g x)) :
          ("p", Rec [("y", Int 2), ("x", Int 1)]) :
          ("q", Ann q (RecT [("y", IntT), ("x", IntT)])) :
          prelude

    compile env TypT `shouldBe` C.TypT
    compile env IntT `shouldBe` C.IntT
    compile env (Int 1) `shouldBe` C.Int 1
    compile env (TupT []) `shouldBe` C.ForT "()" (C.Var "()")
    compile env (TupT [xT, yT]) `shouldBe` C.ForT "()" (C.funT [C.IntT, C.TypT] (C.Var "()"))
    compile env (Tup []) `shouldBe` C.lam ["()"] (C.Var "()")
    compile env (Tup [x, y]) `shouldBe` C.lam ["()"] (C.app (C.Var "()") [C.Int 1, C.Var "y"])
    compile env (RecT []) `shouldBe` C.ForT "()" (C.Var "()")
    compile env (RecT [("a", xT), ("b", yT)]) `shouldBe` C.forT ["()", "a", "b"] (C.funT [C.IntT, C.TypT] (C.Var "()"))
    compile env (RecT [("b", yT), ("a", xT)]) `shouldBe` C.forT ["()", "a", "b"] (C.funT [C.IntT, C.TypT] (C.Var "()"))
    compile env (Rec []) `shouldBe` C.lam ["()"] (C.Var "()")
    compile env (Rec [("a", x), ("b", IntT)]) `shouldBe` C.lam ["()"] (C.app (C.Var "()") [C.Int 1, C.IntT])
    compile env (Rec [("b", IntT), ("a", x)]) `shouldBe` C.lam ["()"] (C.app (C.Var "()") [C.Int 1, C.IntT])
    compile env (Get p "x") `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] x))
    compile env (Get p "y") `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] y))
    compile env (Get q "x") `shouldBe` compile [] (App q (lam ["x", "y"] x))
    compile env (Set p [("x", Int 0)]) `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] (Rec [("x", Int 0), ("y", y)])))
    compile env (Set p [("y", Int 1), ("x", Int 2)]) `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] (Rec [("x", Int 2), ("y", Int 1)])))
    compile env (Set p [("z", Int 3)]) `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] (Rec [("x", x), ("y", y), ("z", Int 3)])))
    compile env (Set q [("z", Int 3)]) `shouldBe` compile [] (App q (lam ["x", "y"] (Rec [("x", x), ("y", y), ("z", Int 3)])))
    let (unit, bool, monad) = (Var "Unit", Var "Bool", Var "Monad")
    compile env neverT `shouldBe` compile [] (ForT "Never" (Var "Never"))
    compile env unitT `shouldBe` compile [] (ForT "Unit" (FunT unit unit))
    compile env boolT `shouldBe` compile [] (ForT "Bool" (funT [bool, bool] bool))
    compile env monadT `shouldBe` compile [] (ForT "Monad" (FunT (FunT a monad) monad))
    compile env (Ctr "Unit" "A") `shouldBe` C.lam ["A"] (C.Var "A")
    compile env (Ctr "Bool" "True") `shouldBe` C.lam ["True", "False"] (C.Var "True")
    compile env (Var "x") `shouldBe` C.Int 1
    compile env (Var "y") `shouldBe` C.Var "y"
    compile env (Var "f") `shouldBe` C.Var "f"
    compile env (Var "g") `shouldBe` C.Fix "g" (C.Lam [] "y" (C.App (C.Var "g") (C.Int 1)))
    compile env (ForT "x" x) `shouldBe` C.ForT "x" (C.Var "x")
    compile env (ForT "y" x) `shouldBe` C.ForT "y" (C.Int 1)
    compile env (FunT f IntT) `shouldBe` C.FunT (C.Var "f") C.IntT
    compile env (Lam "x" x) `shouldBe` C.Lam [] "x" (C.Var "x")
    compile env (Lam "y" x) `shouldBe` C.Lam [] "y" (C.Int 1)
    compile env (App f x) `shouldBe` C.App (C.Var "f") (C.Int 1)
    compile env (Ann x IntT) `shouldBe` C.Int 1
    compile env (If y x z) `shouldBe` compile [] (app y [Int 1, z])
    compile env (Let [("x", Int 2)] x) `shouldBe` C.Int 1
    compile env (Let [("y", Int 2)] x) `shouldBe` C.Int 1
    compile env (Match [([x'], x)]) `shouldBe` compile [] (Lam "x" x)
    compile env (TypeOf x) `shouldBe` C.IntT
    compile env (Op Add) `shouldBe` C.Op C.Add
    compile env (Op Sub) `shouldBe` C.Op C.Sub
    compile env (Op Mul) `shouldBe` C.Op C.Mul
    compile env (Op Eq) `shouldBe` C.Op C.Eq
    compile env (Op (Call "f" IntT)) `shouldBe` C.Op (C.Call "f" C.IntT)

  -- it "☯ decompile" $ do
  --   True `shouldBe` True

  it "☯ eval" $ do
    let env =
          ("x", Int 1) :
          ("xT", IntT) :
          ("p", Rec [("y", Int 2), ("x", Int 1)]) :
          ("q", Ann q (RecT [("y", IntT), ("x", IntT)])) :
          prelude

    eval env Err `shouldBe` Right (Err, Err)
    eval env TypT `shouldBe` Right (TypT, TypT)
    eval env IntT `shouldBe` Right (IntT, TypT)
    eval env (Int 1) `shouldBe` Right (Int 1, IntT)
    eval env (TupT [xT]) `shouldBe` Right (TupT [IntT], TypT)
    eval env (Tup [x]) `shouldBe` Right (Tup [Int 1], TupT [IntT])
    eval env (RecT [("y", xT), ("x", TypT)]) `shouldBe` Right (RecT [("x", TypT), ("y", IntT)], TypT)
    eval env (Rec [("y", x), ("x", IntT)]) `shouldBe` Right (Rec [("x", IntT), ("y", Int 1)], RecT [("x", TypT), ("y", IntT)])
    eval env (Get p "x") `shouldBe` Right (Int 1, IntT)
    eval env (Get p "y") `shouldBe` Right (Int 2, IntT)
    eval env (Get p "z") `shouldBe` Left (UndefinedField "z" [("x", IntT), ("y", IntT)])
    eval env (Get q "x") `shouldBe` Right (Get q "x", IntT)
    eval env (Get q "y") `shouldBe` Right (Get q "y", IntT)
    eval env (Get q "z") `shouldBe` Left (UndefinedField "z" [("x", IntT), ("y", IntT)])
    eval env (Set p []) `shouldBe` Right (Rec [("x", Int 1), ("y", Int 2)], RecT [("x", IntT), ("y", IntT)])
    eval env (Set p [("x", IntT)]) `shouldBe` Right (Rec [("x", IntT), ("y", Int 2)], RecT [("x", TypT), ("y", IntT)])
    eval env (Set p [("z", IntT)]) `shouldBe` Right (Rec [("x", Int 1), ("y", Int 2), ("z", IntT)], RecT [("x", IntT), ("y", IntT), ("z", TypT)])
    eval env (Set q []) `shouldBe` Right (q, RecT [("x", IntT), ("y", IntT)])
    eval env (Set q [("x", IntT)]) `shouldBe` Right (Set q [("x", IntT)], RecT [("x", TypT), ("y", IntT)])
    eval env (Set q [("z", IntT)]) `shouldBe` Right (Set q [("z", IntT)], RecT [("x", IntT), ("y", IntT), ("z", TypT)])
    eval env neverT `shouldBe` Right (neverT, TypT)
    eval env unitT `shouldBe` Right (unitT, TypT)
    eval env monadT `shouldBe` Left (UndefinedVar "a")
    eval env (Var "Monad") `shouldBe` Right (Lam "a" monadT, ForT "aT" (FunT (Var "aT") TypT))
    eval env (App (Var "Monad") IntT) `shouldBe` Right (SumT "Monad" [("M", (["x"], FunT IntT (App (Var "Monad") IntT)))], TypT)
    eval env (Ctr "Unit" "A") `shouldBe` Right (Ctr "Unit" "A", unitT)
    eval env (Ctr "Bool" "True") `shouldBe` Right (Ctr "Bool" "True", boolTDef)
    eval env (Ctr "Monad" "M") `shouldBe` Right (Ctr "Monad" "M", FunT a monadT)
    eval env (Var "x") `shouldBe` Right (Int 1, IntT)
    -- ForT !String !Expr
    -- FunT !Expr !Expr
    -- Lam !String !Expr
    -- App !Expr !Expr
    -- Ann !Expr !Expr
    -- If !Expr !Expr !Expr
    -- Let ![(String, Expr)] !Expr
    -- Match ![Case]
    -- TypeOf !Expr
    -- Op !Operator
    -- Bool
    -- True
    -- False
    True `shouldBe` True
