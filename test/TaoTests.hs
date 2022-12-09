module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

taoTests :: SpecWith ()
taoTests = describe "--== Tao representation ==--" $ do
  let (a, b) = (Var "a", Var "b")
  let (f, g, p) = (Var "f", Var "g", Var "p")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PAs PAny "x", PAs PAny "y", PAs PAny "z")
  let (xT, yT, gT) = (Var "xT", Var "yT", Var "gT")

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

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

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
          [ ("x", Int 1),
            ("y", y),
            ("f", Ann f (ForT "a" $ FunT IntT a)),
            ("g", Lam "g" (Ann (App g (Int 1)) TypT)),
            ("p", Rec [("x", Int 1), ("y", Int 2)]),
            ( "T",
              SumT
                [("a", a), ("b", IntT)]
                [("A", ([], NamT "T" [a, b])), ("B", (["x", "y"], funT [IntT, a] (NamT "T" [a, b])))]
            ),
            ("A", Ctr "T" "A"),
            ("B", Ctr "T" "B")
          ]

    infer env Err `shouldBe` Right (Err, env)
    infer env TypT `shouldBe` Right (TypT, env)
    infer env BoolT `shouldBe` Right (TypT, env)
    infer env (Bool True) `shouldBe` Right (BoolT, env)
    infer env IntT `shouldBe` Right (TypT, env)
    infer env (Int 1) `shouldBe` Right (IntT, env)
    infer env (TupT [a]) `shouldBe` Left (UndefinedVar "a")
    infer env (TupT [IntT]) `shouldBe` Right (TypT, env)
    infer env (Tup [Int 1]) `shouldBe` Right (TupT [IntT], env)
    infer env (RecT [("x", a)]) `shouldBe` Left (UndefinedVar "a")
    infer env (RecT [("x", IntT)]) `shouldBe` Right (TypT, env)
    infer env (Rec [("x", Int 1)]) `shouldBe` Right (RecT [("x", IntT)], env)
    infer env (Get x "x") `shouldBe` Left (NotARecord x IntT)
    infer env (Get p "x") `shouldBe` Right (IntT, env)
    infer env (Get p "y") `shouldBe` Right (IntT, env)
    infer env (Get p "z") `shouldBe` Left (UndefinedField "z" [("x", IntT), ("y", IntT)])
    infer env (Set x []) `shouldBe` Left (NotARecord x IntT)
    infer env (Set p []) `shouldBe` Right (RecT [("x", IntT), ("y", IntT)], env)
    infer env (Set p [("x", Int 0)]) `shouldBe` Right (RecT [("x", IntT), ("y", IntT)], env)
    infer env (Set p [("x", IntT)]) `shouldBe` Right (RecT [("x", TypT), ("y", IntT)], env)
    infer env (Set p [("z", IntT)]) `shouldBe` Right (RecT [("x", IntT), ("y", IntT), ("z", TypT)], env)
    infer env (SumT [] []) `shouldBe` Right (TypT, env)
    infer env (SumT [] [("X", ([], TypT))]) `shouldBe` Left (UndefinedCtr "X")
    infer env (SumT [] [("x", ([], TypT))]) `shouldBe` Left (NotACtr "x" (Int 1))
    infer env (SumT [] [("A", ([], TypT))]) `shouldBe` Right (TypT, env)
    infer env (SumT [] [("A", (["x"], a))]) `shouldBe` Left (UndefinedVar "a")
    infer env (SumT [] [("A", (["x"], IntT))]) `shouldBe` Right (TypT, env)
    infer env (SumT [("a", a)] [("A", (["x"], a))]) `shouldBe` Right (forT ["a"] (funT [a] TypT), env)
    infer env (SumT [("a", a), ("b", IntT)] []) `shouldBe` Right (forT ["a", "b"] (funT [a, IntT] TypT), env)
    infer env (NamT "X" []) `shouldBe` Left (UndefinedType "X")
    infer env (NamT "x" []) `shouldBe` Left (NotASumType "x" (Int 1))
    infer env (NamT "T" []) `shouldBe` Left (NamedTypeArgsMismatch [("a", a), ("b", IntT)] [])
    infer env (NamT "T" [IntT, TypT]) `shouldBe` Left (TypeMismatch TypT IntT)
    infer env (NamT "T" [IntT, Int 1]) `shouldBe` Right (TypT, env)
    infer env (Ctr "X" "A") `shouldBe` Left (UndefinedType "X")
    infer env (Ctr "x" "A") `shouldBe` Left (NotASumType "x" (Int 1))
    infer env (Ctr "T" "X") `shouldBe` Left (CtrNotInSumType "T" "X" ["A", "B"])
    infer env (Ctr "T" "A") `shouldBe` Right (forT ["a", "b"] (NamT "T" [a, b]), env)
    infer env (Ctr "T" "B") `shouldBe` Right (forT ["a", "b"] (funT [IntT, a] (NamT "T" [a, b])), env)
    infer env (Var "x") `shouldBe` Right (IntT, env)
    infer env (Var "y") `shouldBe` Right (yT, ("y", Ann y yT) : ("yT", yT) : env)
    infer env (Var "z") `shouldBe` Left (UndefinedVar "z")
    infer env (Var "f") `shouldBe` Right (ForT "a" (FunT IntT a), env)
    infer env (Var "g") `shouldBe` Right (FunT (FunT IntT TypT) TypT, ("%1", TypT) : ("gT", FunT IntT (Var "%1")) : ("%1", Var "%1") : ("g", Ann g gT) : ("gT", gT) : ("g", g) : env)
    infer env (FunT (Int 1) TypT) `shouldBe` Right (TypT, env)
    infer env (FunT (Var "z") TypT) `shouldBe` Left (UndefinedVar "z")
    infer env (FunT TypT (Var "z")) `shouldBe` Left (UndefinedVar "z")
    infer env (Lam "x" x) `shouldBe` Right (ForT "xT" (FunT xT xT), ("x", Ann x xT) : ("xT", xT) : ("x", x) : env)
    infer env (Lam "x" (Ann x IntT)) `shouldBe` Right (FunT IntT IntT, ("xT", IntT) : ("x", Ann x xT) : ("xT", xT) : ("x", x) : env)
    infer env (App x x) `shouldBe` Left (TypeMismatch (FunT IntT (Var "%1")) IntT)
    infer env (App f TypT) `shouldBe` Left (TypeMismatch TypT IntT)
    infer env (App f (Int 1)) `shouldBe` Right (a, ("%1", a) : ("a", a) : ("%1", Var "%1") : env)
    infer env (App (Lam "x" x) (Int 1)) `shouldBe` Right (IntT, ("%1", IntT) : ("xT1", IntT) : ("xT1", Var "xT1") : ("%1", Var "%1") : ("x", Ann x xT) : ("xT", xT) : ("x", x) : env)
    infer env (Ann x IntT) `shouldBe` Right (IntT, env)
    infer env (Ann x (Int 0)) `shouldBe` Left (NotAType (Int 0) IntT)
    infer env (Ann x TypT) `shouldBe` Left (TypeMismatch TypT IntT)
    infer env (ForT "x" x) `shouldBe` Right (TypT, env)
    infer env (ForT "x" z) `shouldBe` Left (UndefinedVar "z")
    infer env (If (Int 0) (Int 1) (Int 2)) `shouldBe` Left (TypeMismatch IntT BoolT)
    infer env (If (Bool True) (Int 1) TypT) `shouldBe` Left (TypeMismatch IntT TypT)
    infer env (If (Bool True) (Int 1) (Int 1)) `shouldBe` Right (IntT, env)
    infer env (Let [("y", Int 1)] x) `shouldBe` Right (IntT, ("y", Int 1) : env)
    infer env (Let [("y", Int 1)] y) `shouldBe` Right (IntT, ("y", Int 1) : env)
    infer env (Match [([x'], x)]) `shouldBe` Right (ForT "xT" (FunT xT xT), ("x", Ann x xT) : ("xT", xT) : ("x", x) : env)
    infer env (TypeOf (Int 1)) `shouldBe` Right (TypT, env)
    infer env (Op (Call "f" (ForT "a" a))) `shouldBe` Right (ForT "a" a, env)
  -- TODO: Operators
  -- infer env Add `shouldBe` Right (ForT "a" a, env)

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
    freeVars BoolT `shouldBe` []
    freeVars (Bool True) `shouldBe` []
    freeVars IntT `shouldBe` []
    freeVars (Int 1) `shouldBe` []
    freeVars (TupT [x]) `shouldBe` ["x"]
    freeVars (Tup [x]) `shouldBe` ["x"]
    freeVars (RecT [("a", x)]) `shouldBe` ["x"]
    freeVars (Rec [("a", x)]) `shouldBe` ["x"]
    freeVars (Get x "a") `shouldBe` ["x"]
    freeVars (Set x [("a", y)]) `shouldBe` ["x", "y"]
    freeVars (SumT [("x", x)] [("A", (["x", "y"], x))]) `shouldBe` []
    freeVars (SumT [("x", x)] [("A", (["x", "y"], y))]) `shouldBe` ["y"]
    freeVars (NamT "T" [x]) `shouldBe` ["x"]
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
    let env = [("T", SumT [] [("A", ([], NamT "T" []))]), ("A", Ctr "T" "A")]
    ctrType env "X" `shouldBe` Left (UndefinedCtr "X")
    ctrType env "T" `shouldBe` Left (NotACtr "T" (SumT [] [("A", ([], NamT "T" []))]))
    ctrType env "A" `shouldBe` Right "T"

  it "☯ typeAlts" $ do
    let env = [("T", SumT [("a", a)] [("A", (["x", "y"], funT [a, IntT] (NamT "T" [a])))]), ("A", Ctr "T" "A")]
    typeAlts env "X" `shouldBe` Left (UndefinedType "X")
    typeAlts env "A" `shouldBe` Left (NotASumType "A" (Ctr "T" "A"))
    typeAlts env "T" `shouldBe` Right [("A", (["x", "y"], funT [a, IntT] (NamT "T" [a])))]

  it "☯ findAlts" $ do
    let env = [("T", SumT [] [("A", ([], NamT "T" []))]), ("A", Ctr "T" "A")]
    findAlts env [] `shouldBe` Right []
    findAlts env [([], Int 1)] `shouldBe` Right []
    findAlts env [([PAny], Int 1)] `shouldBe` Right []
    findAlts env [([PAs PAny "x"], Int 1)] `shouldBe` Right []
    findAlts env [([PCtr "A" []], Int 1)] `shouldBe` Right [("A", ([], NamT "T" []))]
    findAlts env [([PAs (PCtr "A" []) "x"], Int 1)] `shouldBe` Right [("A", ([], NamT "T" []))]
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
    collapse "x" alt [([PIf PAny (Bool True), z'], Int 1), ([y'], Int 2)] `shouldBe` [([PAny, z'], If (Bool True) (Int 1) (Match [([PAny], Let [("y", x)] (Int 2))]))]

  it "☯ collapseCases" $ do
    let env =
          [ ("x", Int 1),
            ("T", SumT [("a", a)] [("A", ([], NamT "T" [a])), ("B", (["x", "y"], NamT "T" [IntT]))]),
            ("A", Ctr "T" "A"),
            ("B", Ctr "T" "B")
          ]
    collapseCases env [] `shouldBe` Left NotAllCasesCovered
    collapseCases env [([], x)] `shouldBe` Right x
    collapseCases env [([], x), ([], y)] `shouldBe` Right x
    collapseCases env [([x'], x)] `shouldBe` Right (Lam "x" (Match [([], x)]))
    collapseCases env [([PAny], x)] `shouldBe` Right (Lam "%1" (Match [([], x)]))
    collapseCases env [([PAs PAny "x"], x)] `shouldBe` Right (Lam "x" (Match [([], x)]))
    collapseCases env [([PCtr "A" []], x), ([y'], z)] `shouldBe` Right (Lam "y" (app y [Match [([], x), ([], z)], Match [([PAny, PAny], z)]]))
    collapseCases env [([PCtr "B" [x', y']], x), ([y'], z)] `shouldBe` Right (Lam "y" (app y [Match [([], z)], Match [([x', y'], x), ([PAny, PAny], z)]]))
    collapseCases env [([PEq (Int 0)], x), ([y'], z)] `shouldBe` Right (Lam "y" (Match [([], If (eq y (Int 0)) x (Match [([], z)]))]))

  it "☯ compile" $ do
    let env =
          [ ("x", Int 1),
            ("f", f),
            ("g", App g x),
            ("p", Rec [("y", Int 2), ("x", Int 1)]),
            ("T", SumT [("a", a)] [("A", ([], NamT "T" [a])), ("B", (["x", "y"], NamT "T" [IntT]))]),
            ("A", Ctr "T" "A"),
            ("B", Ctr "T" "B")
          ]
    compile env TypT `shouldBe` C.TypT
    compile env BoolT `shouldBe` C.BoolT
    compile env (Bool True) `shouldBe` compile [] (lam ["true", "false"] (Var "true"))
    compile env (Bool False) `shouldBe` compile [] (lam ["true", "false"] (Var "false"))
    compile env IntT `shouldBe` C.IntT
    compile env (Int 1) `shouldBe` C.Int 1
    compile env (TupT [IntT]) `shouldBe` C.TupT [C.IntT]
    compile env (Tup []) `shouldBe` C.lam ["()"] (C.Var "()")
    compile env (Tup [x, y]) `shouldBe` C.lam ["()"] (C.app (C.Var "()") [C.Int 1, C.Var "y"])
    compile env (RecT [("a", IntT)]) `shouldBe` C.RecT [("a", C.IntT)]
    compile env (Rec []) `shouldBe` C.lam ["()"] (C.Var "()")
    compile env (Rec [("a", x), ("b", IntT)]) `shouldBe` C.lam ["()"] (C.app (C.Var "()") [C.Int 1, C.IntT])
    compile env (Rec [("b", IntT), ("a", x)]) `shouldBe` C.lam ["()"] (C.app (C.Var "()") [C.Int 1, C.IntT])
    compile env (Get p "x") `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] x))
    compile env (Get p "y") `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] y))
    compile env (Set p [("x", Int 0)]) `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] (Rec [("x", Int 0), ("y", y)])))
    compile env (Set p [("y", Int 1), ("x", Int 2)]) `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] (Rec [("x", Int 2), ("y", Int 1)])))
    compile env (Set p [("z", Int 3)]) `shouldBe` compile [] (App (Rec [("x", Int 1), ("y", Int 2)]) (lam ["x", "y"] (Rec [("x", x), ("y", y), ("z", Int 3)])))
    compile env (SumT [("a", a)] [("A", ([""], TypT)), ("B", (["x"], TypT))]) `shouldBe` C.SumT [("a", C.Var "a")] [("A", ([""], C.TypT)), ("B", (["x"], C.TypT))]
    compile env (NamT "T" [IntT]) `shouldBe` C.NamT "T" [C.IntT]
    compile env (Ctr "T" "A") `shouldBe` C.lam ["A", "B"] (C.Var "A")
    compile env (Ctr "T" "B") `shouldBe` C.lam ["x1", "y", "A", "B"] (C.app (C.Var "B") [C.Var "x1", C.Var "y"])
    compile env (Var "x") `shouldBe` C.Int 1
    compile env (Var "y") `shouldBe` C.Var "y"
    compile env (Var "f") `shouldBe` C.Var "f"
    compile env (Var "g") `shouldBe` C.Fix "g" (C.App (C.Var "g") (C.Int 1))
    compile env (ForT "x" x) `shouldBe` C.ForT "x" (C.Var "x")
    compile env (ForT "y" x) `shouldBe` C.ForT "y" (C.Int 1)
    compile env (FunT f IntT) `shouldBe` C.FunT (C.Var "f") C.IntT
    compile env (Lam "x" x) `shouldBe` C.Lam [] "x" (C.Var "x")
    compile env (Lam "y" x) `shouldBe` C.Lam [] "y" (C.Int 1)
    compile env (App f x) `shouldBe` C.App (C.Var "f") (C.Int 1)
    compile env (Ann x IntT) `shouldBe` C.Int 1
    compile env (If y x z) `shouldBe` compile [] (app y [Int 1, z])
    compile env (Let [("x", Int 2)] x) `shouldBe` C.Int 2
    compile env (Let [("y", Int 2)] x) `shouldBe` C.Int 1
    compile env (Match [([x'], x)]) `shouldBe` compile [] (Lam "x" x)
    compile env (TypeOf x) `shouldBe` C.IntT
    compile env (Op Add) `shouldBe` C.Op C.Add
    compile env (Op Sub) `shouldBe` C.Op C.Sub
    compile env (Op Mul) `shouldBe` C.Op C.Mul
    compile env (Op Eq) `shouldBe` C.Op C.Eq
    compile env (Op (Call "f" IntT)) `shouldBe` C.Op (C.Call "f" C.IntT)

-- it "☯ decompile" $ do
--   -- TODO