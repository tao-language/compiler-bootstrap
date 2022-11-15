module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

taoTests :: SpecWith ()
taoTests = describe "--== Tao representation ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PAs PAny "x", PAs PAny "y", PAs PAny "z")

  it "☯ lam" $ do
    lam [] x `shouldBe` x
    lam ["x"] y `shouldBe` Lam "x" y
    lam ["x", "y"] z `shouldBe` Lam "x" (Lam "y" z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

  it "☯ fun" $ do
    fun [] x `shouldBe` x
    fun [x] y `shouldBe` Fun x y
    fun [x, y] z `shouldBe` Fun x (Fun y z)

  it "☯ for" $ do
    for [] x `shouldBe` x
    for ["x"] y `shouldBe` For "x" y
    for ["x", "y"] z `shouldBe` For "x" (For "y" z)

  it "☯ built-in operators" $ do
    add x y `shouldBe` App (App Add x) y
    sub x y `shouldBe` App (App Sub x) y
    mul x y `shouldBe` App (App Mul x) y
    eq x y `shouldBe` App (App Eq x) y

  it "☯ bindings" $ do
    bindings PAny `shouldBe` []
    bindings (PAs y' "x") `shouldBe` ["x", "y"]
    bindings (PCtr "A" []) `shouldBe` []
    bindings (PCtr "A" [x', y']) `shouldBe` ["x", "y"]
    bindings (PIf x' y) `shouldBe` ["x"]
    bindings (PEq x) `shouldBe` []

  it "☯ unpack" $ do
    unpack (PAny, x) `shouldBe` []
    unpack (PAs PAny "x", y) `shouldBe` [("x", App (Match [([x'], x)]) y)]

  it "☯ ctrType" $ do
    let env = [("T", TypeDef "T" [("A", [])]), ("A", Ctr "T" "A")]
    ctrType env "X" `shouldBe` Left (UndefinedCtr "X")
    ctrType env "T" `shouldBe` Left (NotACtr (TypeDef "T" [("A", [])]))
    ctrType env "A" `shouldBe` Right "T"

  it "☯ typeAlts" $ do
    let env = [("T", TypeDef "T" [("A", ["x", "y"])]), ("A", Ctr "T" "A")]
    typeAlts env "X" `shouldBe` Left (UndefinedType "X")
    typeAlts env "A" `shouldBe` Left (NotAType (Ctr "T" "A"))
    typeAlts env "T" `shouldBe` Right [("A", ["x", "y"])]

  it "☯ altArgs" $ do
    let alts = [("A", ["x", "y"])]
    altArgs alts "X" `shouldBe` Left (UndefinedCtr "X")
    altArgs alts "A" `shouldBe` Right ["x", "y"]

  it "☯ inferName" $ do
    inferName [] `shouldBe` "%1"
    inferName [([], Var "%42")] `shouldBe` "%43"
    inferName [([PAny], Var "%42")] `shouldBe` "%43"
    inferName [([x'], Var "%42")] `shouldBe` "x"
    inferName [([x'], Var "%42"), ([y'], Int 2)] `shouldBe` "%43"
    inferName [([PAs PAny "x"], Var "%42")] `shouldBe` "x"
    inferName [([PAny, x'], Var "%42")] `shouldBe` "%43"
    inferName [([PAny], Var "%42"), ([x'], x)] `shouldBe` "x"

  it "☯ validatePatterns" $ do
    validatePatterns [] `shouldBe` Right ()
    validatePatterns [([], x)] `shouldBe` Right ()
    validatePatterns [([], x), ([], y)] `shouldBe` Right ()
    validatePatterns [([], x), ([y'], y)] `shouldBe` Left (CaseNumPatternsMismatch 0 1)
    validatePatterns [([x'], x), ([], y)] `shouldBe` Left (CaseNumPatternsMismatch 1 0)
    validatePatterns [([x'], x), ([y'], y)] `shouldBe` Right ()

  it "☯ validateCases" $ do
    let env =
          [ ("T", TypeDef "T" [("A", [])]),
            ("A", Ctr "T" "A"),
            ("U", TypeDef "U" [("B", [])]),
            ("B", Ctr "U" "B")
          ]
    validateCases env "T" [] `shouldBe` Right ()
    validateCases env "T" [([], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PAny], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PCtr "X" []], Int 1)] `shouldBe` Left (UndefinedCtr "X")
    validateCases env "T" [([PCtr "T" []], Int 1)] `shouldBe` Left (NotACtr (TypeDef "T" [("A", [])]))
    validateCases env "T" [([PCtr "A" []], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PCtr "B" []], Int 1)] `shouldBe` Left (CaseTypeMismatch "T" "U")
    validateCases env "T" [([PCtr "A" [x']], Int 1)] `shouldBe` Left (CaseCtrArgsMismatch [] [x'])
    validateCases env "T" [([PAs PAny "x"], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PAs (PCtr "X" []) "x"], Int 1)] `shouldBe` Left (UndefinedCtr "X")
    validateCases env "T" [([PAs (PCtr "A" []) "x"], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PEq (Int 0)], Int 1)] `shouldBe` Right ()

  it "☯ findAlts" $ do
    let env = [("T", TypeDef "T" [("A", [])]), ("A", Ctr "T" "A")]
    findAlts env [] `shouldBe` Right []
    findAlts env [([], Int 1)] `shouldBe` Right []
    findAlts env [([PAny], Int 1)] `shouldBe` Right []
    findAlts env [([PAs PAny "x"], Int 1)] `shouldBe` Right []
    findAlts env [([PCtr "A" []], Int 1)] `shouldBe` Right [("A", [])]
    findAlts env [([PAs (PCtr "A" []) "x"], Int 1)] `shouldBe` Right [("A", [])]
    findAlts env [([PEq (Int 0)], Int 1)] `shouldBe` Right []

  it "☯ collapse" $ do
    let alt = ("A", ["y"])
    collapse "x" alt [] `shouldBe` []
    collapse "x" alt [([], Int 1)] `shouldBe` []
    collapse "x" alt [([PAny, z'], Int 1)] `shouldBe` [([PAny, z'], Int 1)]
    collapse "x" alt [([PAs PAny "x", z'], Int 1)] `shouldBe` [([PAny, z'], Int 1)]
    collapse "x" alt [([PAs PAny "y", z'], Int 1)] `shouldBe` [([PAny, z'], Let [("y", x)] (Int 1))]
    collapse "x" alt [([PCtr "A" [y'], z'], Int 1)] `shouldBe` [([y', z'], Int 1)]
    collapse "x" alt [([PCtr "B" [y'], z'], Int 1)] `shouldBe` []
    collapse "x" alt [([PAnn x' y', z'], x)] `shouldBe` [([PAny, z'], App (Match [([y'], x)]) (TypeOf x))]
    collapse "x" alt [([PIf PAny (Bool True), z'], Int 1), ([y'], Int 2)] `shouldBe` [([PAny, z'], If (Bool True) (Int 1) (Match [([PAny], Let [("y", x)] (Int 2))]))]
    collapse "x" alt [([PEq (Int 0), z'], Int 1), ([y'], Int 2)] `shouldBe` [([PAny, z'], If (eq x (Int 0)) (Int 1) (Match [([PAny], Let [("y", x)] (Int 2))]))]

  it "☯ compile" $ do
    let env =
          [ ("x", IntT),
            ("y", y),
            ("f", App (Var "f") (Var "x")),
            ("T", TypeDef "T" [("A", []), ("B", ["x", "xs"])]),
            ("A", Ctr "T" "A"),
            ("B", Ctr "T" "B")
          ]
    compile env IntT `shouldBe` Right C.IntT
    compile env (TypeDef "T" [("A", [])]) `shouldBe` compile [] (For "T" (fun [Var "T"] (Var "T")))
    compile env (Bool True) `shouldBe` compile [] (lam ["True", "False"] (Var "True"))
    compile env (Bool False) `shouldBe` compile [] (lam ["True", "False"] (Var "False"))
    compile env (Int 1) `shouldBe` Right (C.Int 1)
    compile env (Var "x") `shouldBe` Right C.IntT
    compile env (Var "y") `shouldBe` Right (C.Var "y")
    compile env (Var "z") `shouldBe` Right (C.Var "z")
    compile env (Var "f") `shouldBe` Right (C.Fix "f" (C.App (C.Var "f") C.IntT))
    compile env (Lam "x" x) `shouldBe` Right (C.Lam [] "x" (C.Var "x"))
    compile env (App y x) `shouldBe` Right (C.App (C.Var "y") C.IntT)
    compile env (Fun x y) `shouldBe` Right (C.Fun C.IntT (C.Var "y"))
    compile env (Ann x y) `shouldBe` Right (C.Ann C.IntT (C.Var "y"))
    compile env (Ann x (For "y" y)) `shouldBe` Right (C.Ann C.IntT (C.For "y" (C.Var "y")))
    compile env (For "x" x) `shouldBe` Right (C.For "x" (C.Var "x"))
    compile env (If (Var "cond") (Var "then") (Var "else")) `shouldBe` Right (C.App (C.App (C.Var "cond") (C.Var "then")) (C.Var "else"))
    compile env (Ctr "X" "A") `shouldBe` Left (UndefinedType "X")
    compile env (Ctr "x" "A") `shouldBe` Left (NotAType IntT)
    compile env (Ctr "T" "X") `shouldBe` Left (UndefinedCtr "X")
    compile env (Ctr "T" "A") `shouldBe` compile [] (lam ["A", "B"] (Var "A"))
    compile env (Ctr "T" "B") `shouldBe` compile [] (lam ["x1", "xs", "A", "B"] (app (Var "B") [Var "x1", Var "xs"]))
    compile env (Match []) `shouldBe` Left NotAllCasesCovered
    compile env (Match [([], Int 1)]) `shouldBe` Right (C.Int 1)
    compile env (Match [([PAny], x)]) `shouldBe` compile [] (Lam "%1" IntT)
    compile env (Match [([PAs PAny "y"], y)]) `shouldBe` compile [] (Lam "y" y)
    compile env (Match [([PCtr "A" []], x), ([PAny], y)]) `shouldBe` compile [] (Lam "%1" (app (Var "%1") [IntT, lam ["%1", "%1"] y]))
    compile env (Match [([PCtr "B" [x', y']], x), ([PAny], y)]) `shouldBe` compile [] (Lam "%1" (app (Var "%1") [y, lam ["x", "y"] x]))
    compile env (Match [([PEq (Int 0)], x), ([PAny], y)]) `shouldBe` compile [] (Lam "%1" (If (eq (Var "%1") (Int 0)) IntT y))
    compile env (Call "f" (For "y" y)) `shouldBe` Right (C.Call "f" (C.For "y" (C.Var "y")))
    compile env (TypeOf (Int 1)) `shouldBe` Right C.IntT
    compile env Add `shouldBe` Right C.Add
    compile env Sub `shouldBe` Right C.Sub
    compile env Mul `shouldBe` Right C.Mul
    compile env Eq `shouldBe` Right C.Eq
