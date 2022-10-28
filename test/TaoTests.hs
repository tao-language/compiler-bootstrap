module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

taoTests :: SpecWith ()
taoTests = describe "--== Tao representation ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PVar "x", PVar "y", PVar "z")

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

  it "☯ let'" $ do
    let' ("x", y) z `shouldBe` App (Lam "x" z) y

  it "☯ built-in operators" $ do
    add x y `shouldBe` App (App (Call "+") x) y
    sub x y `shouldBe` App (App (Call "-") x) y
    mul x y `shouldBe` App (App (Call "*") x) y
    eq x y `shouldBe` App (App (Call "==") x) y

  -- it "☯ unpack" $ do
  --   unpack (PAny, x) `shouldBe` []
  --   unpack (PAs PAny "x", y) `shouldBe` [("x", y)]

  it "☯ ctrType" $ do
    let env = [("T", Typ [("A", [])]), ("A", Ctr "T" "A")]
    ctrType env "X" `shouldBe` Left (UndefinedCtr "X")
    ctrType env "T" `shouldBe` Left (NotACtr (Typ [("A", [])]))
    ctrType env "A" `shouldBe` Right "T"

  it "☯ typeAlts" $ do
    let env = [("T", Typ [("A", ["x", "y"])]), ("A", Ctr "T" "A")]
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

  it "☯ validateCases" $ do
    let env =
          [ ("T", Typ [("A", [])]),
            ("A", Ctr "T" "A"),
            ("U", Typ [("B", [])]),
            ("B", Ctr "U" "B")
          ]
    validateCases env "T" [] `shouldBe` Right ()
    validateCases env "T" [([], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PAny], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PVar "x"], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PCtr "X" []], Int 1)] `shouldBe` Left (UndefinedCtr "X")
    validateCases env "T" [([PCtr "T" []], Int 1)] `shouldBe` Left (NotACtr (Typ [("A", [])]))
    validateCases env "T" [([PCtr "A" []], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PCtr "B" []], Int 1)] `shouldBe` Left (CaseTypeMismatch "T" "U")
    validateCases env "T" [([PCtr "A" [x']], Int 1)] `shouldBe` Left (CaseCtrArgsMismatch [] [x'])
    validateCases env "T" [([PAs PAny "x"], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PAs (PCtr "X" []) "x"], Int 1)] `shouldBe` Left (UndefinedCtr "X")
    validateCases env "T" [([PAs (PCtr "A" []) "x"], Int 1)] `shouldBe` Right ()
    validateCases env "T" [([PEq (Int 0)], Int 1)] `shouldBe` Right ()

  it "☯ findAlts" $ do
    let env = [("T", Typ [("A", [])]), ("A", Ctr "T" "A")]
    findAlts env [] `shouldBe` Right []
    findAlts env [([], Int 1)] `shouldBe` Right []
    findAlts env [([PAny], Int 1)] `shouldBe` Right []
    findAlts env [([PAs PAny "x"], Int 1)] `shouldBe` Right []
    findAlts env [([PVar "x"], Int 1)] `shouldBe` Right []
    findAlts env [([PCtr "A" []], Int 1)] `shouldBe` Right [("A", [])]
    findAlts env [([PAs (PCtr "A" []) "x"], Int 1)] `shouldBe` Right [("A", [])]
    findAlts env [([PEq (Int 0)], Int 1)] `shouldBe` Right []

  it "☯ collapse" $ do
    let alt = ("A", ["y"])
    collapse "x" alt [] `shouldBe` []
    collapse "x" alt [([], Int 1)] `shouldBe` []
    collapse "x" alt [([PAny, z'], Int 1)] `shouldBe` [([PAny, z'], Int 1)]
    collapse "x" alt [([PAs PAny "x", z'], Int 1)] `shouldBe` [([PAny, z'], Int 1)]
    collapse "x" alt [([PAs PAny "y", z'], Int 1)] `shouldBe` [([PAny, z'], let' ("y", x) (Int 1))]
    collapse "x" alt [([PVar "y", z'], Int 1)] `shouldBe` [([PAny, z'], let' ("y", x) (Int 1))]
    collapse "x" alt [([PCtr "A" [y'], z'], Int 1)] `shouldBe` [([y', z'], Int 1)]
    collapse "x" alt [([PCtr "B" [y'], z'], Int 1)] `shouldBe` []
    collapse "x" alt [([PEq (Int 0), z'], Int 1), ([y'], Int 2)] `shouldBe` [([z'], If (Eq x (Int 0)) (Int 1) (Match [([PAny], let' ("y", x) (Int 2))]))]

  it "☯ compile" $ do
    let f = Var "f"
    let env =
          [ ("x", IntT),
            ("y", y),
            ("f", App (Var "f") (Var "x")),
            ("T", Typ [("A", []), ("B", ["x", "xs"])]),
            ("A", Ctr "T" "A"),
            ("B", Ctr "T" "B")
          ]
    compile IntT `shouldBe` Right C.IntT
    compile (Typ [("A", [])]) `shouldBe` Right (C.Typ [("A", [])])
    -- TODO: Bool
    compile (Int 1) `shouldBe` Right (C.Int 1)
    compile (Var "x") `shouldBe` Right (C.Var "x")
    compile (Lam "x" x) `shouldBe` Right (C.Lam [] "x" (C.Var "x"))
    compile (App x y) `shouldBe` Right (C.App (C.Var "x") (C.Var "y"))
    compile (Fun x y) `shouldBe` Right (C.Fun (C.Var "x") (C.Var "y"))
    compile (Ann x (T [] y)) `shouldBe` Right (C.Ann (C.Var "x") (C.T [] (C.Var "y")))
    compile (Ann x (T ["y"] y)) `shouldBe` Right (C.Ann (C.Var "x") (C.T ["y"] (C.Var "y")))
    compile (Call "f") `shouldBe` Right (C.Call "f")
    compile (Let env x) `shouldBe` Right C.IntT
    compile (Let env y) `shouldBe` Right (C.Var "y")
    compile (Let env z) `shouldBe` Right (C.Var "z")
    compile (Let env f) `shouldBe` Right (C.Fix "f" (C.App (C.Var "f") C.IntT))
    -- TODO: If
    compile (Let env (Ctr "X" "A")) `shouldBe` Left (UndefinedType "X")
    compile (Let env (Ctr "x" "A")) `shouldBe` Left (NotAType IntT)
    compile (Let env (Ctr "T" "X")) `shouldBe` Left (UndefinedCtr "X")
    compile (Let env (Ctr "T" "A")) `shouldBe` compile (lam ["A", "B"] (Var "A"))
    compile (Let env (Ctr "T" "B")) `shouldBe` compile (lam ["x1", "xs", "A", "B"] (app (Var "B") [Var "x1", Var "xs"]))
    compile (Let env (Match [])) `shouldBe` Left NotAllCasesCovered
    compile (Let env (Match [([], Int 1)])) `shouldBe` Right (C.Int 1)
    compile (Let env (Match [([PAny], x)])) `shouldBe` compile (Lam "%1" x)
    compile (Let env (Match [([PAs PAny "y"], y)])) `shouldBe` compile (Lam "y" y)
    compile (Let env (Match [([PVar "y"], y)])) `shouldBe` compile (Lam "y" y)
    compile (Let env (Match [([PCtr "A" []], x), ([PAny], y)])) `shouldBe` compile (Lam "%1" (app (Var "%1") [x, lam ["%1", "%1"] y]))
    compile (Let env (Match [([PCtr "B" [x', y']], x), ([PAny], y)])) `shouldBe` compile (Lam "%1" (app (Var "%1") [y, lam ["x", "y"] x]))

-- compile (Let env (Match [([PEq (Int 0)], x)])) `shouldBe` compile (Lam "%1" x)
-- TODO: Eq

-- it "☯ bindings" $ do
--   bindings PAny `shouldBe` []
--   bindings x_ `shouldBe` ["x"]
--   bindings (PInt 1) `shouldBe` []
--   bindings (PCtr "A" []) `shouldBe` []
--   bindings (PCtr "A" [x_, y_]) `shouldBe` ["x", "y"]
