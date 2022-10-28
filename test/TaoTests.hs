module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

taoTests :: SpecWith ()
taoTests = describe "--== Tao representation ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PVar "x", PVar "y", PVar "z")

  -- TODO: syntax sugar
  it "☯ lam" $ do
    lam [] x `shouldBe` Var "x"
    lam ["x"] y `shouldBe` Lam "x" y
    lam ["x", "y"] z `shouldBe` Lam "x" (Lam "y" z)

  it "☯ app" $ do
    app x [] `shouldBe` x
    app x [y] `shouldBe` App x y
    app x [y, z] `shouldBe` App (App x y) z

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

  it "☯ validateCtrCases" $ do
    let env =
          [ ("T", Typ [("A", [])]),
            ("A", Ctr "T" "A"),
            ("U", Typ [("B", [])]),
            ("B", Ctr "U" "B")
          ]
    validateCtrCases env "T" [] `shouldBe` Right ()
    validateCtrCases env "T" [([], Int 1)] `shouldBe` Right ()
    validateCtrCases env "T" [([PAny], Int 1)] `shouldBe` Right ()
    validateCtrCases env "T" [([PVar "x"], Int 1)] `shouldBe` Right ()
    validateCtrCases env "T" [([PCtr "X" []], Int 1)] `shouldBe` Left (UndefinedCtr "X")
    validateCtrCases env "T" [([PCtr "T" []], Int 1)] `shouldBe` Left (NotACtr (Typ [("A", [])]))
    validateCtrCases env "T" [([PCtr "A" []], Int 1)] `shouldBe` Right ()
    validateCtrCases env "T" [([PCtr "B" []], Int 1)] `shouldBe` Left (CaseTypeMismatch "T" "U")
    validateCtrCases env "T" [([PCtr "A" [x']], Int 1)] `shouldBe` Left (CaseCtrArgsMismatch [] [x'])
    validateCtrCases env "T" [([PAs PAny "x"], Int 1)] `shouldBe` Right ()
    validateCtrCases env "T" [([PAs (PCtr "X" []) "x"], Int 1)] `shouldBe` Left (UndefinedCtr "X")
    validateCtrCases env "T" [([PAs (PCtr "A" []) "x"], Int 1)] `shouldBe` Right ()

  it "☯ findAlts" $ do
    let env = [("T", Typ [("A", [])]), ("A", Ctr "T" "A")]
    findAlts env [] `shouldBe` Right []
    findAlts env [([], Int 1)] `shouldBe` Right []
    findAlts env [([PAny], Int 1)] `shouldBe` Right []
    findAlts env [([PAs PAny "x"], Int 1)] `shouldBe` Right []
    findAlts env [([PVar "x"], Int 1)] `shouldBe` Right []
    findAlts env [([PCtr "A" []], Int 1)] `shouldBe` Right [("A", [])]
    findAlts env [([PAs (PCtr "A" []) "x"], Int 1)] `shouldBe` Right [("A", [])]
    findAlts env [([PInt 0], Int 1)] `shouldBe` Right []

  it "☯ filterAny" $ do
    filterAny "x" ([], x) `shouldBe` Nothing
    filterAny "x" ([PAny, y'], x) `shouldBe` Just ([y'], x)
    filterAny "x" ([PAs PAny "x", y'], x) `shouldBe` Just ([y'], x)
    filterAny "x" ([PAs PAny "y", z'], y) `shouldBe` Just ([z'], Let [("y", x)] y)
    filterAny "x" ([PVar "y", z'], y) `shouldBe` Just ([z'], Let [("y", x)] y)
    filterAny "x" ([PCtr "A" [], y'], x) `shouldBe` Nothing
    filterAny "x" ([PInt 1, y'], x) `shouldBe` Nothing

  -- it "☯ filterCtr" $ do
  --   filterCtr ("A", ["x", "y"]) "z" ([], x) `shouldBe` Nothing
  --   filterCtr ("A", ["x", "y"]) "z" ([PAny, y'], x) `shouldBe` Just ([PAny, PAny, x'], x)
  --   filterCtr ("A", ["x", "y"]) "z" ([x', y'], x) `shouldBe` Just ([PAny, PAny, x'], x)

  -- it "☯ chompDefault" $ do
  --   chompDefault "x" ([PAny, y_], Int 0) `shouldBe` Just ([y_], Int 0)
  --   chompDefault "x" ([PInt 0, y_], Int 0) `shouldBe` Nothing
  --   chompDefault "x" ([PCtr "A" [], y_], Int 0) `shouldBe` Nothing
  --   chompDefault "x" ([x_, y_], Int 0) `shouldBe` Just ([y_], Int 0)
  --   chompDefault "x" ([y_, z_], Int 0) `shouldBe` Just ([z_], Let [("y", x)] (Int 0))
  -- -- chompDefault "x" ([PAnn (y_) PAny, z_], Int 0) `shouldBe` Just ([z_], Let [("y", x)] (Int 0))

  -- it "☯ chompCtr" $ do
  --   chompCtr "x" ("A", 0) ([PAny, y_], Int 0) `shouldBe` Just ([y_], Int 0)
  --   chompCtr "x" ("B", 1) ([PAny, y_], Int 0) `shouldBe` Just ([PAny, y_], Int 0)
  --   chompCtr "x" ("A", 0) ([PInt 0, y_], Int 0) `shouldBe` Nothing
  --   chompCtr "x" ("A", 0) ([PCtr "A" [], y_], Int 0) `shouldBe` Just ([y_], Int 0)
  --   chompCtr "x" ("B", 1) ([PCtr "A" [], y_], Int 0) `shouldBe` Nothing
  --   chompCtr "x" ("B", 1) ([PCtr "B" [y_], z_], Int 0) `shouldBe` Just ([y_, z_], Int 0)
  --   chompCtr "x" ("A", 0) ([x_, y_], Int 0) `shouldBe` Just ([y_], Int 0)
  --   chompCtr "x" ("A", 0) ([y_, z_], Int 0) `shouldBe` Just ([z_], Let [("y", x)] (Int 0))
  -- -- chompCtr "x" ("A", 0) ([PAnn y_ PAny, z_], Int 0) `shouldBe` Just ([z_], Let [("y", x)] (Int 0))

  -- it "☯ bindings" $ do
  --   bindings PAny `shouldBe` []
  --   bindings x_ `shouldBe` ["x"]
  --   bindings (PInt 1) `shouldBe` []
  --   bindings (PCtr "A" []) `shouldBe` []
  --   bindings (PCtr "A" [x_, y_]) `shouldBe` ["x", "y"]

  it "☯ compile" $ do
    let env =
          [ ("x", IntT),
            ("y", y),
            ("f", App (Var "f") (Var "x")),
            ("T", Typ [("A", []), ("B", ["x", "y"])]),
            ("A", Ctr "T" "A"),
            ("B", Ctr "T" "B")
          ]
    compile env IntT `shouldBe` Right C.IntT
    compile env (Typ [("A", [])]) `shouldBe` Right (C.Typ [("A", [])])
    compile env (Int 1) `shouldBe` Right (C.Int 1)
    compile env (Var "x") `shouldBe` Right C.IntT
    compile env (Var "y") `shouldBe` Right (C.Var "y")
    compile env (Var "z") `shouldBe` Left (UndefinedVar "z")
    compile env (Var "f") `shouldBe` Right (C.Fix "f" (C.App (C.Var "f") C.IntT))
    compile env (Lam "x" x) `shouldBe` Right (C.Lam [] "x" (C.Var "x"))
    compile env (Lam "y" x) `shouldBe` Right (C.Lam [] "y" C.IntT)
    compile env (App y x) `shouldBe` Right (C.App (C.Var "y") C.IntT)
    compile env (Fun x y) `shouldBe` Right (C.Fun C.IntT (C.Var "y"))
    compile env (Ann y (T [] x)) `shouldBe` Right (C.Ann (C.Var "y") (C.T [] C.IntT))
    compile env (Ann y (T ["x"] x)) `shouldBe` Right (C.Ann (C.Var "y") (C.T ["x"] (C.Var "x")))
    compile env (Call "f") `shouldBe` Right (C.Call "f")
    compile env (Let [] x) `shouldBe` Right C.IntT
    compile env (Let [("y", x)] y) `shouldBe` Right C.IntT
    compile env (Let [("x", Int 1)] x) `shouldBe` Right (C.Int 1)
    compile env (Ctr "X" "A") `shouldBe` Left (UndefinedType "X")
    compile env (Ctr "x" "A") `shouldBe` Left (NotAType IntT)
    compile env (Ctr "T" "X") `shouldBe` Left (UndefinedCtr "X")
    compile env (Ctr "T" "A") `shouldBe` compile [] (lam ["A", "B"] (Var "A"))
    compile env (Ctr "T" "B") `shouldBe` compile [] (lam ["x", "y", "A", "B"] (app (Var "B") [x, y]))
    compile env (Match [] [] (Int 0)) `shouldBe` Right (C.Int 0)
    compile env (Match [] [([], Int 1)] (Int 0)) `shouldBe` Right (C.Int 1)
    compile env (Match ["x"] [] (Int 0)) `shouldBe` compile [] (Lam "x" (Int 0))
    compile env (Match ["x"] [([PCtr "A" []], x)] (Int 0)) `shouldBe` compile [] (Lam "x" (app x [x, lam ["x", "y"] (Int 0)]))
    compile env (Match ["x"] [([PCtr "B" [x', y']], x)] (Int 0)) `shouldBe` compile [] (Lam "x" (app x [Int 0, lam ["x", "y"] x]))
    compile env (Match ["x"] [([PAs PAny "y"], y)] (Int 0)) `shouldBe` compile [] (Lam "x" x)
    compile env (Match ["x"] [([y'], y)] (Int 0)) `shouldBe` compile [] (Lam "x" x)
