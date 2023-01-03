module ExamplesTests where

import TaoLang
import Test.Hspec

examplesTests :: SpecWith ()
examplesTests = describe "--== Examples end-to-end ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PVar "x", PVar "y", PVar "z")

  it "☯ loadExpr" $ do
    loadExpr "42" `shouldReturn` Int 42

  it "☯ loadDef" $ do
    loadDef "x = y" `shouldReturn` [("x", y)]
    loadDef "x : y\nx = z" `shouldReturn` [("x", Ann z y)]
    loadDef "x y = 1" `shouldReturn` [("x", Match [([y'], Int 1)])]
    loadDef "x y = 1\nx z = 2" `shouldReturn` [("x", Match [([y'], Int 1), ([z'], Int 2)])]
    loadDef "x : y\nx z = 1" `shouldReturn` [("x", Ann (Match [([z'], Int 1)]) y)]
    loadDef "_ = y" `shouldReturn` []
    loadDef "(A x) = y" `shouldReturn` [("x", App (Match [([PCtr "A" [x']], x)]) y)]
    loadDef "(A x y) = z" `shouldReturn` [("x", App (Match [([PCtr "A" [x', y']], x)]) z), ("y", App (Match [([PCtr "A" [x', y']], y)]) z)]

  it "☯ loadEnv" $ do
    loadEnv "" `shouldReturn` []
    loadEnv "x = 1" `shouldReturn` [("x", Int 1)]
    loadEnv "x = 1\n" `shouldReturn` [("x", Int 1)]
    loadEnv "x = 1\ny = 2" `shouldReturn` [("x", Int 1), ("y", Int 2)]

  it "☯ loadBlock" $ do
    loadBlock "42" `shouldReturn` ([], Int 42)
    loadBlock "x = 1; 42" `shouldReturn` ([("x", Int 1)], Int 42)

  it "☯ loadFile" $ do
    loadFile "example/basic" "expr.tao" `shouldReturn` [("x", Int 42)]
    loadFile "example/basic" "func.tao" `shouldReturn` [("id", Match [([x'], x)])]

  it "☯ loadModule" $ do
    loadModule "example/basic" `shouldReturn` [("x", Int 42), ("id", Match [([x'], x)])]

  it "☯ eval" $ do
    let env =
          ("p", Rec [("y", Int 2), ("x", Int 1)]) :
          ("q", Ann (Var "q") (RecT [("y", IntT), ("x", IntT)])) :
          prelude
    let eval src = do (env', expr) <- parseBlock src; TaoLang.eval env (Let env' expr)
    eval "!error" `shouldBe` Right (Err, Err)
    eval "Type" `shouldBe` Right (TypT, TypT)
    eval "Int" `shouldBe` Right (IntT, TypT)
    eval "42" `shouldBe` Right (Int 42, IntT)
    eval "(() : Type)" `shouldBe` Right (TupT [], TypT)
    eval "((Int,) : Type)" `shouldBe` Right (TupT [IntT], TypT)
    eval "()" `shouldBe` Right (Tup [], TupT [])
    eval "(1,)" `shouldBe` Right (Tup [Int 1], TupT [IntT])
    eval "(1, Int)" `shouldBe` Right (Tup [Int 1, IntT], TupT [IntT, TypT])
    eval "(1, Int,)" `shouldBe` Right (Tup [Int 1, IntT], TupT [IntT, TypT])
    eval "(x : Int)" `shouldBe` Right (RecT [("x", IntT)], TypT)
    eval "(x : Int,)" `shouldBe` Right (RecT [("x", IntT)], TypT)
    eval "(x : Int, y : Type)" `shouldBe` Right (RecT [("x", IntT), ("y", TypT)], TypT)
    eval "(y : Type, x : Int,)" `shouldBe` Right (RecT [("x", IntT), ("y", TypT)], TypT)
    eval "(x = 1)" `shouldBe` Right (Rec [("x", Int 1)], RecT [("x", IntT)])
    eval "(x = 1,)" `shouldBe` Right (Rec [("x", Int 1)], RecT [("x", IntT)])
    eval "(x = 1, y = 2)" `shouldBe` Right (Rec [("x", Int 1), ("y", Int 2)], RecT [("x", IntT), ("y", IntT)])
    eval "(y = 2, x = 1,)" `shouldBe` Right (Rec [("x", Int 1), ("y", Int 2)], RecT [("x", IntT), ("y", IntT)])
    eval "(x = 1).x" `shouldBe` Right (Int 1, IntT)
    eval "p.x" `shouldBe` Right (Int 1, IntT)
    eval "p.y" `shouldBe` Right (Int 2, IntT)
    eval "q.x" `shouldBe` Right (Get (Var "q") "x", IntT)
    eval "q.y" `shouldBe` Right (Get (Var "q") "y", IntT)
    eval "(p | x = Int)" `shouldBe` Right (Rec [("x", IntT), ("y", Int 2)], RecT [("x", TypT), ("y", IntT)])
    eval "(p | x = Int,)" `shouldBe` Right (Rec [("x", IntT), ("y", Int 2)], RecT [("x", TypT), ("y", IntT)])
    eval "(p | x = Int, y = 0)" `shouldBe` Right (Rec [("x", IntT), ("y", Int 0)], RecT [("x", TypT), ("y", IntT)])
    eval "(q | x = Int)" `shouldBe` Right (Set (Var "q") [("x", IntT)], RecT [("x", TypT), ("y", IntT)])
    eval "T = A; A" `shouldBe` Right (Ctr "T" "A", SumT [("A", ([], Var "T"))])
    eval "x = 1; x" `shouldBe` Right (Int 1, IntT)
  -- TODO: ForT
  -- TODO: FunT
  -- TODO: Lam
  -- TODO: App
  -- TODO: Ann
  -- TODO: If
  -- TODO: Let
  -- TODO: Match
  -- TODO: TypeOf
  -- TODO: Op

  it "☯ factorial" $ do
    env <- loadFile "example/e2e" "factorial.tao"
    let f = Var "factorial"
    let factorial n = eval (env ++ prelude) (App f (Int n))
    factorial 0 `shouldBe` Right (Int 1, IntT)
    factorial 1 `shouldBe` Right (Int 1, IntT)
    factorial 5 `shouldBe` Right (Int 120, IntT)
    fmap snd (eval (env ++ prelude) f) `shouldBe` Right (FunT IntT IntT)

  it "☯ fibonacci" $ do
    env <- loadFile "example/e2e" "fibonacci.tao"
    let f = Var "fibonacci"
    let fibonacci n = eval (env ++ prelude) (App f (Int n))
    fibonacci 0 `shouldBe` Right (Int 0, IntT)
    fibonacci 1 `shouldBe` Right (Int 1, IntT)
    fibonacci 2 `shouldBe` Right (Int 1, IntT)
    fibonacci 3 `shouldBe` Right (Int 2, IntT)
    fibonacci 4 `shouldBe` Right (Int 3, IntT)
    fibonacci 5 `shouldBe` Right (Int 5, IntT)
    fmap snd (eval (env ++ prelude) f) `shouldBe` Right (FunT IntT IntT)
