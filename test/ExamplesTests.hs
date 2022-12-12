module ExamplesTests where

import Tao
import TaoLang
import Test.Hspec

examplesTests :: SpecWith ()
examplesTests = describe "--== Examples end-to-end ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  -- let (p, q) = (Var "p", Var "q")
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
    loadBlock "42" `shouldReturn` Int 42
    loadBlock "x = 1; 42" `shouldReturn` Let [("x", Int 1)] (Int 42)

  it "☯ loadFile" $ do
    loadFile "example/basic" "expr.tao" `shouldReturn` [("x", Int 42)]
    loadFile "example/basic" "func.tao" `shouldReturn` [("id", Match [([x'], x)])]

  it "☯ loadModule" $ do
    loadModule "example/basic" `shouldReturn` [("x", Int 42), ("id", Match [([x'], x)])]

  -- it "☯ syntax" $ do
  --   let env =
  --         ("p", Rec [("y", Int 2), ("x", Int 1)]) :
  --         ("q", Ann q (RecT [("y", IntT), ("x", IntT)])) :
  --         prelude
  --   let run' src = do a <- parseBlock src; run env a
  --   run' "!error" `shouldBe` Right (Err, Err)
  --   run' "Type" `shouldBe` Right (TypT, TypT)
  --   run' "Bool" `shouldBe` Right (boolT, TypT)
  --   -- run' "True" `shouldBe` Right (true, boolT)
  --   -- run' "False" `shouldBe` Right (false, boolT)
  --   run' "Int" `shouldBe` Right (IntT, TypT)
  --   run' "42" `shouldBe` Right (Int 42, IntT)
  -- -- run' "()" `shouldBe` Right (Tup [], Tup [])
  -- -- run' "(1,)" `shouldBe` Right (Tup [Int 1], Tup [IntT])
  -- -- run' "(1, Int)" `shouldBe` Right (Tup [Int 1, IntT], Tup [IntT, TypT])
  -- -- run' "(1, Int,)" `shouldBe` Right (Tup [Int 1, IntT], Tup [IntT, TypT])
  -- -- run' "(x = 1)" `shouldBe` Right (Rec [("x", Int 1)], Rec [("x", IntT)])
  -- -- run' "(x = 1,)" `shouldBe` Right (Rec [("x", Int 1)], Rec [("x", IntT)])
  -- -- run' "(x = 1, y = 2)" `shouldBe` Right (Rec [("x", Int 1), ("y", Int 2)], Rec [("x", IntT), ("y", IntT)])
  -- -- run' "(y = 2, x = 1,)" `shouldBe` Right (Rec [("x", Int 1), ("y", Int 2)], Rec [("x", IntT), ("y", IntT)])
  -- -- run' "(x = 1).x" `shouldBe` Right (Int 1, IntT)
  -- -- run' "p.x" `shouldBe` Right (Int 1, IntT)

  it "☯ factorial" $ do
    env <- loadFile "example/e2e" "factorial.tao"
    let f = Var "factorial"
    let factorial n = Tao.eval (env ++ prelude) (App f (Int n))
    factorial 0 `shouldBe` Right (Int 1, IntT)
    factorial 1 `shouldBe` Right (Int 1, IntT)
    factorial 5 `shouldBe` Right (Int 120, IntT)
    fmap snd (Tao.eval (env ++ prelude) f) `shouldBe` Right (FunT IntT IntT)

  it "☯ fibonacci" $ do
    env <- loadFile "example/e2e" "fibonacci.tao"
    let f = Var "fibonacci"
    let fibonacci n = Tao.eval (env ++ prelude) (App f (Int n))
    fibonacci 0 `shouldBe` Right (Int 0, IntT)
    fibonacci 1 `shouldBe` Right (Int 1, IntT)
    fibonacci 2 `shouldBe` Right (Int 1, IntT)
    fibonacci 3 `shouldBe` Right (Int 2, IntT)
    fibonacci 4 `shouldBe` Right (Int 3, IntT)
    fibonacci 5 `shouldBe` Right (Int 5, IntT)
    fmap snd (Tao.eval (env ++ prelude) f) `shouldBe` Right (FunT IntT IntT)
