module ExamplesTests where

import qualified Core as C
import Tao (Expr (..), Pattern (..), eval)
import TaoLang (loadExpr, loadFile, loadModule)
import Test.Hspec

examplesTests :: SpecWith ()
examplesTests = describe "--== Examples end-to-end ==--" $ do
  let x = Var "x"
  let x' = PAs PAny "x"

  describe "☯ loading" $ do
    it "☯ loadExpr" $ do
      loadExpr "42" `shouldReturn` Int 42

    it "☯ loadFile" $ do
      loadFile "example/loading" "expr.tao" `shouldReturn` [("x", Int 42)]
      loadFile "example/loading" "func.tao" `shouldReturn` [("id", Match [([x'], x)])]

    it "☯ loadModule" $ do
      loadModule "example/loading" `shouldReturn` [("x", Int 42), ("id", Match [([x'], x)])]

  it "☯ syntax" $ do
    True `shouldBe` True

  describe "☯ end-to-end" $ do
    it "☯ factorial" $ do
      env <- loadFile "example/end-to-end" "factorial.tao"
      let factorial n = eval env (App (Var "factorial") (Int n))
      factorial 0 `shouldBe` Right (C.Int 1)
      factorial 1 `shouldBe` Right (C.Int 1)
      factorial 5 `shouldBe` Right (C.Int 120)

    it "☯ fibonacci" $ do
      env <- loadFile "example/end-to-end" "fibonacci.tao"
      let fibonacci n = eval env (App (Var "fib") (Int n))
      fibonacci 0 `shouldBe` Right (C.Int 0)
      fibonacci 1 `shouldBe` Right (C.Int 1)
      fibonacci 2 `shouldBe` Right (C.Int 1)
      fibonacci 3 `shouldBe` Right (C.Int 2)
      fibonacci 4 `shouldBe` Right (C.Int 3)
      fibonacci 5 `shouldBe` Right (C.Int 5)