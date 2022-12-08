module ExamplesTests where

import Tao
import TaoLang
import Test.Hspec

examplesTests :: SpecWith ()
examplesTests = describe "--== Examples end-to-end ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PVar "x", PVar "y", PVar "z")

  describe "☯ basic" $ do
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

  describe "☯ end-to-end" $ do
    let path = "example/e2e"

    it "☯ factorial" $ do
      env <- loadFile path "factorial.tao"
      let factorial n = eval env (App (Var "factorial") (Int n))
      factorial 0 `shouldBe` Int 1
      factorial 1 `shouldBe` Int 1
      factorial 5 `shouldBe` Int 120
      eval env (Var "factorial") `shouldNotBe` Err

    it "☯ fibonacci" $ do
      env <- loadFile path "fibonacci.tao"
      let fibonacci n = eval env (App (Var "fibonacci") (Int n))
      fibonacci 0 `shouldBe` Int 0
      fibonacci 1 `shouldBe` Int 1
      fibonacci 2 `shouldBe` Int 1
      fibonacci 3 `shouldBe` Int 2
      fibonacci 4 `shouldBe` Int 3
      fibonacci 5 `shouldBe` Int 5
      eval env (Var "fibonacci") `shouldNotBe` Err
