module ExamplesTests where

import qualified Core as C
import Tao
import TaoLang (loadDef, loadEnv, loadExpr, loadFile, loadModule)
import Test.Hspec

examplesTests :: SpecWith ()
examplesTests = describe "--== Examples end-to-end ==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PVar "x", PVar "y", PVar "z")
  let eval' env expr = case eval env expr of
        Right result -> Just result
        Left _ -> Nothing

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

    it "☯ loadFile" $ do
      loadFile "example/basic" "expr.tao" `shouldReturn` [("x", Int 42)]
      loadFile "example/basic" "func.tao" `shouldReturn` [("id", Match [([x'], x)])]

    it "☯ loadModule" $ do
      loadModule "example/basic" `shouldReturn` [("x", Int 42), ("id", Match [([x'], x)])]

  describe "☯ syntax" $ do
    it "☯ atoms" $ do
      loadExpr "42" `shouldReturn` Int 42
      loadExpr "x" `shouldReturn` Var "x"
      loadExpr "(x : y)" `shouldReturn` Ann x y
      loadExpr "(+)" `shouldReturn` Add
      loadExpr "(-)" `shouldReturn` Sub
      loadExpr "(*)" `shouldReturn` Mul
      loadExpr "(==)" `shouldReturn` Eq

    it "☯ operators" $ do
      loadExpr "x y z" `shouldReturn` App (App x y) z
      loadExpr "x + y + z" `shouldReturn` add (add x y) z
      loadExpr "x - y - z" `shouldReturn` sub (sub x y) z
      loadExpr "x * y * z" `shouldReturn` mul (mul x y) z
      loadExpr "x == y == z" `shouldReturn` eq (eq x y) z
      loadExpr "x -> y -> z" `shouldReturn` Fun x (Fun y z)
      loadExpr "(x -> y) -> z" `shouldReturn` Fun (Fun x y) z

    it "☯ pattern matching" $ do
      loadExpr "\\x -> y" `shouldReturn` Match [([x'], y)]
      loadExpr "\\ x -> y | _ -> z" `shouldReturn` Match [([x'], y), ([PAny], z)]
      loadExpr "\\ x -> y\n| _ -> z" `shouldReturn` Match [([x'], y), ([PAny], z)]

    it "☯ definitions" $ do
      loadExpr "x = y; 42" `shouldReturn` Let [("x", y)] (Int 42)
      loadExpr "x : y\nx = z; 42" `shouldReturn` Let [("x", Ann z y)] (Int 42)
      loadExpr "(A x y) = z; 42" `shouldReturn` Let [("x", App (Match [([PCtr "A" [x', y']], x)]) z), ("y", App (Match [([PCtr "A" [x', y']], y)]) z)] (Int 42)

    it "☯ builtin" $ do
      loadExpr "@Int" `shouldReturn` IntT
      loadExpr "@True" `shouldReturn` Bool True
      loadExpr "@False" `shouldReturn` Bool False
      loadExpr "@Type {}" `shouldReturn` TypeDef "Type" []
      loadExpr "@Maybe {Just x | Nothing}" `shouldReturn` TypeDef "Maybe" [("Just", ["x"]), ("Nothing", [])]
      loadExpr "@func type" `shouldReturn` Call "func" (Var "type")

  describe "☯ end-to-end" $ do
    it "☯ factorial" $ do
      env <- loadFile "example/end-to-end" "factorial.tao"
      let factorial n = eval' env (App (Var "factorial") (Int n))
      factorial 0 `shouldBe` Just (C.Int 1)
      factorial 1 `shouldBe` Just (C.Int 1)
      factorial 5 `shouldBe` Just (C.Int 120)
      eval' env (Var "factorial") `shouldNotBe` Nothing

    it "☯ fibonacci" $ do
      env <- loadFile "example/end-to-end" "fibonacci.tao"
      let fibonacci n = eval' env (App (Var "fibonacci") (Int n))
      fibonacci 0 `shouldBe` Just (C.Int 0)
      fibonacci 1 `shouldBe` Just (C.Int 1)
      fibonacci 2 `shouldBe` Just (C.Int 1)
      fibonacci 3 `shouldBe` Just (C.Int 2)
      fibonacci 4 `shouldBe` Just (C.Int 3)
      fibonacci 5 `shouldBe` Just (C.Int 5)
      eval' env (Var "fibonacci") `shouldNotBe` Nothing
