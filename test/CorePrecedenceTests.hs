module CorePrecedenceTests where

import Core
import Parser (State (..))
import Test.Hspec

run :: SpecWith ()
run = describe "--== Core precedence ==--" $ do
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")

  let prec' :: String -> Either String (Expr, String)
      prec' src = case parse 0 "<CorePrecedence>" src of
        Right (a, s) | s.remaining /= "" -> Right (a, "remaining: " ++ s.remaining)
        Right (a, _) -> Right (a, show a)
        Left s -> Left ("syntax error, remaining: " ++ s.remaining)
  let prec :: String -> Either String Expr
      prec src = do
        (a, out) <- prec' src
        if src == out then Right a else Left ("expected: " ++ src ++ ", got: " ++ out)

  it "☯ CorePrecedence.Fix" $ do
    prec "&x. y | z" `shouldBe` Right (Fix "x" (y `Or` z))
    prec "&x. @y. z" `shouldBe` Right (Fix "x" (for ["y"] z))
    prec "&x. y : z" `shouldBe` Right (Fix "x" (y `Ann` z))
    prec "&x. y -> z" `shouldBe` Right (Fix "x" (y `Fun` z))
    prec "&x. y z" `shouldBe` Right (Fix "x" (y `App` z))

  it "☯ CorePrecedence.Or" $ do
    prec "x | y | z" `shouldBe` Right (x `Or` (y `Or` z))
    prec "x | @y. z" `shouldBe` Right (Or x (for ["y"] z))
    prec "x | y : z" `shouldBe` Right (x `Or` (y `Ann` z))
    prec "x | y -> z" `shouldBe` Right (x `Or` (y `Fun` z))
    prec "x | y z" `shouldBe` Right (x `Or` (y `App` z))

  it "☯ CorePrecedence.For" $ do
    prec "@x. y | z" `shouldBe` Right (Or (for ["x"] y) z)
    prec' "@x. @y. z" `shouldBe` Right (for ["x"] (for ["y"] z), "@x y. z")
    prec "@x. y : z" `shouldBe` Right (Ann (for ["x"] y) z)
    prec "@x. y -> z" `shouldBe` Right (for ["x"] (y `Fun` z))
    prec "@x. y z" `shouldBe` Right (for ["x"] (y `App` z))

  it "☯ CorePrecedence.Ann" $ do
    prec "x : y | z" `shouldBe` Right (x `Ann` y `Or` z)
    prec "x : y : z" `shouldBe` Right (x `Ann` (y `Ann` z))
    prec "x : @y. z" `shouldBe` Right (Ann x (for ["y"] z))
    prec "x : y -> z" `shouldBe` Right (x `Ann` (y `Fun` z))
    prec "x : y z" `shouldBe` Right (x `Ann` (y `App` z))

  it "☯ CorePrecedence.Fun" $ do
    prec "x -> y | z" `shouldBe` Right (x `Fun` y `Or` z)
    prec "x -> @y. z" `shouldBe` Right (Fun x (for ["y"] z))
    prec "x -> y : z" `shouldBe` Right (x `Fun` y `Ann` z)
    prec "x -> y -> z" `shouldBe` Right (x `Fun` (y `Fun` z))
    prec "x -> y z" `shouldBe` Right (x `Fun` (y `App` z))

  it "☯ CorePrecedence.App" $ do
    prec "x y | z" `shouldBe` Right (x `App` y `Or` z)
    prec "x (@y. z)" `shouldBe` Right (App x (for ["y"] z))
    prec "x y : z" `shouldBe` Right (x `App` y `Ann` z)
    prec "x y -> z" `shouldBe` Right (x `App` y `Fun` z)
    prec "x y z" `shouldBe` Right (x `App` y `App` z)
