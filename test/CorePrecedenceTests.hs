module CorePrecedenceTests where

import Core
import Parser (State (..))
import Test.Hspec

run :: SpecWith ()
run = describe "--== Core precedence ==--" $ do
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")

  let prec' :: String -> Either String (Expr, String)
      prec' src = case parse 0 "filename" src of
        Right (a, s) | s.remaining /= "" -> Right (a, "remaining: " ++ s.remaining)
        Right (a, _) -> Right (a, format 80 a)
        Left s -> Left ("syntax error, remaining: " ++ s.remaining)
  let prec :: String -> Either String Expr
      prec src = do
        (a, out) <- prec' src
        if src == out then Right a else Left ("wrong precedence, got: " ++ out)

  it "☯ CorePrecedence.Fix" $ do
    prec' "&x. &y. z" `shouldBe` Right (Fix "x" (Fix "y" z), "&x y. z")
    prec "&x. y | z" `shouldBe` Right (Fix "x" (Or y z))
    prec "&x. y : z" `shouldBe` Right (Fix "x" (Ann y z))
    prec "&x. @y. z" `shouldBe` Right (Fix "x" (For "y" z))
    prec "&x. y -> z" `shouldBe` Right (Fix "x" (Fun y z))
    prec "&x. y z" `shouldBe` Right (Fix "x" (App y z))

  it "☯ CorePrecedence.Or" $ do
    prec "x | &y. z" `shouldBe` Right (Or x (Fix "y" z))
    prec "x | y | z" `shouldBe` Right (Or x (Or y z))
    prec "x | y : z" `shouldBe` Right (Or x (Ann y z))
    prec "x | @y. z" `shouldBe` Right (Or x (For "y" z))
    prec "x | y -> z" `shouldBe` Right (Or x (Fun y z))
    prec "x | y z" `shouldBe` Right (Or x (App y z))

  it "☯ CorePrecedence.Ann" $ do
    prec "x : &y. z" `shouldBe` Right (Ann x (Fix "y" z))
    prec "x : y | z" `shouldBe` Right (Or (Ann x y) z)
    prec "x : y : z" `shouldBe` Right (Ann x (Ann y z))
    prec "x : @y. z" `shouldBe` Right (Ann x (For "y" z))
    prec "x : y -> z" `shouldBe` Right (Ann x (Fun y z))
    prec "x : y z" `shouldBe` Right (Ann x (App y z))

  it "☯ CorePrecedence.For" $ do
    prec "@x. &y. z" `shouldBe` Right (For "x" (Fix "y" z))
    prec "@x. y | z" `shouldBe` Right (Or (For "x" y) z)
    prec "@x. y : z" `shouldBe` Right (Ann (For "x" y) z)
    prec' "@x. @y. z" `shouldBe` Right (For "x" (For "y" z), "@x y. z")
    prec "@x. y -> z" `shouldBe` Right (For "x" (Fun y z))
    prec "@x. y z" `shouldBe` Right (For "x" (App y z))

  it "☯ CorePrecedence.Fun" $ do
    prec "x -> &y. z" `shouldBe` Right (Fun x (Fix "y" z))
    prec "x -> y | z" `shouldBe` Right (Or (Fun x y) z)
    prec "x -> y : z" `shouldBe` Right (Ann (Fun x y) z)
    prec "x -> @y. z" `shouldBe` Right (Fun x (For "y" z))
    prec "x -> y -> z" `shouldBe` Right (Fun x (Fun y z))
    prec "x -> y z" `shouldBe` Right (Fun x (App y z))

  it "☯ CorePrecedence.App" $ do
    prec "x &y. z" `shouldBe` Right (App x (Fix "y" z))
    prec "x y | z" `shouldBe` Right (Or (App x y) z)
    prec "x y : z" `shouldBe` Right (Ann (App x y) z)
    prec' "x @y. z" `shouldBe` Right (x, "remaining: @y. z")
    prec "x (@y. z)" `shouldBe` Right (App x (For "y" z))
    prec "x y -> z" `shouldBe` Right (Fun (App x y) z)
    prec "x y z" `shouldBe` Right (App (App x y) z)
