module TaoPrecedenceTests where

import Parser (State (..))
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--== Tao precedence ==--" $ do
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")

  let prec' :: String -> Either String (Expr, String)
      prec' src = case parse "<TaoPrecedence>" src of
        Right (a, s) | s.remaining /= "" -> Right (dropMeta a, "remaining: " ++ s.remaining)
        Right (a, _) -> Right (dropMeta a, format 80 (dropMeta a))
        Left s -> Left ("syntax error, remaining: " ++ s.remaining)
  let prec :: String -> Either (Expr, String) Expr
      prec src = case prec' src of
        Right (a, out) | src == out -> Right a
        Right (a, out) -> Left (a, out)
        Left err -> Left (Any, err)

  it "☯ TaoPrecedence.Let" $ do
    prec "let x = let y = z\na\nb" `shouldBe` Right (Let (x, Let (y, z) a) b)
    prec "let x = y | z\na" `shouldBe` Right (Let (x, y `Or` z) a)
    prec "let x = y == z\na" `shouldBe` Right (Let (x, y `eq` z) a)
    prec "let x = y != z\na" `shouldBe` Right (Let (x, y `ne` z) a)
    prec "let x = y < z\na" `shouldBe` Right (Let (x, y `lt` z) a)
    prec "let x = y <= z\na" `shouldBe` Right (Let (x, y `le` z) a)
    prec "let x = y > z\na" `shouldBe` Right (Let (x, y `gt` z) a)
    prec "let x = y >= z\na" `shouldBe` Right (Let (x, y `ge` z) a)
    prec "let x = y : z\na" `shouldBe` Right (Let (x, y `Ann` z) a)
    prec "let x = y -> z\na" `shouldBe` Right (Let (x, y `Fun` z) a)
    prec "let x = @y. z\na" `shouldBe` Right (Let (x, For ["y"] z) a)
    prec "let x = y + z\na" `shouldBe` Right (Let (x, y `add` z) a)
    prec "let x = y - z\na" `shouldBe` Right (Let (x, y `sub` z) a)
    prec "let x = y * z\na" `shouldBe` Right (Let (x, y `mul` z) a)
    prec "let x = y / z\na" `shouldBe` Right (Let (x, y `div'` z) a)
    prec "let x = y // z\na" `shouldBe` Right (Let (x, y `divI` z) a)
    prec "let x = y ^ z\na" `shouldBe` Right (Let (x, y `pow` z) a)
    prec "let x = -y\na" `shouldBe` Right (Let (x, neg y) a)
    prec "let x = y(z)\na" `shouldBe` Right (Let (x, y `app1` z) a)

  -- it "☯ TaoPrecedence.Bind" $ do

  it "☯ TaoPrecedence.Or" $ do
    prec "x | y | z" `shouldBe` Right (x `Or` (y `Or` z))
    prec "x | y == z" `shouldBe` Right (x `Or` (y `eq` z))
    prec "x | y != z" `shouldBe` Right (x `Or` (y `ne` z))
    prec "x | y < z" `shouldBe` Right (x `Or` (y `lt` z))
    prec "x | y <= z" `shouldBe` Right (x `Or` (y `le` z))
    prec "x | y > z" `shouldBe` Right (x `Or` (y `gt` z))
    prec "x | y >= z" `shouldBe` Right (x `Or` (y `ge` z))
    prec "x | y : z" `shouldBe` Right (x `Or` (y `Ann` z))
    prec "x | y -> z" `shouldBe` Right (x `Or` (y `Fun` z))
    prec "x | @y. z" `shouldBe` Right (x `Or` For ["y"] z)
    prec "x | y + z" `shouldBe` Right (x `Or` (y `add` z))
    prec "x | y - z" `shouldBe` Right (x `Or` (y `sub` z))
    prec "x | y * z" `shouldBe` Right (x `Or` (y `mul` z))
    prec "x | y / z" `shouldBe` Right (x `Or` (y `div'` z))
    prec "x | y // z" `shouldBe` Right (x `Or` (y `divI` z))
    prec "x | y ^ z" `shouldBe` Right (x `Or` (y `pow` z))
    prec "x | -y" `shouldBe` Right (x `Or` neg y)
    prec "x | y(z)" `shouldBe` Right (x `Or` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Eq" $ do
    prec "x == y | z" `shouldBe` Right (x `eq` y `Or` z)
    prec "x == y == z" `shouldBe` Right (x `eq` y `eq` z)
    prec "x == y != z" `shouldBe` Right (x `eq` y `ne` z)
    prec "x == y < z" `shouldBe` Right (x `eq` (y `lt` z))
    prec "x == y <= z" `shouldBe` Right (x `eq` (y `le` z))
    prec "x == y > z" `shouldBe` Right (x `eq` (y `gt` z))
    prec "x == y >= z" `shouldBe` Right (x `eq` (y `ge` z))
    prec "x == y : z" `shouldBe` Right (x `eq` (y `Ann` z))
    prec "x == y -> z" `shouldBe` Right (x `eq` (y `Fun` z))
    prec "x == @y. z" `shouldBe` Right (x `eq` For ["y"] z)
    prec "x == y + z" `shouldBe` Right (x `eq` (y `add` z))
    prec "x == y - z" `shouldBe` Right (x `eq` (y `sub` z))
    prec "x == y * z" `shouldBe` Right (x `eq` (y `mul` z))
    prec "x == y / z" `shouldBe` Right (x `eq` (y `div'` z))
    prec "x == y // z" `shouldBe` Right (x `eq` (y `divI` z))
    prec "x == y ^ z" `shouldBe` Right (x `eq` (y `pow` z))
    prec "x == -y" `shouldBe` Right (x `eq` neg y)
    prec "x == y(z)" `shouldBe` Right (x `eq` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Ne" $ do
    prec "x != y | z" `shouldBe` Right (x `ne` y `Or` z)
    prec "x != y == z" `shouldBe` Right (x `ne` y `eq` z)
    prec "x != y != z" `shouldBe` Right (x `ne` y `ne` z)
    prec "x != y < z" `shouldBe` Right (x `ne` (y `lt` z))
    prec "x != y <= z" `shouldBe` Right (x `ne` (y `le` z))
    prec "x != y > z" `shouldBe` Right (x `ne` (y `gt` z))
    prec "x != y >= z" `shouldBe` Right (x `ne` (y `ge` z))
    prec "x != y : z" `shouldBe` Right (x `ne` (y `Ann` z))
    prec "x != y -> z" `shouldBe` Right (x `ne` (y `Fun` z))
    prec "x != @y. z" `shouldBe` Right (x `ne` For ["y"] z)
    prec "x != y + z" `shouldBe` Right (x `ne` (y `add` z))
    prec "x != y - z" `shouldBe` Right (x `ne` (y `sub` z))
    prec "x != y * z" `shouldBe` Right (x `ne` (y `mul` z))
    prec "x != y / z" `shouldBe` Right (x `ne` (y `div'` z))
    prec "x != y // z" `shouldBe` Right (x `ne` (y `divI` z))
    prec "x != y ^ z" `shouldBe` Right (x `ne` (y `pow` z))
    prec "x != -y" `shouldBe` Right (x `ne` neg y)
    prec "x != y(z)" `shouldBe` Right (x `ne` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Lt" $ do
    prec "x < y | z" `shouldBe` Right (x `lt` y `Or` z)
    prec "x < y == z" `shouldBe` Right (x `lt` y `eq` z)
    prec "x < y != z" `shouldBe` Right (x `lt` y `ne` z)
    prec "x < y < z" `shouldBe` Right (x `lt` y `lt` z)
    prec "x < y <= z" `shouldBe` Right (x `lt` y `le` z)
    prec "x < y > z" `shouldBe` Right (x `lt` y `gt` z)
    prec "x < y >= z" `shouldBe` Right (x `lt` y `ge` z)
    prec "x < y : z" `shouldBe` Right (x `lt` (y `Ann` z))
    prec "x < y -> z" `shouldBe` Right (x `lt` (y `Fun` z))
    prec "x < @y. z" `shouldBe` Right (x `lt` For ["y"] z)
    prec "x < y + z" `shouldBe` Right (x `lt` (y `add` z))
    prec "x < y - z" `shouldBe` Right (x `lt` (y `sub` z))
    prec "x < y * z" `shouldBe` Right (x `lt` (y `mul` z))
    prec "x < y / z" `shouldBe` Right (x `lt` (y `div'` z))
    prec "x < y // z" `shouldBe` Right (x `lt` (y `divI` z))
    prec "x < y ^ z" `shouldBe` Right (x `lt` (y `pow` z))
    prec "x < -y" `shouldBe` Right (x `lt` neg y)
    prec "x < y(z)" `shouldBe` Right (x `lt` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Le" $ do
    prec "x <= y | z" `shouldBe` Right (x `le` y `Or` z)
    prec "x <= y == z" `shouldBe` Right (x `le` y `eq` z)
    prec "x <= y != z" `shouldBe` Right (x `le` y `ne` z)
    prec "x <= y < z" `shouldBe` Right (x `le` y `lt` z)
    prec "x <= y <= z" `shouldBe` Right (x `le` y `le` z)
    prec "x <= y > z" `shouldBe` Right (x `le` y `gt` z)
    prec "x <= y >= z" `shouldBe` Right (x `le` y `ge` z)
    prec "x <= y : z" `shouldBe` Right (x `le` (y `Ann` z))
    prec "x <= y -> z" `shouldBe` Right (x `le` (y `Fun` z))
    prec "x <= @y. z" `shouldBe` Right (x `le` For ["y"] z)
    prec "x <= y + z" `shouldBe` Right (x `le` (y `add` z))
    prec "x <= y - z" `shouldBe` Right (x `le` (y `sub` z))
    prec "x <= y * z" `shouldBe` Right (x `le` (y `mul` z))
    prec "x <= y / z" `shouldBe` Right (x `le` (y `div'` z))
    prec "x <= y // z" `shouldBe` Right (x `le` (y `divI` z))
    prec "x <= y ^ z" `shouldBe` Right (x `le` (y `pow` z))
    prec "x <= -y" `shouldBe` Right (x `le` neg y)
    prec "x <= y(z)" `shouldBe` Right (x `le` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Gt" $ do
    prec "x > y | z" `shouldBe` Right (x `gt` y `Or` z)
    prec "x > y == z" `shouldBe` Right (x `gt` y `eq` z)
    prec "x > y != z" `shouldBe` Right (x `gt` y `ne` z)
    prec "x > y < z" `shouldBe` Right (x `gt` y `lt` z)
    prec "x > y <= z" `shouldBe` Right (x `gt` y `le` z)
    prec "x > y > z" `shouldBe` Right (x `gt` y `gt` z)
    prec "x > y >= z" `shouldBe` Right (x `gt` y `ge` z)
    prec "x > y : z" `shouldBe` Right (x `gt` (y `Ann` z))
    prec "x > y -> z" `shouldBe` Right (x `gt` (y `Fun` z))
    prec "x > @y. z" `shouldBe` Right (x `gt` For ["y"] z)
    prec "x > y + z" `shouldBe` Right (x `gt` (y `add` z))
    prec "x > y - z" `shouldBe` Right (x `gt` (y `sub` z))
    prec "x > y * z" `shouldBe` Right (x `gt` (y `mul` z))
    prec "x > y / z" `shouldBe` Right (x `gt` (y `div'` z))
    prec "x > y // z" `shouldBe` Right (x `gt` (y `divI` z))
    prec "x > y ^ z" `shouldBe` Right (x `gt` (y `pow` z))
    prec "x > -y" `shouldBe` Right (x `gt` neg y)
    prec "x > y(z)" `shouldBe` Right (x `gt` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Ge" $ do
    prec "x >= y | z" `shouldBe` Right (x `ge` y `Or` z)
    prec "x >= y == z" `shouldBe` Right (x `ge` y `eq` z)
    prec "x >= y != z" `shouldBe` Right (x `ge` y `ne` z)
    prec "x >= y < z" `shouldBe` Right (x `ge` y `lt` z)
    prec "x >= y <= z" `shouldBe` Right (x `ge` y `le` z)
    prec "x >= y > z" `shouldBe` Right (x `ge` y `gt` z)
    prec "x >= y >= z" `shouldBe` Right (x `ge` y `ge` z)
    prec "x >= y : z" `shouldBe` Right (x `ge` (y `Ann` z))
    prec "x >= y -> z" `shouldBe` Right (x `ge` (y `Fun` z))
    prec "x >= @y. z" `shouldBe` Right (x `ge` For ["y"] z)
    prec "x >= y + z" `shouldBe` Right (x `ge` (y `add` z))
    prec "x >= y - z" `shouldBe` Right (x `ge` (y `sub` z))
    prec "x >= y * z" `shouldBe` Right (x `ge` (y `mul` z))
    prec "x >= y / z" `shouldBe` Right (x `ge` (y `div'` z))
    prec "x >= y // z" `shouldBe` Right (x `ge` (y `divI` z))
    prec "x >= y ^ z" `shouldBe` Right (x `ge` (y `pow` z))
    prec "x >= -y" `shouldBe` Right (x `ge` neg y)
    prec "x >= y(z)" `shouldBe` Right (x `ge` (y `app1` z))

  it "☯ TaoPrecedence.Ann" $ do
    prec "x : y | z" `shouldBe` Right (x `Ann` y `Or` z)
    prec "x : y == z" `shouldBe` Right (x `Ann` y `eq` z)
    prec "x : y != z" `shouldBe` Right (x `Ann` y `ne` z)
    prec "x : y < z" `shouldBe` Right (x `Ann` y `lt` z)
    prec "x : y <= z" `shouldBe` Right (x `Ann` y `le` z)
    prec "x : y > z" `shouldBe` Right (x `Ann` y `gt` z)
    prec "x : y >= z" `shouldBe` Right (x `Ann` y `ge` z)
    prec "x : y : z" `shouldBe` Right (x `Ann` (y `Ann` z))
    prec "x : y -> z" `shouldBe` Right (x `Ann` (y `Fun` z))
    prec "x : @y. z" `shouldBe` Right (x `Ann` For ["y"] z)
    prec "x : y + z" `shouldBe` Right (x `Ann` (y `add` z))
    prec "x : y - z" `shouldBe` Right (x `Ann` (y `sub` z))
    prec "x : y * z" `shouldBe` Right (x `Ann` (y `mul` z))
    prec "x : y / z" `shouldBe` Right (x `Ann` (y `div'` z))
    prec "x : y // z" `shouldBe` Right (x `Ann` (y `divI` z))
    prec "x : y ^ z" `shouldBe` Right (x `Ann` (y `pow` z))
    prec "x : -y" `shouldBe` Right (x `Ann` neg y)
    prec "x : y(z)" `shouldBe` Right (x `Ann` (y `app1` z))

  it "☯ TaoPrecedence.Fun" $ do
    prec "x -> y | z" `shouldBe` Right (x `Fun` y `Or` z)
    prec "x -> y == z" `shouldBe` Right (x `Fun` y `eq` z)
    prec "x -> y != z" `shouldBe` Right (x `Fun` y `ne` z)
    prec "x -> y < z" `shouldBe` Right (x `Fun` y `lt` z)
    prec "x -> y <= z" `shouldBe` Right (x `Fun` y `le` z)
    prec "x -> y > z" `shouldBe` Right (x `Fun` y `gt` z)
    prec "x -> y >= z" `shouldBe` Right (x `Fun` y `ge` z)
    prec "x -> y : z" `shouldBe` Right (x `Fun` y `Ann` z)
    prec "x -> y -> z" `shouldBe` Right (x `Fun` (y `Fun` z))
    prec "x -> @y. z" `shouldBe` Right (x `Fun` For ["y"] z)
    prec "x -> y + z" `shouldBe` Right (x `Fun` (y `add` z))
    prec "x -> y - z" `shouldBe` Right (x `Fun` (y `sub` z))
    prec "x -> y * z" `shouldBe` Right (x `Fun` (y `mul` z))
    prec "x -> y / z" `shouldBe` Right (x `Fun` (y `div'` z))
    prec "x -> y // z" `shouldBe` Right (x `Fun` (y `divI` z))
    prec "x -> y ^ z" `shouldBe` Right (x `Fun` (y `pow` z))
    prec "x -> -y" `shouldBe` Right (x `Fun` neg y)
    prec "x -> y(z)" `shouldBe` Right (x `Fun` (y `app1` z))

  it "☯ TaoPrecedence.For" $ do
    prec "@x. y | z" `shouldBe` Right (For ["x"] y `Or` z)
    prec "@x. y == z" `shouldBe` Right (For ["x"] y `eq` z)
    prec "@x. y != z" `shouldBe` Right (For ["x"] y `ne` z)
    prec "@x. y < z" `shouldBe` Right (For ["x"] y `lt` z)
    prec "@x. y <= z" `shouldBe` Right (For ["x"] y `le` z)
    prec "@x. y > z" `shouldBe` Right (For ["x"] y `gt` z)
    prec "@x. y >= z" `shouldBe` Right (For ["x"] y `ge` z)
    prec "@x. y : z" `shouldBe` Right (For ["x"] y `Ann` z)
    prec "@x. y -> z" `shouldBe` Right (For ["x"] y `Fun` z)
    prec "@x. @y. z" `shouldBe` Right (For ["x"] (For ["y"] z))
    prec "@x. y + z" `shouldBe` Right (For ["x"] (add y z))
    prec "@x. y - z" `shouldBe` Right (For ["x"] (sub y z))
    prec "@x. y * z" `shouldBe` Right (For ["x"] (mul y z))
    prec "@x. y / z" `shouldBe` Right (For ["x"] (div' y z))
    prec "@x. y // z" `shouldBe` Right (For ["x"] (divI y z))
    prec "@x. y ^ z" `shouldBe` Right (For ["x"] (pow y z))
    prec "@x. -y" `shouldBe` Right (For ["x"] (neg y))
    prec "@x. y(z)" `shouldBe` Right (For ["x"] (app1 y z))

  it "☯ TaoPrecedence.Op2.Add" $ do
    prec "x + y | z" `shouldBe` Right (x `add` y `Or` z)
    prec "x + y == z" `shouldBe` Right (x `add` y `eq` z)
    prec "x + y != z" `shouldBe` Right (x `add` y `ne` z)
    prec "x + y < z" `shouldBe` Right (x `add` y `lt` z)
    prec "x + y <= z" `shouldBe` Right (x `add` y `le` z)
    prec "x + y > z" `shouldBe` Right (x `add` y `gt` z)
    prec "x + y >= z" `shouldBe` Right (x `add` y `ge` z)
    prec "x + y : z" `shouldBe` Right (x `add` y `Ann` z)
    prec "x + y -> z" `shouldBe` Right (x `add` y `Fun` z)
    prec "x + (@y. z)" `shouldBe` Right (x `add` For ["y"] z)
    prec "x + y + z" `shouldBe` Right (x `add` y `add` z)
    prec "x + y - z" `shouldBe` Right (x `add` y `sub` z)
    prec "x + y * z" `shouldBe` Right (x `add` (y `mul` z))
    prec "x + y / z" `shouldBe` Right (x `add` (y `div'` z))
    prec "x + y // z" `shouldBe` Right (x `add` (y `divI` z))
    prec "x + y ^ z" `shouldBe` Right (x `add` (y `pow` z))
    prec "x + -y" `shouldBe` Right (x `add` neg y)
    prec "x + y(z)" `shouldBe` Right (x `add` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Sub" $ do
    prec "x - y | z" `shouldBe` Right (x `sub` y `Or` z)
    prec "x - y == z" `shouldBe` Right (x `sub` y `eq` z)
    prec "x - y != z" `shouldBe` Right (x `sub` y `ne` z)
    prec "x - y < z" `shouldBe` Right (x `sub` y `lt` z)
    prec "x - y <= z" `shouldBe` Right (x `sub` y `le` z)
    prec "x - y > z" `shouldBe` Right (x `sub` y `gt` z)
    prec "x - y >= z" `shouldBe` Right (x `sub` y `ge` z)
    prec "x - y : z" `shouldBe` Right (x `sub` y `Ann` z)
    prec "x - y -> z" `shouldBe` Right (x `sub` y `Fun` z)
    prec "x - (@y. z)" `shouldBe` Right (x `sub` For ["y"] z)
    prec "x - y + z" `shouldBe` Right (x `sub` y `add` z)
    prec "x - y - z" `shouldBe` Right (x `sub` y `sub` z)
    prec "x - y * z" `shouldBe` Right (x `sub` (y `mul` z))
    prec "x - y / z" `shouldBe` Right (x `sub` (y `div'` z))
    prec "x - y // z" `shouldBe` Right (x `sub` (y `divI` z))
    prec "x - y ^ z" `shouldBe` Right (x `sub` (y `pow` z))
    prec "x - -y" `shouldBe` Right (x `sub` neg y)
    prec "x - y(z)" `shouldBe` Right (x `sub` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Mul" $ do
    prec "x * y | z" `shouldBe` Right (x `mul` y `Or` z)
    prec "x * y == z" `shouldBe` Right (x `mul` y `eq` z)
    prec "x * y != z" `shouldBe` Right (x `mul` y `ne` z)
    prec "x * y < z" `shouldBe` Right (x `mul` y `lt` z)
    prec "x * y <= z" `shouldBe` Right (x `mul` y `le` z)
    prec "x * y > z" `shouldBe` Right (x `mul` y `gt` z)
    prec "x * y >= z" `shouldBe` Right (x `mul` y `ge` z)
    prec "x * y : z" `shouldBe` Right (x `mul` y `Ann` z)
    prec "x * y -> z" `shouldBe` Right (x `mul` y `Fun` z)
    prec "x * (@y. z)" `shouldBe` Right (x `mul` For ["y"] z)
    prec "x * y + z" `shouldBe` Right (x `mul` y `add` z)
    prec "x * y - z" `shouldBe` Right (x `mul` y `sub` z)
    prec "x * y * z" `shouldBe` Right (x `mul` y `mul` z)
    prec "x * y / z" `shouldBe` Right (x `mul` y `div'` z)
    prec "x * y // z" `shouldBe` Right (x `mul` y `divI` z)
    prec "x * y ^ z" `shouldBe` Right (x `mul` (y `pow` z))
    prec "x * -y" `shouldBe` Right (x `mul` neg y)
    prec "x * y(z)" `shouldBe` Right (x `mul` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Div" $ do
    prec "x / y | z" `shouldBe` Right (x `div'` y `Or` z)
    prec "x / y == z" `shouldBe` Right (x `div'` y `eq` z)
    prec "x / y != z" `shouldBe` Right (x `div'` y `ne` z)
    prec "x / y < z" `shouldBe` Right (x `div'` y `lt` z)
    prec "x / y <= z" `shouldBe` Right (x `div'` y `le` z)
    prec "x / y > z" `shouldBe` Right (x `div'` y `gt` z)
    prec "x / y >= z" `shouldBe` Right (x `div'` y `ge` z)
    prec "x / y : z" `shouldBe` Right (x `div'` y `Ann` z)
    prec "x / y -> z" `shouldBe` Right (x `div'` y `Fun` z)
    prec "x / (@y. z)" `shouldBe` Right (x `div'` For ["y"] z)
    prec "x / y + z" `shouldBe` Right (x `div'` y `add` z)
    prec "x / y - z" `shouldBe` Right (x `div'` y `sub` z)
    prec "x / y * z" `shouldBe` Right (x `div'` y `mul` z)
    prec "x / y / z" `shouldBe` Right (x `div'` y `div'` z)
    prec "x / y // z" `shouldBe` Right (x `div'` y `divI` z)
    prec "x / y ^ z" `shouldBe` Right (x `div'` (y `pow` z))
    prec "x / -y" `shouldBe` Right (x `div'` neg y)
    prec "x / y(z)" `shouldBe` Right (x `div'` (y `app1` z))

  it "☯ TaoPrecedence.Op2.DivI" $ do
    prec "x // y | z" `shouldBe` Right (x `divI` y `Or` z)
    prec "x // y == z" `shouldBe` Right (x `divI` y `eq` z)
    prec "x // y != z" `shouldBe` Right (x `divI` y `ne` z)
    prec "x // y < z" `shouldBe` Right (x `divI` y `lt` z)
    prec "x // y <= z" `shouldBe` Right (x `divI` y `le` z)
    prec "x // y > z" `shouldBe` Right (x `divI` y `gt` z)
    prec "x // y >= z" `shouldBe` Right (x `divI` y `ge` z)
    prec "x // y : z" `shouldBe` Right (x `divI` y `Ann` z)
    prec "x // y -> z" `shouldBe` Right (x `divI` y `Fun` z)
    prec "x // (@y. z)" `shouldBe` Right (x `divI` For ["y"] z)
    prec "x // y + z" `shouldBe` Right (x `divI` y `add` z)
    prec "x // y - z" `shouldBe` Right (x `divI` y `sub` z)
    prec "x // y * z" `shouldBe` Right (x `divI` y `mul` z)
    prec "x // y / z" `shouldBe` Right (x `divI` y `div'` z)
    prec "x // y // z" `shouldBe` Right (x `divI` y `divI` z)
    prec "x // y ^ z" `shouldBe` Right (x `divI` (y `pow` z))
    prec "x // -y" `shouldBe` Right (x `divI` neg y)
    prec "x // y(z)" `shouldBe` Right (x `divI` (y `app1` z))

  it "☯ TaoPrecedence.Op2.Pow" $ do
    prec "x ^ y | z" `shouldBe` Right (x `pow` y `Or` z)
    prec "x ^ y == z" `shouldBe` Right (x `pow` y `eq` z)
    prec "x ^ y != z" `shouldBe` Right (x `pow` y `ne` z)
    prec "x ^ y < z" `shouldBe` Right (x `pow` y `lt` z)
    prec "x ^ y <= z" `shouldBe` Right (x `pow` y `le` z)
    prec "x ^ y > z" `shouldBe` Right (x `pow` y `gt` z)
    prec "x ^ y >= z" `shouldBe` Right (x `pow` y `ge` z)
    prec "x ^ y : z" `shouldBe` Right (x `pow` y `Ann` z)
    prec "x ^ y -> z" `shouldBe` Right (x `pow` y `Fun` z)
    prec "x ^ (@y. z)" `shouldBe` Right (x `pow` For ["y"] z)
    prec "x ^ y + z" `shouldBe` Right (x `pow` y `add` z)
    prec "x ^ y - z" `shouldBe` Right (x `pow` y `sub` z)
    prec "x ^ y * z" `shouldBe` Right (x `pow` y `mul` z)
    prec "x ^ y / z" `shouldBe` Right (x `pow` y `div'` z)
    prec "x ^ y // z" `shouldBe` Right (x `pow` y `divI` z)
    prec "x ^ y ^ z" `shouldBe` Right (x `pow` (y `pow` z))
    prec "x ^ -y" `shouldBe` Right (x `pow` neg y)
    prec "x ^ y(z)" `shouldBe` Right (x `pow` (y `app1` z))

  it "☯ TaoPrecedence.Op1.Neg" $ do
    prec "-x | y" `shouldBe` Right (neg x `Or` y)
    prec "-x == y" `shouldBe` Right (neg x `eq` y)
    prec "-x != y" `shouldBe` Right (neg x `ne` y)
    prec "-x < y" `shouldBe` Right (neg x `lt` y)
    prec "-x <= y" `shouldBe` Right (neg x `le` y)
    prec "-x > y" `shouldBe` Right (neg x `gt` y)
    prec "-x >= y" `shouldBe` Right (neg x `ge` y)
    prec "-x : y" `shouldBe` Right (neg x `Ann` y)
    prec "-x -> y" `shouldBe` Right (neg x `Fun` y)
    prec "-(@x. y)" `shouldBe` Right (neg (For ["x"] y))
    prec "-x + y" `shouldBe` Right (neg x `add` y)
    prec "-x - y" `shouldBe` Right (neg x `sub` y)
    prec "-x * y" `shouldBe` Right (neg x `mul` y)
    prec "-x / y" `shouldBe` Right (neg x `div'` y)
    prec "-x // y" `shouldBe` Right (neg x `divI` y)
    prec "-x ^ y" `shouldBe` Right (neg x `pow` y)
    prec "-x(y)" `shouldBe` Right (neg x `app1` y)

  it "☯ TaoPrecedence.App" $ do
    prec "x(y) | z" `shouldBe` Right (x `app1` y `Or` z)
    prec "x(y) == z" `shouldBe` Right (x `app1` y `eq` z)
    prec "x(y) != z" `shouldBe` Right (x `app1` y `ne` z)
    prec "x(y) < z" `shouldBe` Right (x `app1` y `lt` z)
    prec "x(y) <= z" `shouldBe` Right (x `app1` y `le` z)
    prec "x(y) > z" `shouldBe` Right (x `app1` y `gt` z)
    prec "x(y) >= z" `shouldBe` Right (x `app1` y `ge` z)
    prec "x(y) : z" `shouldBe` Right (x `app1` y `Ann` z)
    prec "x(y) -> z" `shouldBe` Right (x `app1` y `Fun` z)
    prec "x(@y. z)" `shouldBe` Right (x `app1` For ["y"] z)
    prec "x(y) + z" `shouldBe` Right (x `app1` y `add` z)
    prec "x(y) - z" `shouldBe` Right (x `app1` y `sub` z)
    prec "x(y) * z" `shouldBe` Right (x `app1` y `mul` z)
    prec "x(y) / z" `shouldBe` Right (x `app1` y `div'` z)
    prec "x(y) // z" `shouldBe` Right (x `app1` y `divI` z)
    prec "x(y) ^ z" `shouldBe` Right (x `app1` y `pow` z)
    prec "x(y)(z)" `shouldBe` Right (x `app1` y `app1` z)

-- Metadata.TrailingComment
