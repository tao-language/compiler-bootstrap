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

  -- it "☯ TaoPrecedence.Bind" $ do

  it "☯ TaoPrecedence.Or" $ do
    prec "x | y | z" `shouldBe` Right (x `Or` (y `Or` z))
    prec "x | y <| z" `shouldBe` Right (x `Or` (y `pipeL` z))

  it "☯ TaoPrecedence.Op2.PipeL" $ do
    prec "x <| y | z" `shouldBe` Right ((x `pipeL` y) `Or` z)
    prec "x <| y <| z" `shouldBe` Right (x `pipeL` (y `pipeL` z))
    prec "x <| y |> z" `shouldBe` Right (x `pipeL` (y `pipeR` z))

  it "☯ TaoPrecedence.Op2.PipeR" $ do
    prec "x |> y <| z" `shouldBe` Right ((x `pipeR` y) `pipeL` z)
    prec "x |> y |> z" `shouldBe` Right ((x `pipeR` y) `pipeR` z)
    prec "x |> y << z" `shouldBe` Right (x `pipeR` (y `shiftL` z))

  it "☯ TaoPrecedence.Op2.ShiftL" $ do
    prec "x << y |> z" `shouldBe` Right ((x `shiftL` y) `pipeR` z)
    prec "x << y << z" `shouldBe` Right (x `shiftL` (y `shiftL` z))
    prec "x << y >> z" `shouldBe` Right (x `shiftL` (y `shiftR` z))

  it "☯ TaoPrecedence.Op2.ShiftR" $ do
    prec "x >> y << z" `shouldBe` Right ((x `shiftR` y) `shiftL` z)
    prec "x >> y >> z" `shouldBe` Right ((x `shiftR` y) `shiftR` z)
    prec "x >> y : z" `shouldBe` Right (x `shiftR` (y `Ann` z))

  it "☯ TaoPrecedence.Ann" $ do
    prec "x : y |> z" `shouldBe` Right ((x `Ann` y) `pipeR` z)
    prec "x : y : z" `shouldBe` Right (x `Ann` (y `Ann` z))
    prec "x : y -> z" `shouldBe` Right (x `Ann` (y `Fun` z))

  it "☯ TaoPrecedence.Fun" $ do
    prec "x -> y : z" `shouldBe` Right ((x `Fun` y) `Ann` z)
    prec "x -> y -> z" `shouldBe` Right (x `Fun` (y `Fun` z))
    prec "x -> y if z" `shouldBe` Right (x `Fun` (y `If` z))

  it "☯ TaoPrecedence.If" $ do
    prec "x if y -> z" `shouldBe` Right ((x `If` y) `Fun` z)
    prec "x if y if z" `shouldBe` Right (x `If` (y `If` z))
    prec "x if y or z" `shouldBe` Right (x `If` (y `orOp` z))

  it "☯ TaoPrecedence.Op2.Or" $ do
    prec "x or y if z" `shouldBe` Right ((x `orOp` y) `If` z)
    prec "x or y or z" `shouldBe` Right ((x `orOp` y) `orOp` z)
    prec "x or y xor z" `shouldBe` Right ((x `orOp` y) `xorOp` z)
    prec "x or y and z" `shouldBe` Right (x `orOp` (y `andOp` z))

  it "☯ TaoPrecedence.Op2.Xor" $ do
    prec "x xor y if z" `shouldBe` Right ((x `xorOp` y) `If` z)
    prec "x xor y or z" `shouldBe` Right ((x `xorOp` y) `orOp` z)
    prec "x xor y xor z" `shouldBe` Right ((x `xorOp` y) `xorOp` z)
    prec "x xor y and z" `shouldBe` Right (x `xorOp` (y `andOp` z))

  it "☯ TaoPrecedence.Op2.And" $ do
    prec "x and y or z" `shouldBe` Right ((x `andOp` y) `orOp` z)
    prec "x and y xor z" `shouldBe` Right ((x `andOp` y) `xorOp` z)
    prec "x and y and z" `shouldBe` Right ((x `andOp` y) `andOp` z)
    prec "x and y == z" `shouldBe` Right (x `andOp` (y `eq` z))

  it "☯ TaoPrecedence.Op2.Eq" $ do
    prec "x == y and z" `shouldBe` Right ((x `eq` y) `andOp` z)
    prec "x == y == z" `shouldBe` Right ((x `eq` y) `eq` z)
    prec "x == y != z" `shouldBe` Right ((x `eq` y) `ne` z)
    prec "x == y < z" `shouldBe` Right (x `eq` (y `lt` z))

  it "☯ TaoPrecedence.Op2.Ne" $ do
    prec "x != y and z" `shouldBe` Right ((x `ne` y) `andOp` z)
    prec "x != y == z" `shouldBe` Right ((x `ne` y) `eq` z)
    prec "x != y != z" `shouldBe` Right ((x `ne` y) `ne` z)
    prec "x != y < z" `shouldBe` Right (x `ne` (y `lt` z))

  it "☯ TaoPrecedence.Op2.Lt" $ do
    prec "x < y == z" `shouldBe` Right ((x `lt` y) `eq` z)
    prec "x < y < z" `shouldBe` Right ((x `lt` y) `lt` z)
    prec "x < y <= z" `shouldBe` Right ((x `lt` y) `le` z)
    prec "x < y > z" `shouldBe` Right ((x `lt` y) `gt` z)
    prec "x < y >= z" `shouldBe` Right ((x `lt` y) `ge` z)
    prec "x < y :: z" `shouldBe` Right (x `lt` (y `cons` z))

  it "☯ TaoPrecedence.Op2.Le" $ do
    prec "x <= y == z" `shouldBe` Right ((x `le` y) `eq` z)
    prec "x <= y < z" `shouldBe` Right ((x `le` y) `lt` z)
    prec "x <= y <= z" `shouldBe` Right ((x `le` y) `le` z)
    prec "x <= y > z" `shouldBe` Right ((x `le` y) `gt` z)
    prec "x <= y >= z" `shouldBe` Right ((x `le` y) `ge` z)
    prec "x <= y :: z" `shouldBe` Right (x `le` (y `cons` z))

  it "☯ TaoPrecedence.Op2.Gt" $ do
    prec "x > y == z" `shouldBe` Right ((x `gt` y) `eq` z)
    prec "x > y < z" `shouldBe` Right ((x `gt` y) `lt` z)
    prec "x > y <= z" `shouldBe` Right ((x `gt` y) `le` z)
    prec "x > y > z" `shouldBe` Right ((x `gt` y) `gt` z)
    prec "x > y >= z" `shouldBe` Right ((x `gt` y) `ge` z)
    prec "x > y :: z" `shouldBe` Right (x `gt` (y `cons` z))

  it "☯ TaoPrecedence.Op2.Ge" $ do
    prec "x >= y == z" `shouldBe` Right ((x `ge` y) `eq` z)
    prec "x >= y < z" `shouldBe` Right ((x `ge` y) `lt` z)
    prec "x >= y <= z" `shouldBe` Right ((x `ge` y) `le` z)
    prec "x >= y > z" `shouldBe` Right ((x `ge` y) `gt` z)
    prec "x >= y >= z" `shouldBe` Right ((x `ge` y) `ge` z)
    prec "x >= y :: z" `shouldBe` Right (x `ge` (y `cons` z))

  it "☯ TaoPrecedence.Op2.Cons" $ do
    prec "x :: y < z" `shouldBe` Right ((x `cons` y) `lt` z)
    prec "x :: y :: z" `shouldBe` Right (x `cons` (y `cons` z))
    prec "x :: y + z" `shouldBe` Right (x `cons` (y `add` z))

  it "☯ TaoPrecedence.For" $ do
    prec "@x. y :: z" `shouldBe` Right (For ["x"] (y `cons` z))
    prec "@x. @y. z" `shouldBe` Right (For ["x"] (For ["y"] z))
    prec "@x. y + z" `shouldBe` Right (For ["x"] (y `add` z))

  it "☯ TaoPrecedence.Op2.Add" $ do
    prec "x + y :: z" `shouldBe` Right ((x `add` y) `cons` z)
    prec "x + @y. z" `shouldBe` Right (x `add` (For ["y"] z))
    prec "x + y + z" `shouldBe` Right ((x `add` y) `add` z)
    prec "x + y - z" `shouldBe` Right ((x `add` y) `sub` z)
    prec "x + y * z" `shouldBe` Right (x `add` (y `mul` z))

  it "☯ TaoPrecedence.Op2.Sub" $ do
    prec "x - y :: z" `shouldBe` Right ((x `sub` y) `cons` z)
    prec "x - y + z" `shouldBe` Right ((x `sub` y) `add` z)
    prec "x - y - z" `shouldBe` Right ((x `sub` y) `sub` z)
    prec "x - y * z" `shouldBe` Right (x `sub` (y `mul` z))

  it "☯ TaoPrecedence.Op2.Mul" $ do
    prec "x * y + z" `shouldBe` Right ((x `mul` y) `add` z)
    prec "x * y * z" `shouldBe` Right ((x `mul` y) `mul` z)
    prec "x * y / z" `shouldBe` Right ((x `mul` y) `div'` z)
    prec "x * y // z" `shouldBe` Right ((x `mul` y) `div2` z)
    prec "x * y ^ z" `shouldBe` Right (x `mul` (y `pow` z))

  it "☯ TaoPrecedence.Op2.Div" $ do
    prec "x / y + z" `shouldBe` Right ((x `div'` y) `add` z)
    prec "x / y * z" `shouldBe` Right ((x `div'` y) `mul` z)
    prec "x / y / z" `shouldBe` Right ((x `div'` y) `div'` z)
    prec "x / y // z" `shouldBe` Right ((x `div'` y) `div2` z)
    prec "x / y ^ z" `shouldBe` Right (x `div'` (y `pow` z))

  it "☯ TaoPrecedence.Op2.Div2" $ do
    prec "x // y + z" `shouldBe` Right ((x `div2` y) `add` z)
    prec "x // y * z" `shouldBe` Right ((x `div2` y) `mul` z)
    prec "x // y / z" `shouldBe` Right ((x `div2` y) `div'` z)
    prec "x // y // z" `shouldBe` Right ((x `div2` y) `div2` z)
    prec "x // y ^ z" `shouldBe` Right (x `div2` (y `pow` z))

  it "☯ TaoPrecedence.Op2.Pow" $ do
    prec "x ^ y * z" `shouldBe` Right ((x `pow` y) `mul` z)
    prec "x ^ y ^ z" `shouldBe` Right (x `pow` (y `pow` z))
    prec "x ^ y(z)" `shouldBe` Right (x `pow` (y `app1` z))

  it "☯ TaoPrecedence.Op1.Neg" $ do
    prec "-@x. y" `shouldBe` Right (neg (For ["x"] y))
    prec "--x" `shouldBe` Right (neg (neg x))
    prec "-x(y)" `shouldBe` Right (neg x `app1` y)

  it "☯ TaoPrecedence.App" $ do
    prec "x(y) ^ z" `shouldBe` Right ((x `app1` y) `pow` z)
    prec "x(y)(z)" `shouldBe` Right ((x `app1` y) `app1` z)

-- Metadata.TrailingComment
