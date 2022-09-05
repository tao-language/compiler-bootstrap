module TaoTests where

import Core
import Parser
import Tao
import Test.Hspec

taoTests :: SpecWith ()
taoTests = describe "--==☯ Tao language ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x_, y_, z_) = (PAs PAny "x", PAs PAny "y", PAs PAny "z")
  let parse' src parser = case Parser.parse src parser of
        Right x -> Just x
        Left _ -> Nothing

  it "☯ variableName" $ do
    parse' "" variableName `shouldBe` Nothing
    parse' "a" variableName `shouldBe` Just "a"
    parse' "a1" variableName `shouldBe` Just "a1"

  it "☯ constructorName" $ do
    parse' "" constructorName `shouldBe` Nothing
    parse' "A" constructorName `shouldBe` Just "A"
    parse' "A1" constructorName `shouldBe` Just "A1"

  it "☯ comment" $ do
    let comment' src = parse' src comment
    comment' "" `shouldBe` Nothing
    comment' "--my comment" `shouldBe` Just "my comment"
    comment' "-- my comment" `shouldBe` Just "my comment"
    comment' "--   my  comment  " `shouldBe` Just "  my  comment  "

  it "☯ emptyLine" $ do
    let emptyLine' src = parse' src emptyLine
    emptyLine' "" `shouldBe` Nothing
    emptyLine' "\n" `shouldBe` Just ""
    emptyLine' "  \n" `shouldBe` Just ""
    emptyLine' "  --my comment\n" `shouldBe` Just "my comment"
    emptyLine' "  -- my comment\n" `shouldBe` Just "my comment"
    emptyLine' "  --   my  comment  \n" `shouldBe` Just "  my  comment  "

  it "☯ newLine" $ do
    let indent = "  "
    let newLine' src = parse' src (do _ <- newLine indent; letter)
    newLine' "" `shouldBe` Nothing
    newLine' "   " `shouldBe` Nothing
    newLine' "\nx" `shouldBe` Nothing
    newLine' "\n x" `shouldBe` Nothing
    newLine' "\n  x" `shouldBe` Just 'x'
    newLine' "\n   x" `shouldBe` Nothing
    newLine' "\n\n   \n  x" `shouldBe` Just 'x'
    newLine' "\n -- comment\n  x" `shouldBe` Just 'x'

  it "☯ continueLine" $ do
    let indent = "  "
    let continueLine' src = parse' src (continueLine indent)
    continueLine' "" `shouldBe` Just "  "
    continueLine' "\n" `shouldBe` Just "  "
    continueLine' "\n  " `shouldBe` Just "  "
    continueLine' "\n   " `shouldBe` Just "   "
    continueLine' "\n    " `shouldBe` Just "    "

  it "☯ operator" $ do
    let indent = "  "
    let operator' src = parse' src (operator indent)
    operator' "+" `shouldBe` Nothing
    operator' "( + )" `shouldBe` Just "+"
    operator' "(+)" `shouldBe` Just "+"
    operator' "(-)" `shouldBe` Just "-"
    operator' "(*)" `shouldBe` Just "*"
    operator' "(==)" `shouldBe` Just "=="
    operator' "( + )" `shouldBe` Just "+"
    operator' "(\n+\n)" `shouldBe` Nothing
    operator' "(\n  +\n  )" `shouldBe` Nothing
    operator' "(\n   +\n  )" `shouldBe` Just "+"

  it "☯ pattern" $ do
    parse' "" pattern `shouldBe` Nothing
    parse' "_" pattern `shouldBe` Just PAny
    parse' "42" pattern `shouldBe` Just (PInt 42)
    parse' "x@_" pattern `shouldBe` Just x_
    parse' "x" pattern `shouldBe` Just x_
    parse' "A" pattern `shouldBe` Just (PCtr "A" [])
    parse' "B x" pattern `shouldBe` Just (PCtr "B" [])
    parse' "(B x)" pattern `shouldBe` Just (PCtr "B" [x_])
    parse' "(C x y)" pattern `shouldBe` Just (PCtr "C" [x_, y_])

  it "☯ expression" $ do
    let indent = "  "
    let expr src = parse' src (expression indent)
    expr "" `shouldBe` Nothing
    expr "x" `shouldBe` Just x
    expr "42" `shouldBe` Just (Int 42)
    expr "(+)" `shouldBe` Just (Call "+")
    expr "x = 1; y" `shouldBe` Just (Let [("x", Int 1)] y)
    expr "x = 1\n  y" `shouldBe` Just (Let [("x", Int 1)] y)
    expr "x@_ = 1; y" `shouldBe` Just (Let [("x", Int 1)] y)
    expr "f x = 1; y" `shouldBe` Just (Let [("f", lambda [x_] (Int 1))] y)
    expr "f x = 1; y@_ = 2; z" `shouldBe` Just (Let [("f", lambda [x_] (Int 1)), ("y", Int 2)] z)
    expr "x -> y" `shouldBe` Just (lambda [x_] y)
    expr "1 -> y | x -> z" `shouldBe` Just (Cases [([PInt 1], y), ([x_], z)])
    expr "1 -> y\n  x -> z" `shouldBe` Just (Cases [([PInt 1], y), ([x_], z)])
    expr "(x)" `shouldBe` Just x
    expr "( x )" `shouldBe` Just x
    expr "x == y" `shouldBe` Just (eq x y)
    expr "x + y" `shouldBe` Just (add x y)
    expr "x - y" `shouldBe` Just (sub x y)
    expr "x * y" `shouldBe` Just (mul x y)

  it "☯ case'" $ do
    let indent = "  "
    let case_ src = parse' src (case' indent)
    case_ "" `shouldBe` Nothing
    case_ "x -> y" `shouldBe` Just ([x_], y)
    case_ "x\n  -> y" `shouldBe` Nothing
    case_ "x\n   -> y" `shouldBe` Just ([x_], y)
    case_ "x ->\n  y" `shouldBe` Nothing
    case_ "x ->\n   y" `shouldBe` Just ([x_], y)
    case_ "x\n   ->\n   y" `shouldBe` Nothing
    case_ "x\n   ->\n    y" `shouldBe` Just ([x_], y)
    case_ "x y -> z" `shouldBe` Just ([x_, y_], z)

  it "☯ cases" $ do
    let indent = "  "
    let cases' src = parse' src (cases indent)
    cases' "" `shouldBe` Nothing
    cases' "x -> 1" `shouldBe` Just [([x_], Int 1)]
    cases' "x -> 1 | y -> 2" `shouldBe` Just [([x_], Int 1), ([y_], Int 2)]
    cases' "x -> 1\n y -> 2" `shouldBe` Just [([x_], Int 1)]
    cases' "x -> 1\n  y -> 2" `shouldBe` Just [([x_], Int 1), ([y_], Int 2)]
    cases' "x -> 1\n   y -> 2" `shouldBe` Just [([x_], Int 1)]
    cases' "x -> 1 | y -> 2\n  z -> 3" `shouldBe` Just [([x_], Int 1), ([y_], Int 2), ([z_], Int 3)]
    cases' "x -> 1\n  y -> 2 | z -> 3" `shouldBe` Just [([x_], Int 1), ([y_], Int 2), ([z_], Int 3)]

  it "☯ defineRules" $ do
    let indent = "  "
    let defineRules' src = parse' src (defineRules indent)
    defineRules' "" `shouldBe` Nothing
    defineRules' "x = y" `shouldBe` Just ("x", y)
    defineRules' "f _ = y" `shouldBe` Just ("f", lambda [PAny] y)
    defineRules' "f x = y" `shouldBe` Just ("f", lambda [x_] y)
    defineRules' "f x y = z" `shouldBe` Just ("f", lambda [x_, y_] z)
    defineRules' "f A = x" `shouldBe` Just ("f", lambda [PCtr "A" []] x)
    defineRules' "f A = x\n f B = y" `shouldBe` Just ("f", Cases [([PCtr "A" []], x)])
    defineRules' "f A = x\n  f B = y" `shouldBe` Just ("f", Cases [([PCtr "A" []], x), ([PCtr "B" []], y)])
    defineRules' "f A = x\n   f B = y" `shouldBe` Just ("f", Cases [([PCtr "A" []], x)])
    defineRules' "f\n  x = y" `shouldBe` Nothing
    defineRules' "f\n   x = y" `shouldBe` Just ("f", lambda [x_] y)
    defineRules' "f x\n  = y" `shouldBe` Nothing
    defineRules' "f x\n   = y" `shouldBe` Just ("f", lambda [x_] y)
    defineRules' "f x =\n  y" `shouldBe` Nothing
    defineRules' "f x =\n   y" `shouldBe` Just ("f", lambda [x_] y)
    defineRules' "f\n   x\n   =\n   y" `shouldBe` Nothing
    defineRules' "f\n   x\n   =\n    y" `shouldBe` Just ("f", lambda [x_] y)

  it "☯ unpackPattern" $ do
    let indent = "  "
    let unpackPattern' src = parse' src (unpackPattern indent)
    unpackPattern' "" `shouldBe` Nothing
    unpackPattern' "_ = y" `shouldBe` Just []
    unpackPattern' "x = y" `shouldBe` Just [("x", y)]
    unpackPattern' "42 = y" `shouldBe` Just []
    unpackPattern' "A = y" `shouldBe` Just []
    unpackPattern' "(B x) = y" `shouldBe` Just [("x", match [y] [([PCtr "B" [x_]], x)])]
    unpackPattern' "(C x y) = z" `shouldBe` Just [("x", match [z] [([PCtr "C" [x_, y_]], x)]), ("y", match [z] [([PCtr "C" [x_, y_]], y)])]
    unpackPattern' "x\n  = y" `shouldBe` Nothing
    unpackPattern' "x\n   = y" `shouldBe` Just [("x", y)]
    unpackPattern' "x =\n  y" `shouldBe` Nothing
    unpackPattern' "x =\n   y" `shouldBe` Just [("x", y)]
    unpackPattern' "x\n   =\n   y" `shouldBe` Nothing
    unpackPattern' "x\n   =\n    y" `shouldBe` Just [("x", y)]

  it "☯ operator precedence" $ do
    let expr src = parse' src (expression "")
    expr "x == y == z" `shouldBe` Just (eq (eq x y) z)
    expr "x == y + z" `shouldBe` Just (eq x (add y z))
    expr "x + y == z" `shouldBe` Just (eq (add x y) z)
    expr "x + y + z" `shouldBe` Just (add (add x y) z)
    expr "x + y - z" `shouldBe` Just (sub (add x y) z)
    expr "x + y * z" `shouldBe` Just (add x (mul y z))
    expr "x - y + z" `shouldBe` Just (add (sub x y) z)
    expr "x - y - z" `shouldBe` Just (sub (sub x y) z)
    expr "x - y * z" `shouldBe` Just (sub x (mul y z))
    expr "x * y + z" `shouldBe` Just (add (mul x y) z)
    expr "x * y - z" `shouldBe` Just (sub (mul x y) z)
    expr "x * y * z" `shouldBe` Just (mul (mul x y) z)
    expr "x * y z" `shouldBe` Just (mul x (App y [z]))
    expr "x y * z" `shouldBe` Just (mul (App x [y]) z)
    expr "x y z" `shouldBe` Just (App (App x [y]) [z])
