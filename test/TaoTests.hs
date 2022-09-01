module TaoTests where

import Core
import Parser
import Tao
import Test.Hspec

taoTests :: SpecWith ()
taoTests = describe "--==☯ Tao language ☯==--" $ do
  let parse' src parser = case Parser.parse src parser of
        Right x -> Just x
        Left _ -> Nothing

  it "☯ variableName" $ do
    parse' "a" variableName `shouldBe` Just "a"
    parse' "a1" variableName `shouldBe` Just "a1"

  it "☯ constructorName" $ do
    parse' "A" constructorName `shouldBe` Just "A"
    parse' "A1" constructorName `shouldBe` Just "A1"

  it "☯ operator" $ do
    parse' "( + )" operator `shouldBe` Just "+"
    parse' "(+)" operator `shouldBe` Just "+"
    parse' "(-)" operator `shouldBe` Just "-"
    parse' "(*)" operator `shouldBe` Just "*"
    parse' "(==)" operator `shouldBe` Just "=="

  it "☯ comment" $ do
    let indent = "  "
    let comment' src = parse' src (comment indent)
    comment' "--my comment" `shouldBe` Just "my comment"
    comment' "-- my comment" `shouldBe` Just "my comment"
    comment' "--  my  comment  \n x" `shouldBe` Nothing
    comment' "--  my  comment  \n  x" `shouldBe` Just " my  comment  "
    comment' "--  my  comment  \n   x" `shouldBe` Just " my  comment  "
  -- TODO: support multi-line comments

  it "☯ pattern" $ do
    parse' "_" pattern `shouldBe` Just PAny
    parse' "_ @ x" pattern `shouldBe` Just (PAs PAny "x")
    parse' "x" pattern `shouldBe` Just (PAs PAny "x")
    parse' "42" pattern `shouldBe` Just (PInt 42)
    parse' "True" pattern `shouldBe` Just (PCtr "True" [])
    parse' "Cons 1 xs" pattern `shouldBe` Just (PCtr "Cons" [PInt 1, PAs PAny "xs"])
    parse' "(Cons 1 xs)" pattern `shouldBe` Just (PCtr "Cons" [PInt 1, PAs PAny "xs"])

  it "☯ definition" $ do
    let indent = "  "
    let definition' src = fmap (\(x, a) -> (x, a empty)) (parse' src (definition indent))
    definition' "x = 1;" `shouldBe` Just (bind "x", Int 1)
    definition' "x = 1\n" `shouldBe` Just (bind "x", Int 1)
    definition' "x = 1" `shouldBe` Just (bind "x", Int 1)
    definition' "x =\n  1" `shouldBe` Nothing
    definition' "x =\n   1" `shouldBe` Just (bind "x", Int 1)
    definition' "x =\n\n   1" `shouldBe` Just (bind "x", Int 1)
    definition' "x =\n     \n   1" `shouldBe` Just (bind "x", Int 1)
  -- TODO: definition with arguments

  it "☯ case" $ do
    let indent = "  "
    let case_ src = fmap (\(ps, a) -> (ps, a empty)) (parse' src (case' indent))
    case_ "x -> y" `shouldBe` Just ([bind "x"], Var "y")
    case_ "x ->\n  y" `shouldBe` Nothing
    case_ "x ->\n   y" `shouldBe` Just ([bind "x"], Var "y")
    case_ "x ->\n\n   y" `shouldBe` Just ([bind "x"], Var "y")
    case_ "x ->\n     \n   y" `shouldBe` Just ([bind "x"], Var "y")
    case_ "x y -> z" `shouldBe` Just ([bind "x", bind "y"], Var "z")

  it "☯ expression" $ do
    let indent = "  "
    let expr src = fmap (\t -> t empty) (parse' src (expression indent))
    expr "#error" `shouldBe` Just Err
    expr "x" `shouldBe` Just (Var "x")
    expr "42" `shouldBe` Just (Int 42)
    expr "(+)" `shouldBe` Just (Call "+")
    expr "x = 1\n y" `shouldBe` Just (Var "x")
    expr "x = 1\n  x" `shouldBe` Just (letRec ("x", int 1) (var "x") empty)
    expr "x = 1\n   y" `shouldBe` Just (Var "x")
    expr "x = 1\n  y = 2\n  x" `shouldBe` Just (letRec ("x", int 1) (var "x") empty)
    expr "x = 1; y = 2; x" `shouldBe` Just (letRec ("x", int 1) (var "x") empty)
    expr "x -> y" `shouldBe` Just (Lam "x" (Var "y"))
    expr "1 -> y\n x -> z" `shouldBe` Just (Int 1)
    expr "1 -> y\n  x -> z" `shouldBe` Just (lam ["%0"] (if' (eq (var "%0") (int 1)) (var "y") (letVar ("x", var "%0") (var "z"))) empty)
    expr "1 -> y\n   x -> z" `shouldBe` Just (lam ["%0"] (if' (eq (var "%0") (int 1)) (var "y") (app err [var "%0"])) empty)
    expr "1 -> y | x -> z" `shouldBe` Just (lam ["%0"] (if' (eq (var "%0") (int 1)) (var "y") (letVar ("x", var "%0") (var "z"))) empty)
    -- TODO: move comment into empty or definition
    expr "-- comment\n x" `shouldBe` Nothing
    expr "-- comment\n  x" `shouldBe` Just (Var "x")
    expr "-- comment\n   x" `shouldBe` Nothing
    -- End of TODO
    expr "(x)" `shouldBe` Just (Var "x")
    expr "( x )" `shouldBe` Just (Var "x")
    expr "x == y" `shouldBe` Just (eq (var "x") (var "y") empty)
    expr "x + y" `shouldBe` Just (add (var "x") (var "y") empty)
    expr "x - y" `shouldBe` Just (sub (var "x") (var "y") empty)
    expr "x * y" `shouldBe` Just (mul (var "x") (var "y") empty)

  it "☯ operator precedence" $ do
    let expr src = fmap (\t -> t empty) (parse' src (expression ""))
    let (x, y, z) = (var "x", var "y", var "z")
    expr "x == y == z" `shouldBe` Just (eq (eq x y) z empty)
    expr "x == y + z" `shouldBe` Just (eq x (add y z) empty)
    expr "x + y == z" `shouldBe` Just (eq (add x y) z empty)
    expr "x + y + z" `shouldBe` Just (add (add x y) z empty)
    expr "x + y - z" `shouldBe` Just (sub (add x y) z empty)
    expr "x + y * z" `shouldBe` Just (add x (mul y z) empty)
    expr "x - y + z" `shouldBe` Just (add (sub x y) z empty)
    expr "x - y - z" `shouldBe` Just (sub (sub x y) z empty)
    expr "x - y * z" `shouldBe` Just (sub x (mul y z) empty)
    expr "x * y + z" `shouldBe` Just (add (mul x y) z empty)
    expr "x * y - z" `shouldBe` Just (sub (mul x y) z empty)
    expr "x * y * z" `shouldBe` Just (mul (mul x y) z empty)
    expr "x * y z" `shouldBe` Just (mul x (app y [z]) empty)
    expr "x y * z" `shouldBe` Just (mul (app x [y]) z empty)
    expr "x y z" `shouldBe` Just (app (app x [y]) [z] empty)
