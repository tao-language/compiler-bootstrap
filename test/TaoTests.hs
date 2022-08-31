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
    parse' "--my comment" comment `shouldBe` Just "my comment"
    parse' "-- my comment" comment `shouldBe` Just "my comment"
    parse' "--  my  comment  \nx" comment `shouldBe` Just " my  comment  "

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
    let parseDef src = fmap (\(x, a) -> (x, a empty)) (parse' src (definition indent))
    parseDef "x = 1;" `shouldBe` Just (bind "x", Int 1)
    parseDef "x = 1\n" `shouldBe` Just (bind "x", Int 1)
    parseDef "x = 1" `shouldBe` Just (bind "x", Int 1)
    parseDef "x =\n  1" `shouldBe` Nothing
    parseDef "x =\n   1" `shouldBe` Just (bind "x", Int 1)
    parseDef "x =\n\n   1" `shouldBe` Just (bind "x", Int 1)
    parseDef "x =\n     \n   1" `shouldBe` Just (bind "x", Int 1)
  -- TODO: definition with arguments

  it "☯ case" $ do
    let indent = "  "
    let parseCase src = fmap (\(ps, a) -> (ps, a empty)) (parse' src (case' indent))
    parseCase "| x -> y" `shouldBe` Just ([bind "x"], Var "y")
    parseCase "| x ->\n  y" `shouldBe` Nothing
    parseCase "| x ->\n   y" `shouldBe` Just ([bind "x"], Var "y")
    parseCase "| x ->\n\n   y" `shouldBe` Just ([bind "x"], Var "y")
    parseCase "| x ->\n     \n   y" `shouldBe` Just ([bind "x"], Var "y")
    parseCase "| x y -> z" `shouldBe` Just ([bind "x", bind "y"], Var "z")

  it "☯ expression" $ do
    let indent = "  "
    let parseExpr src = fmap (\t -> t empty) (parse' src (expression indent))
    parseExpr "x" `shouldBe` Just (Var "x")
    parseExpr "42" `shouldBe` Just (Int 42)
    parseExpr "(+)" `shouldBe` Just (Call "+")
    parseExpr "x = 1\n y" `shouldBe` Just (Var "x")
    parseExpr "x = 1\n  x" `shouldBe` Just (letRec ("x", letVar ("%0", int 1) $ letVar ("x", var "%0") $ var "x") (var "x") empty)
    parseExpr "x = 1\n   y" `shouldBe` Just (Var "x")
    parseExpr "x = 1\n  y = 2\n  x" `shouldBe` Just (letRec ("x", letVar ("%0", int 1) $ letVar ("x", var "%0") $ var "x") (var "x") empty)
    parseExpr "x = 1; y = 2; x" `shouldBe` Just (letRec ("x", letVar ("%0", int 1) $ letVar ("x", var "%0") $ var "x") (var "x") empty)

--   -- parseExpr "\\ x -> y"  `shouldBe` Just (Lam "%0" (Var "y"))
--   -- parseExpr "\\ x -> y | _ -> z"  `shouldBe` Just (Lam "%0" (Var "y"))
--   -- parseExpr "\\ 1 -> y | x -> z"  `shouldBe` Just (lam ["%0"] (app (eq (var "%0") (int 1)) [var "y", app (lam ["%0"] (var "z")) [var "%0"]]) empty)
--   parseExpr "#error" `shouldBe` Just Err
--   parseExpr "-- comment\nx"  `shouldBe` Just (Var "x") -- TODO: move comment into empty or definition
--   parseExpr "(x)"  `shouldBe` Just (Var "x")
--   parseExpr "x + y"  `shouldBe` Just (add (var "x") (var "y") empty)
--   parseExpr "x - y"  `shouldBe` Just (sub (var "x") (var "y") empty)
--   parseExpr "x * y"  `shouldBe` Just (mul (var "x") (var "y") empty)
--   parseExpr "x == y"  `shouldBe` Just (eq (var "x") (var "y") empty)

-- it "☯ operator precedence" $ do
--   let parseExpr src = fmap (\t -> t empty) (parse src (expression ""))
--   let (x, y, z) = (var "x", var "y", var "z")
--   parseExpr "x == y == z" `shouldBe` Right (eq (eq x y) z empty)
--   parseExpr "x == y + z" `shouldBe` Right (eq x (add y z) empty)
--   parseExpr "x + y == z" `shouldBe` Right (eq (add x y) z empty)
--   parseExpr "x + y + z" `shouldBe` Right (add (add x y) z empty)
--   parseExpr "x + y - z" `shouldBe` Right (sub (add x y) z empty)
--   parseExpr "x + y * z" `shouldBe` Right (add x (mul y z) empty)
--   parseExpr "x - y + z" `shouldBe` Right (add (sub x y) z empty)
--   parseExpr "x - y - z" `shouldBe` Right (sub (sub x y) z empty)
--   parseExpr "x - y * z" `shouldBe` Right (sub x (mul y z) empty)
--   parseExpr "x * y + z" `shouldBe` Right (add (mul x y) z empty)
--   parseExpr "x * y - z" `shouldBe` Right (sub (mul x y) z empty)
--   parseExpr "x * y * z" `shouldBe` Right (mul (mul x y) z empty)
--   parseExpr "x * y z" `shouldBe` Right (mul x (app y [z]) empty)
--   parseExpr "x y * z" `shouldBe` Right (mul (app x [y]) z empty)
--   parseExpr "x y z" `shouldBe` Right (app (app x [y]) [z] empty)
