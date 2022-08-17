module TaoTests where

import Core
import Parser (parse)
import Tao
import Test.Hspec

taoTests :: SpecWith ()
taoTests = describe "--== ☯ Tao language ☯ ==--" $ do
  it "☯ variableName" $ do
    parse "a" variableName `shouldBe` Right "a"
    parse "a1" variableName `shouldBe` Right "a1"

  it "☯ constructorName" $ do
    parse "A" constructorName `shouldBe` Right "A"
    parse "A1" constructorName `shouldBe` Right "A1"

  it "☯ comment" $ do
    parse "--my comment" comment `shouldBe` Right "my comment"
    parse "-- my comment" comment `shouldBe` Right "my comment"
    parse "--  my  comment  \nx" comment `shouldBe` Right " my  comment  "

  it "☯ binding" $ do
    parse "_" binding `shouldBe` Right (PAny, "")
    parse "_" binding `shouldBe` Right (PAny, "")
    parse "42" binding `shouldBe` Right (PInt 42, "")
    parse "True" binding `shouldBe` Right (PCtr "True" [], "")
    parse "x@_" binding `shouldBe` Right (PAny, "x")
    parse "x@42" binding `shouldBe` Right (PInt 42, "x")
    parse "x@True" binding `shouldBe` Right (PCtr "True" [], "x")
    parse "x" binding `shouldBe` Right (PAny, "x")

  it "☯ pattern" $ do
    parse "_" pattern `shouldBe` Right PAny
    parse "42" pattern `shouldBe` Right (PInt 42)
    parse "True" pattern `shouldBe` Right (PCtr "True" [])
    parse "Cons 1 xs" pattern `shouldBe` Right (PCtr "Cons" [(PInt 1, ""), (PAny, "xs")])
    parse "(Cons 1 xs)" pattern `shouldBe` Right (PCtr "Cons" [(PInt 1, ""), (PAny, "xs")])

  it "☯ case" $ do
    let parseCase src ctx = fmap (\(ps, a) -> (ps, a ctx)) (parse src (case' '|'))
    parseCase "| x -> y" empty `shouldBe` Right ([(PAny, "x")], Var "y")
    parseCase "| x y -> z" empty `shouldBe` Right ([(PAny, "x"), (PAny, "y")], Var "z")

  it "☯ definition" $ do
    let parseDefinition src ctx = fmap (\(x, a) -> (x, a ctx)) (parse src definition)
    parseDefinition "@x = 1;" empty `shouldBe` Right ("x", Int 1)
  -- parseDefinition "x = 1\n" empty `shouldBe` Right ("x", Int 1)

  it "☯ expression" $ do
    let parseExpr src ctx = fmap (\t -> t ctx) (parse src expression)
    parseExpr "_" empty `shouldBe` Right Err
    parseExpr "x" empty `shouldBe` Right (Var "x")
    parseExpr "42" empty `shouldBe` Right (Int 42)
    parseExpr "(+)" empty `shouldBe` Right (Call "+")
    parseExpr "(-)" empty `shouldBe` Right (Call "-")
    parseExpr "(*)" empty `shouldBe` Right (Call "*")
    parseExpr "(==)" empty `shouldBe` Right (Call "==")
    parseExpr "@x = 1; x" empty `shouldBe` Right (App (Lam "x" (Var "x")) (App Fix (Lam "x" (Int 1))))
    -- parseExpr "x = 1\nx" empty `shouldBe` Right (Int 1)
    parseExpr "\\ x -> y" empty `shouldBe` Right (Lam "%0" (Var "y"))
    parseExpr "\\ x -> y | _ -> z" empty `shouldBe` Right (Lam "%0" (Var "y"))
    parseExpr "\\ 1 -> y | x -> z" empty `shouldBe` Right (lam ["%0"] (app (eq (var "%0") (int 1)) [var "y", app (lam ["%0"] (var "z")) [var "%0"]]) empty)
    parseExpr "-- comment\nx" empty `shouldBe` Right (Var "x") -- TODO: move comment into empty or definition
    parseExpr "(x)" empty `shouldBe` Right (Var "x")
    parseExpr "x + y" empty `shouldBe` Right (add (var "x") (var "y") empty)
    parseExpr "x - y" empty `shouldBe` Right (sub (var "x") (var "y") empty)
    parseExpr "x * y" empty `shouldBe` Right (mul (var "x") (var "y") empty)
    parseExpr "x == y" empty `shouldBe` Right (eq (var "x") (var "y") empty)

  it "☯ operator precedence" $ do
    let parseExpr src ctx = fmap (\t -> t ctx) (parse src expression)
    let (x, y, z) = (var "x", var "y", var "z")
    parseExpr "x == y == z" empty `shouldBe` Right (eq (eq x y) z empty)
    parseExpr "x == y + z" empty `shouldBe` Right (eq x (add y z) empty)
    parseExpr "x + y == z" empty `shouldBe` Right (eq (add x y) z empty)
    parseExpr "x + y + z" empty `shouldBe` Right (add (add x y) z empty)
    parseExpr "x + y - z" empty `shouldBe` Right (sub (add x y) z empty)
    parseExpr "x + y * z" empty `shouldBe` Right (add x (mul y z) empty)
    parseExpr "x - y + z" empty `shouldBe` Right (add (sub x y) z empty)
    parseExpr "x - y - z" empty `shouldBe` Right (sub (sub x y) z empty)
    parseExpr "x - y * z" empty `shouldBe` Right (sub x (mul y z) empty)
    parseExpr "x * y + z" empty `shouldBe` Right (add (mul x y) z empty)
    parseExpr "x * y - z" empty `shouldBe` Right (sub (mul x y) z empty)
    parseExpr "x * y * z" empty `shouldBe` Right (mul (mul x y) z empty)
    parseExpr "x * y z" empty `shouldBe` Right (mul x (app y [z]) empty)
    parseExpr "x y * z" empty `shouldBe` Right (mul (app x [y]) z empty)
    parseExpr "x y z" empty `shouldBe` Right (app (app x [y]) [z] empty)
