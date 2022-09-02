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

  it "☯ expression" $ do
    let indent = "  "
    let expr src = fmap (\t -> t empty) (parse' src (expression indent))
    expr "" `shouldBe` Nothing
    expr "#error" `shouldBe` Just Err
    expr "x" `shouldBe` Just (Var "x")
    expr "42" `shouldBe` Just (Int 42)
    expr "(+)" `shouldBe` Just (Call "+")
    expr "x = 1; x" `shouldBe` Just (letRec ("x", int 1) (var "x") empty)
    expr "x = 1\n  x" `shouldBe` Just (letRec ("x", int 1) (var "x") empty)
    expr "x = 1; y = 2; x" `shouldBe` Just (letRec ("x", int 1) (var "x") empty)
    expr "x -> y" `shouldBe` Just (Lam "x" (Var "y"))
    expr "1 -> y | x -> z" `shouldBe` Just (lam ["%0"] (if' (eq (var "%0") (int 1)) (var "y") (letVar ("x", var "%0") (var "z"))) empty)
    expr "1 -> y\n  x -> z" `shouldBe` Just (lam ["%0"] (if' (eq (var "%0") (int 1)) (var "y") (letVar ("x", var "%0") (var "z"))) empty)
    expr "(x)" `shouldBe` Just (Var "x")
    expr "( x )" `shouldBe` Just (Var "x")
    expr "x == y" `shouldBe` Just (eq (var "x") (var "y") empty)
    expr "x + y" `shouldBe` Just (add (var "x") (var "y") empty)
    expr "x - y" `shouldBe` Just (sub (var "x") (var "y") empty)
    expr "x * y" `shouldBe` Just (mul (var "x") (var "y") empty)
    True `shouldBe` True

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
    parse' "_ @ x" pattern `shouldBe` Just (bind "x")
    parse' "x" pattern `shouldBe` Just (bind "x")
    parse' "42" pattern `shouldBe` Just (PInt 42)
    parse' "Nil" pattern `shouldBe` Just (PCtr "Nil" [])
    parse' "Cons x xs" pattern `shouldBe` Just (PCtr "Cons" [])
    parse' "(Cons x xs)" pattern `shouldBe` Just (PCtr "Cons" [bind "x", bind "xs"])

  it "☯ defineRules" $ do
    let indent = "  "
    let ctx = defineType "T" [] [("A", 0), ("B", 0)] empty
    let defineRules' src = fmap (\(x, a) -> (x, a ctx)) (parse' src (defineRules indent))
    defineRules' "" `shouldBe` Nothing
    defineRules' "x = y" `shouldBe` Just ("x", Var "y")
    defineRules' "f _ = y" `shouldBe` Just ("f", Lam "%0" (Var "y"))
    defineRules' "f x = y" `shouldBe` Just ("f", Lam "x" (Var "y"))
    defineRules' "f x y = z" `shouldBe` Just ("f", Lam "x" (Lam "y" (Var "z")))
    defineRules' "f A = x" `shouldBe` Just ("f", lam ["%0"] (app (var "%0") [var "x", err]) empty)
    defineRules' "f A = x\n f B = y" `shouldBe` Just ("f", lam ["%0"] (app (var "%0") [var "x", err]) empty)
    defineRules' "f A = x\n  f B = y" `shouldBe` Just ("f", lam ["%0"] (app (var "%0") [var "x", var "y"]) empty)
    defineRules' "f A = x\n   f B = y" `shouldBe` Just ("f", lam ["%0"] (app (var "%0") [var "x", err]) empty)
    defineRules' "f\n  x = y" `shouldBe` Nothing
    defineRules' "f\n   x = y" `shouldBe` Just ("f", Lam "x" (Var "y"))
    defineRules' "f x\n  = y" `shouldBe` Nothing
    defineRules' "f x\n   = y" `shouldBe` Just ("f", Lam "x" (Var "y"))
    defineRules' "f x =\n  y" `shouldBe` Nothing
    defineRules' "f x =\n   y" `shouldBe` Just ("f", Lam "x" (Var "y"))
    defineRules' "f\n   x\n   =\n   y" `shouldBe` Nothing
    defineRules' "f\n   x\n   =\n    y" `shouldBe` Just ("f", Lam "x" (Var "y"))

  it "☯ unpackPattern" $ do
    let indent = "  "
    let ctx = defineType "List" [] [("Nil", 0), ("Cons", 2)] empty
    let unpackPattern' src = fmap (map (\(x, a) -> (x, a ctx))) (parse' src (unpackPattern indent))
    unpackPattern' "" `shouldBe` Nothing
    unpackPattern' "_ = y" `shouldBe` Just []
    unpackPattern' "_ @ x = y" `shouldBe` Just [("x", Var "y")]
    unpackPattern' "x = y" `shouldBe` Just [("x", Var "y")]
    unpackPattern' "42 = y" `shouldBe` Just []
    unpackPattern' "Nil = y" `shouldBe` Just []
    unpackPattern' "(Cons x xs) = y"
      `shouldBe` Just
        [ ("x", letVar ("%0", var "y") (app (var "%0") [err, lam ["x", "xs"] (var "x")]) empty),
          ("xs", letVar ("%0", var "y") (app (var "%0") [err, lam ["x", "xs"] (var "xs")]) empty)
        ]
    unpackPattern' "x\n  = y" `shouldBe` Nothing
    unpackPattern' "x\n   = y" `shouldBe` Just [("x", Var "y")]
    unpackPattern' "x =\n  y" `shouldBe` Nothing
    unpackPattern' "x =\n   y" `shouldBe` Just [("x", Var "y")]
    unpackPattern' "x\n   =\n   y" `shouldBe` Nothing
    unpackPattern' "x\n   =\n    y" `shouldBe` Just [("x", Var "y")]

  it "☯ definitions" $ do
    let indent = "  "
    let ctx = defineType "T" [] [("A", 0), ("B", 0)] empty
    let definitions' src = fmap (map (\(x, a) -> (x, a ctx))) (parse' src (definitions indent))
    definitions' "" `shouldBe` Nothing
    definitions' "f x = y" `shouldBe` Just [("f", Lam "x" (Var "y"))]
    definitions' "f x = y; _@g = z" `shouldBe` Just [("f", Lam "x" (Var "y")), ("g", Var "z")]
    definitions' "f x = y\n _@g = z" `shouldBe` Just [("f", Lam "x" (Var "y"))]
    definitions' "f x = y\n  _@g = z" `shouldBe` Just [("f", Lam "x" (Var "y")), ("g", Var "z")]
    definitions' "f x = y\n   _@g = z" `shouldBe` Just [("f", Lam "x" (Var "y"))]

  it "☯ case'" $ do
    let indent = "  "
    let case_ src = fmap (\(ps, a) -> (ps, a empty)) (parse' src (case' indent))
    case_ "" `shouldBe` Nothing
    case_ "x -> y" `shouldBe` Just ([bind "x"], Var "y")
    case_ "x\n  -> y" `shouldBe` Nothing
    case_ "x\n   -> y" `shouldBe` Just ([bind "x"], Var "y")
    case_ "x ->\n  y" `shouldBe` Nothing
    case_ "x ->\n   y" `shouldBe` Just ([bind "x"], Var "y")
    case_ "x\n   ->\n   y" `shouldBe` Nothing
    case_ "x\n   ->\n    y" `shouldBe` Just ([bind "x"], Var "y")
    case_ "x y -> z" `shouldBe` Just ([bind "x", bind "y"], Var "z")

  it "☯ cases" $ do
    let indent = "  "
    let cases' src = fmap (map (\(ps, a) -> (ps, a empty))) (parse' src (cases indent))
    cases' "" `shouldBe` Nothing
    cases' "x -> 1" `shouldBe` Just [([bind "x"], Int 1)]
    cases' "x -> 1 | y -> 2" `shouldBe` Just [([bind "x"], Int 1), ([bind "y"], Int 2)]
    cases' "x -> 1\n y -> 2" `shouldBe` Just [([bind "x"], Int 1)]
    cases' "x -> 1\n  y -> 2" `shouldBe` Just [([bind "x"], Int 1), ([bind "y"], Int 2)]
    cases' "x -> 1\n   y -> 2" `shouldBe` Just [([bind "x"], Int 1)]
    cases' "x -> 1 | y -> 2\n  z -> 3" `shouldBe` Just [([bind "x"], Int 1), ([bind "y"], Int 2), ([bind "z"], Int 3)]
    cases' "x -> 1\n  y -> 2 | z -> 3" `shouldBe` Just [([bind "x"], Int 1), ([bind "y"], Int 2), ([bind "z"], Int 3)]

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
