module TaoLangTests where

import Parser
import Tao
import TaoLang
import Test.Hspec

taoLangTests :: SpecWith ()
taoLangTests = describe "--==☯ Tao language ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (pvar "x", pvar "y", pvar "z")
  let parse' src parser = case Parser.parse src parser of
        Right x -> Just x
        Left _ -> Nothing

  it "☯ lowerName" $ do
    parse' "" lowerName `shouldBe` Nothing
    parse' "a" lowerName `shouldBe` Just "a"
    parse' "a1" lowerName `shouldBe` Just "a1"

  it "☯ upperName" $ do
    parse' "" upperName `shouldBe` Nothing
    parse' "A" upperName `shouldBe` Just "A"
    parse' "A1" upperName `shouldBe` Just "A1"

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

  it "☯ spaces" $ do
    let indent = "  "
    let spaces' src = parse' src (spaces indent)
    spaces' "" `shouldBe` Just "  "
    spaces' "\n" `shouldBe` Just "  "
    spaces' "\n  " `shouldBe` Just "  "
    spaces' "\n   " `shouldBe` Just "   "
    spaces' "\n    " `shouldBe` Just "    "

  it "☯ operator" $ do
    let indent = "  "
    let operator' src = parse' src (operator indent)
    operator' "+" `shouldBe` Nothing
    operator' "( + )" `shouldBe` Just Add
    operator' "(+)" `shouldBe` Just Add
    operator' "(-)" `shouldBe` Just Sub
    operator' "(*)" `shouldBe` Just Mul
    operator' "(==)" `shouldBe` Just Eq
    operator' "( + )" `shouldBe` Just Add
    operator' "(\n+\n)" `shouldBe` Nothing
    operator' "(\n  +\n  )" `shouldBe` Nothing
    operator' "(\n   +\n  )" `shouldBe` Just Add

  it "☯ pattern" $ do
    parse' "" pattern `shouldBe` Nothing
    parse' "_" pattern `shouldBe` Just PAny
    parse' "42" pattern `shouldBe` Just (PEq (Int 42))
    parse' "x@_" pattern `shouldBe` Just x'
    parse' "x" pattern `shouldBe` Just x'
    parse' "A" pattern `shouldBe` Just (PCtr "A" [])
    parse' "B x" pattern `shouldBe` Just (PCtr "B" [])
    parse' "(B x)" pattern `shouldBe` Just (PCtr "B" [x'])
    parse' "(C x y)" pattern `shouldBe` Just (PCtr "C" [x', y'])

  it "☯ builtin" $ do
    let builtin' src = parse' src builtin
    builtin' "@" `shouldBe` Nothing
    builtin' "@Int" `shouldBe` Just IntT
    builtin' "@True" `shouldBe` Just (Bool True)
    builtin' "@False" `shouldBe` Just (Bool False)
    builtin' "@Type {}" `shouldBe` Just (TypeDef "Type" [])
    builtin' "@Maybe {Just x | Nothing}" `shouldBe` Just (TypeDef "Maybe" [("Just", ["x"]), ("Nothing", [])])
    builtin' "@func @Int" `shouldBe` Just (Call "func" IntT)

  it "☯ expression" $ do
    let indent = "  "
    let expr src = parse' src (expression indent)
    expr "" `shouldBe` Nothing
    expr "x" `shouldBe` Just x
    expr "42" `shouldBe` Just (Int 42)
    expr "(+)" `shouldBe` Just Add
    expr "x = 1; y" `shouldBe` Just (Let [("x", Int 1)] y)
    expr "x = 1\n  y" `shouldBe` Just (Let [("x", Int 1)] y)
    expr "x@_ = 1; y" `shouldBe` Just (Let [("x", App (Match [([x'], x)]) (Int 1))] y)
    expr "f x = 1; y" `shouldBe` Just (Let [("f", Match [([x'], Int 1)])] y)
    expr "f x = 1; y@_ = 2; z" `shouldBe` Just (Let [("f", Match [([x'], Int 1)]), ("y", App (Match [([y'], y)]) (Int 2))] z)
    expr "\\x -> y" `shouldBe` Just (Match [([x'], y)])
    expr "\\1 -> y | x -> z" `shouldBe` Just (Match [([PEq (Int 1)], y), ([x'], z)])
    expr "\\1 -> y\n  x -> z" `shouldBe` Just (Match [([PEq (Int 1)], y), ([x'], z)])
    expr "(x)" `shouldBe` Just x
    expr "( x )" `shouldBe` Just x
    expr "x -> y" `shouldBe` Just (Fun x y)
    expr "x == y" `shouldBe` Just (eq x y)
    expr "x + y" `shouldBe` Just (add x y)
    expr "x - y" `shouldBe` Just (sub x y)
    expr "x * y" `shouldBe` Just (mul x y)

  it "☯ case'" $ do
    let indent = "  "
    let case_ src = parse' src (case' indent)
    case_ "" `shouldBe` Nothing
    case_ "x -> y" `shouldBe` Just ([x'], y)
    case_ "x\n  -> y" `shouldBe` Nothing
    case_ "x\n   -> y" `shouldBe` Just ([x'], y)
    case_ "x ->\n  y" `shouldBe` Nothing
    case_ "x ->\n   y" `shouldBe` Just ([x'], y)
    case_ "x\n   ->\n   y" `shouldBe` Nothing
    case_ "x\n   ->\n    y" `shouldBe` Just ([x'], y)
    case_ "x y -> z" `shouldBe` Just ([x', y'], z)

  it "☯ match" $ do
    let indent = "  "
    let match' src = parse' src (match indent)
    match' "" `shouldBe` Nothing
    match' "\\x -> 1" `shouldBe` Just (Match [([x'], Int 1)])
    match' "\\x -> 1 | y -> 2" `shouldBe` Just (Match [([x'], Int 1), ([y'], Int 2)])
    match' "\\x -> 1\n y -> 2" `shouldBe` Just (Match [([x'], Int 1)])
    match' "\\x -> 1\n  y -> 2" `shouldBe` Just (Match [([x'], Int 1), ([y'], Int 2)])
    match' "\\x -> 1\n   y -> 2" `shouldBe` Just (Match [([x'], Int 1)])
    match' "\\x -> 1 | y -> 2\n  z -> 3" `shouldBe` Just (Match [([x'], Int 1), ([y'], Int 2), ([z'], Int 3)])
    match' "\\x -> 1\n  y -> 2 | z -> 3" `shouldBe` Just (Match [([x'], Int 1), ([y'], Int 2), ([z'], Int 3)])

  it "☯ rule" $ do
    let indent = "  "
    let rule' src = parse' src (rule indent)
    rule' "= x" `shouldBe` Just ([], x)
    rule' "x = y" `shouldBe` Just ([x'], y)
    rule' "x y = z" `shouldBe` Just ([x', y'], z)
    rule' "x\n  = y" `shouldBe` Nothing
    rule' "x\n   = y" `shouldBe` Just ([x'], y)
    rule' "x =\n  y" `shouldBe` Nothing
    rule' "x =\n   y" `shouldBe` Just ([x'], y)
    rule' "x\n   =\n   y" `shouldBe` Nothing
    rule' "x\n   =\n    y" `shouldBe` Just ([x'], y)

  it "☯ rules" $ do
    let indent = "  "
    let rules' src = parse' src (rules indent "f")
    rules' "= x" `shouldBe` Just x
    rules' "x = y" `shouldBe` Just (Match [([x'], y)])
    rules' "x = y\n f y = z" `shouldBe` Just (Match [([x'], y)])
    rules' "x = y\n  f y = z" `shouldBe` Just (Match [([x'], y), ([y'], z)])
    rules' "x = y\n   f y = z" `shouldBe` Just (Match [([x'], y)])

  it "☯ define" $ do
    let indent = "  "
    let define' src = parse' src (define indent)
    define' "" `shouldBe` Nothing
    define' "x = y" `shouldBe` Just ("x", y)
    define' "f _ = y" `shouldBe` Just ("f", Match [([PAny], y)])
    define' "f x = y" `shouldBe` Just ("f", Match [([x'], y)])
    define' "f x y = z" `shouldBe` Just ("f", Match [([x', y'], z)])
    define' "f A = x" `shouldBe` Just ("f", Match [([PCtr "A" []], x)])
    define' "f A = x\n  f B = y" `shouldBe` Just ("f", Match [([PCtr "A" []], x), ([PCtr "B" []], y)])
    define' "f\n  x = y" `shouldBe` Nothing
    define' "f\n   x = y" `shouldBe` Just ("f", Match [([x'], y)])
    define' "x : z = y" `shouldBe` Just ("x", Ann y z)
    define' "x : z\n  x = y" `shouldBe` Just ("x", Ann y z)
    define' "f : z\n  f A = x\n  f B = y" `shouldBe` Just ("f", Ann (Match [([PCtr "A" []], x), ([PCtr "B" []], y)]) z)

  it "☯ unpack" $ do
    let indent = "  "
    let unpack_ src = parse' src (unpack' indent)
    unpack_ "" `shouldBe` Nothing
    unpack_ "_ = y" `shouldBe` Just []
    unpack_ "x = y" `shouldBe` Just [("x", App (Match [([x'], x)]) y)]
    unpack_ "42 = y" `shouldBe` Just []
    unpack_ "A = y" `shouldBe` Just []
    unpack_ "(B x) = y" `shouldBe` Just [("x", App (Match [([PCtr "B" [x']], x)]) y)]
    unpack_ "(C x y) = z" `shouldBe` Just [("x", App (Match [([PCtr "C" [x', y']], x)]) z), ("y", App (Match [([PCtr "C" [x', y']], y)]) z)]
    unpack_ "x\n  = y" `shouldBe` Nothing
    unpack_ "x\n   = y" `shouldBe` Just [("x", App (Match [([x'], x)]) y)]
    unpack_ "x =\n  y" `shouldBe` Nothing
    unpack_ "x =\n   y" `shouldBe` Just [("x", App (Match [([x'], x)]) y)]
    unpack_ "x\n   =\n   y" `shouldBe` Nothing
    unpack_ "x\n   =\n    y" `shouldBe` Just [("x", App (Match [([x'], x)]) y)]

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
    expr "x * y z" `shouldBe` Just (mul x (App y z))
    expr "x y * z" `shouldBe` Just (mul (App x y) z)
    expr "x y z" `shouldBe` Just (App (App x y) z)
