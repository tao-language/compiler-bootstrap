module TaoLangTests where

import Parser
import Tao
import TaoLang
import Test.Hspec

taoLangTests :: SpecWith ()
taoLangTests = describe "--==☯ Tao language ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PVar "x", PVar "y", PVar "z")
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
    let newLine' src = parse' src (do _ <- newLine "  "; letter)
    newLine' "" `shouldBe` Nothing
    newLine' "   " `shouldBe` Nothing
    newLine' "\nx" `shouldBe` Nothing
    newLine' "\n x" `shouldBe` Nothing
    newLine' "\n  x" `shouldBe` Just 'x'
    newLine' "\n   x" `shouldBe` Nothing
    newLine' "\n\n   \n  x" `shouldBe` Just 'x'
    newLine' "\n -- comment\n  x" `shouldBe` Just 'x'

  it "☯ maybeNewLine" $ do
    let maybeNewLine' src = parse' src (maybeNewLine "  ")
    maybeNewLine' "" `shouldBe` Just "  "
    maybeNewLine' "\n" `shouldBe` Just "  "
    maybeNewLine' "\n  " `shouldBe` Just "  "
    maybeNewLine' "\n   " `shouldBe` Just "   "
    maybeNewLine' "\n    " `shouldBe` Just "    "

  it "☯ operator" $ do
    let operator' src = parse' src operator
    operator' "+" `shouldBe` Nothing
    operator' "( + )" `shouldBe` Just Add
    operator' "(+)" `shouldBe` Just Add
    operator' "(-)" `shouldBe` Just Sub
    operator' "(*)" `shouldBe` Just Mul
    operator' "(==)" `shouldBe` Just Eq
    operator' "( + )" `shouldBe` Just Add

  it "☯ tuple" $ do
    let tuple' src = parse' src (tuple "  ")
    tuple' "()" `shouldBe` Just (Tup [])
    tuple' "(x)" `shouldBe` Nothing
    tuple' "(x,)" `shouldBe` Just (Tup [x])
    tuple' "(x, y)" `shouldBe` Just (Tup [x, y])
    tuple' "(x, y,)" `shouldBe` Just (Tup [x, y])

  it "☯ record" $ do
    let record' src = parse' src (record "  ")
    record' "()" `shouldBe` Nothing
    record' "(x = 1)" `shouldBe` Just (Rec [("x", Int 1)])
    record' "(x = 1, y = 2)" `shouldBe` Just (Rec [("x", Int 1), ("y", Int 2)])

  it "☯ pattern" $ do
    let pattern' src = parse' src (pattern "  ")
    pattern' "" `shouldBe` Nothing
    pattern' "_" `shouldBe` Just PAny
    pattern' "42" `shouldBe` Just (PEq (Int 42))
    pattern' "x'" `shouldBe` Just (PEq x)
    pattern' "x@_" `shouldBe` Just (PAs PAny "x")
    pattern' "x" `shouldBe` Just (PVar "x")
    pattern' "A" `shouldBe` Just (PCtr "A" [])
    pattern' "B x" `shouldBe` Just (PCtr "B" [])
    pattern' "(B x)" `shouldBe` Just (PCtr "B" [x'])
    pattern' "(C x y)" `shouldBe` Just (PCtr "C" [x', y'])
    pattern' "()" `shouldBe` Just (PTup [])
    pattern' "(x,)" `shouldBe` Just (PTup [x'])
    pattern' "(x, y)" `shouldBe` Just (PTup [x', y'])
    pattern' "(x, y,)" `shouldBe` Just (PTup [x', y'])
    pattern' "(.x)" `shouldBe` Just (PRec [("x", x')])
    pattern' "(.x,)" `shouldBe` Just (PRec [("x", x')])
    pattern' "(.x, y = _)" `shouldBe` Just (PRec [("x", x'), ("y", PAny)])
    pattern' "(.x, y = _,)" `shouldBe` Just (PRec [("x", x'), ("y", PAny)])
    pattern' "(x : y)" `shouldBe` Just (PAnn x' y')
    pattern' "(x)" `shouldBe` Just (PEq x)
    pattern' "(x + y)" `shouldBe` Just (PEq (add x y))
    pattern' "x | y" `shouldBe` Just (PIf x' y)

  it "☯ builtin" $ do
    let builtin' src = parse' src builtin
    builtin' "@" `shouldBe` Nothing
    builtin' "@Int" `shouldBe` Just IntT
    -- builtin' "@Type" `shouldBe` Just (TypeDef "Type" [])
    builtin' "@func @Int" `shouldBe` Just (Op (Call "func" IntT))

  it "☯ case'" $ do
    let case_ src = parse' src (case' "  ")
    case_ "" `shouldBe` Nothing
    case_ "x -> y" `shouldBe` Just ([x'], y)
    case_ "x ->\n  y" `shouldBe` Nothing
    case_ "x ->\n   y" `shouldBe` Just ([x'], y)
    case_ "x y -> z" `shouldBe` Just ([x', y'], z)

  it "☯ match" $ do
    let match' src = parse' src (match "  ")
    match' "" `shouldBe` Nothing
    match' "\\x -> 1" `shouldBe` Just (Match [([x'], Int 1)])
    match' "\\x -> 1 | y -> 2" `shouldBe` Just (Match [([x'], Int 1), ([y'], Int 2)])
    match' "\\x -> 1\n | y -> 2" `shouldBe` Just (Match [([x'], Int 1)])
    match' "\\x -> 1\n  | y -> 2" `shouldBe` Just (Match [([x'], Int 1), ([y'], Int 2)])
    match' "\\x -> 1\n   | y -> 2" `shouldBe` Just (Match [([x'], Int 1)])
    match' "\\x -> 1 | y -> 2\n  | z -> 3" `shouldBe` Just (Match [([x'], Int 1), ([y'], Int 2), ([z'], Int 3)])
    match' "\\x -> 1\n  | y -> 2 | z -> 3" `shouldBe` Just (Match [([x'], Int 1), ([y'], Int 2), ([z'], Int 3)])

  it "☯ rule" $ do
    let rule' src = parse' src (rule "  ")
    rule' "= x" `shouldBe` Just ([], x)
    rule' "x = y" `shouldBe` Just ([x'], y)
    rule' "x y = z" `shouldBe` Just ([x', y'], z)
    rule' "x =\n  y" `shouldBe` Nothing
    rule' "x =\n   y" `shouldBe` Just ([x'], y)

  it "☯ rules" $ do
    let rules' src = parse' src (rules "  " "f")
    rules' "= x" `shouldBe` Just x
    rules' "x = y" `shouldBe` Just (Match [([x'], y)])
    rules' "x = y\n f y = z" `shouldBe` Just (Match [([x'], y)])
    rules' "x = y\n  f y = z" `shouldBe` Just (Match [([x'], y), ([y'], z)])
    rules' "x = y\n   f y = z" `shouldBe` Just (Match [([x'], y)])

  it "☯ define" $ do
    let define' src = parse' src (define "  ")
    define' "" `shouldBe` Nothing
    define' "x = y" `shouldBe` Just [("x", y)]
    define' "f _ = y" `shouldBe` Just [("f", Match [([PAny], y)])]
    define' "f x = y" `shouldBe` Just [("f", Match [([x'], y)])]
    define' "f x y = z" `shouldBe` Just [("f", Match [([x', y'], z)])]
    define' "f A = x" `shouldBe` Just [("f", Match [([PCtr "A" []], x)])]
    define' "f A = x\n  f B = y" `shouldBe` Just [("f", Match [([PCtr "A" []], x), ([PCtr "B" []], y)])]
    define' "x : z = y" `shouldBe` Just [("x", Ann y z)]
    define' "x : z\n  x = y" `shouldBe` Just [("x", Ann y z)]
    define' "f : z\n  f A = x\n  f B = y" `shouldBe` Just [("f", Ann (Match [([PCtr "A" []], x), ([PCtr "B" []], y)]) z)]
    define' "_ = y" `shouldBe` Just []
    define' "42 = y" `shouldBe` Just []
    define' "A = y" `shouldBe` Just []
    define' "(B x) = y" `shouldBe` Just [("x", App (Match [([PCtr "B" [x']], x)]) y)]
    define' "(C x y) = z" `shouldBe` Just [("x", App (Match [([PCtr "C" [x', y']], x)]) z), ("y", App (Match [([PCtr "C" [x', y']], y)]) z)]

  it "☯ expression" $ do
    let expr src = parse' src (expression "  ")
    expr "" `shouldBe` Nothing
    expr "x" `shouldBe` Just x
    expr "42" `shouldBe` Just (Int 42)
    expr "(+)" `shouldBe` Just (Op Add)
    expr "()" `shouldBe` Just (Tup [])
    expr "(x, y)" `shouldBe` Just (Tup [x, y])
    expr "(x = 1, y = 2)" `shouldBe` Just (Rec [("x", Int 1), ("y", Int 2)])
    expr "\\x -> y" `shouldBe` Just (Match [([x'], y)])
    expr "\\1 -> y | x -> z" `shouldBe` Just (Match [([PEq (Int 1)], y), ([x'], z)])
    expr "\\1 -> y\n  | x -> z" `shouldBe` Just (Match [([PEq (Int 1)], y), ([x'], z)])
    expr "(x)" `shouldBe` Just x
    expr "( x )" `shouldBe` Just x
    expr "x -> y" `shouldBe` Just (FunT x y)
    expr "x == y" `shouldBe` Just (eq x y)
    expr "x + y" `shouldBe` Just (add x y)
    expr "x - y" `shouldBe` Just (sub x y)
    expr "x * y" `shouldBe` Just (mul x y)

  it "☯ operator precedence" $ do
    let expr src = parse' src (expression "  ")
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

  it "☯ block" $ do
    let block' src = parse' src (block "  ")
    block' "42" `shouldBe` Just (Int 42)
    block' "x = 1; y" `shouldBe` Just (Let [("x", Int 1)] y)
    block' "x = 1\n  y" `shouldBe` Just (Let [("x", Int 1)] y)
    block' "x@_ = 1; y" `shouldBe` Just (Let [("x", App (Match [([PAs PAny "x"], x)]) (Int 1))] y)
    block' "f x = 1; y" `shouldBe` Just (Let [("f", Match [([x'], Int 1)])] y)
    block' "f x = 1; y = 2; z" `shouldBe` Just (Let [("f", Match [([x'], Int 1)]), ("y", Int 2)] z)
    block' "x : z = y; 42" `shouldBe` Just (Let [("x", Ann y z)] (Int 42))
    block' "x : z\n  x = y; 42" `shouldBe` Just (Let [("x", Ann y z)] (Int 42))
