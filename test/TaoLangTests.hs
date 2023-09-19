module TaoLangTests where

import qualified Parser as P
import Tao
import TaoLang
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao language ☯==--" $ do
  let (a, b) = (Var "a", Var "b")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (_x, _y, _z) = (PVar "x", PVar "y", PVar "z")
  let (i1, i2) = (Int 1, Int 2)

  let parse' parser src = case parseSome parser src of
        Right (x, P.State {P.source = remaining}) ->
          Right (x, remaining)
        Left (SyntaxError (P.SyntaxError _ P.State {P.source = remaining})) ->
          Left remaining
        Left (TypeError err) -> Left (show err)

  it "☯ token" $ do
    let p = parse' (P.zeroOrMore (token P.letter))
    p "abc.d" `shouldBe` Right ("abc", ".d")
    p "a b c . d" `shouldBe` Right ("abc", ". d")

  it "☯ emptyLine" $ do
    let p = parse' emptyLine
    p "" `shouldBe` Left ""
    p "  " `shouldBe` Left ""
    p "\nabc" `shouldBe` Right ("", "abc")
    p "  \nabc" `shouldBe` Right ("  ", "abc")
    p " a \nbc" `shouldBe` Left "a "
    p ";abc" `shouldBe` Right ("", "abc")
    p "  ;abc" `shouldBe` Right ("  ", "abc")
    p " a ;bc" `shouldBe` Left "a "

  it "☯ keyword" $ do
    let p = parse' (keyword True "A")
    p "A" `shouldBe` Right (True, "")
    p "ABC" `shouldBe` Left "BC"
    p "A2" `shouldBe` Left "2"
    p "A_" `shouldBe` Left "_"
    p "A'" `shouldBe` Left "'"

  it "☯ identifier" $ do
    let p = parse' (identifier P.lowercase)
    p "" `shouldBe` Left ""
    p "a" `shouldBe` Right ("a", "")
    p "a1" `shouldBe` Right ("a1", "")
    p "_a1" `shouldBe` Right ("_a1", "")

  it "☯ commentSingleLine" $ do
    let p = parse' commentSingleLine
    p "" `shouldBe` Left ""
    p "--" `shouldBe` Right ("", "")
    p "--abc" `shouldBe` Right ("abc", "")
    p "-- abc " `shouldBe` Right ("abc ", "")
    p "--  abc  " `shouldBe` Right (" abc  ", "")
    p "-- abc\ndef" `shouldBe` Right ("abc", "def")

  it "☯ commentMultiLine" $ do
    let p = parse' commentMultiLine
    p "" `shouldBe` Left ""
    p "{----}" `shouldBe` Right ("", "")
    p "{--abc--}" `shouldBe` Right ("abc", "")
    p "{-- abc --}" `shouldBe` Right ("abc", "")
    p "{--  abc  --}" `shouldBe` Right (" abc ", "")
    p "{-- abc\ndef --}" `shouldBe` Right ("abc\ndef", "")

  it "☯ comments" $ do
    let p = parse' comments
    p "" `shouldBe` Right ("", "")
    p "-- a" `shouldBe` Right ("a", "")
    p "-- a\n-- b" `shouldBe` Right ("a\nb", "")
    p "-- a\n{-- b --}" `shouldBe` Right ("a\nb", "")
    p "{-- a --}\n-- b" `shouldBe` Right ("a\nb", "")

  it "☯ pattern" $ do
    let p = parse' (pattern' 0)
    p "_ " `shouldBe` Right (PAny, "")
    p "1 " `shouldBe` Right (PInt 1, "")
    p "x " `shouldBe` Right (PVar "x", "")
    p "A " `shouldBe` Right (PTag "A", "")
    p "B x y " `shouldBe` Right (PApp (PApp (PTag "B") _x) _y, "")
    p "(_) " `shouldBe` Right (PAny, "")
    p "(1) " `shouldBe` Right (PInt 1, "")
    p "(x) " `shouldBe` Right (PVar "x", "")
    p "(A) " `shouldBe` Right (PTag "A", "")
    p "(B x y) " `shouldBe` Right (PApp (PApp (PTag "B") _x) _y, "")

  it "☯ expression" $ do
    let p = parse' (expression 0)
    p "Type" `shouldBe` Right (Var "Type", "")
    p "Int" `shouldBe` Right (Var "Int", "")
    p "Num" `shouldBe` Right (Var "Num", "")
    p "42" `shouldBe` Right (Int 42, "")
    p "3.14" `shouldBe` Right (Num 3.14, "")
    p "x" `shouldBe` Right (Var "x", "")
    p "A" `shouldBe` Right (Var "A", "")
    p "\\x = 1" `shouldBe` Right (lam [_x] i1, "")
    p "\\x y = 1" `shouldBe` Right (lam [_x, _y] i1, "")
    p "\\x = 1 | y = 2" `shouldBe` Right (Match [([_x], i1), ([_y], i2)], "")
    p "x = 1; a" `shouldBe` Right (Let [(_x, i1)] a, "")
    p "x = 1\na" `shouldBe` Right (Let [(_x, i1)] a, "")
    p "x = 1; y = 2; a" `shouldBe` Right (Let [(_x, i1), (_y, i2)] a, "")
    p "x = 1\ny = 2\na" `shouldBe` Right (Let [(_x, i1), (_y, i2)] a, "")
    p "x -> y" `shouldBe` Right (fun [x] y, "")
    p "x == y" `shouldBe` Right (Eq x y, "")
    p "x < y" `shouldBe` Right (Lt x y, "")
    p "x + y" `shouldBe` Right (Add x y, "")
    p "x - y" `shouldBe` Right (Sub x y, "")
    p "x * y" `shouldBe` Right (Mul x y, "")
    p "x ^ y" `shouldBe` Right (Pow x y, "")
    p "x y" `shouldBe` Right (App x y, "")
    p "(x)" `shouldBe` Right (x, "")

  -- it "☯ definition" $ do
  --   let p = parse' definition

  --   -- Untyped rules
  --   p "x = 1" `shouldBe` Right (Untyped "x" i1, "")
  --   p "x y = 1" `shouldBe` Right (Untyped "x" (lam ["y"] i1), "")
  --   p "x y z = 1" `shouldBe` Right (Untyped "x" (lam ["y", "z"] i1), "")
  --   p "x y = 1; x z = 2;" `shouldBe` Right (Untyped "x" (Match [Br [y'] i1, Br [z'] i2]), "")
  --   p "x y = 1\nx z = 2\n" `shouldBe` Right (Untyped "x" (Match [Br [y'] i1, Br [z'] i2]), "")
  --   p "x y = 1\n\nx z = 2\n\n" `shouldBe` Right (Untyped "x" (Match [Br [y'] i1, Br [z'] i2]), "")

  --   -- Typed rules
  --   p "x : Int; x = 1" `shouldBe` Right (Typed "x" (Var "Int") i1, "")
  --   p "x : Int\nx = 1" `shouldBe` Right (Typed "x" (Var "Int") i1, "")
  --   p "x : a -> Int; x y = 1" `shouldBe` Right (Typed "x" (Fun (Var "a") (Var "Int")) (lam ["y"] i1), "")
  --   p "x : a -> Int\nx y = 1" `shouldBe` Right (Typed "x" (Fun (Var "a") (Var "Int")) (lam ["y"] i1), "")
  --   p "x : a -> b -> Int; x y z = 1" `shouldBe` Right (Typed "x" (fun [Var "a", Var "b"] (Var "Int")) (lam ["y", "z"] i1), "")
  --   p "x : a -> b -> Int\nx y z = 1" `shouldBe` Right (Typed "x" (fun [Var "a", Var "b"] (Var "Int")) (lam ["y", "z"] i1), "")
  --   p "x : a -> b -> Int; x y = 1; x z = 2;" `shouldBe` Right (Typed "x" (fun [Var "a", Var "b"] (Var "Int")) (Match [Br [y'] i1, Br [z'] i2]), "")
  --   p "x : a -> b -> Int\nx y = 1\nx z = 2\n" `shouldBe` Right (Typed "x" (fun [Var "a", Var "b"] (Var "Int")) (Match [Br [y'] i1, Br [z'] i2]), "")
  --   p "x : a -> Int; x y = 1; x z = 2;" `shouldBe` Right (Typed "x" (Fun (Var "a") (Var "Int")) (Match [Br [y'] i1, Br [z'] i2]), "")
  --   p "x : a -> Int\nx y = 1\nx z = 2\n" `shouldBe` Right (Typed "x" (Fun (Var "a") (Var "Int")) (Match [Br [y'] i1, Br [z'] i2]), "")
  --   p "x : a -> Int\n\nx y = 1\n\nx z = 2\n\n" `shouldBe` Right (Typed "x" (Fun (Var "a") (Var "Int")) (Match [Br [y'] i1, Br [z'] i2]), "")

  --   -- Typed variable
  --   p "x : Int = 1" `shouldBe` Right (Typed "x" (Var "Int") i1, "")

  --   -- Pattern unpack
  --   p "A x y = z" `shouldBe` Right (Unpack (CtrP "A" [x', y']) [] z, "")
  --   p "x : a; y : b; A x y = z" `shouldBe` Right (Unpack (CtrP "A" [x', y']) [("x", Var "a"), ("y", Var "b")] z, "")
  --   p "x : a\ny : b\nA x y = z\n" `shouldBe` Right (Unpack (CtrP "A" [x', y']) [("x", Var "a"), ("y", Var "b")] z, "")

  -- it "☯ unionTypeDefinition" $ do
  --   let p = parse' unionTypeDefinition

  --   -- Simple definition
  --   p "type T = _" `shouldBe` Right (UnionType "T" [] [], "")
  --   p "type T = A" `shouldBe` Right (UnionType "T" [] [("A", Var "T")], "")

  --   -- Constructor arguments
  --   p "type T = A a" `shouldBe` Right (UnionType "T" [] [("A", Fun (Var "a") (Var "T"))], "")
  --   p "type T = A a b" `shouldBe` Right (UnionType "T" [] [("A", fun [Var "a", Var "b"] (Var "T"))], "")

  --   -- Arguments
  --   p "type T a = A" `shouldBe` Right (UnionType "T" [("a", Var "Type")] [("A", App (Var "T") (Var "a"))], "")
  --   p "type T a b = A" `shouldBe` Right (UnionType "T" [("a", Var "Type"), ("b", Var "Type")] [("A", app (Var "T") [Var "a", Var "b"])], "")

  --   -- Typed arguments
  --   p "type T (a : Int) = A" `shouldBe` Right (UnionType "T" [("a", Var "Int")] [("A", App (Var "T") (Var "a"))], "")

  --   -- Typed constructors
  --   p "type T = A : U" `shouldBe` Right (UnionType "T" [] [("A", Var "U")], "")

  --   -- Multiple constructors
  --   p "type T = A | B" `shouldBe` Right (UnionType "T" [] [("A", Var "T"), ("B", Var "T")], "")

  --   -- End-to-end
  --   p "type Bool = True | False" `shouldBe` Right (UnionType "Bool" [] [("True", Var "Bool"), ("False", Var "Bool")], "")
  --   p "type Maybe a = Just a | Nothing" `shouldBe` Right (UnionType "Maybe" [("a", Var "Type")] [("Just", Fun (Var "a") (App (Var "Maybe") (Var "a"))), ("Nothing", App (Var "Maybe") (Var "a"))], "")
  --   p "type Vec (n : Int) a = Cons a (Vec n a) : Vec (n + 1) a | Nil : Vec 0 a" `shouldBe` Right (UnionType "Vec" [("n", Var "Int"), ("a", Var "Type")] [("Cons", fun [Var "a", app (Var "Vec") [Var "n", Var "a"]] (app (Var "Vec") [Op2 Add (Var "n") (Int 1), Var "a"])), ("Nil", app (Var "Vec") [Int 0, Var "a"])], "")

  -- it "☯ contextDefinition" $ do
  --   let p = parse' contextDefinition
  --   p "type T = _" `shouldBe` Right (UnionType "T" [] [], "")
  --   p "x = 1" `shouldBe` Right (Value (Untyped "x" (Int 1)), "")

  -- describe "☯ operator precedence" $ do
  --   it "☯ Let" $ do
  --     let p = parse' (expression 0)
  --     p "x = 1; y = 2; z" `shouldBe` Right (Let [Untyped "x" i1, Untyped "y" i2] z, "")
  --     p "x = 1; @forall y. z" `shouldBe` Right (Let [Untyped "x" i1] (For "y" z), "")
  --     p "x = 1; y == z" `shouldBe` Right (Let [Untyped "x" i1] (eq y z), "")
  --     p "x = 1; y -> z" `shouldBe` Right (Let [Untyped "x" i1] (Fun y z), "")
  --     p "x = 1; y < z" `shouldBe` Right (Let [Untyped "x" i1] (lt y z), "")
  --     p "x = 1; y + z" `shouldBe` Right (Let [Untyped "x" i1] (add y z), "")
  --     p "x = 1; y - z" `shouldBe` Right (Let [Untyped "x" i1] (sub y z), "")
  --     p "x = 1; y * z" `shouldBe` Right (Let [Untyped "x" i1] (mul y z), "")
  --     p "x = 1; y z" `shouldBe` Right (Let [Untyped "x" i1] (App y z), "")

  --   it "☯ For" $ do
  --     let p = parse' (expression 0)
  --     p "@forall x. y = 1; z" `shouldBe` Right (For "x" (Let [Untyped "y" i1] z), "")
  --     p "@forall x. @forall y. z" `shouldBe` Right (For "x" (For "y" z), "")
  --     p "@forall x. y == z" `shouldBe` Right (eq (For "x" y) z, "")
  --     p "@forall x. y -> z" `shouldBe` Right (For "x" (Fun y z), "")
  --     p "@forall x. y < z" `shouldBe` Right (For "x" (lt y z), "")
  --     p "@forall x. y + z" `shouldBe` Right (For "x" (add y z), "")
  --     p "@forall x. y - z" `shouldBe` Right (For "x" (sub y z), "")
  --     p "@forall x. y * z" `shouldBe` Right (For "x" (mul y z), "")
  --     p "@forall x. y z" `shouldBe` Right (For "x" (App y z), "")

  --   it "☯ Eq (==)" $ do
  --     let p = parse' (expression 0)
  --     p "x == y = 1; z" `shouldBe` Right (eq x (Let [Untyped "y" i1] z), "")
  --     p "x == @forall y. z" `shouldBe` Right (eq x (For "y" z), "")
  --     p "x == y == z" `shouldBe` Right (eq (eq x y) z, "")
  --     p "x == y -> z" `shouldBe` Right (eq x (Fun y z), "")
  --     p "x == y < z" `shouldBe` Right (eq x (lt y z), "")
  --     p "x == y + z" `shouldBe` Right (eq x (add y z), "")
  --     p "x == y - z" `shouldBe` Right (eq x (sub y z), "")
  --     p "x == y * z" `shouldBe` Right (eq x (mul y z), "")
  --     p "x == y z" `shouldBe` Right (eq x (App y z), "")

  --   it "☯ Fun (->)" $ do
  --     let p = parse' (expression 0)
  --     p "x -> y = 1; z" `shouldBe` Right (Fun x (Let [Untyped "y" i1] z), "")
  --     p "x -> @forall y. z" `shouldBe` Right (Fun x (For "y" z), "")
  --     p "x -> y == z" `shouldBe` Right (eq (Fun x y) z, "")
  --     p "x -> y -> z" `shouldBe` Right (Fun x (Fun y z), "")
  --     p "x -> y < z" `shouldBe` Right (Fun x (lt y z), "")
  --     p "x -> y + z" `shouldBe` Right (Fun x (add y z), "")
  --     p "x -> y - z" `shouldBe` Right (Fun x (sub y z), "")
  --     p "x -> y * z" `shouldBe` Right (Fun x (mul y z), "")
  --     p "x -> y z" `shouldBe` Right (Fun x (App y z), "")

  --   it "☯ Lt (<)" $ do
  --     let p = parse' (expression 0)
  --     p "x < y = 1; z" `shouldBe` Right (lt x (Let [Untyped "y" i1] z), "")
  --     p "x < @forall y. z" `shouldBe` Right (lt x (For "y" z), "")
  --     p "x < y == z" `shouldBe` Right (eq (lt x y) z, "")
  --     p "x < y -> z" `shouldBe` Right (Fun (lt x y) z, "")
  --     p "x < y < z" `shouldBe` Right (lt (lt x y) z, "")
  --     p "x < y + z" `shouldBe` Right (lt x (add y z), "")
  --     p "x < y - z" `shouldBe` Right (lt x (sub y z), "")
  --     p "x < y * z" `shouldBe` Right (lt x (mul y z), "")
  --     p "x < y z" `shouldBe` Right (lt x (App y z), "")

  --   it "☯ Add (+)" $ do
  --     let p = parse' (expression 0)
  --     p "x + y = 1; z" `shouldBe` Right (add x (Let [Untyped "y" i1] z), "")
  --     p "x + @forall y. z" `shouldBe` Right (add x (For "y" z), "")
  --     p "x + y == z" `shouldBe` Right (eq (add x y) z, "")
  --     p "x + y -> z" `shouldBe` Right (Fun (add x y) z, "")
  --     p "x + y < z" `shouldBe` Right (lt (add x y) z, "")
  --     p "x + y + z" `shouldBe` Right (add (add x y) z, "")
  --     p "x + y - z" `shouldBe` Right (sub (add x y) z, "")
  --     p "x + y * z" `shouldBe` Right (add x (mul y z), "")
  --     p "x + y z" `shouldBe` Right (add x (App y z), "")

  --   it "☯ Sub (-)" $ do
  --     let p = parse' (expression 0)
  --     p "x - y = 1; z" `shouldBe` Right (sub x (Let [Untyped "y" i1] z), "")
  --     p "x - @forall y. z" `shouldBe` Right (sub x (For "y" z), "")
  --     p "x - y == z" `shouldBe` Right (eq (sub x y) z, "")
  --     p "x - y -> z" `shouldBe` Right (Fun (sub x y) z, "")
  --     p "x - y < z" `shouldBe` Right (lt (sub x y) z, "")
  --     p "x - y + z" `shouldBe` Right (add (sub x y) z, "")
  --     p "x - y - z" `shouldBe` Right (sub (sub x y) z, "")
  --     p "x - y * z" `shouldBe` Right (sub x (mul y z), "")
  --     p "x - y z" `shouldBe` Right (sub x (App y z), "")

  --   it "☯ Mul (*)" $ do
  --     let p = parse' (expression 0)
  --     p "x * y = 1; z" `shouldBe` Right (mul x (Let [Untyped "y" i1] z), "")
  --     p "x * @forall y. z" `shouldBe` Right (mul x (For "y" z), "")
  --     p "x * y == z" `shouldBe` Right (eq (mul x y) z, "")
  --     p "x * y -> z" `shouldBe` Right (Fun (mul x y) z, "")
  --     p "x * y < z" `shouldBe` Right (lt (mul x y) z, "")
  --     p "x * y + z" `shouldBe` Right (add (mul x y) z, "")
  --     p "x * y - z" `shouldBe` Right (sub (mul x y) z, "")
  --     p "x * y * z" `shouldBe` Right (mul (mul x y) z, "")
  --     p "x * y z" `shouldBe` Right (mul x (App y z), "")

  --   it "☯ App" $ do
  --     let p = parse' (expression 0)
  --     p "x @forall y. z" `shouldBe` Right (App x (For "y" z), "")
  --     p "x y == z" `shouldBe` Right (eq (App x y) z, "")
  --     p "x y -> z" `shouldBe` Right (Fun (App x y) z, "")
  --     p "x y < z" `shouldBe` Right (lt (App x y) z, "")
  --     p "x y + z" `shouldBe` Right (add (App x y) z, "")
  --     p "x y - z" `shouldBe` Right (sub (App x y) z, "")
  --     p "x y * z" `shouldBe` Right (mul (App x y) z, "")
  --     p "x y z" `shouldBe` Right (App (App x y) z, "")
  it "TODO" $ do
    True `shouldBe` True
