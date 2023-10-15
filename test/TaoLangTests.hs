{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module TaoLangTests where

import Parser (Parser)
import qualified Parser as P
import Tao
import TaoLang
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao language ☯==--" $ do
  let tok :: a -> Int -> Int -> Token a
      tok x row col = (newToken x) {row = row, col = col}
  let tok' :: Int -> Int -> Token'
      tok' = tok ()

  let parse' :: Parser a -> String -> Either String (a, String)
      parse' parser src = case P.parse parser src of
        Right (x, P.State {P.source = remaining}) -> Right (x, remaining)
        Left (P.State {P.source = remaining}) -> Left remaining

  it "☯ identifier" $ do
    let p = parse' identifier
    p "" `shouldBe` Left ""
    p "a" `shouldBe` Right ("a", "")
    p "A" `shouldBe` Right ("A", "")
    p "9" `shouldBe` Left "9" -- cannot start with number
    p "-" `shouldBe` Left "-" -- cannot start with dash
    p "_" `shouldBe` Left "_" -- cannot start with underscore
    p "ab" `shouldBe` Right ("ab", "")
    p "aB" `shouldBe` Right ("aB", "")
    p "a9" `shouldBe` Right ("a9", "")
    p "a-" `shouldBe` Right ("a-", "")
    p "a_" `shouldBe` Right ("a_", "")
    p "CamelCaseName" `shouldBe` Right ("CamelCaseName", "")
    p "snake_case_name" `shouldBe` Right ("snake_case_name", "")
    p "dash-case-name" `shouldBe` Right ("dash-case-name", "")
    p "dash-case-name-1" `shouldBe` Right ("dash-case-name-1", "")
    p "dash-case-name - 1" `shouldBe` Right ("dash-case-name", " - 1")
    p "a->" `shouldBe` Right ("a", "->")

  -- it "☯ inbetween" $ do
  --   let p = parse' (inbetween "(" ")" (P.zeroOrMore P.letter))
  --   p "" `shouldBe` Left ""
  --   p "()" `shouldBe` Right ("", "")
  --   p "(abc)" `shouldBe` Right ("abc", "")
  --   p "( \n abc \n )  \ndef" `shouldBe` Right ("abc", "  \ndef")

  -- it "☯ collection" $ do
  --   let p = parse' $ collection "[" "," "]" P.letter
  --   p "[] ." `shouldBe` Right ("", " .")
  --   p "[,]" `shouldBe` Left ",]"
  --   p "[a]" `shouldBe` Right ("a", "")
  --   p "[a,]" `shouldBe` Right ("a", "")
  --   p "[a, b]" `shouldBe` Right ("ab", "")
  --   p "[a, b,]" `shouldBe` Right ("ab", "")
  --   p "[ \n a \n , \n b \n , \n ]" `shouldBe` Right ("ab", "")

  it "☯ token simple" $ do
    let p = parse' $ token (P.text "abc")
    p "abcdef" `shouldBe` Right (tok "abc" 1 1, "def")
    p "abc   def" `shouldBe` Right (tok "abc" 1 1, "def")

  it "☯ token comments" $ do
    let p = parse' $ token (P.text "abc")
    p "#A\n#B\nabc def" `shouldBe` Right ((tok "abc" 3 1) {comments = ["A", "B"]}, "def")
    p "# A \n \n \n  #  B  \n  abc  def" `shouldBe` Right ((tok "abc" 5 3) {comments = ["A", "B"]}, "def")

  it "☯ token comments (trailing)" $ do
    let p = parse' $ token (P.text "abc")
    p "abc#comment" `shouldBe` Right ((tok "abc" 1 1) {trailingComments = ["comment"]}, "")
    p "abc  #  comment  " `shouldBe` Right ((tok "abc" 1 1) {trailingComments = ["comment"]}, "")

  -- it "☯ token docstrings" $ do
  --   let p = parse' $ token (P.text "abc")
  --   let result public docs start end =
  --         Token
  --           { start = start,
  --             end = end,
  --             docs = DocString {public = public, description = docs},
  --             comments = [],
  --             trailingComment = "",
  --             value = "abc"
  --           }
  --   p "---\n---\nabc" `shouldBe` Right (result True "" (3, 1) (3, 4), "")
  --   p "---\ndocs\n---\nabc" `shouldBe` Right (result True "docs" (4, 1) (4, 4), "")
  --   p "---  \n  docs  \n  ---  \nabc" `shouldBe` Right (result True "docs" (4, 1) (4, 4), "")
  --   p "---  private  \nA\nB\n\nC\n  ---  \nabc" `shouldBe` Right (result False "A\nB\n\nC" (7, 1) (7, 4), "")

  it "☯ patternName" $ do
    let p = parse' patternName
    p "Type abc" `shouldBe` Right (KndP $ tok' 1 1, "abc")
    p "Int abc" `shouldBe` Right (IntTP $ tok' 1 1, "abc")
    p "Num abc" `shouldBe` Right (NumTP $ tok' 1 1, "abc")
    p "Tag abc" `shouldBe` Right (TagP $ tok "Tag" 1 1, "abc")
    p "var abc" `shouldBe` Right (VarP $ tok "var" 1 1, "abc")

  it "☯ patternRecordField" $ do
    let p = parse' patternRecordField
    p "x" `shouldBe` Right ((tok "x" 1 1, VarP (tok "x" 1 1)), "")
    p "x:y" `shouldBe` Right ((tok "x" 1 1, VarP (tok "y" 1 3)), "")
    p "x \n : \n y" `shouldBe` Right ((tok "x" 1 1, VarP (tok "y" 3 2)), "")

  it "☯ patternRecord" $ do
    let p = parse' patternRecord
    p "{} abc" `shouldBe` Right (RecordP (tok' 1 1) [] (tok' 1 2), "abc")
    p "{x} abc" `shouldBe` Right (RecordP (tok' 1 1) [(tok "x" 1 2, VarP $ tok "x" 1 2)] (tok' 1 3), "abc")
    p "{x,} abc" `shouldBe` Right (RecordP (tok' 1 1) [(tok "x" 1 2, VarP $ tok "x" 1 2)] (tok' 1 4), "abc")
    p "{x: y} abc" `shouldBe` Right (RecordP (tok' 1 1) [(tok "x" 1 2, VarP $ tok "y" 1 5)] (tok' 1 6), "abc")
    p "{x: y, z} abc" `shouldBe` Right (RecordP (tok' 1 1) [(tok "x" 1 2, VarP $ tok "y" 1 5), (tok "z" 1 8, VarP $ tok "z" 1 8)] (tok' 1 9), "abc")

  it "☯ patternTuple" $ do
    let p = parse' patternTuple
    p "() abc" `shouldBe` Right (TupleP (tok' 1 1) [] (tok' 1 2), "abc")
    p "(x) abc" `shouldBe` Right (VarP $ tok "x" 1 2, "abc")
    p "(x,) abc" `shouldBe` Right (TupleP (tok' 1 1) [VarP $ tok "x" 1 2] (tok' 1 4), "abc")
    p "(x, y) abc" `shouldBe` Right (TupleP (tok' 1 1) [VarP $ tok "x" 1 2, VarP $ tok "y" 1 5] (tok' 1 6), "abc")

  it "☯ patternAtom" $ do
    let p = parse' patternAtom
    p "_ abc" `shouldBe` Right (AnyP $ tok' 1 1, "abc")
    p "x abc" `shouldBe` Right (VarP $ tok "x" 1 1, "abc")
    p "42 abc" `shouldBe` Right (IntP $ tok 42 1 1, "abc")
    p "{} abc" `shouldBe` Right (RecordP (tok' 1 1) [] (tok' 1 2), "abc")
    p "() abc" `shouldBe` Right (TupleP (tok' 1 1) [] (tok' 1 2), "abc")
    p "(x y) abc" `shouldBe` Right (AppP (VarP $ tok "x" 1 2) (tok' 1 4) (VarP $ tok "y" 1 4), "abc")
    p "(x \n y) abc" `shouldBe` Right (AppP (VarP $ tok "x" 1 2) (tok' 2 2) (VarP $ tok "y" 2 2), "abc")

  -- it "☯ pattern'" $ do
  --   let (x, y) = (VarP "x", VarP "y")
  --   let p = parse' pattern'
  --   p "x y" `shouldBe` Right (tok2 AppP x (1, 1) (1, 2) y (1, 3) (1, 4), "")
  --   p "x \n y" `shouldBe` Right (tok x (1, 1) (1, 2), "\n y")
  --   p "x->y" `shouldBe` Right (tok2 FunP x (1, 1) (1, 2) y (1, 4) (1, 5), "")
  --   p "x \n -> \n y" `shouldBe` Right (tok2 FunP x (1, 1) (1, 2) y (3, 2) (3, 3), "")

  -- TODO: it "☯ operator precedence" $ do

  -- it "☯ expressionAtom" $ do
  --   let p = parse' expressionAtom
  --   p "Type abc" `shouldBe` Right (tok Knd (1, 1) (1, 5), "abc")
  --   p "Int abc" `shouldBe` Right (tok IntT (1, 1) (1, 4), "abc")
  --   p "Num abc" `shouldBe` Right (tok NumT (1, 1) (1, 4), "abc")
  --   p "42 abc" `shouldBe` Right (tok (Int 42) (1, 1) (1, 3), "abc")
  --   p "3.14 abc" `shouldBe` Right (tok (Num 3.14) (1, 1) (1, 5), "abc")
  --   p "Tag abc" `shouldBe` Right (tok (Tag "Tag") (1, 1) (1, 4), "abc")
  --   p "var abc" `shouldBe` Right (tok (Var "var") (1, 1) (1, 4), "abc")
  --   p "x y" `shouldBe` Right (tok (Var "x") (1, 1) (1, 2), "y")
  --   p "(x y) abc" `shouldBe` Right (tok2 App (Var "x") (1, 2) (1, 3) (Var "y") (1, 4) (1, 5), "abc")

  -- it "☯ expression" $ do
  --   let (x, y, z) = (Var "x", Var "y", Var "z")
  --   -- let (x', y') = (VarP "x", VarP "y")
  --   let p = parse' expression
  --   p "\\=y" `shouldBe` Left "\\=y"
  --   -- p "\\x=y" `shouldBe` Right (tokLam [(x', (1, 2), (1, 3))] y (1, 4) (1, 5), "")
  --   -- p "\\ \n x \n = \n y" `shouldBe` Right (tokLam [(x', (2, 2), (2, 3))] y (4, 2) (4, 3), "")
  --   -- p "\\x y = z" `shouldBe` Right (tokLam [(x', (1, 2), (1, 3)), (y', (1, 4), (1, 5))] z (1, 8) (1, 9), "")
  --   p "x | y" `shouldBe` Right (tok2 Or x (1, 1) (1, 2) y (1, 5) (1, 6), "")
  --   p "x : y" `shouldBe` Right (tokAnn x (1, 1) (1, 2) [] y (1, 5) (1, 6), "")
  --   p "x : @a. y" `shouldBe` Right (tokAnn x (1, 1) (1, 2) [("a", (1, 6), (1, 7))] y (1, 9) (1, 10), "")
  --   p "x : @a b. y" `shouldBe` Right (tokAnn x (1, 1) (1, 2) [("a", (1, 6), (1, 7)), ("b", (1, 8), (1, 9))] y (1, 11) (1, 12), "")
  --   p "x == y" `shouldBe` Right (tok2 Eq x (1, 1) (1, 2) y (1, 6) (1, 7), "")
  --   p "x < y" `shouldBe` Right (tok2 Lt x (1, 1) (1, 2) y (1, 5) (1, 6), "")
  --   p "x -> y" `shouldBe` Right (tok2 Fun x (1, 1) (1, 2) y (1, 6) (1, 7), "")
  --   p "x + y" `shouldBe` Right (tok2 Add x (1, 1) (1, 2) y (1, 5) (1, 6), "")
  --   p "x - y" `shouldBe` Right (tok2 Sub x (1, 1) (1, 2) y (1, 5) (1, 6), "")
  --   p "x * y" `shouldBe` Right (tok2 Mul x (1, 1) (1, 2) y (1, 5) (1, 6), "")
  --   p "x y" `shouldBe` Right (tok2 App x (1, 1) (1, 2) y (1, 3) (1, 4), "")
  --   p "x ^ y" `shouldBe` Right (tok2 Pow x (1, 1) (1, 2) y (1, 5) (1, 6), "")

  -- it "☯ typeAnnotation" $ do
  --   let p = parseAll typeAnnotation
  --   p "x : a" `shouldBe` Right ("x", For [] a)
  --   p "x : @a. b" `shouldBe` Right ("x", For ["a"] b)
  --   p "x : @a b. c" `shouldBe` Right ("x", For ["a", "b"] c)

  -- it "☯ untypedDef" $ do
  --   let p = parseAll untypedDef
  --   p "x = 1" `shouldBe` Right ([], _x, i1)
  --   p "x y = 1" `shouldBe` Right ([], _x, Lam _y i1)
  --   p "x y z = 1" `shouldBe` Right ([], _x, lam [_y, _z] i1)
  --   p "x y = 1; x z = 2;" `shouldBe` Right ([], _x, Match [([_y], i1), ([_z], i2)])
  --   p "x y = 1\nx z = 2\n" `shouldBe` Right ([], _x, Match [([_y], i1), ([_z], i2)])
  --   p "x y = 1\n\nx z = 2\n\n" `shouldBe` Right ([], _x, Match [([_y], i1), ([_z], i2)])

  -- it "☯ typedVarDef" $ do
  --   let p = parseAll typedVarDef
  --   p "x : Int = 1" `shouldBe` Right ([("x", For [] IntT)], _x, i1)

  -- it "☯ typedDef" $ do
  --   let p = parseAll typedDef
  --   p "x : Int; x = 1" `shouldBe` Right ([("x", For [] IntT)], _x, i1)
  --   p "x : Int\nx = 1" `shouldBe` Right ([("x", For [] IntT)], _x, i1)
  --   p "x : a -> Int; x y = 1" `shouldBe` Right ([("x", For [] $ fun [a] IntT)], _x, Lam _y i1)
  --   p "x : a -> Int\nx y = 1" `shouldBe` Right ([("x", For [] $ fun [a] IntT)], _x, Lam _y i1)
  --   p "x : a -> b -> Int; x y z = 1" `shouldBe` Right ([("x", For [] $ fun [a, b] IntT)], _x, lam [_y, _z] i1)
  --   p "x : a -> b -> Int\nx y z = 1" `shouldBe` Right ([("x", For [] $ fun [a, b] IntT)], _x, lam [_y, _z] i1)
  --   p "x : a -> b -> Int; x y = 1; x z = 2;" `shouldBe` Right ([("x", For [] $ fun [a, b] IntT)], _x, Match [([_y], i1), ([_z], i2)])
  --   p "x : a -> b -> Int\nx y = 1\nx z = 2\n" `shouldBe` Right ([("x", For [] $ fun [a, b] IntT)], _x, Match [([_y], i1), ([_z], i2)])
  --   p "x : a -> Int; x y = 1; x z = 2;" `shouldBe` Right ([("x", For [] $ fun [a] IntT)], _x, Match [([_y], i1), ([_z], i2)])
  --   p "x : a -> Int\nx y = 1\nx z = 2\n" `shouldBe` Right ([("x", For [] $ fun [a] IntT)], _x, Match [([_y], i1), ([_z], i2)])
  --   p "x : a -> Int\n\nx y = 1\n\nx z = 2\n\n" `shouldBe` Right ([("x", For [] $ fun [a] IntT)], _x, Match [([_y], i1), ([_z], i2)])

  -- it "☯ unpackDef" $ do
  --   let p = parseAll unpackDef
  --   p "A x y = z" `shouldBe` Right ([], pApp (PTag "A") [_x, _y], z)
  --   p "x : a; y : b; A x y = z" `shouldBe` Right ([("x", For [] a), ("y", For [] b)], pApp (PTag "A") [_x, _y], z)
  --   p "x : a\ny : b\nA x y = z\n" `shouldBe` Right ([("x", For [] a), ("y", For [] b)], pApp (PTag "A") [_x, _y], z)

  -- it "☯ definition" $ do
  --   let p = parseAll definition
  --   p "x = 1" `shouldBe` Right ([], _x, i1)
  --   p "x : Int = 1" `shouldBe` Right ([("x", For [] IntT)], _x, i1)
  --   p "x : Int; x = 1" `shouldBe` Right ([("x", For [] IntT)], _x, i1)
  --   p "A x y = z" `shouldBe` Right ([], pApp (PTag "A") [_x, _y], z)

  -- it "☯ definition types" $ do
  --   let p = parseAll definition
  --   let (_n, _a) = (PVar "n", PVar "a")
  --   p "Bool = True | False" `shouldBe` Right ([], PTag "Bool", or' [Tag "True", Tag "False"])
  --   p "Maybe a = Just a | Nothing" `shouldBe` Right ([], PApp (PTag "Maybe") _a, or' [App (Tag "Just") a, Tag "Nothing"])

  --   let n = Var "n"
  --   let vec n a = app (Tag "Vec") [n, a]
  --   let (cons, consTy) = (Tag "Cons", For [] (fun [a, vec n a] (vec (Add n i1) a)))
  --   let (nil, nilTy) = (Tag "Nil", For [] (vec i0 a))
  --   p "Vec n a = Cons : a -> Vec n a -> Vec (n + 1) a | Nil : Vec 0 a" `shouldBe` Right ([], pApp (PTag "Vec") [_n, _a], or' [Ann cons consTy, Ann nil nilTy])

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
