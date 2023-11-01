{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

module TaoLangTests where

import Core (DocString (..), Metadata (..))
import Error
import qualified Parser as P
import Tao
import TaoLang
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao language ☯==--" $ do
  let sourceName = "test"

  let parse' :: TaoParser a -> String -> Either ([ParserContext], String) (a, String)
      parse' parser src = case P.parse sourceName parser src of
        Right (x, P.State {remaining}) -> Right (x, remaining)
        Left P.State {context, remaining} -> Left (context, remaining)

  let loc row col = Meta [Location sourceName row col]
  let var row col = loc row col . Var
  let ploc row col = PMeta [Location sourceName row col]
  let pvar row col = ploc row col . PVar

  it "☯ identifier" $ do
    let p = parse' identifier
    -- p "" `shouldBe` Left ([SyntaxError NameError "test" 1 1], "")
    p "" `shouldBe` Left ([], "")
    p "a" `shouldBe` Right ("a", "")
    p "A" `shouldBe` Right ("A", "")
    -- p "9" `shouldBe` Left ([SyntaxError NameError "test" 1 1], "9") -- cannot start with number
    -- p "-" `shouldBe` Left ([SyntaxError NameError "test" 1 1], "-") -- cannot start with dash
    -- p "_" `shouldBe` Left ([SyntaxError NameError "test" 1 1], "_") -- cannot start with underscore
    p "9" `shouldBe` Left ([], "9") -- cannot start with number
    p "-" `shouldBe` Left ([], "-") -- cannot start with dash
    p "_" `shouldBe` Left ([], "_") -- cannot start with underscore
    p "ab" `shouldBe` Right ("ab", "")
    p "aB" `shouldBe` Right ("aB", "")
    p "a9" `shouldBe` Right ("a9", "")
    p "a-" `shouldBe` Right ("a-", "")
    p "a_" `shouldBe` Right ("a_", "")
    p "CamelCaseName" `shouldBe` Right ("CamelCaseName", "")
    p "snake_case_name" `shouldBe` Right ("snake_case_name", "")
    p "dash-case-name" `shouldBe` Right ("dash-case-name", "")
    p "dash-case-name-1" `shouldBe` Right ("dash-case-name-1", "")
    p "dash-case-name - 1" `shouldBe` Right ("dash-case-name", "- 1")
    p "a->" `shouldBe` Right ("a", "->")

  it "☯ inbetween" $ do
    let p = parse' (inbetween "(" ")" (P.zeroOrMore P.letter))
    p "" `shouldBe` Left ([], "")
    p "()" `shouldBe` Right ("", "")
    p "(abc)" `shouldBe` Right ("abc", "")
    p "( \n abc \n )  \ndef" `shouldBe` Right ("abc", "  \ndef")

  it "☯ collection" $ do
    let p = parse' $ collection "[" "," "]" (P.paddedR P.whitespaces P.letter)
    p "[] ." `shouldBe` Right ("", " .")
    p "[,]" `shouldBe` Left ([], ",]")
    p "[a]" `shouldBe` Right ("a", "")
    p "[a,]" `shouldBe` Right ("a", "")
    p "[a, b]" `shouldBe` Right ("ab", "")
    p "[a, b,]" `shouldBe` Right ("ab", "")
    p "[ \n a \n , \n b \n , \n ]" `shouldBe` Right ("ab", "")

  it "☯ docString" $ do
    let docs public description = DocString {public = public, description = description}
    let p = parse' $ docString (P.text "---")
    p "---\n---\nabc" `shouldBe` Right (docs True "", "abc")
    p "---\ndocs\n---\nabc" `shouldBe` Right (docs True "docs", "abc")
    p "---  \n  docs  \n  ---  \nabc" `shouldBe` Right (docs True "docs", "abc")
    p "---  private  \nA\nB\n\nC\n  ---  \nabc" `shouldBe` Right (docs False "A\nB\n\nC", "abc")

  -- it "☯ metadata location" $ do
  --   let meta row col x = ([Location sourceName row col], x)
  --   let p = parse' $ metadata (P.text "abc")
  --   p "abcdef" `shouldBe` Right (meta 1 1 "abc", "def")
  --   p "abc   def" `shouldBe` Right (meta 1 1 "abc", "def")
  --   p "abc \n  def" `shouldBe` Right (meta 1 1 "abc", "\n  def")

  -- it "☯ metadata comments" $ do
  --   let meta row col comments x = ([Location sourceName row col, Comments comments], x)
  --   let p = parse' $ metadata (P.text "abc")
  --   p "#A\n#B\nabc def" `shouldBe` Right (meta 3 1 ["A", "B"] "abc", "def")
  --   p "# A \n \n \n  #  B  \n  abc  def" `shouldBe` Right (meta 5 3 ["A", "B"] "abc", "def")

  -- it "☯ metadata comments (trailing)" $ do
  --   let meta row col comment x = ([Location sourceName row col, TrailingComment comment], x)
  --   let p = parse' $ metadata (P.text "abc")
  --   p "abc#comment" `shouldBe` Right (meta 1 1 "comment" "abc", "")
  --   p "abc#  comment  " `shouldBe` Right (meta 1 1 "comment" "abc", "")

  it "☯ patternName" $ do
    let p = parse' patternName
    p "Type abc" `shouldBe` Right (PKnd, "abc")
    p "Int abc" `shouldBe` Right (PIntT, "abc")
    p "Num abc" `shouldBe` Right (PNumT, "abc")
    p "Tag abc" `shouldBe` Right (PTag "Tag", "abc")
    p "var abc" `shouldBe` Right (PVar "var", "abc")

  it "☯ patternTuple" $ do
    let p = parse' patternTuple
    p "() abc" `shouldBe` Right (PTuple [], " abc")
    p "(x) abc" `shouldBe` Right (PVar "x", " abc")
    p "(x,) abc" `shouldBe` Right (PTuple [pvar 1 2 "x"], " abc")
    p "(x, y) abc" `shouldBe` Right (PTuple [pvar 1 2 "x", pvar 1 5 "y"], " abc")

  it "☯ patternRecordField" $ do
    let p = parse' patternRecordField
    p "x" `shouldBe` Right (("x", pvar 1 1 "x"), "")
    p "x:y" `shouldBe` Right (("x", pvar 1 3 "y"), "")
    p "x \n : \n y" `shouldBe` Right (("x", pvar 3 2 "y"), "")

  it "☯ patternRecord" $ do
    let p = parse' patternRecord
    p "{} abc" `shouldBe` Right (PRecord [], " abc")
    p "{x} abc" `shouldBe` Right (PRecord [("x", pvar 1 2 "x")], " abc")
    p "{x,} abc" `shouldBe` Right (PRecord [("x", pvar 1 2 "x")], " abc")
    p "{x: y} abc" `shouldBe` Right (PRecord [("x", pvar 1 5 "y")], " abc")
    p "{x: y, z} abc" `shouldBe` Right (PRecord [("x", pvar 1 5 "y"), ("z", pvar 1 8 "z")], " abc")

  it "☯ pattern'" $ do
    let p = parse' (pattern' $ P.ok ())
    p "_" `shouldBe` Right (ploc 1 1 PAny, "")
    p "x" `shouldBe` Right (ploc 1 1 $ PVar "x", "")
    p "42" `shouldBe` Right (ploc 1 1 $ PInt 42, "")
    p "()" `shouldBe` Right (ploc 1 1 $ PTuple [], "")
    p "{}" `shouldBe` Right (ploc 1 1 $ PRecord [], "")
    p "x->" `shouldBe` Right (PMeta [Location "test" 1 1] (PVar "x"), "->")
    p "x->y" `shouldBe` Right (ploc 1 2 $ PFun (pvar 1 1 "x") (pvar 1 4 "y"), "")
    p "x y" `shouldBe` Right (PApp (pvar 1 1 "x") (pvar 1 3 "y"), "")
    p "x\ny" `shouldBe` Right (ploc 1 1 $ PVar "x", "\ny")
    p "(x\ny)" `shouldBe` Right (ploc 1 1 $ PApp (pvar 1 2 "x") (pvar 2 1 "y"), "")

  it "☯ expressionName" $ do
    let p = parse' expressionName
    p "Type abc" `shouldBe` Right (Knd, "abc")
    p "Int abc" `shouldBe` Right (IntT, "abc")
    p "Num abc" `shouldBe` Right (NumT, "abc")
    p "Tag abc" `shouldBe` Right (Tag "Tag", "abc")
    p "var abc" `shouldBe` Right (Var "var", "abc")

  it "☯ expressionTuple" $ do
    let p = parse' expressionTuple
    p "() abc" `shouldBe` Right (Tuple [], " abc")
    p "(x) abc" `shouldBe` Right (Var "x", " abc")
    p "(x,) abc" `shouldBe` Right (Tuple [var 1 2 "x"], " abc")
    p "(x, y) abc" `shouldBe` Right (Tuple [var 1 2 "x", var 1 5 "y"], " abc")

  it "☯ expressionRecordField" $ do
    let p = parse' expressionRecordField
    p "x" `shouldBe` Left ([CRecordField "x"], "")
    p "x:y" `shouldBe` Right (("x", var 1 3 "y"), "")
    p "x \n : \n y" `shouldBe` Right (("x", var 3 2 "y"), "")

  it "☯ expressionRecord" $ do
    let p = parse' expressionRecord
    p "{} abc" `shouldBe` Right (Record [], " abc")
    p "{x: y} abc" `shouldBe` Right (Record [("x", var 1 5 "y")], " abc")
    p "{x: y, z: w} abc" `shouldBe` Right (Record [("x", var 1 5 "y"), ("z", var 1 11 "w")], " abc")

  it "☯ expression'" $ do
    let p = parse' (expression $ P.ok ())
    p "Type" `shouldBe` Right (loc 1 1 Knd, "")
    p "Int" `shouldBe` Right (loc 1 1 IntT, "")
    p "Num" `shouldBe` Right (loc 1 1 NumT, "")
    p "Tag" `shouldBe` Right (loc 1 1 $ Tag "Tag", "")
    p "var" `shouldBe` Right (loc 1 1 $ Var "var", "")
    p "42" `shouldBe` Right (loc 1 1 $ Int 42, "")
    p "3.14" `shouldBe` Right (loc 1 1 $ Num 3.14, "")
    p "()" `shouldBe` Right (loc 1 1 $ Tuple [], "")
    p "{}" `shouldBe` Right (loc 1 1 $ Record [], "")
    p "\\x=y" `shouldBe` Right (loc 1 1 $ lam [pvar 1 2 "x"] (var 1 4 "y"), "")
    p "\\x\ny\n=\nz" `shouldBe` Right (loc 1 1 $ lam [pvar 1 2 "x", pvar 2 1 "y"] (var 4 1 "z"), "")
    p "x |  y" `shouldBe` Right (loc 1 3 $ Or (var 1 1 "x") (var 1 6 "y"), "")
    p "x :  y" `shouldBe` Right (ann (var 1 1 "x") (var 1 6 "y"), "")
    p "x : @a. y" `shouldBe` Right (Ann (var 1 1 "x") (For ["a"] $ var 1 9 "y"), "")
    p "x : @a b. y" `shouldBe` Right (Ann (var 1 1 "x") (For ["a", "b"] $ var 1 11 "y"), "")
    p "x == y" `shouldBe` Right (loc 1 3 $ Eq (var 1 1 "x") (var 1 6 "y"), "")
    p "x <  y" `shouldBe` Right (loc 1 3 $ Lt (var 1 1 "x") (var 1 6 "y"), "")
    p "x -> y" `shouldBe` Right (loc 1 3 $ Fun (var 1 1 "x") (var 1 6 "y"), "")
    p "x +  y" `shouldBe` Right (loc 1 3 $ Add (var 1 1 "x") (var 1 6 "y"), "")
    p "x -  y" `shouldBe` Right (loc 1 3 $ Sub (var 1 1 "x") (var 1 6 "y"), "")
    p "x *  y" `shouldBe` Right (loc 1 3 $ Mul (var 1 1 "x") (var 1 6 "y"), "")
    p "x    y" `shouldBe` Right (App (var 1 1 "x") (var 1 6 "y"), "")
    p "x ^  y" `shouldBe` Right (loc 1 3 $ Pow (var 1 1 "x") (var 1 6 "y"), "")
    p "x\ny" `shouldBe` Right (loc 1 1 $ Var "x", "\ny")
    p "(x\ny)" `shouldBe` Right (loc 1 1 $ App (var 1 2 "x") (var 2 1 "y"), "")

  -- it "☯ letDef" $ do
  --   let p = parse' letDef
  --   let def = LetDef {docs = Nothing, name = "x", type' = Nothing, value = Err, meta = [Location sourceName 1 1]}
  --   p "x = y" `shouldBe` Right (def {value = var 1 5 "y"}, "")
  --   p "x : Int = y" `shouldBe` Right (def {type' = Just (For [] $ loc 1 5 IntT), value = var 1 11 "y"}, "")
  --   p "x : Int\nx = y" `shouldBe` Right (def {type' = Just (For [] $ loc 1 5 IntT), value = var 2 5 "y"}, "")
  --   p "x p = y\nx q = z" `shouldBe` Right (def {value = Match [([pvar 1 3 "p"], var 1 7 "y"), ([pvar 2 3 "q"], var 2 7 "z")]}, "")

  -- -- it "☯ unpackDef" $ do
  -- -- it "☯ typeDef" $ do
  -- -- it "☯ test" $ do

  -- it "☯ statement" $ do
  --   let p = parse' statement
  --   p "x = y" `shouldBe` Right (LetDef {docs = Nothing, name = "x", type' = Nothing, value = var 1 5 "y", meta = [Location sourceName 1 1]}, "")

  it "☯ import'" $ do
    let p = parse' import'
    p "import mod" `shouldBe` Right (Import "mod" "mod" [] [Location "test" 1 1], "")
    p "import dir/to/mod" `shouldBe` Right (Import "dir/to/mod" "mod" [] [Location "test" 1 1], "")
    p "import mod as m" `shouldBe` Right (Import "mod" "m" [] [Location "test" 1 1], "")
    p "import mod as m ()" `shouldBe` Right (Import "mod" "m" [] [Location "test" 1 1], "")
    p "import mod as m (a, b)" `shouldBe` Right (Import "mod" "m" ["a", "b"] [Location "test" 1 1], "")

  it "☯ module'" $ do
    let p = parse' (module' "mod")
    let docs = Just DocString {public = True, description = "docs"}
    p "===\ndocs\n===" `shouldBe` Right (Module {name = "mod", docs = docs, body = []}, "")
    -- let defs = [LetDef {docs = Nothing, name = "x", type' = Nothing, value = var 4 5 "y", meta = [Location sourceName 4 1]}]
    -- p "===\ndocs\n===\nx = y" `shouldBe` Right (Module {name = "mod", docs = docs, body = defs}, "")
    True `shouldBe` True
