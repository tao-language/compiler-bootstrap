{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

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

  it "☯ patternTuple" $ do
    let p = parse' patternTuple
    p "() abc" `shouldBe` Right (TupleP (tok' 1 1) [] (tok' 1 2), "abc")
    p "(x) abc" `shouldBe` Right (VarP $ tok "x" 1 2, "abc")
    p "(x,) abc" `shouldBe` Right (TupleP (tok' 1 1) [VarP $ tok "x" 1 2] (tok' 1 4), "abc")
    p "(x, y) abc" `shouldBe` Right (TupleP (tok' 1 1) [VarP $ tok "x" 1 2, VarP $ tok "y" 1 5] (tok' 1 6), "abc")

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

  it "☯ pattern'" $ do
    let p = parse' (pattern' $ P.succeed ())
    p "_" `shouldBe` Right (AnyP $ tok' 1 1, "")
    p "x" `shouldBe` Right (VarP $ tok "x" 1 1, "")
    p "42" `shouldBe` Right (IntP $ tok 42 1 1, "")
    p "()" `shouldBe` Right (TupleP (tok' 1 1) [] (tok' 1 2), "")
    p "{}" `shouldBe` Right (RecordP (tok' 1 1) [] (tok' 1 2), "")
    p "x->y" `shouldBe` Right (FunP (VarP $ tok "x" 1 1) (tok' 1 2) (VarP $ tok "y" 1 4), "")
    p "x y" `shouldBe` Right (AppP (VarP $ tok "x" 1 1) (tok' 1 3) (VarP $ tok "y" 1 3), "")
    p "x\ny" `shouldBe` Right (VarP $ tok "x" 1 1, "\ny")
    p "(x\ny)" `shouldBe` Right (AppP (VarP $ tok "x" 1 2) (tok' 1 3) (VarP $ tok "y" 2 1), "")

  it "☯ expressionName" $ do
    let p = parse' expressionName
    p "Type abc" `shouldBe` Right (Knd $ tok' 1 1, "abc")
    p "Int abc" `shouldBe` Right (IntT $ tok' 1 1, "abc")
    p "Num abc" `shouldBe` Right (NumT $ tok' 1 1, "abc")
    p "Tag abc" `shouldBe` Right (Tag $ tok "Tag" 1 1, "abc")
    p "var abc" `shouldBe` Right (Var $ tok "var" 1 1, "abc")

  it "☯ expressionTuple" $ do
    let p = parse' expressionTuple
    p "() abc" `shouldBe` Right (Tuple (tok' 1 1) [] (tok' 1 2), "abc")
    p "(x) abc" `shouldBe` Right (Var $ tok "x" 1 2, "abc")
    p "(x,) abc" `shouldBe` Right (Tuple (tok' 1 1) [Var $ tok "x" 1 2] (tok' 1 4), "abc")
    p "(x, y) abc" `shouldBe` Right (Tuple (tok' 1 1) [Var $ tok "x" 1 2, Var $ tok "y" 1 5] (tok' 1 6), "abc")

  it "☯ expressionRecordField" $ do
    let p = parse' expressionRecordField
    p "x" `shouldBe` Left ""
    p "x:y" `shouldBe` Right ((tok "x" 1 1, Var (tok "y" 1 3)), "")
    p "x \n : \n y" `shouldBe` Right ((tok "x" 1 1, Var (tok "y" 3 2)), "")

  it "☯ expressionRecord" $ do
    let p = parse' expressionRecord
    p "{} abc" `shouldBe` Right (Record (tok' 1 1) [] (tok' 1 2), "abc")
    p "{x: y} abc" `shouldBe` Right (Record (tok' 1 1) [(tok "x" 1 2, Var $ tok "y" 1 5)] (tok' 1 6), "abc")
    p "{x: y, z: w} abc" `shouldBe` Right (Record (tok' 1 1) [(tok "x" 1 2, Var $ tok "y" 1 5), (tok "z" 1 8, Var $ tok "w" 1 11)] (tok' 1 12), "abc")

  it "☯ expression'" $ do
    let p = parse' (expression $ P.succeed ())
    p "Type" `shouldBe` Right (Knd $ tok' 1 1, "")
    p "Int" `shouldBe` Right (IntT $ tok' 1 1, "")
    p "Num" `shouldBe` Right (NumT $ tok' 1 1, "")
    p "Tag" `shouldBe` Right (Tag $ tok "Tag" 1 1, "")
    p "var" `shouldBe` Right (Var $ tok "var" 1 1, "")
    p "42" `shouldBe` Right (Int $ tok 42 1 1, "")
    p "3.14" `shouldBe` Right (Num $ tok 3.14 1 1, "")
    p "()" `shouldBe` Right (Tuple (tok' 1 1) [] (tok' 1 2), "")
    p "{}" `shouldBe` Right (Record (tok' 1 1) [] (tok' 1 2), "")
    p "\\x=y" `shouldBe` Right (Lambda [VarP $ tok "x" 1 2] (Var $ tok "y" 1 4), "")
    p "\\x y = z" `shouldBe` Right (Lambda [VarP $ tok "x" 1 2, VarP $ tok "y" 1 4] (Var $ tok "z" 1 8), "")
    p "\\x\ny\n=\nz" `shouldBe` Right (Lambda [VarP $ tok "x" 1 2, VarP $ tok "y" 2 1] (Var $ tok "z" 4 1), "")
    p "x |  y" `shouldBe` Right (Or (Var $ tok "x" 1 1) (tok' 1 3) (Var $ tok "y" 1 6), "")
    p "x :  y" `shouldBe` Right (Ann (Var $ tok "x" 1 1) (For [] $ Var $ tok "y" 1 6), "")
    p "x : @a. y" `shouldBe` Right (Ann (Var $ tok "x" 1 1) (For [tok "a" 1 6] $ Var $ tok "y" 1 9), "")
    p "x : @a b. y" `shouldBe` Right (Ann (Var $ tok "x" 1 1) (For [tok "a" 1 6, tok "b" 1 8] $ Var $ tok "y" 1 11), "")
    p "x == y" `shouldBe` Right (Eq (Var $ tok "x" 1 1) (tok' 1 3) (Var $ tok "y" 1 6), "")
    p "x <  y" `shouldBe` Right (Lt (Var $ tok "x" 1 1) (tok' 1 3) (Var $ tok "y" 1 6), "")
    p "x -> y" `shouldBe` Right (Fun (Var $ tok "x" 1 1) (tok' 1 3) (Var $ tok "y" 1 6), "")
    p "x +  y" `shouldBe` Right (Add (Var $ tok "x" 1 1) (tok' 1 3) (Var $ tok "y" 1 6), "")
    p "x -  y" `shouldBe` Right (Sub (Var $ tok "x" 1 1) (tok' 1 3) (Var $ tok "y" 1 6), "")
    p "x *  y" `shouldBe` Right (Mul (Var $ tok "x" 1 1) (tok' 1 3) (Var $ tok "y" 1 6), "")
    p "x    y" `shouldBe` Right (App (Var $ tok "x" 1 1) (tok' 1 6) (Var $ tok "y" 1 6), "")
    p "x ^  y" `shouldBe` Right (Pow (Var $ tok "x" 1 1) (tok' 1 3) (Var $ tok "y" 1 6), "")
    p "x\ny" `shouldBe` Right (Var $ tok "x" 1 1, "\ny")
    p "(x\ny)" `shouldBe` Right (App (Var $ tok "x" 1 2) (tok' 1 3) (Var $ tok "y" 2 1), "")

  it "☯ letDef" $ do
    let p = parse' letDef
    let def = LetDef {docs = Nothing, name = tok "" 1 1, type' = Nothing, rules = []}
    p "x = 42" `shouldBe` Right (def {name = tok "x" 1 1, rules = [([], Int $ tok 42 1 5)]}, "")
    p "x : Int = 42" `shouldBe` Right (def {name = tok "x" 1 1, type' = Just (For [] $ IntT $ tok' 1 5), rules = [([], Int $ tok 42 1 11)]}, "")
    p "x : Int\nx = 42" `shouldBe` Right (def {name = tok "x" 1 1, type' = Just (For [] $ IntT $ tok' 1 5), rules = [([], Int $ tok 42 2 5)]}, "")
    p "f x = 1\nf y = 2" `shouldBe` Right (def {name = tok "f" 1 1, type' = Nothing, rules = [([VarP $ tok "x" 1 3], Int $ tok 1 1 7), ([VarP $ tok "y" 2 3], Int $ tok 2 2 7)]}, "")

  -- it "☯ unpackDef" $ do
  -- it "☯ typeDef" $ do
  -- it "☯ test" $ do

  it "☯ definition" $ do
    let p = parse' definition
    p "x = 42" `shouldBe` Right (LetDef {docs = Nothing, name = tok "x" 1 1, type' = Nothing, rules = [([], Int $ tok 42 1 5)]}, "")

  it "☯ import'" $ do
    let p = parse' import'
    let imp = Import {path = tok "" 1 1, name = tok "" 1 1, exposing = []}
    p "import mod" `shouldBe` Right (imp {path = tok "mod" 1 8, name = tok "mod" 1 8}, "")
    p "import dir/to/mod" `shouldBe` Right (imp {path = tok "dir/to/mod" 1 8, name = tok "mod" 1 15}, "")
    p "import mod as m" `shouldBe` Right (imp {path = tok "mod" 1 8, name = tok "m" 1 15}, "")
    p "import mod as m ()" `shouldBe` Right (imp {path = tok "mod" 1 8, name = tok "m" 1 15}, "")
    p "import mod as m (a, b)" `shouldBe` Right (imp {path = tok "mod" 1 8, name = tok "m" 1 15, exposing = [tok "a" 1 18, tok "b" 1 21]}, "")

  it "☯ sourceFile" $ do
    let p = parse' sourceFile
    let docs = Just DocString {public = True, description = "docs"}
    p "===\ndocs\n===" `shouldBe` Right (SourceFile {docs = docs, imports = [], definitions = []}, "")
    let imports = [tok (Import {path = tok "mod" 4 8, name = tok "mod" 4 8, exposing = []}) 4 1]
    p "===\ndocs\n===\nimport mod" `shouldBe` Right (SourceFile {docs = docs, imports = imports, definitions = []}, "")
    let defs = [LetDef {docs = Nothing, name = tok "x" 5 1, type' = Nothing, rules = [([], Int $ tok 42 5 5)]}]
    p "===\ndocs\n===\nimport mod\nx = 42" `shouldBe` Right (SourceFile {docs = docs, imports = imports, definitions = defs}, "")

  -- it "☯ module" $ do

  it "TODO" $ do
    True `shouldBe` True
