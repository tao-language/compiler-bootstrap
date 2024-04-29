module TaoParserTests where

import qualified Core as C
import qualified Parser as P
import Tao
import TaoParser
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ TaoParser ☯==--" $ do
  let sourceName = "TaoParserTests"
  let loc row col = C.Location sourceName (row, col)
  let expr row col = meta [loc row col]
  let var row col x = expr row col (Var x)

  let parse' :: Parser a -> String -> Either ([ParserContext], String) (a, String)
      parse' parser src = case P.parse sourceName parser src of
        Right (x, P.State {remaining}) -> Right (x, remaining)
        Left P.State {context, remaining} -> Left (context, remaining)

  it "☯ parseIdentifier" $ do
    let p = parse' parseIdentifier
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

  it "☯ parseLineBreak" $ do
    let p = parse' parseLineBreak
    p "" `shouldBe` Right ("", "")
    p "x" `shouldBe` Left ([], "x")
    p "\n" `shouldBe` Right ("", "")
    p ";" `shouldBe` Right ("", "")
    p "# trailing parseComment" `shouldBe` Right ("trailing parseComment", "")

  it "☯ parseInbetween" $ do
    let p = parse' (parseInbetween "(" ")" (P.zeroOrMore P.letter))
    p "" `shouldBe` Left ([], "")
    p "()" `shouldBe` Right ("", "")
    p "(abc)" `shouldBe` Right ("abc", "")
    p "( \n abc \n )  \ndef" `shouldBe` Right ("abc", "  \ndef")

  it "☯ parseCollection" $ do
    let p = parse' $ parseCollection "[" "," "]" (P.paddedR P.whitespaces P.letter)
    p "[] ." `shouldBe` Right ("", " .")
    p "[,]" `shouldBe` Left ([], ",]")
    p "[a]" `shouldBe` Right ("a", "")
    p "[a,]" `shouldBe` Right ("a", "")
    p "[a, b]" `shouldBe` Right ("ab", "")
    p "[a, b,]" `shouldBe` Right ("ab", "")
    p "[ \n a \n , \n b \n , \n ]" `shouldBe` Right ("ab", "")

  -- it "☯ docString" $ do
  --   let p = parse' $ docString (P.text "---")
  --   p "---\n---\nabc" `shouldBe` Right (newDocString {public = True, meta = [loc 1 1]}, "abc")
  --   p "---\ndocs\n---\nabc" `shouldBe` Right (newDocString {public = True, description = "docs", meta = [loc 1 1]}, "abc")
  --   p "---  \n  docs  \n  ---  \nabc" `shouldBe` Right (newDocString {public = True, description = "docs", meta = [loc 1 1]}, "abc")
  --   p "---  private  \nA\nB\n\nC\n  ---  \nabc" `shouldBe` Right (newDocString {public = False, description = "A\nB\n\nC", meta = [loc 1 1]}, "abc")
  --   let src =
  --         [ "# A",
  --           "--- # B",
  --           "Docs",
  --           "--- # C",
  --           "# end"
  --         ]
  --   p (intercalate "\n" src)
  --     `shouldBe` Right
  --       ( newDocString
  --           { public = True,
  --             description = "Docs",
  --             meta =
  --               [ loc 2 1,
  --                 parseComments [parseComment (1, 3) "A"],
  --                 TrailingparseComment (parseComment (2, 7) "B"),
  --                 TrailingparseComment (parseComment (4, 7) "C")
  --               ]
  --           },
  --         "# end"
  --       )

  -- it "☯ metadata parseLocation" $ do
  --   let meta row col x = ([parseLocation sourceName row col], x)
  --   let p = parse' $ metadata (P.text "abc")
  --   p "abcdef" `shouldBe` Right (meta 1 1 "abc", "def")
  --   p "abc   def" `shouldBe` Right (meta 1 1 "abc", "def")
  --   p "abc \n  def" `shouldBe` Right (meta 1 1 "abc", "\n  def")

  -- it "☯ metadata parseComments" $ do
  --   let meta row col parseComments x = ([parseLocation sourceName row col, parseComments parseComments], x)
  --   let p = parse' $ metadata (P.text "abc")
  --   p "#A\n#B\nabc def" `shouldBe` Right (meta 3 1 ["A", "B"] "abc", "def")
  --   p "# A \n \n \n  #  B  \n  abc  def" `shouldBe` Right (meta 5 3 ["A", "B"] "abc", "def")

  -- it "☯ metadata parseComments (trailing)" $ do
  --   let meta row col parseComment x = ([parseLocation sourceName row col, TrailingparseComment parseComment], x)
  --   let p = parse' $ metadata (P.text "abc")
  --   p "abc#parseComment" `shouldBe` Right (meta 1 1 "parseComment" "abc", "")
  --   p "abc#  parseComment  " `shouldBe` Right (meta 1 1 "parseComment" "abc", "")

  it "☯ parseName" $ do
    let p = parse' parseName
    p "var x y;" `shouldBe` Right (Var "var", "x y;")
    p "Tag;" `shouldBe` Right (Tag "Tag" [], ";")
    p "Tag x y;" `shouldBe` Right (Tag "Tag" [var 1 5 "x", var 1 7 "y"], ";")

  it "☯ parseTuple" $ do
    let p = parse' parseTuple
    p "() abc" `shouldBe` Right (Tuple [], " abc")
    p "(x) abc" `shouldBe` Right (Var "x", " abc")
    p "(x,) abc" `shouldBe` Right (Tuple [var 1 2 "x"], " abc")
    p "(x, y) abc" `shouldBe` Right (Tuple [var 1 2 "x", var 1 5 "y"], " abc")

  it "☯ parseRecordField" $ do
    let p = parse' parseRecordField
    p "x" `shouldBe` Left ([CRecordField "x"], "")
    p "x:y" `shouldBe` Right (("x", var 1 3 "y"), "")
    p "x \n : \n y" `shouldBe` Right (("x", var 3 2 "y"), "")

  it "☯ parseRecord" $ do
    let p = parse' parseRecord
    p "{} abc" `shouldBe` Right (Record [], " abc")
    p "{x: y} abc" `shouldBe` Right (Record [("x", var 1 5 "y")], " abc")
    p "{x: y, z: w} abc" `shouldBe` Right (Record [("x", var 1 5 "y"), ("z", var 1 11 "w")], " abc")

  it "☯ parseExpr'" $ do
    let p = parse' (parseExpr $ P.ok ())
    p "Type" `shouldBe` Right (meta [loc 1 1] $ Tag "Type" [], "")
    p "Int" `shouldBe` Right (meta [loc 1 1] $ Tag "Int" [], "")
    p "Num" `shouldBe` Right (meta [loc 1 1] $ Tag "Num" [], "")
    p "42" `shouldBe` Right (meta [loc 1 1] $ Int 42, "")
    p "3.14" `shouldBe` Right (meta [loc 1 1] $ Num 3.14, "")
    p "var" `shouldBe` Right (meta [loc 1 1] $ Var "var", "")
    p "Tag" `shouldBe` Right (meta [loc 1 1] $ Tag "Tag" [], "")
    p "()" `shouldBe` Right (meta [loc 1 1] $ Tuple [], "")
    p "{}" `shouldBe` Right (meta [loc 1 1] $ Record [], "")
    p "x |  y" `shouldBe` Right (meta [loc 1 3] $ Or (var 1 1 "x") (var 1 6 "y"), "")
    p "x :  y" `shouldBe` Right (meta [loc 1 3] $ Ann (var 1 1 "x") (var 1 6 "y"), "")
    p "x == y" `shouldBe` Right (meta [loc 1 3] $ eq (var 1 1 "x") (var 1 6 "y"), "")
    p "x <  y" `shouldBe` Right (meta [loc 1 3] $ lt (var 1 1 "x") (var 1 6 "y"), "")
    p "x -> y" `shouldBe` Right (meta [loc 1 3] $ Fun (var 1 1 "x") (var 1 6 "y"), "")
    p "x +  y" `shouldBe` Right (meta [loc 1 3] $ add (var 1 1 "x") (var 1 6 "y"), "")
    p "x -  y" `shouldBe` Right (meta [loc 1 3] $ sub (var 1 1 "x") (var 1 6 "y"), "")
    p "x *  y" `shouldBe` Right (meta [loc 1 3] $ mul (var 1 1 "x") (var 1 6 "y"), "")
    p "x    y" `shouldBe` Right (App (var 1 1 "x") (var 1 6 "y"), "")
    p "x ^  y" `shouldBe` Right (meta [loc 1 3] $ pow (var 1 1 "x") (var 1 6 "y"), "")
    p "x\ny" `shouldBe` Right (meta [loc 1 1] $ Var "x", "\ny")
    p "(x\ny)" `shouldBe` Right (meta [loc 1 1] $ App (var 1 2 "x") (var 2 1 "y"), "")

  it "☯ parseDefinition" $ do
    let p = parse' parseDefinition
    p "x = y" `shouldBe` Right ((DefName "x" Any, [], var 1 5 "y"), "")
    p "x = y;" `shouldBe` Right ((DefName "x" Any, [], var 1 5 "y"), "")
    p "x = y\n" `shouldBe` Right ((DefName "x" Any, [], var 1 5 "y"), "")
    p "x =\ny" `shouldBe` Right ((DefName "x" Any, [], var 2 1 "y"), "")
    p "x\n= y" `shouldBe` Right ((DefName "x" Any, [], var 2 3 "y"), "")
    p "x : a = y" `shouldBe` Right ((DefName "x" (var 1 5 "a"), [], var 1 9 "y"), "")

  it "☯ parseTypeAnnotation" $ do
    let p = parse' parseTypeAnnotation
    p "x : a" `shouldBe` Right (("x", var 1 5 "a"), "")
    p "x : a;" `shouldBe` Right (("x", var 1 5 "a"), "")
    p "x : a\n" `shouldBe` Right (("x", var 1 5 "a"), "")

  it "☯ parseImport" $ do
    let p = parse' parseImport
    p "import mod" `shouldBe` Right (Import "mod" "mod" [], "")
    p "import dir/to/mod" `shouldBe` Right (Import "dir/to/mod" "dir/to/mod" [], "")
    p "import mod as m" `shouldBe` Right (Import "mod" "m" [], "")
    p "import mod as m ()" `shouldBe` Right (Import "mod" "m" [], "")
    p "import mod as m (a, b as c)" `shouldBe` Right (Import "mod" "m" [("a", "a"), ("b", "c")], "")

  it "☯ parseTest" $ do
    let p = parse' parseTest
    p "> x; y" `shouldBe` Right (Test (var 1 3 "x") (var 1 6 "y"), "")
    p "> x\ny" `shouldBe` Right (Test (var 1 3 "x") (var 2 1 "y"), "")
    p "> x : a" `shouldBe` Right (Test (meta [loc 1 5] $ Ann (var 1 3 "x") (var 1 7 "a")) (var 1 3 "x"), "")
    p "> x" `shouldBe` Right (Test (var 1 3 "x") (Tag "True" []), "")

  it "☯ parseStmt" $ do
    let p = parse' parseStmt
    p "x = y" `shouldBe` Right (Def (DefName "x" Any) [] (var 1 5 "y"), "")
    p "import mod" `shouldBe` Right (Import "mod" "mod" [], "")
    p "> x; y" `shouldBe` Right (Test (var 1 3 "x") (var 1 6 "y"), "")

  it "☯ parseModule" $ do
    let p = parse' (parseModule "my-file.tao")
    p "" `shouldBe` Right (Module "my-file.tao" [], "")
    p "x" `shouldBe` Left ([CModule], "x")
    p "import m" `shouldBe` Right (Module "my-file.tao" [Import "m" "m" []], "")

  it "☯ parsePackage'" $ do
    -- Skip modules that are already in the package.
    let pkg = Package {name = "pkg", modules = [Module "my-file" []]}
    parsePackage "my-file" pkg `shouldReturn` pkg

    -- Parse new modules.
    let pkg = Package {name = "pkg", modules = []}
    parsePackage "examples/empty.tao" pkg `shouldReturn` pkg {modules = [Module "examples/empty.tao" []]}
