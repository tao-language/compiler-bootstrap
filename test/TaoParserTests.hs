{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TaoParserTests where

import Core
import qualified Parser as P
import Tao
import TaoParser
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ TaoParser ☯==--" $ do
  let sourceName = "test"
  let loc row col = Location sourceName (row, col)
  let expr row col = taoMeta [loc row col]
  let var row col x = expr row col (TaoVar x)

  let parse' :: TaoParser a -> String -> Either ([ParserContext], String) (a, String)
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
  --   p "---\n---\nabc" `shouldBe` Right (newDocString {public = True, taoMeta = [loc 1 1]}, "abc")
  --   p "---\ndocs\n---\nabc" `shouldBe` Right (newDocString {public = True, description = "docs", taoMeta = [loc 1 1]}, "abc")
  --   p "---  \n  docs  \n  ---  \nabc" `shouldBe` Right (newDocString {public = True, description = "docs", taoMeta = [loc 1 1]}, "abc")
  --   p "---  private  \nA\nB\n\nC\n  ---  \nabc" `shouldBe` Right (newDocString {public = False, description = "A\nB\n\nC", taoMeta = [loc 1 1]}, "abc")
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
  --             taoMeta =
  --               [ loc 2 1,
  --                 parseComments [parseComment (1, 3) "A"],
  --                 TrailingparseComment (parseComment (2, 7) "B"),
  --                 TrailingparseComment (parseComment (4, 7) "C")
  --               ]
  --           },
  --         "# end"
  --       )

  -- it "☯ taoMetadata parseLocation" $ do
  --   let taoMeta row col x = ([parseLocation sourceName row col], x)
  --   let p = parse' $ taoMetadata (P.text "abc")
  --   p "abcdef" `shouldBe` Right (taoMeta 1 1 "abc", "def")
  --   p "abc   def" `shouldBe` Right (taoMeta 1 1 "abc", "def")
  --   p "abc \n  def" `shouldBe` Right (taoMeta 1 1 "abc", "\n  def")

  -- it "☯ taoMetadata parseComments" $ do
  --   let taoMeta row col parseComments x = ([parseLocation sourceName row col, parseComments parseComments], x)
  --   let p = parse' $ taoMetadata (P.text "abc")
  --   p "#A\n#B\nabc def" `shouldBe` Right (taoMeta 3 1 ["A", "B"] "abc", "def")
  --   p "# A \n \n \n  #  B  \n  abc  def" `shouldBe` Right (taoMeta 5 3 ["A", "B"] "abc", "def")

  -- it "☯ taoMetadata parseComments (trailing)" $ do
  --   let taoMeta row col parseComment x = ([parseLocation sourceName row col, TrailingparseComment parseComment], x)
  --   let p = parse' $ taoMetadata (P.text "abc")
  --   p "abc#parseComment" `shouldBe` Right (taoMeta 1 1 "parseComment" "abc", "")
  --   p "abc#  parseComment  " `shouldBe` Right (taoMeta 1 1 "parseComment" "abc", "")

  it "☯ parseName" $ do
    let p = parse' parseName
    p "var x y;" `shouldBe` Right (TaoVar "var", "x y;")
    p "Tag;" `shouldBe` Right (TaoTag "Tag" [], ";")
    p "Tag x y;" `shouldBe` Right (TaoTag "Tag" [var 1 5 "x", var 1 7 "y"], ";")

  it "☯ parseTuple" $ do
    let p = parse' parseTuple
    p "() abc" `shouldBe` Right (TaoTuple [], " abc")
    p "(x) abc" `shouldBe` Right (TaoVar "x", " abc")
    p "(x,) abc" `shouldBe` Right (TaoTuple [var 1 2 "x"], " abc")
    p "(x, y) abc" `shouldBe` Right (TaoTuple [var 1 2 "x", var 1 5 "y"], " abc")

  it "☯ parseRecordField" $ do
    let p = parse' parseRecordField
    p "x" `shouldBe` Left ([CRecordField "x"], "")
    p "x:y" `shouldBe` Right (("x", var 1 3 "y"), "")
    p "x \n : \n y" `shouldBe` Right (("x", var 3 2 "y"), "")

  it "☯ parseRecord" $ do
    let p = parse' parseRecord
    p "{} abc" `shouldBe` Right (TaoRecord [], " abc")
    p "{x: y} abc" `shouldBe` Right (TaoRecord [("x", var 1 5 "y")], " abc")
    p "{x: y, z: w} abc" `shouldBe` Right (TaoRecord [("x", var 1 5 "y"), ("z", var 1 11 "w")], " abc")

  it "☯ parseExpr'" $ do
    let p = parse' (parseExpr $ P.ok ())
    p "Type" `shouldBe` Right (taoMeta [loc 1 1] $ TaoTag "Type" [], "")
    p "Int" `shouldBe` Right (taoMeta [loc 1 1] $ TaoTag "Int" [], "")
    p "Num" `shouldBe` Right (taoMeta [loc 1 1] $ TaoTag "Num" [], "")
    p "42" `shouldBe` Right (taoMeta [loc 1 1] $ TaoInt 42, "")
    p "3.14" `shouldBe` Right (taoMeta [loc 1 1] $ TaoNum 3.14, "")
    p "var" `shouldBe` Right (taoMeta [loc 1 1] $ TaoVar "var", "")
    p "Tag" `shouldBe` Right (taoMeta [loc 1 1] $ TaoTag "Tag" [], "")
    p "()" `shouldBe` Right (taoMeta [loc 1 1] $ TaoTuple [], "")
    p "{}" `shouldBe` Right (taoMeta [loc 1 1] $ TaoRecord [], "")
    p "x |  y" `shouldBe` Right (taoMeta [loc 1 3] $ TaoOr (var 1 1 "x") (var 1 6 "y"), "")
    p "x :  y" `shouldBe` Right (taoMeta [loc 1 3] $ TaoAnn (var 1 1 "x") (var 1 6 "y"), "")
    p "x == y" `shouldBe` Right (taoMeta [loc 1 3] $ taoEq (var 1 1 "x") (var 1 6 "y"), "")
    p "x <  y" `shouldBe` Right (taoMeta [loc 1 3] $ taoLt (var 1 1 "x") (var 1 6 "y"), "")
    p "x -> y" `shouldBe` Right (taoMeta [loc 1 3] $ TaoFun (var 1 1 "x") (var 1 6 "y"), "")
    p "x +  y" `shouldBe` Right (taoMeta [loc 1 3] $ taoAdd (var 1 1 "x") (var 1 6 "y"), "")
    p "x -  y" `shouldBe` Right (taoMeta [loc 1 3] $ taoSub (var 1 1 "x") (var 1 6 "y"), "")
    p "x *  y" `shouldBe` Right (taoMeta [loc 1 3] $ taoMul (var 1 1 "x") (var 1 6 "y"), "")
    p "x    y" `shouldBe` Right (TaoApp (var 1 1 "x") (var 1 6 "y"), "")
    p "x ^  y" `shouldBe` Right (taoMeta [loc 1 3] $ taoPow (var 1 1 "x") (var 1 6 "y"), "")
    p "x\ny" `shouldBe` Right (taoMeta [loc 1 1] $ TaoVar "x", "\ny")
    p "(x\ny)" `shouldBe` Right (taoMeta [loc 1 1] $ TaoApp (var 1 2 "x") (var 2 1 "y"), "")

  it "☯ parseDefinition" $ do
    let p = parse' parseDefinition
    p "x = y" `shouldBe` Right ((var 1 1 "x", var 1 5 "y"), "")
    p "x = y;" `shouldBe` Right ((var 1 1 "x", var 1 5 "y"), "")
    p "x = y\n" `shouldBe` Right ((var 1 1 "x", var 1 5 "y"), "")
    p "x =\ny" `shouldBe` Right ((var 1 1 "x", var 2 1 "y"), "")
    p "x\n= y" `shouldBe` Right ((var 1 1 "x", var 2 3 "y"), "")
    p "x : a = y" `shouldBe` Right ((taoMeta [loc 1 3] $ TaoAnn (var 1 1 "x") (var 1 5 "a"), var 1 9 "y"), "")

  it "☯ parseTypeAnnotation" $ do
    let p = parse' parseTypeAnnotation
    p "x : a" `shouldBe` Right (("x", var 1 5 "a"), "")
    p "x : a;" `shouldBe` Right (("x", var 1 5 "a"), "")
    p "x : a\n" `shouldBe` Right (("x", var 1 5 "a"), "")

  it "☯ parseImport" $ do
    let p = parse' parseImport
    p "import mod" `shouldBe` Right (TaoImport "mod" "mod" [], "")
    p "import dir/to/mod" `shouldBe` Right (TaoImport "dir/to/mod" "dir/to/mod" [], "")
    p "import mod as m" `shouldBe` Right (TaoImport "mod" "m" [], "")
    p "import mod as m ()" `shouldBe` Right (TaoImport "mod" "m" [], "")
    p "import mod as m (a, b)" `shouldBe` Right (TaoImport "mod" "m" ["a", "b"], "")

  it "☯ parseTest" $ do
    let p = parse' parseTest
    p "> x; y" `shouldBe` Right (TaoTest (var 1 3 "x") (var 1 6 "y"), "")
    p "> x\ny" `shouldBe` Right (TaoTest (var 1 3 "x") (var 2 1 "y"), "")
    p "> x : a" `shouldBe` Right (TaoTest (taoMeta [loc 1 5] $ TaoAnn (var 1 3 "x") (var 1 7 "a")) (var 1 3 "x"), "")
    p "> x" `shouldBe` Right (TaoTest (var 1 3 "x") (TaoTag "True" []), "")

  it "☯ parseStmt" $ do
    let p = parse' parseStmt
    p "x = y" `shouldBe` Right (TaoDef (var 1 1 "x") (var 1 5 "y"), "")
    p "x : a" `shouldBe` Right (TaoTypeAnn "x" (var 1 5 "a"), "")
    p "import mod" `shouldBe` Right (TaoImport "mod" "mod" [], "")
    p "> x; y" `shouldBe` Right (TaoTest (var 1 3 "x") (var 1 6 "y"), "")

  it "☯ parseFile" $ do
    let p = parse' (parseFile "my-file.tao")
    p "" `shouldBe` Right (("my-file.tao", []), "")
    p "x" `shouldBe` Left ([CFile], "x")
    p "import m" `shouldBe` Right (("my-file.tao", [TaoImport "m" "m" []]), "")

  it "☯ parseModule'" $ do
    -- Skip modules that are already in the package.
    let mod = TaoModule {name = "mod", files = [("my-file", [])]}
    parseModule "my-file" mod `shouldReturn` mod

    -- Parse new modules.
    let mod = TaoModule {name = "mod", files = []}
    parseModule "examples/empty.tao" mod `shouldReturn` mod {files = [("examples/empty.tao", [])]}
