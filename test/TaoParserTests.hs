module TaoParserTests where

import qualified Core as C
import qualified Parser as P
import System.Directory (withCurrentDirectory)
import Tao
import TaoParser
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ TaoParser ☯==--" $ do
  let parse' :: Parser a -> String -> Either ([ParserContext], String) (a, String)
      parse' parser src = case P.parse "TaoParserTests" parser src of
        Right (x, P.State {remaining}) -> Right (x, remaining)
        Left P.State {context, remaining} -> Left (context, remaining)

  it "☯ parseName" $ do
    let p = parse' (parseName P.letter)
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
    p "dash-case-name - 1" `shouldBe` Right ("dash-case-name", " - 1")
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

  -- it "☯ parseRecordField" $ do
  --   let p = parse' parseRecordField
  --   p "x" `shouldBe` Right (("x", Var "x"), "")
  --   p "x=y" `shouldBe` Right (("x", Var "y"), "")
  --   p "x:y" `shouldBe` Right (("x", Ann (Var "x") (Var "y")), "")
  --   p "x:y=z" `shouldBe` Right (("x", Ann (Var "z") (Var "y")), "")
  --   p "x \n = \n y" `shouldBe` Right (("x", Var "y"), "")
  --   p "x \n : \n y" `shouldBe` Right (("x", Ann (Var "x") (Var "y")), "")
  --   p "x \n : \n y \n = z" `shouldBe` Right (("x", Ann (Var "z") (Var "y")), "")

  -- it "☯ parseRecord" $ do
  --   let p = parse' parseRecord
  --   p "{} abc" `shouldBe` Right (record [], " abc")
  --   p "{x} abc" `shouldBe` Right (record [("x", Var "x")], " abc")
  --   p "{x, y} abc" `shouldBe` Right (record [("x", Var "x"), ("y", Var "y")], " abc")

  it "☯ parseCases" $ do
    let p = parse' parseCases
    p "{}" `shouldBe` Left ([], "}")
    p "{ x }" `shouldBe` Left ([], "x }")
    p "{ | x }" `shouldBe` Right ([Var "x"], "")
    p "{ | x | y }" `shouldBe` Right ([Var "x", Var "y"], "")
    p "{\n|\nx\n|\ny\n}" `shouldBe` Right ([Var "x", Var "y"], "")

  it "☯ parseMatch" $ do
    let p = parse' parseMatch
    p "match" `shouldBe` Left ([CMatch], "")
    p "match {}" `shouldBe` Left ([CMatch], "")
    p "match {| x}" `shouldBe` Right (Match [] [Var "x"], "")
    p "match a {| x}" `shouldBe` Right (Match [Var "a"] [Var "x"], "")
    p "match a, b {| x}" `shouldBe` Right (Match [Var "a", Var "b"] [Var "x"], "")

  it "☯ parseExpr" $ do
    let p = parse' (parseExpr 0 P.spaces)
    p "_" `shouldBe` Right (Any, "")
    p "Int" `shouldBe` Right (IntType, "")
    p "Num" `shouldBe` Right (NumType, "")
    p "42" `shouldBe` Right (Int 42, "")
    p "3.14" `shouldBe` Right (Num 3.14, "")
    p "var" `shouldBe` Right (Var "var", "")
    p "Tag" `shouldBe` Right (Tag "Tag", "")
    p "@. x" `shouldBe` Right (For [] (Var "x"), "")
    p "@ x . y" `shouldBe` Right (For ["x"] (Var "y"), "")
    p "@ x y . z" `shouldBe` Right (For ["x", "y"] (Var "z"), "")
    p "@\nx\n.\ny" `shouldBe` Right (For ["x"] (Var "y"), "")
    p "x -> y" `shouldBe` Right (Fun (Var "x") (Var "y"), "")
    p "x\n->\ny" `shouldBe` Right (Fun (Var "x") (Var "y"), "")
    p "x y" `shouldBe` Right (App (Var "x") (Var "y"), "")
    p "x\ny" `shouldBe` Right (Var "x", "\ny")
    p "(x\ny)" `shouldBe` Right (App (Var "x") (Var "y"), "")
    p "()" `shouldBe` Right (Unit, "")
    p "(\n)" `shouldBe` Right (Unit, "")
    p "(x)" `shouldBe` Right (Var "x", "")
    p "(x,)" `shouldBe` Right (Var "x", "")
    p "(\nx\n,\n)" `shouldBe` Right (Var "x", "")
    p "(x, y)" `shouldBe` Right (And (Var "x") (Var "y"), "")
    p "(\nx\n,\ny\n)" `shouldBe` Right (And (Var "x") (Var "y"), "")
    p "(x, y, z)" `shouldBe` Right (and' [Var "x", Var "y", Var "z"], "")
    p "x | y" `shouldBe` Right (Or (Var "x") (Var "y"), "")
    p "x\n|\ny" `shouldBe` Right (Or (Var "x") (Var "y"), "")
    p "x : y" `shouldBe` Right (Ann (Var "x") (Var "y"), "")
    p "x\n:\ny" `shouldBe` Right (Ann (Var "x") (Var "y"), "")
    p "$call" `shouldBe` Right (Call "call" [], "")
    p "$call()" `shouldBe` Right (Call "call" [], "")
    p "$call(x)" `shouldBe` Right (Call "call" [Var "x"], "")
    p "$call(x, y, z)" `shouldBe` Right (Call "call" [Var "x", Var "y", Var "z"], "")
    p "$call(\nx,\ny)" `shouldBe` Right (Call "call" [Var "x", Var "y"], "")
    p "- x" `shouldBe` Right (neg (Var "x"), "")
    p "-\nx" `shouldBe` Right (neg (Var "x"), "")
    p "x == y" `shouldBe` Right (eq (Var "x") (Var "y"), "")
    p "x <  y" `shouldBe` Right (lt (Var "x") (Var "y"), "")
    p "x +  y" `shouldBe` Right (add (Var "x") (Var "y"), "")
    p "x -  y" `shouldBe` Right (sub (Var "x") (Var "y"), "")
    p "x *  y" `shouldBe` Right (mul (Var "x") (Var "y"), "")
    p "x ^  y" `shouldBe` Right (pow (Var "x") (Var "y"), "")
    -- p "x = y; z" `shouldBe` Right (Err, "")
    -- p "x\n=\ny\nz" `shouldBe` Right (Err, "")

    p "{}" `shouldBe` Right (Record [], "")
    p "{| x }" `shouldBe` Right (Match [] [Var "x"], "")
    p "match {| x}" `shouldBe` Right (Match [] [Var "x"], "")

  it "☯ parseImport" $ do
    let p = parse' parseImport
    p "import pkg" `shouldBe` Right (Import "pkg" "pkg" [], "")
    p "import pkg/mod" `shouldBe` Right (Import "pkg/mod" "mod" [], "")
    p "import pkg (a, b as c)" `shouldBe` Right (Import "pkg" "pkg" [("a", "a"), ("b", "c")], "")
  -- p "import /mod" `shouldBe` Right (Import "/mod" "mod" [], "")

  it "☯ parseDef" $ do
    let p = parse' parseDef
    p "x = y" `shouldBe` Right ((Var "x", Var "y"), "")
    p "x y = z" `shouldBe` Right ((App (Var "x") (Var "y"), Var "z"), "")
    p "x : a = y" `shouldBe` Right ((Ann (Var "x") (Var "a"), Var "y"), "")
    p ": a\nx = y" `shouldBe` Right ((Ann (Var "x") (Var "a"), Var "y"), "")

  it "☯ parseTypeDef" $ do
    let p = parse' parseTypeDef
    p "type A = x" `shouldBe` Right (("A", [], Var "x"), "")
    p "type A x y = z" `shouldBe` Right (("A", [Var "x", Var "y"], Var "z"), "")

  it "☯ parseTest" $ do
    let p = parse' parseTest
    p "> x; y" `shouldBe` Right (Test "" (Var "x") (Var "y"), "")
    p "> x\ny" `shouldBe` Right (Test "" (Var "x") (Var "y"), "")
    p "> x" `shouldBe` Right (Test "" (Var "x") (Tag "True"), "")

  it "☯ parseStmt" $ do
    let p = parse' parseStmt
    p "import pkg" `shouldBe` Right (Import "pkg" "pkg" [], "")
    -- p "x = y" `shouldBe` Right (Define (Def [] (Var "x") (Var "y")), "")
    p "> x; y" `shouldBe` Right (Test "" (Var "x") (Var "y"), "")

  it "☯ parseModule" $ do
    let p = parse' (parseModule "path/my-file.tao")
    p "" `shouldBe` Right (("path/my-file.tao", []), "")
    p "x" `shouldBe` Left ([CModule], "x")
    p "import pkg" `shouldBe` Right (("path/my-file.tao", [Import "pkg" "pkg" []]), "")

  -- it "☯ parsePackage directory" $ do
  --   let pkg = Package {name = "empty", modules = [Module "empty/empty-file" []]}
  --   parsePackage "examples/empty" `shouldReturn` (pkg, [])
  --   withCurrentDirectory "examples" (parsePackage "empty") `shouldReturn` (pkg, [])

  -- it "☯ parsePackage file" $ do
  --   let pkg = Package {name = "empty", modules = [Module "empty/empty" []]}
  --   parsePackage "examples/empty.tao" `shouldReturn` (pkg, [])
  --   withCurrentDirectory "examples" (parsePackage "empty.tao") `shouldReturn` (pkg, [])

  it "☯ loadModule" $ do
    let pkg = ("pkg", [])
    let expect = ("pkg", [("examples/empty", [])])
    loadModule "examples" "empty.tao" (pkg, []) `shouldReturn` (expect, [])

  it "☯ loadModule exists" $ do
    let pkg = ("pkg", [("my-file", [])])
    loadModule "base-path" "my-file" (pkg, []) `shouldReturn` (pkg, [])

  it "☯ loadPackage" $ do
    let load path = loadPackage path (("pkg", []), [])
    let pkg =
          ( "pkg",
            [ ( "sub/mod",
                [ defVar ("x", Int 1),
                  defVar ("y", Int 2)
                ]
              )
            ]
          )
    load "examples/sub" `shouldReturn` (pkg, [] :: [SyntaxError])

  it "☯ load" $ do
    let pkg =
          ( "sub",
            [ ("empty/empty-file", []),
              ( "sub/mod",
                [ defVar ("x", Int 1),
                  defVar ("y", Int 2)
                ]
              )
            ]
          )
    let errors = []
    load "examples/sub" ["examples/empty"] `shouldReturn` (pkg, errors)
