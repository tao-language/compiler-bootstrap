module TaoParserTests where

import qualified Core as C
import qualified Parser as P
import System.Directory (withCurrentDirectory)
import Tao
import TaoParser
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ TaoParser ☯==--" $ do
  let sourceName = "TaoParserTests"
  let loc row col = C.Location sourceName (row, col)
  let expr row col = meta [loc row col]
  let var row col x = expr row col (Var x)
  let pat row col = PMeta (loc row col)
  let pvar row col x = pat row col (PVar x)

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
    p "dash-case-name - 1" `shouldBe` Right ("dash-case-name", " - 1")
    p "a->" `shouldBe` Right ("a", "->")

  it "☯ parsePath" $ do
    let p = parse' parsePath
    p "name" `shouldBe` Left ([], "name")
    p "@package" `shouldBe` Right ("@package", "")
    p "@package.name" `shouldBe` Right ("@package", ".name")
    p "@package/module.name" `shouldBe` Right ("@package/module", ".name")
    p "@package/path/to/module.name" `shouldBe` Right ("@package/path/to/module", ".name")
    p "@/path/to/module.name" `shouldBe` Right ("@/path/to/module", ".name")

  it "☯ parseName" $ do
    let p = parse' parseName
    p "name" `shouldBe` Right ("name", "")
    p "@package" `shouldBe` Left ([], "@package")
    p "@package.name" `shouldBe` Right ("@package.name", "")
    p "@package/module.name" `shouldBe` Right ("@package/module.name", "")
    p "@package/path/to/module.name" `shouldBe` Right ("@package/path/to/module.name", "")
    p "@/path/to/module.name" `shouldBe` Right ("@/path/to/module.name", "")

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

  it "☯ parseTuple" $ do
    let p = parse' (parseTuple Tuple (parseExpr 0 P.whitespaces))
    p "() abc" `shouldBe` Right (Tuple [], " abc")
    p "(x) abc" `shouldBe` Right (var 1 2 "x", " abc")
    p "(x,) abc" `shouldBe` Right (Tuple [var 1 2 "x"], " abc")
    p "(x, y) abc" `shouldBe` Right (Tuple [var 1 2 "x", var 1 5 "y"], " abc")

  -- it "☯ parseRecordField" $ do
  --   let p = parse' parseRecordField
  --   p "x" `shouldBe` Right (("x", var 1 1 "x"), "")
  --   p "x=y" `shouldBe` Right (("x", var 1 3 "y"), "")
  --   p "x:y" `shouldBe` Right (("x", Ann (var 1 1 "x") (var 1 3 "y")), "")
  --   p "x:y=z" `shouldBe` Right (("x", Ann (var 1 5 "z") (var 1 3 "y")), "")
  --   p "x \n = \n y" `shouldBe` Right (("x", var 3 2 "y"), "")
  --   p "x \n : \n y" `shouldBe` Right (("x", Ann (var 1 1 "x") (var 3 2 "y")), "")
  --   p "x \n : \n y \n = z" `shouldBe` Right (("x", Ann (var 4 4 "z") (var 3 2 "y")), "")

  -- it "☯ parseRecord" $ do
  --   let p = parse' parseRecord
  --   p "{} abc" `shouldBe` Right (record [], " abc")
  --   p "{x} abc" `shouldBe` Right (record [("x", var 1 2 "x")], " abc")
  --   p "{x, y} abc" `shouldBe` Right (record [("x", var 1 2 "x"), ("y", var 1 5 "y")], " abc")

  it "☯ parsePattern" $ do
    let p = parse' parsePattern
    p "_ y" `shouldBe` Right (pat 1 1 PAny, "y")
    p "42 y" `shouldBe` Right (pat 1 1 (PInt 42), "y")
    p "3.14 y" `shouldBe` Right (pat 1 1 (PNum 3.14), "y")
    p "x y" `shouldBe` Right (pvar 1 1 "x", "y")
    -- PType [String]
    p "A" `shouldBe` Right (pat 1 1 (PTag "A" []), "")
    -- p "A y" `shouldBe` Right (pat 1 1 (pTag "A" [pvar 1 3 "y"]), "")
    -- PRecord [(String, Pattern)]
    -- PTag String [Pattern]
    -- PFun Pattern Pattern
    -- POr [Pattern]
    -- PEq Expr
    -- PMeta C.Metadata Pattern
    -- PErr
    True `shouldBe` True

  it "☯ parseCase" $ do
    let p = parse' parseCase
    p "%" `shouldBe` Left ([], "%")
    p "=> y;" `shouldBe` Left ([], "=> y;")
    p "x => y;" `shouldBe` Right (Case [pvar 1 1 "x"] Nothing (var 1 6 "y"), "")
    p "x, y => z;" `shouldBe` Right (Case [pvar 1 1 "x", pvar 1 4 "y"] Nothing (var 1 9 "z"), "")
    p "x if y => z;" `shouldBe` Right (Case [pvar 1 1 "x"] (Just $ var 1 6 "y") (var 1 11 "z"), "")

  it "☯ parseMatch" $ do
    let p = parse' parseMatch
    p "match" `shouldBe` Left ([CMatch], "")
    p "match; x => y" `shouldBe` Left ([CMatch], "; x => y")
    p "match a\nx => y" `shouldBe` Right (match [var 1 7 "a"] [Case [pvar 2 1 "x"] Nothing (var 2 6 "y")], "")
    p "match a, b\nx => y" `shouldBe` Right (match [var 1 7 "a", var 1 10 "b"] [Case [pvar 2 1 "x"] Nothing (var 2 6 "y")], "")
    p "match a\nx => y\na => b" `shouldBe` Right (match [var 1 7 "a"] [Case [pvar 2 1 "x"] Nothing (var 2 6 "y"), Case [pvar 3 1 "a"] Nothing (var 3 6 "b")], "")

  it "☯ parseExpr" $ do
    let p = parse' (parseExpr 0 P.spaces)
    p "Type" `shouldBe` Right (meta [loc 1 1] $ Tag "Type" [], "")
    p "Int" `shouldBe` Right (meta [loc 1 1] $ Tag "Int" [], "")
    p "Num" `shouldBe` Right (meta [loc 1 1] $ Tag "Num" [], "")
    p "42" `shouldBe` Right (meta [loc 1 1] $ Int 42, "")
    p "3.14" `shouldBe` Right (meta [loc 1 1] $ Num 3.14, "")
    p "var" `shouldBe` Right (meta [loc 1 1] $ Var "var", "")
    p "@pkg/mod.name" `shouldBe` Right (meta [loc 1 1] $ Var "@pkg/mod.name", "")
    p "Tag" `shouldBe` Right (meta [loc 1 1] $ Tag "Tag" [], "")
    p "x => y" `shouldBe` Right (match [] [Case [pvar 1 1 "x"] Nothing (var 1 6 "y")], "")
    p "x => y\na => b" `shouldBe` Right (match [] [Case [pvar 1 1 "x"] Nothing (var 1 6 "y"), Case [pvar 2 1 "a"] Nothing (var 2 6 "b")], "")
    p "match a\nx => y" `shouldBe` Right (meta [loc 1 1] $ match [var 1 7 "a"] [Case [pvar 2 1 "x"] Nothing (var 2 6 "y")], "")
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
    p "x = y" `shouldBe` Right (([], pvar 1 1 "x", var 1 5 "y"), "")
    p "x : a = y" `shouldBe` Right (([("x", var 1 5 "a")], pvar 1 1 "x", var 1 9 "y"), "")
    p "x : a\nx = y" `shouldBe` Right (([("x", var 1 5 "a")], pvar 2 1 "x", var 2 5 "y"), "")
    p "x : a\ny : b\nx = y" `shouldBe` Right (([("x", var 1 5 "a"), ("y", var 2 5 "b")], pvar 3 1 "x", var 3 5 "y"), "")

  it "☯ parseImport" $ do
    let p = parse' parseImport
    p "import @pkg" `shouldBe` Right (Import "@pkg" [], "")
    p "import @pkg/mod" `shouldBe` Right (Import "@pkg/mod" [], "")
    p "import @pkg (a, b as c)" `shouldBe` Right (Import "@pkg" [("a", "a"), ("b", "c")], "")
    p "import @/mod" `shouldBe` Right (Import "@/mod" [], "")

  it "☯ parseTest" $ do
    let p = parse' parseTest
    p "> x; y" `shouldBe` Right (Test "" (var 1 3 "x") (pvar 1 6 "y"), "")
    p "> x\ny" `shouldBe` Right (Test "" (var 1 3 "x") (pvar 2 1 "y"), "")
    p "> x" `shouldBe` Right (Test "" (var 1 3 "x") (PTag "True" []), "")

  it "☯ parseStmt" $ do
    let p = parse' parseStmt
    p "import @pkg" `shouldBe` Right (Import "@pkg" [], "")
    -- p "x = y" `shouldBe` Right (Define (Def [] (pvar 1 1 "x") (var 1 5 "y")), "")
    p "> x; y" `shouldBe` Right (Test "" (var 1 3 "x") (pvar 1 6 "y"), "")

  it "☯ parseModule" $ do
    let p = parse' (parseModule "path/my-file.tao")
    p "" `shouldBe` Right (Module "path/my-file.tao" [], "")
    p "x" `shouldBe` Left ([CModule], "x")
    p "import @pkg" `shouldBe` Right (Module "path/my-file.tao" [Import "@pkg" []], "")

  it "☯ parseFile" $ do
    let pkg = Package {name = "pkg", modules = []}
    parseFile "examples" "empty.tao" (pkg, []) `shouldReturn` (pkg {modules = [Module "empty" []]}, [])

  it "☯ parseFile exists" $ do
    let pkg = Package {name = "pkg", modules = [Module "my-file" []]}
    parseFile "base-path" "my-file" (pkg, []) `shouldReturn` (pkg, [])

  it "☯ parsePackage directory" $ do
    let pkg = Package {name = "empty", modules = [Module "empty-file" []]}
    parsePackage "examples/empty" `shouldReturn` (pkg, [])
    withCurrentDirectory "examples" (parsePackage "empty") `shouldReturn` (pkg, [])

  it "☯ parsePackage file" $ do
    let pkg = Package {name = "empty", modules = [Module "empty" []]}
    parsePackage "examples/empty.tao" `shouldReturn` (pkg, [])
    withCurrentDirectory "examples" (parsePackage "empty.tao") `shouldReturn` (pkg, [])

  it "☯ loadPackage" $ do
    let env =
          [ ("@sub/mod.x", C.Int 1),
            ("@sub/mod.y", C.Int 2)
          ]
    let s =
          [ (("@sub/mod", "x"), "@sub/mod.x"),
            (("@sub/mod", "y"), "@sub/mod.y")
          ]
    let errors = []
    let load path = do
          (env, s, errors) <- loadPackage path
          let env' = map C.dropMeta env
          return (env', s, errors)
    load "examples/sub" `shouldReturn` (env, s, errors)
