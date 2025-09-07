module TaoTests where

import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap, second))
import Data.Function ((&))
import Error
import Location
import qualified Parser as P
import Tao
import Test.Hspec

-- TODO: isolate errors and error reporting into its own test file

filename :: String
filename = "TaoTests"

syntaxErr :: Int -> Int -> Int -> Int -> String -> String -> String -> C.Metadata Expr
syntaxErr r1 c1 r2 c2 committed expected got = do
  let loc = Location filename (Range (Pos r1 c1) (Pos r2 c2))
  C.Error (SyntaxError (loc, committed, expected, got))

parse' :: String -> Either (String, String) (Expr, String)
parse' text = case parse 0 filename text of
  Right (a, s) -> Right (a, s.remaining)
  Left s -> Left (s.expected, s.remaining)

parseCollection' :: String -> String -> String -> String -> String -> Either (String, String) ([Expr], String)
parseCollection' msg open delim close text = do
  let parser = parseCollection msg open delim close syntaxErrorExpr Err (parseExpr 0)
  case P.parse parser filename text of
    Right (xs, s) -> Right (xs, s.remaining)
    Left s -> Left (s.expected, s.remaining)

parseStmt' :: String -> Either (String, String) (Stmt, String)
parseStmt' text = case P.parse parseStmt filename text of
  Right (a, s) -> Right (a, s.remaining)
  Left s -> Left (s.expected, s.remaining)

parseModule' :: String -> Either (String, String) ([Stmt], String)
parseModule' text = case P.parse (parseModule "m") filename text of
  Right ((_, stmts), s) -> Right (stmts, s.remaining)
  Left s -> Left (s.expected, s.remaining)

-- fmt :: Expr -> String
-- fmt = show . dropLocations

-- core :: C.Expr -> String
-- core = show . C.dropMeta

-- letDef' :: String -> String -> Stmt
-- letDef' a b = case (parse ("ctx." ++ a) a, parse ("ctx." ++ a) b) of
--   (Right (a, _), Right (b, _)) -> letDef (a, b)
--   (Left s, _) -> error ("ctx[pattern] syntax error, remaining: " ++ s.remaining)
--   (_, Left s) -> error ("ctx[value] syntax error, remaining: " ++ s.remaining)

-- -- let defOp1 op f = letDef op (For ["a"] (lambda [Var "a"] (Call f [Var "a"])))
-- -- let defOp2 op f = letDef op (For ["a", "b"] (lambda [Var "a", Var "b"] (Call f [Var "a", Var "b"])))

-- syntax :: String -> Either String Expr
-- syntax src = syntax' src src

-- syntax' :: String -> String -> Either String Expr
-- syntax' src expected = case parse filename src of
--   Right (a, _)
--     | fmt a == expected -> Right a
--     | otherwise -> Left ("format error: " ++ expected ++ " != " ++ fmt a)
--   Left s -> Left ("syntax error, remaining: " ++ s.remaining)

-- check' :: C.Expr -> [(Maybe (Int, Int, Int, Int), Error Expr)]
-- check' a = do
--   let f (Just (Location _ (Range start end)), err) = (Just (start.row, start.col, end.row, end.col), err)
--       f (Nothing, err) = (Nothing, err)
--   map f (check (lift a))

-- eval' :: C.Env -> C.Expr -> C.Type -> (String, String)
-- eval' env expr type' = do
--   let a = eval env expr
--   let t = eval env type'
--   (fmt $ dropTypes a, fmt $ dropTypes t)

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
  let loc' r1 c1 r2 c2 = Location filename (Range (Pos r1 c1) (Pos r2 c2))
  let loc r1 c1 r2 c2 = Meta (C.Loc $ loc' r1 c1 r2 c2)
  let any r c = loc r c r (c + 1) Any
  let int r c i = loc r c r (c + length (show i)) (Int i)
  let num r c n = loc r c r (c + length (show n)) (Num n)
  let char r c ch = loc r c r (c + 4) (Char ch)
  let var r c x = loc r c r (c + length x) (Var x)
  let tag r c k args = loc r c r (c + length k) (Tag k args)
  let ann r c a b = loc r c r (c + 1) (Ann a b)
  let or' r c a b = loc r c r (c + 1) (Or a b)
  let fun r c a b = loc r c r (c + 2) (Fun a b)
  let call r c f args = loc r c r (c + length ('%' : f)) (Call f args)
  let op1 r c op a = loc r c r (c + length (showOp1 op)) (Op1 op a)
  let op2 r c op a b = loc r c r (c + length (showOp2 op)) (Op2 op a b)
  let match r c arg cases = loc r c r (c + length "match") (Match arg cases)

  let name r c x = MetaName (C.Loc $ loc' r c r (c + length x)) (Name x)

  let a r c = var r c "a"
  let b r c = var r c "b"
  let c r c = var r c "c"
  let x r c = var r c "x"
  let y r c = var r c "y"
  let z r c = var r c "z"

  let (a', b', c') = (C.Var "a", C.Var "b", C.Var "c")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")

  it "☯ Tao.grammar.parser.Any" $ do
    parse' "_ \n" `shouldBe` Right (any 1 1, "\n")

  it "☯ Tao.grammar.parser.Int" $ do
    parse' "42 \n" `shouldBe` Right (int 1 1 42, "\n")
    parse' "-42 \n" `shouldBe` Right (int 1 1 (-42), "\n")
  -- TODO: integer binary: 0b1010 == 10
  -- TODO: integer octal: 0o52 == 42
  -- TODO: integer hexadecimal: 0xFEEDCA7 == 267312295

  it "☯ Tao.grammar.parser.Num" $ do
    parse' "3.14 \n" `shouldBe` Right (num 1 1 3.14, "\n")
    parse' "-3.14 \n" `shouldBe` Right (num 1 1 (-3.14), "\n")
  -- TODO: number scientific notation pos: 4.2e1 == 42.0
  -- TODO: number scientific notation neg: 314e-2 == 3.14

  it "☯ Tao.grammar.parser.Char" $ do
    parse' "c'x' \n" `shouldBe` Right (char 1 1 'x', "\n")
    parse' "c\"x\" \n" `shouldBe` Right (char 1 1 'x', "\n")
  -- TODO: char escape sequence: c'\a'
  -- TODO: char escape sequence: c'\b'
  -- TODO: char escape sequence: c'\f'
  -- TODO: char escape sequence: c'\n'
  -- TODO: char escape sequence: c'\r'
  -- TODO: char escape sequence: c'\t'
  -- TODO: char escape sequence: c'\v'
  -- TODO: char escape sequence: c'\''
  -- TODO: char escape sequence: c"\""
  -- TODO: char escape sequence: c'\0'
  -- TODO: char escape sequence: c'\oNNN'
  -- TODO: char escape sequence: c'\xNN'
  -- TODO: char escape sequence: c'\uHH'

  it "☯ Tao.grammar.parser.Var" $ do
    parse' "x \n" `shouldBe` Right (x 1 1, "\n")
  -- TODO: variable escaped: v'x'

  it "☯ Tao.grammar.parser.collection" $ do
    let p = parseCollection' "item" "[" "," "]"
    -- Do not parse trailing spaces to allow other parsers to get (start, end) locations.
    p "[] \n" `shouldBe` Right ([], " \n")
    p "[x] \n" `shouldBe` Right ([x 1 2], " \n")
    p "[x,] \n" `shouldBe` Right ([x 1 2], " \n")
    p "[x,y] \n" `shouldBe` Right ([x 1 2, y 1 4], " \n")
    p "[x,y,z,] \n" `shouldBe` Right ([x 1 2, y 1 4, z 1 6], " \n")
    p "[\nx\n,\ny\n] \n" `shouldBe` Right ([x 2 1, y 4 1], " \n")
    p "[\nx\n,\ny\n,\n] \n" `shouldBe` Right ([x 2 1, y 4 1], " \n")
    p "[ \n" `shouldBe` Right ([Meta (syntaxErr 2 1 2 1 "" "closing ']'" "") Err], "")
    p "[ \nx \n" `shouldBe` Right ([x 2 1, Meta (syntaxErr 3 1 3 1 "" "closing ']'" "") Err], "")
    p "[ \nx \n y \n" `shouldBe` Right ([x 2 1, Meta (syntaxErr 3 2 3 4 "" "closing ']'" "y ") Err], "\n")
    p "[)] \n" `shouldBe` Right ([Meta (syntaxErr 1 2 1 3 "" "closing ']'" ")") Err], "] \n")
    p "[x)] \n" `shouldBe` Right ([x 1 2, Meta (syntaxErr 1 3 1 4 "" "closing ']'" ")") Err], "] \n")
    p "[$)] \n" `shouldBe` Right ([Meta (syntaxErr 1 2 1 4 "" "closing ']'" "$)") Err], "] \n")
    p "[$] \n" `shouldBe` Right ([Meta (syntaxErr 1 2 1 4 "" "closing ']'" "$]") Err], " \n")
    p "[$], \n" `shouldBe` Right ([Meta (syntaxErr 1 2 1 4 "" "closing ']'" "$]") Err], ", \n")
    p "[$]] \n" `shouldBe` Right ([Meta (syntaxErr 1 2 1 4 "" "closing ']'" "$]") Err], "] \n")
    p "[$]) \n" `shouldBe` Right ([Meta (syntaxErr 1 2 1 4 "" "closing ']'" "$]") Err], ") \n")
    p "[x$] \n" `shouldBe` Right ([x 1 2, Meta (syntaxErr 1 3 1 5 "" "closing ']'" "$]") Err], " \n")
    p "[$, x] \n" `shouldBe` Right ([Meta (syntaxErr 1 2 1 3 "" "item" "$") Err, x 1 5], " \n")
    p "[x, $] \n" `shouldBe` Right ([x 1 2, Meta (syntaxErr 1 5 1 7 "" "closing ']'" "$]") Err], " \n")

  it "☯ Tao.grammar.parser.Tag" $ do
    parse' "A \n" `shouldBe` Right (tag 1 1 "A" [], "\n")
    parse' "A() \n" `shouldBe` Right (tag 1 1 "A" [], "\n")
    parse' "A(x) \n" `shouldBe` Right (tag 1 1 "A" [x 1 3], "\n")
    parse' "A(x,y) \n" `shouldBe` Right (tag 1 1 "A" [x 1 3, y 1 5], "\n")
    parse' "A(x, y, z) \n" `shouldBe` Right (tag 1 1 "A" [x 1 3, y 1 6, z 1 9], "\n")
    parse' "A(\nx\n,\ny\n,\n) \n" `shouldBe` Right (tag 1 1 "A" [x 2 1, y 4 1], "\n")
    parse' "A\n() \n" `shouldBe` Right (tag 1 1 "A" [], "\n")
  -- TODO: tag escaped: t'A'
  -- TODO: tag escaped: t'A'(x)
  -- Error recovery
  -- parse' "A<$> \n" `shouldBe` Right (tag 1 1 "A" [syntaxError (loc' 1 3 1 4, "tag argument", "$")], "\n")
  -- parse' "A<$, x> \n" `shouldBe` Right (tag 1 1 "A" [syntaxError (loc' 1 3 1 4, "tag argument", "$"), x 1 6], "\n")
  -- parse' "A<x, $> \n" `shouldBe` Right (tag 1 1 "A" [x 1 3, syntaxError (loc' 1 6 1 7, "tag argument", "$")], "\n")

  it "☯ Tao.grammar.parser.Tuple" $ do
    parse' "() \n" `shouldBe` Right (loc 1 1 1 3 $ Tuple [], "\n")
    parse' "(x) \n" `shouldBe` Right (x 1 2, "\n")
    parse' "(x,) \n" `shouldBe` Right (loc 1 1 1 5 $ Tuple [x 1 2], "\n")
    parse' "(x, y, z) \n" `shouldBe` Right (loc 1 1 1 10 $ Tuple [x 1 2, y 1 5, z 1 8], "\n")
    parse' "(\nx\n,\ny\n,\n) \n" `shouldBe` Right (loc 1 1 6 2 $ Tuple [x 2 1, y 4 1], "\n")

  it "☯ Tao.grammar.parser.List" $ do
    parse' "[] \n" `shouldBe` Right (loc 1 1 1 3 $ List [], "\n")
    parse' "[x] \n" `shouldBe` Right (loc 1 1 1 4 $ List [x 1 2], "\n")
    parse' "[x,] \n" `shouldBe` Right (loc 1 1 1 5 $ List [x 1 2], "\n")
    parse' "[x, y, z] \n" `shouldBe` Right (loc 1 1 1 10 $ List [x 1 2, y 1 5, z 1 8], "\n")
    parse' "[\nx\n,\ny\n,\n] \n" `shouldBe` Right (loc 1 1 6 2 $ List [x 2 1, y 4 1], "\n")
  -- Error recovery
  -- parse' "[$] \n" `shouldBe` Right (loc 1 1 1 4 $ List [syntaxError (loc' 1 2 1 3, "list item", "$")], "\n")
  -- parse' "[$, x] \n" `shouldBe` Right (loc 1 1 1 7 $ List [syntaxError (loc' 1 2 1 3, "list item", "$"), x 1 5], "\n")
  -- parse' "[x, $] \n" `shouldBe` Right (loc 1 1 1 7 $ List [x 1 2, syntaxError (loc' 1 5 1 6, "list item", "$")], "\n")

  it "☯ Tao.grammar.parser.String" $ do
    parse' "'' \n" `shouldBe` Right (loc 1 1 1 3 $ String [Str ""], "\n")
    parse' "'abc' \n" `shouldBe` Right (loc 1 1 1 6 $ String [Str "abc"], "\n")
    parse' "\"abc\" \n" `shouldBe` Right (loc 1 1 1 6 $ String [Str "abc"], "\n")
  -- TODO: string escape sequences
  -- TODO: string interpolation bare: "ab$x c"
  -- TODO: string interpolation with brackets: "ab${x}c"
  -- TODO: string multi-line: """\nabc\n"""
  -- TODO: string multi-line indented
  -- TODO: string templates: f`abc`
  -- TODO: string templates multi-line: ```f\nabc\n```
  -- Error recovery
  -- TODO: missing closing quote

  it "☯ Tao.grammar.parser.For" $ do
    parse' "@x.y \n" `shouldBe` Right (loc 1 1 1 3 $ For ["x"] (y 1 4), "\n")
    parse' "@ x .\ny \n" `shouldBe` Right (loc 1 1 1 4 $ For ["x"] (y 2 1), "\n")
    parse' "@ x y \nz \n" `shouldBe` Right (loc 1 1 1 6 $ For ["x", "y"] (z 2 1), "\n")
    parse' "@\nx. y \n" `shouldBe` Left ([], "@\nx. y \n")

  it "☯ Tao.grammar.parser.Ann" $ do
    parse' "x:y \n" `shouldBe` Right (ann 1 2 (x 1 1) (y 1 3), "\n")
    parse' "x : y : z \n" `shouldBe` Right (ann 1 3 (x 1 1) (ann 1 7 (y 1 5) (z 1 9)), "\n")
    parse' "x\n:\ny \n" `shouldBe` Right (x 1 1, "\n:\ny \n")
    parse' "x :\ny \n" `shouldBe` Right (ann 1 3 (x 1 1) (y 2 1), "\n")

  it "☯ Tao.grammar.parser.Or" $ do
    parse' "x|y \n" `shouldBe` Right (or' 1 2 (x 1 1) (y 1 3), "\n")
    parse' "x | y | z \n" `shouldBe` Right (or' 1 3 (x 1 1) (or' 1 7 (y 1 5) (z 1 9)), "\n")
    parse' "x\n|\ny \n" `shouldBe` Right (or' 2 1 (x 1 1) (y 3 1), "\n")

  it "☯ Tao.grammar.parser.Fun" $ do
    parse' "x->y \n" `shouldBe` Right (fun 1 2 (x 1 1) (y 1 4), "\n")
    parse' "x -> y -> z \n" `shouldBe` Right (fun 1 3 (x 1 1) (fun 1 8 (y 1 6) (z 1 11)), "\n")
    parse' "x\n->\ny \n" `shouldBe` Right (fun 2 1 (x 1 1) (y 3 1), "\n")

  it "☯ Tao.grammar.parser.App" $ do
    parse' "a() \n" `shouldBe` Right (loc 1 2 1 4 $ app (a 1 1) [], "\n")
    parse' "a(x) \n" `shouldBe` Right (loc 1 2 1 5 $ app (a 1 1) [x 1 3], "\n")
    parse' "a (x, y, z) \n" `shouldBe` Right (loc 1 3 1 12 $ app (a 1 1) [x 1 4, y 1 7, z 1 10], "\n")
    parse' "a(\nx\n,\ny\n,\n) \n" `shouldBe` Right (loc 1 2 6 2 $ app (a 1 1) [x 2 1, y 4 1], "\n")
    parse' "a\n() \n" `shouldBe` Right (loc 2 1 2 3 $ app (a 1 1) [], "\n")

  it "☯ Tao.grammar.parser.Call" $ do
    parse' "%f() \n" `shouldBe` Right (call 1 1 "f" [], "\n")
    parse' "%f(x) \n" `shouldBe` Right (call 1 1 "f" [x 1 4], "\n")
    parse' "%f (x, y, z) \n" `shouldBe` Right (call 1 1 "f" [x 1 5, y 1 8, z 1 11], "\n")
    parse' "%f(\nx\n,\ny\n,\n) \n" `shouldBe` Right (call 1 1 "f" [x 2 1, y 4 1], "\n")
    parse' "%f\n() \n" `shouldBe` Right (call 1 1 "f" [], "\n")

  it "☯ Tao.grammar.parser.Op1" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Op2" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Dot" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Spread" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Get" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Slice" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Match" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.MatchFun" $ do
    "" `shouldBe` ""

  it "☯ Tao.grammar.parser.Let" $ do
    -- parse' "^{}y \n" `shouldBe` Right (Let [] y, "\n")
    -- parse' "^ { } y \n" `shouldBe` Right (Let [] y, "\n")
    -- parse' "^\n{\n}\ny \n" `shouldBe` Right (Let [] y, "\n")
    -- parse' "^x=a;y \n" `shouldBe` Right (Let [("x", a)] y, "\n")
    -- parse' "^ x = a ; ^ y = b ; z \n" `shouldBe` Right (Let [("x", a), ("y", b)] z, "\n")
    -- parse' "^\nx\n=\na \n^\ny\n=\nb \nz \n" `shouldBe` Right (Let [("x", a), ("y", b)] z, "\n")
    "" `shouldBe` ""

  it "☯ Tao.grammar.parser.Bind" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Record" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Select" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.With" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.If" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.IfElse" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Meta" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.parser.Err" $ do
    "" `shouldBe` ""

  it "☯ Tao.Stmt.parser.empty" $ do
    let p = parseStmt'
    p "" `shouldBe` Left ("", "")

  it "☯ Tao.Stmt.parser.Import" $ do
    let p = parseStmt'
    p "import m " `shouldBe` Right (Import "m" "m" [], "")
    p "import m as n " `shouldBe` Right (Import "m" "n" [], "")
    p "import m (x) " `shouldBe` Right (Import "m" "m" [("x", "x")], "")
    p "import m (x as y) " `shouldBe` Right (Import "m" "m" [("x", "y")], "")
    p "import m (x, y) " `shouldBe` Right (Import "m" "m" [("x", "x"), ("y", "y")], "")
    -- TODO: Handle Meta on import names correctly.
    -- p "import $" `shouldBe` Right (Import "![syntax error]TaoTests:1:8,1:9: expected import module path, got \"$\"" "" [], "")
    -- p "import" `shouldBe` Right (Import "![syntax error]TaoTests:1:7: expected import module path, got \"\"" "" [], "")
    "" `shouldBe` ""

  it "☯ Tao.Stmt.parser.Let" $ do
    let p = parseStmt'
    p "let x = y " `shouldBe` Right (Let (x 1 5) (y 1 9), "")
    p "let $ = y " `shouldBe` Right (Let (Meta (syntaxErr 1 5 1 7 "definition" "pattern" "$ ") Err) (y 1 9), "")
    p "let x $ y " `shouldBe` Right (Let (x 1 5) (Meta (syntaxErr 1 7 1 9 "definition" "'=' or '<-'" "$ ") (y 1 9)), "")
    p "let x = $ " `shouldBe` Right (Let (x 1 5) (Meta (syntaxErr 1 9 1 11 "definition" "body" "$ ") Err), "")

  it "☯ Tao.Stmt.parser.Bind" $ do
    let p = parseStmt'
    p "let x <- y " `shouldBe` Right (Bind (x 1 5) (y 1 10), "")
    p "let $ <- y " `shouldBe` Right (Bind (Meta (syntaxErr 1 5 1 7 "definition" "pattern" "$ ") Err) (y 1 10), "")
    p "let x <$ y " `shouldBe` Right (Let (x 1 5) (Meta (syntaxErr 1 7 1 10 "definition" "'=' or '<-'" "<$ ") (y 1 10)), "")
    p "let x <- $ " `shouldBe` Right (Bind (x 1 5) (Meta (syntaxErr 1 10 1 12 "definition" "body" "$ ") Err), "")

  it "☯ Tao.Stmt.parser.Mut" $ do
    let p = parseStmt'
    p "mut x = y " `shouldBe` Right (Mut (name 1 5 "x") (y 1 9), "")
    p "mut $ = y " `shouldBe` Right (Mut (MetaName (syntaxErr 1 5 1 7 "mutate" "variable name" "$ ") (Name "")) (y 1 9), "")
    p "mut x $ y " `shouldBe` Right (Mut (name 1 5 "x") (Meta (syntaxErr 1 7 1 9 "mutate" "'='" "$ ") (y 1 9)), "")
    p "mut x = $ " `shouldBe` Right (Mut (name 1 5 "x") (Meta (syntaxErr 1 9 1 11 "mutate" "body" "$ ") Err), "")

  it "☯ Tao.Stmt.parser.Test" $ do
    let p = parseStmt'
    p "> x ~> y " `shouldBe` Right (Test "TaoTests:1:1: x" (x 1 3) (y 1 8), "")
    p "> $ ~> y " `shouldBe` Right (Test "TaoTests:1:1: !error" (Meta (syntaxErr 1 3 1 5 "test" "expression" "$ ") Err) (y 1 8), "")
    p "> x ~$ y " `shouldBe` Right (Test "TaoTests:1:1: x" (x 1 3) (Meta (syntaxErr 1 5 1 8 "test" "'~>'" "~$ ") (y 1 8)), "")
    p "> x ~> $ " `shouldBe` Right (Test "TaoTests:1:1: x" (x 1 3) (Meta (syntaxErr 1 8 1 10 "test" "result" "$ ") Err), "")
    p "> x \ny " `shouldBe` Right (Test "TaoTests:1:1: x" (x 1 3) (y 2 1), "")
    p "> $ \ny " `shouldBe` Right (Test "TaoTests:1:1: !error" (Meta (syntaxErr 1 3 1 5 "test" "expression" "$ ") Err) (y 2 1), "")
    p "> x \n$ " `shouldBe` Right (Test "TaoTests:1:1: x" (x 1 3) (Tag "True" []), "$ ")

  it "☯ Tao.Stmt.parser.Test" $ do
    let p = parseStmt'
    p "type T = x " `shouldBe` Right (TypeDef (name 1 6 "T") [] (x 1 10), "")
    p "type $ = x " `shouldBe` Right (TypeDef (MetaName (syntaxErr 1 6 1 8 "type definition" "type name" "$ ") (Name "")) [] (x 1 10), "")
    p "type T $ = x " `shouldBe` Right (TypeDef (MetaName (syntaxErr 1 8 1 10 "type definition" "" "$ ") $ name 1 6 "T") [] (x 1 12), "")
    p "type T $ x " `shouldBe` Right (TypeDef (name 1 6 "T") [] (Meta (syntaxErr 1 8 1 10 "type definition" "'='" "$ ") (x 1 10)), "")
    p "type T() = x " `shouldBe` Right (TypeDef (name 1 6 "T") [] (x 1 12), "")
    p "type T($ = x " `shouldBe` Right (TypeDef (name 1 6 "T") [] (Meta (syntaxErr 1 7 1 7 "type definition" "'='" "") $ Meta (syntaxErr 1 7 1 14 "type definition" "body" "($ = x ") Err), "")
    p "type T<>() = x " `shouldBe` Right (TypeDef (MetaName (syntaxErr 1 7 1 9 "type definition" "" "<>") $ name 1 6 "T") [] (x 1 14), "")
    p "type T(x) = y " `shouldBe` Right (TypeDef (name 1 6 "T") [x 1 8] (y 1 13), "")
    p "type T(x,) = y " `shouldBe` Right (TypeDef (name 1 6 "T") [x 1 8] (y 1 14), "")
    p "type T(x, y) = z " `shouldBe` Right (TypeDef (name 1 6 "T") [x 1 8, y 1 11] (z 1 16), "")

  it "☯ Tao.Stmt.parser.Errors" $ do
    let p = parseStmt'
    p "" `shouldBe` Left ("", "")
    p "$ " `shouldBe` Right (Nop (syntaxErr 1 1 1 3 "" "statement" "$ "), "")
    p "$ \n " `shouldBe` Right (Nop (syntaxErr 1 1 1 3 "" "statement" "$ "), "")
    p "$ \n$$ " `shouldBe` Right (Nop (syntaxErr 1 1 1 3 "" "statement" "$ "), "$$ ")

  it "☯ Tao.Module.parser" $ do
    let p = parseModule'
    p "" `shouldBe` Right ([], "")
    p "$ " `shouldBe` Right ([Nop (syntaxErr 1 1 1 3 "" "statement" "$ ")], "")

  -- Run String [Expr]
  -- Test UnitTest
  -- TypeDef String [Expr] [(Expr, Maybe Type)]
  -- IfStmt Expr Block (Maybe Block)
  -- While Expr Block
  -- Repeat Block Expr
  -- ForStmt Pattern Expr Block
  -- Nop (C.Metadata Expr)

  -- it "☯ Tao.Stmt.parser.letDef" $ do
  --   let p = parseStmt'
  --   p "let x = y " `shouldBe` Right (letDef (x 1 5, y 1 9), "")
  --   p "let x = $ " `shouldBe` Right (letDef (x 1 5, Meta (syntaxErr 1 9 1 11 "definition" "body" "$ ") Err), "")
  --   p "let x $ y " `shouldBe` Right (Nop (syntaxErr 1 1 1 11 "" "\"=\"" "let x $ y "), "")
  --   p "let $ = y " `shouldBe` Right (letDef (Meta (syntaxErr 1 5 1 7 "definition" "pattern" "$ ") Err, y 1 9), "")
  --   p "let x = " `shouldBe` Right (letDef (x 1 5, Meta (syntaxErr 1 9 1 9 "definition" "body" "") Err), "")
  --   p "let x " `shouldBe` Right (Nop $ syntaxErr 1 1 1 7 "" "\"=\"" "let x ", "")
  --   p "let" `shouldBe` Right (Nop $ syntaxErr 1 1 1 4 "definition" "pattern" "let", "")

  -- it "☯ Tao.Stmt.parser.TypeDef" $ do
  --   let p = parseStmt'
  --   p "type T = x " `shouldBe` Right (TypeDef ("T", [], [(x 1 10, Nothing)]), "")
  --   p "type T $ = x " `shouldBe` Right (TypeDef ("T", [Meta (syntaxErr 1 8 1 10 "" "" "$ ") Err], [(x 1 12, Nothing)]), "")
  --   p "type T<> = x " `shouldBe` Right (TypeDef ("T", [], [(x 1 12, Nothing)]), "")
  --   p "type T<x> = y " `shouldBe` Right (TypeDef ("T", [x 1 8], [(y 1 13, Nothing)]), "")

  -- it "☯ Tao.Stmt.parser.Test" $ do
  --   "" `shouldBe` ""
  -- it "☯ Tao.Stmt.parser.Run" $ do
  --   "" `shouldBe` ""
  -- it "☯ Tao.Stmt.parser.Nop" $ do
  --   "" `shouldBe` ""

  it "☯ Tao.grammar.layout.Any" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Int" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Num" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Char" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Var" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Tag" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Tuple" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.List" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.String" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.For" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Ann" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Or" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Fun" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.App" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Call" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Let" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Op1" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Op2" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Dot" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Spread" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Get" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Slice" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Match" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.MatchFun" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Let" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Bind" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Record" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Select" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.With" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.If" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.IfElse" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Meta" $ do
    "" `shouldBe` ""
  it "☯ Tao.grammar.layout.Err" $ do
    "" `shouldBe` ""

  it "☯ Tao.resolve" $ do
    let (x, y, z, w) = (Var "x", Var "y", Var "z", Var "w")
    let (i1, i2) = (Int 1, Int 2)

    -- Stmt
    let ctx = []
    resolve ctx "m1" ("x", Let x y) `shouldBe` [("m1", y)]
    resolve ctx "m1" ("x", Let y z) `shouldBe` []
    resolve ctx "m1" ("x", TypeDef (Name "x") [] y) `shouldBe` [("m1", Fun (Tuple []) y)]
    resolve ctx "m1" ("x", Test "name" y z) `shouldBe` []

    -- [Stmt]
    let ctx = []
    resolve ctx "m1" ("x", [] :: [Stmt]) `shouldBe` []
    resolve ctx "m1" ("x", [Let x y]) `shouldBe` [("m1", y)]
    resolve ctx "m1" ("x", [Let x y, Let x z]) `shouldBe` [("m1", y), ("m1", z)]

    -- Module
    let ctx = []
    resolve ctx "m1" ("x", ("m1", []) :: Module) `shouldBe` []
    resolve ctx "m1" ("x", ("m1", [Let x y])) `shouldBe` [("m1", y)]
    resolve ctx "m1" ("x", ("m1", [Let x y, Let x z])) `shouldBe` [("m1", y), ("m1", z)]
    resolve ctx "m1" ("x", ("m2", [Let x y])) `shouldBe` []

    -- Name
    let ctx = [("m1", [Let x y]), ("m1/@f1", [Let x z])]
    resolve ctx "m1" "x" `shouldBe` [("m1", y), ("m1", z)]
    resolve ctx "m1/@f1" "x" `shouldBe` [("m1", y), ("m1", z)]
    resolve ctx "m1" "y" `shouldBe` []

    -- Imports
    -- let ctx = [("m1", [Let (x, y)]), ("m1/@f1", [Let (x, z)])]
    -- resolve ctx "m" ("x", [Import "m1" "m1" [("x", "x")], Let (x, w)]) `shouldBe` [("m1", y), ("m1/@f1", z), ("m", w)]
    -- resolve ctx "m1" ("x", [Import "m1" "m1" [("x", "x")], Let (x, w)]) `shouldBe` [("m1", w)]
    -- resolve ctx "m1" ("x", [Import "m1/@f1" "m1" [("x", "x")], Let (x, w)]) `shouldBe` [("m1/@f1", z), ("m1", w)]

    -- Self imports
    let ctx =
          [ ("m1", [Import "m1" "m1" [("x", "x")], Let x i1]),
            ("m1/@f1", [Import "m1" "m1" [("x", "x")], Let x i2]),
            ("m2/@f1", [Import "m2" "m2" [("y", "y")], Let y i1]),
            ("m2/@f2", [Import "m2" "m2" [("y", "y")], Let y i2]),
            ("m3/@f1", [Import "m3/@f1" "m3/@f1" [("z", "z")], Let z i1]),
            ("m3/@f2", [Import "m3/@f1" "m3/@f1" [("z", "z")], Let z i2])
          ]
    resolve ctx "m1" "x" `shouldBe` [("m1", i1), ("m1", i2)]
    resolve ctx "m2" "y" `shouldBe` [("m2", i1), ("m2", i2)]
    resolve ctx "m2/@f1" "y" `shouldBe` [("m2", i1), ("m2", i2)]
    -- resolve ctx "m3" "z" `shouldBe` [("m3", i1), ("m3", i2)]
    -- resolve ctx "m3/@f1" "z" `shouldBe` [("m3", i1), ("m3", i2)]

    -- Import wildcards
    let ctx = [("m1", [Let x y])]
    resolve ctx "m" ("x", [Import "m1" "m1" [("*", "")], Let x w]) `shouldBe` [("m1", y), ("m", w)]

  it "☯ Tao.lower" $ do
    let (x, y, z) = (Var "x", Var "y", Var "z")
    let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
    lower Any `shouldBe` C.Any
    lower (Int 1) `shouldBe` C.Int 1
    lower (Num 1.1) `shouldBe` C.Num 1.1
    lower (Char 'a') `shouldBe` C.Tag "Char" (C.Int 97)
    lower (Var "x") `shouldBe` C.Var "x"
    lower (Tag "A" []) `shouldBe` C.Tag "A" C.Unit
    lower (Tag "A" [x]) `shouldBe` C.Tag "A" x'
    lower (Tag "A" [x, y]) `shouldBe` C.Tag "A" (C.And x' y')
    lower (Tuple []) `shouldBe` C.Unit
    lower (Tuple [x]) `shouldBe` x'
    lower (Tuple [x, y]) `shouldBe` C.And x' y'
    lower (Tuple [x, y, z]) `shouldBe` C.And x' (C.And y' z')
    lower (List []) `shouldBe` C.tag' "[]"
    lower (List [x]) `shouldBe` C.tag "::" [x', C.tag' "[]"]
    lower (List [x, y]) `shouldBe` C.tag "::" [x', C.tag "::" [y', C.tag' "[]"]]
    -- String [Segment]
    -- For [String] Expr
    -- Ann Expr Type
    -- Or Expr Expr
    -- Fun Pattern Expr
    -- App Expr Expr
    -- Call String [Expr]
    -- Op1 Op1 Expr
    -- Op2 Op2 Expr Expr
    lower (Do [Return x]) `shouldBe` x'
    -- Dot Expr String (Maybe [Expr])
    -- Spread Expr
    -- Get Expr Expr
    -- Slice Expr (Expr, Expr)
    -- Match Expr [Expr]
    -- MatchFun [Expr]
    -- Record [(String, Expr)]
    -- Select Expr [(String, Expr)]
    -- With Expr [(String, Expr)]
    -- If Expr Expr
    -- IfElse Expr Expr Expr
    -- Meta (C.Metadata Expr) Expr
    lower Err `shouldBe` C.Err

  it "☯ Tao.lower.Do" $ do
    let (x, y, z) = (Var "x", Var "y", Var "z")
    let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
    -- lower (Do []) `shouldBe` C.Err
    lower (Do [Return x]) `shouldBe` x'
    lower (Do [Let x y, Return z]) `shouldBe` C.App (C.Fun x' z') y'

  it "☯ TODO" $ do
    "" `shouldBe` ""
