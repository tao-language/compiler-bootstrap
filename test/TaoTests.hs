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
filename = "<TaoTests>"

parse' :: String -> Either ([String], String) (Expr, String)
parse' text = case parse 0 filename text of
  Right (a, s) -> Right (a, s.remaining)
  Left s -> Left (s.context, s.remaining)

-- fmt :: Expr -> String
-- fmt = show . dropLocations

-- core :: C.Expr -> String
-- core = show . C.dropMeta

-- def' :: String -> String -> Stmt
-- def' a b = case (parse ("ctx." ++ a) a, parse ("ctx." ++ a) b) of
--   (Right (a, _), Right (b, _)) -> def (a, b)
--   (Left s, _) -> error ("ctx[pattern] syntax error, remaining: " ++ s.remaining)
--   (_, Left s) -> error ("ctx[value] syntax error, remaining: " ++ s.remaining)

-- -- let defOp1 op f = def op (For ["a"] (lambda [Var "a"] (Call f [Var "a"])))
-- -- let defOp2 op f = def op (For ["a", "b"] (lambda [Var "a", Var "b"] (Call f [Var "a", Var "b"])))

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
  let op1 r c op a = loc r c r (c + length (showOp1 op)) (Op1 op a)
  let op2 r c op a b = loc r c r (c + length (showOp2 op)) (Op2 op a b)
  let match r c arg cases = loc r c r (c + length "match") (Match arg cases)
  let let' r c (x, y) z = loc r c r (c + 3) (Let (x, y) z)

  let a r c = var r c "a"
  let b r c = var r c "b"
  let c r c = var r c "c"
  let x r c = var r c "x"
  let y r c = var r c "y"
  let z r c = var r c "z"

  let (a', b', c') = (C.Var "a", C.Var "b", C.Var "c")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")

  it "☯ Tao.grammar.parser" $ do
    parse' "_ \n" `shouldBe` Right (any 1 1, "\n")
    parse' "42 \n" `shouldBe` Right (int 1 1 42, "\n")
    parse' "-42 \n" `shouldBe` Right (int 1 1 (-42), "\n")
    -- TODO: integer binary: 0b1010 == 10
    -- TODO: integer octal: 0o52 == 42
    -- TODO: integer hexadecimal: 0xFEEDCA7 == 267312295
    parse' "3.14 \n" `shouldBe` Right (num 1 1 3.14, "\n")
    parse' "-3.14 \n" `shouldBe` Right (num 1 1 (-3.14), "\n")
    -- TODO: number scientific notation pos: 4.2e1 == 42.0
    -- TODO: number scientific notation neg: 314e-2 == 3.14
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
    parse' "x \n" `shouldBe` Right (x 1 1, "\n")
    -- TODO: variable escaped: v'x'
    parse' "A \n" `shouldBe` Right (tag 1 1 "A" [], "\n")
    parse' "A() \n" `shouldBe` Right (tag 1 1 "A" [], "\n")
    parse' "A(x) \n" `shouldBe` Right (tag 1 1 "A" [x 1 3], "\n")
    parse' "A(x,y) \n" `shouldBe` Right (tag 1 1 "A" [x 1 3, y 1 5], "\n")
    parse' "A(x, y, z) \n" `shouldBe` Right (tag 1 1 "A" [x 1 3, y 1 6, z 1 9], "\n")
    parse' "A(\nx\n,\ny\n,\n) \n" `shouldBe` Right (tag 1 1 "A" [x 2 1, y 4 1], "\n")
    -- TODO: tag escaped: t'A'
    -- TODO: tag escaped: t'A'(x)
    parse' "() \n" `shouldBe` Right (loc 1 1 1 3 $ Tuple [], "\n")
    parse' "(x) \n" `shouldBe` Right (x 1 2, "\n")
    parse' "(x,) \n" `shouldBe` Right (loc 1 1 1 5 $ Tuple [x 1 2], "\n")
    parse' "(x, y, z) \n" `shouldBe` Right (loc 1 1 1 10 $ Tuple [x 1 2, y 1 5, z 1 8], "\n")
    parse' "(\nx\n,\ny\n,\n) \n" `shouldBe` Right (loc 1 1 6 2 $ Tuple [x 2 1, y 4 1], "\n")
    parse' "[] \n" `shouldBe` Right (loc 1 1 1 3 $ List [], "\n")
    parse' "[x] \n" `shouldBe` Right (loc 1 1 1 4 $ List [x 1 2], "\n")
    parse' "[x,] \n" `shouldBe` Right (loc 1 1 1 5 $ List [x 1 2], "\n")
    parse' "[x, y, z] \n" `shouldBe` Right (loc 1 1 1 10 $ List [x 1 2, y 1 5, z 1 8], "\n")
    parse' "[\nx\n,\ny\n,\n] \n" `shouldBe` Right (loc 1 1 6 2 $ List [x 2 1, y 4 1], "\n")
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
    parse' "@x.y \n" `shouldBe` Right (loc 1 1 1 3 $ For ["x"] (y 1 4), "\n")
    parse' "@ x .\ny \n" `shouldBe` Right (loc 1 1 1 4 $ For ["x"] (y 2 1), "\n")
    parse' "@ x y \nz \n" `shouldBe` Right (loc 1 1 1 6 $ For ["x", "y"] (z 2 1), "\n")
    parse' "@\nx. y \n" `shouldBe` Left ([], "@\nx. y \n")
    -- Ann Expr Type
    -- Or Expr Expr
    -- Fun Pattern Expr
    -- App Expr Expr
    -- Call String [Expr]
    -- parse' "&x.y \n" `shouldBe` Right (Fix "x" y, "\n")
    -- parse' "& x .\ny \n" `shouldBe` Right (Fix "x" y, "\n")
    -- parse' "& x y \nz \n" `shouldBe` Right (fix ["x", "y"] z, "\n")
    -- parse' "&\nx. y \n" `shouldBe` Left ([], "&\nx. y \n")
    -- parse' "x:y \n" `shouldBe` Right (Ann x y, "\n")
    -- parse' "x :\ny \n" `shouldBe` Right (Ann x y, "\n")
    -- parse' "x\n:\ny \n" `shouldBe` Right (Ann x y, "\n")
    -- parse' "x : y : z \n" `shouldBe` Right (Ann x (Ann y z), "\n")
    -- parse' "(x) \n" `shouldBe` Right (x, "\n")
    -- parse' "(\nx\n) \n" `shouldBe` Right (x, "\n")
    -- parse' "(x,y) \n" `shouldBe` Right (and' [x, y], "\n")
    -- parse' "(x, y, z) \n" `shouldBe` Right (and' [x, y, z], "\n")
    -- parse' "(\nx\n,\ny\n,\n) \n" `shouldBe` Right (and' [x, y], "\n")
    -- parse' "x|y \n" `shouldBe` Right (Or x y, "\n")
    -- parse' "x | y | z \n" `shouldBe` Right (Or x (Or y z), "\n")
    -- parse' "x\n|\ny \n" `shouldBe` Right (Or x y, "\n")
    -- parse' "x->y \n" `shouldBe` Right (Fun x y, "\n")
    -- parse' "x -> y -> z \n" `shouldBe` Right (Fun x (Fun y z), "\n")
    -- parse' "x\n->\ny\n->\nz \n" `shouldBe` Right (Fun x (Fun y z), "\n")
    -- parse' "a() \n" `shouldBe` Right (app a [], "\n")
    -- parse' "a(x) \n" `shouldBe` Right (app a [x], "\n")
    -- parse' "a(x,y) \n" `shouldBe` Right (app a [x, y], "\n")
    -- parse' "a (x, y, z) \n" `shouldBe` Right (app a [x, y, z], "\n")
    -- parse' "a(\nx\n,\ny\n,\n) \n" `shouldBe` Right (app a [x, y], "\n")
    -- parse' "%f \n" `shouldBe` Right (call "f" [], "\n")
    -- parse' "%f() \n" `shouldBe` Right (call "f" [], "\n")
    -- parse' "%f(x) \n" `shouldBe` Right (call "f" [x], "\n")
    -- parse' "%f(x,y) \n" `shouldBe` Right (call "f" [x, y], "\n")
    -- parse' "%f (x, y, z) \n" `shouldBe` Right (call "f" [x, y, z], "\n")
    -- parse' "%f(\nx\n,\ny\n,\n) \n" `shouldBe` Right (call "f" [x, y], "\n")
    -- parse' "^{}y \n" `shouldBe` Right (Let [] y, "\n")
    -- parse' "^ { } y \n" `shouldBe` Right (Let [] y, "\n")
    -- parse' "^\n{\n}\ny \n" `shouldBe` Right (Let [] y, "\n")
    -- parse' "^x=a;y \n" `shouldBe` Right (Let [("x", a)] y, "\n")
    -- parse' "^ x = a ; ^ y = b ; z \n" `shouldBe` Right (Let [("x", a), ("y", b)] z, "\n")
    -- parse' "^\nx\n=\na \n^\ny\n=\nb \nz \n" `shouldBe` Right (Let [("x", a), ("y", b)] z, "\n")
    -- Op1 Op1 Expr
    -- Op2 Op2 Expr Expr
    -- Dot Expr String (Maybe [Expr])
    -- Spread Expr
    -- Get Expr Expr
    -- Slice Expr (Expr, Expr)
    -- Match Expr [Expr]
    -- MatchFun [Expr]
    -- Let (Pattern, Expr) Expr
    -- Bind (Pattern, Expr) Expr
    -- Record [(String, Expr)]
    -- Select Expr [(String, Expr)]
    -- With Expr [(String, Expr)]
    -- If Expr Expr
    -- IfElse Expr Expr Expr
    -- Meta (C.Metadata Expr) Expr
    -- Err
    "" `shouldBe` ""

  it "☯ Tao.grammar.parser.errors" $ do
    parse' "$" `shouldBe` Left ([], "$")

  it "☯ Tao.grammar.layout" $ do
    "" `shouldBe` ""

  it "☯ Tao.resolve" $ do
    let (x, y, z, w) = (Var "x", Var "y", Var "z", Var "w")
    let (i1, i2) = (Int 1, Int 2)
    let test a b = Test (UnitTest "filename" (Pos 1 2) "name" a b)

    -- Stmt
    let ctx = []
    resolve ctx "m1" ("x", Def (x, y)) `shouldBe` [("m1", y)]
    resolve ctx "m1" ("x", Def (y, z)) `shouldBe` []
    resolve ctx "m1" ("x", TypeDef ("x", [], [])) `shouldBe` [("m1", Fun (Tuple []) (Tuple []))]
    resolve ctx "m1" ("x", test y z) `shouldBe` []

    -- [Stmt]
    let ctx = []
    resolve ctx "m1" ("x", [] :: [Stmt]) `shouldBe` []
    resolve ctx "m1" ("x", [Def (x, y)]) `shouldBe` [("m1", y)]
    resolve ctx "m1" ("x", [Def (x, y), Def (x, z)]) `shouldBe` [("m1", y), ("m1", z)]

    -- Module
    let ctx = []
    resolve ctx "m1" ("x", ("m1", []) :: Module) `shouldBe` []
    resolve ctx "m1" ("x", ("m1", [Def (x, y)])) `shouldBe` [("m1", y)]
    resolve ctx "m1" ("x", ("m1", [Def (x, y), Def (x, z)])) `shouldBe` [("m1", y), ("m1", z)]
    resolve ctx "m1" ("x", ("m2", [Def (x, y)])) `shouldBe` []

    -- Name
    let ctx = [("m1", [Def (x, y)]), ("m1/@f1", [Def (x, z)])]
    resolve ctx "m1" "x" `shouldBe` [("m1", y), ("m1", z)]
    resolve ctx "m1/@f1" "x" `shouldBe` [("m1", y), ("m1", z)]
    resolve ctx "m1" "y" `shouldBe` []

    -- Imports
    -- let ctx = [("m1", [Def (x, y)]), ("m1/@f1", [Def (x, z)])]
    -- resolve ctx "m" ("x", [Import "m1" "m1" [("x", "x")], Def (x, w)]) `shouldBe` [("m1", y), ("m1/@f1", z), ("m", w)]
    -- resolve ctx "m1" ("x", [Import "m1" "m1" [("x", "x")], Def (x, w)]) `shouldBe` [("m1", w)]
    -- resolve ctx "m1" ("x", [Import "m1/@f1" "m1" [("x", "x")], Def (x, w)]) `shouldBe` [("m1/@f1", z), ("m1", w)]

    -- Self imports
    let ctx =
          [ ("m1", [Import "m1" "m1" [("x", "x")], Def (x, i1)]),
            ("m1/@f1", [Import "m1" "m1" [("x", "x")], Def (x, i2)]),
            ("m2/@f1", [Import "m2" "m2" [("y", "y")], Def (y, i1)]),
            ("m2/@f2", [Import "m2" "m2" [("y", "y")], Def (y, i2)]),
            ("m3/@f1", [Import "m3/@f1" "m3/@f1" [("z", "z")], Def (z, i1)]),
            ("m3/@f2", [Import "m3/@f1" "m3/@f1" [("z", "z")], Def (z, i2)])
          ]
    resolve ctx "m1" "x" `shouldBe` [("m1", i1), ("m1", i2)]
    resolve ctx "m2" "y" `shouldBe` [("m2", i1), ("m2", i2)]
    resolve ctx "m2/@f1" "y" `shouldBe` [("m2", i1), ("m2", i2)]
    -- resolve ctx "m3" "z" `shouldBe` [("m3", i1), ("m3", i2)]
    -- resolve ctx "m3/@f1" "z" `shouldBe` [("m3", i1), ("m3", i2)]

    -- Import wildcards
    let ctx = [("m1", [Def (x, y)])]
    resolve ctx "m" ("x", [Import "m1" "m1" [("*", "")], Def (x, w)]) `shouldBe` [("m1", y), ("m", w)]

  it "☯ TODO" $ do
    "" `shouldBe` ""
