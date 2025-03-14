module TaoTests where

import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import Error
import Location (Location (Location), Position (Pos), Range (Range))
import qualified Parser as P
import Tao
import Test.Hspec

filename :: String
filename = "<test>"

fmt :: Expr -> String
fmt = format 80 . dropLocations

fmt' :: C.Expr -> String
fmt' = C.format 80 . C.dropMeta

def :: String -> String -> Stmt
def a b = case (parse ("ctx." ++ a) a, parse ("ctx." ++ a ++ " = " ++ b) b) of
  (Right (a, _), Right (b, _)) -> Def (a, b)
  (Left s, _) -> error ("ctx[pattern] syntax error, remaining: " ++ s.remaining)
  (_, Left s) -> error ("ctx[value] syntax error, remaining: " ++ s.remaining)

-- let defOp1 op f = def op (For ["a"] (lambda [Var "a"] (Call f [Var "a"])))
-- let defOp2 op f = def op (For ["a", "b"] (lambda [Var "a", Var "b"] (Call f [Var "a", Var "b"])))

syntax :: String -> Either String Expr
syntax src = syntax' src src

syntax' :: String -> String -> Either String Expr
syntax' src expected = case parse filename src of
  Right (a, _)
    | fmt a == expected -> Right a
    | otherwise -> Left ("format error: " ++ expected ++ " != " ++ fmt a)
  Left s -> Left ("syntax error, remaining: " ++ s.remaining)

core :: Context -> FilePath -> Expr -> String
core ctx path expr = do
  let (env, a) = compile ctx path expr
  case C.annOf a of
    Just (a, _) -> fmt' a
    Nothing -> fmt' a

eval' :: Context -> FilePath -> Expr -> (String, String, [(Expr, Error Expr)])
eval' ctx path expr = do
  let (result, type', errors) = eval ctx path expr
  (fmt result, fmt type', errors)

run :: SpecWith ()
run = describe "--==☯ TaoGrammar ☯==--" $ do
  let loc' r1 c1 r2 c2 = Location filename (Range (Pos r1 c1) (Pos r2 c2))
  let loc r1 c1 r2 c2 = Meta (C.Loc $ loc' r1 c1 r2 c2)
  let any r c = loc r c r (c + 1) Any
  let intT r c = loc r c r (c + 3) IntT
  let numT r c = loc r c r (c + 3) NumT
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
  let let' r c (x, y) z = loc r c r (c + 1) (Let (x, y) z)

  let a r c = var r c "a"
  let b r c = var r c "b"
  let c r c = var r c "c"
  let x r c = var r c "x"
  let y r c = var r c "y"
  let z r c = var r c "z"

  let (a', b', c') = (C.Var "a", C.Var "b", C.Var "c")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")

  it "☯ Tao.Any" $ do
    let ctx = []
    let expr = any 1 1
    syntax "_" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "_"
    eval' ctx "m" expr `shouldBe` ("_", "@_1. _1", [])

  it "☯ Tao.Meta.Location" $ do
    let ctx = []
    let expr = Meta (C.Loc $ Location "file" (Range (Pos 1 2) (Pos 3 4))) (any 1 17)
    syntax "@[:1:2,3:4] _" `shouldBe` Left "syntax error, remaining: :1:2,3:4] _"
    syntax' "@[file:1:2,3:4] _" "_" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "_"
    eval' ctx "m" expr `shouldBe` ("_", "@_1. _1", [])

  it "☯ Tao.Meta.Comments.1" $ do
    let ctx = []
    let expr = Meta (C.Comments ["c1"]) (any 2 1)
    syntax "# c1\n_" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "_"
    eval' ctx "m" expr `shouldBe` ("# c1\n_", "@_1. _1", [])

  it "☯ Tao.Meta.Comments.2" $ do
    let ctx = []
    let expr = Meta (C.Comments ["c1", "c2"]) (any 3 1)
    syntax "# c1\n# c2\n_" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "_"
    eval' ctx "m" expr `shouldBe` ("# c1\n# c2\n_", "@_1. _1", [])

  it "☯ Tao.Meta.TrailingComment" $ do
    let ctx = []
    let expr = Meta (C.TrailingComment "c") (any 1 1)
    syntax "_  # c\n" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "_"
    eval' ctx "m" expr `shouldBe` ("_  # c\n", "@_1. _1", [])

  -- TODO: multi-line comments

  it "☯ Tao.IntT" $ do
    let ctx = []
    let expr = intT 1 1
    syntax "Int" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "^Int"
    eval' ctx "m" expr `shouldBe` ("Int", "Int", [])

  it "☯ Tao.NumT" $ do
    let ctx = []
    let expr = numT 1 1
    syntax "Num" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "^Num"
    eval' ctx "m" expr `shouldBe` ("Num", "Num", [])

  it "☯ Tao.Int" $ do
    let ctx = []
    let expr = int 1 1 42
    syntax "42" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "42"
    eval' ctx "m" expr `shouldBe` ("42", "Int", [])

  it "☯ Tao.Num" $ do
    let ctx = []
    let expr = num 1 1 3.14
    syntax "3.14" `shouldBe` Right expr
    fmt expr `shouldBe` "3.14"
    core ctx "m" expr `shouldBe` "3.14"
    eval' ctx "m" expr `shouldBe` ("3.14", "Num", [])

  it "☯ Tao.Char" $ do
    let ctx = []
    let expr = char 1 1 'x'
    syntax "c'x'" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "(Char, 120)"
    eval' ctx "m" expr `shouldBe` ("c'x'", "Char(Int)", [])

  it "☯ Tao.Var.undefined" $ do
    let ctx = []
    let expr = x 1 1
    syntax "x" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x"
    eval' ctx "m" expr `shouldBe` ("x", "!undefined-var(x)", [(x 1 1, undefinedVar "x")])

  it "☯ Tao.Var.direct" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = x 1 1
    syntax "x" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x"
    eval' ctx "m" expr `shouldBe` ("42", "Int", [])

  it "☯ Tao.Var.indirect" $ do
    let ctx = [("m", [def "y" "42", def "x" "y"])]
    let expr = x 1 1
    syntax "x" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x"
    eval' ctx "m" expr `shouldBe` ("42", "Int", [])

  it "☯ Tao.Tag.0" $ do
    let ctx = []
    let expr = tag 1 1 "A" []
    syntax "A" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "A"
    eval' ctx "m" expr `shouldBe` ("A", "A", [])

  it "☯ Tao.Tag.1" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = tag 1 1 "A" [x 1 3]
    syntax "A(x)" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "(A, x)"
    eval' ctx "m" expr `shouldBe` ("A(42)", "A(Int)", [])

  it "☯ Tao.Tag.2" $ do
    let ctx = [("m", [def "x" "42", def "y" "3.14"])]
    let expr = tag 1 1 "A" [x 1 3, y 1 6]
    syntax "A(x, y)" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "(A, x, y)"
    eval' ctx "m" expr `shouldBe` ("A(42, 3.14)", "A(Int, Num)", [])

  it "☯ Tao.Ann.ok" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = Ann (x 1 1) (intT 1 5)
    syntax "x : Int" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x"
    eval' ctx "m" expr `shouldBe` ("42", "Int", [])

  it "☯ Tao.Ann.type-mismatch" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = Ann (x 1 1) (numT 1 5)
    syntax "x : Num" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x"
    eval' ctx "m" expr `shouldBe` ("42", "!type-mismatch(Int, @[<test>:1:5,1:8](Num))", [(x 1 1, typeMismatch IntT (numT 1 5))])

  it "☯ Tao.Tuple.0" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (Tuple [])
    syntax "()" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "()"
    eval' ctx "m" expr `shouldBe` ("()", "()", [])

  it "☯ Tao.Tuple.1" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = loc 1 1 1 3 (Tuple [x 1 2])
    syntax' "(x)" "x" `shouldBe` Right (x 1 2)
    core ctx "m" expr `shouldBe` "x"
    eval' ctx "m" expr `shouldBe` ("42", "Int", [])

  it "☯ Tao.Tuple.2" $ do
    let ctx = [("m", [def "x" "42", def "y" "3.14"])]
    let expr = loc 1 1 1 7 (Tuple [x 1 2, y 1 5])
    syntax "(x, y)" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "(x, y)"
    eval' ctx "m" expr `shouldBe` ("(42, 3.14)", "(Int, Num)", [])

  it "☯ Tao.Tuple.error" $ do
    let ctx = [("m", [def "x" "42", def "y" "3.14"])]
    let expr = loc 1 1 1 7 (Tuple [x 1 2, z 1 5])
    syntax "(x, z)" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "(x, z)"
    eval' ctx "m" expr `shouldBe` ("(42, z)", "(Int, !undefined-var(z))", [(Any, undefinedVar "z")])

  it "☯ Tao.List.0" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (List [])
    syntax "[]" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "[]"
    eval' ctx "m" expr `shouldBe` ("[]", "[]", [])

  it "☯ Tao.List.1" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = loc 1 1 1 4 (List [x 1 2])
    syntax "[x]" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "(::, x, [])"
    eval' ctx "m" expr `shouldBe` ("[42]", "[Int]", [])

  it "☯ Tao.List.2" $ do
    let ctx = [("m", [def "x" "42", def "y" "9"])]
    let expr = loc 1 1 1 7 (List [x 1 2, y 1 5])
    syntax "[x, y]" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "(::, x, ::, y, [])"
    eval' ctx "m" expr `shouldBe` ("[42, 9]", "[Int, Int]", [])

  it "☯ Tao.String.empty" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (String [])
    syntax "''" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "''"
    eval' ctx "m" expr `shouldBe` ("''", "''", [])

  -- it "☯ Tao.String literal" $ do
  -- it "☯ Tao.String interpolation" $ do

  it "☯ Tao.Or.different" $ do
    let ctx = [("m", [def "x" "42", def "y" "3.14"])]
    let expr = or' 1 3 (x 1 1) (y 1 5)
    syntax "x | y" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x | y"
    eval' ctx "m" expr `shouldBe` ("42 | 3.14", "Int | Num", [])

  it "☯ Tao.Or.same" $ do
    let ctx = [("m", [def "x" "42", def "y" "9"])]
    let expr = or' 1 3 (x 1 1) (y 1 5)
    syntax "x | y" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x | y"
    eval' ctx "m" expr `shouldBe` ("42 | 9", "Int", [])

  it "☯ Tao.For.0" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = loc 1 1 1 2 (For [] (x 1 4))
    syntax "@. x" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x"
    eval' ctx "m" expr `shouldBe` ("42", "Int", [])

  it "☯ Tao.For.1" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = loc 1 1 1 3 (For ["a"] (x 1 5))
    syntax "@a. x" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "@a. x"
    eval' ctx "m" expr `shouldBe` ("@a. 42", "Int", [])

  it "☯ Tao.For.2" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = loc 1 1 1 5 (For ["a", "b"] (x 1 7))
    syntax "@a b. x" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "@a b. x"
    eval' ctx "m" expr `shouldBe` ("@a b. 42", "Int", [])

  it "☯ Tao.Fun.unbound" $ do
    let ctx = [("m", [def "x" "42", def "y" "3.14"])]
    let expr = fun 1 3 (x 1 1) (y 1 6)
    syntax "x -> y" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "@x1T x. (x : x1T) -> y"
    eval' ctx "m" expr `shouldBe` ("x -> 3.14", "x1T -> Num", [])

  it "☯ Tao.Fun.bound" $ do
    let ctx = [("m", [def "x" "42", def "y" "3.14"])]
    let expr = loc 1 1 1 2 (For [] $ fun 1 6 (x 1 4) (y 1 9))
    syntax "@. x -> y" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "(x : ^Int) -> y"
    eval' ctx "m" expr `shouldBe` ("42 -> 3.14", "Int -> Num", [])

  it "☯ Tao.App.empty" $ do
    let ctx = [("m", [def "x" "() -> 42"])]
    let expr = loc 1 2 1 4 (App (x 1 1) [])
    syntax "x()" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x (() : ())"
    eval' ctx "m" expr `shouldBe` ("42", "Int", [])

  it "☯ Tao.App.args1" $ do
    let ctx = [("m", [def "x" "a -> a", def "y" "42"])]
    let expr = loc 1 2 1 5 (app (x 1 1) [y 1 3])
    syntax "x(y)" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x (y : ^Int)"
    eval' ctx "m" expr `shouldBe` ("42", "Int", [])

  it "☯ Tao.App.args2" $ do
    let ctx = [("m", [def "x" "(a, b) -> b", def "y" "42", def "z" "3.14"])]
    let expr = loc 1 2 1 8 (app (x 1 1) [y 1 3, z 1 6])
    syntax "x(y, z)" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "x ((y, z) : (^Int, ^Num))"
    eval' ctx "m" expr `shouldBe` ("3.14", "Num", [])

  -- TODO: App named arguments
  -- TODO: App default values

  it "☯ Tao.Call.0" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (Call "f" [])
    syntax "%f" `shouldBe` Right expr
    syntax' "%f()" "%f" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "%f()"
    eval' ctx "m" expr `shouldBe` ("%f", "_1", [])

  it "☯ Tao.Call.1" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = loc 1 1 1 9 (Call "int_neg" [x 1 10])
    syntax "%int_neg(x)" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "%int_neg(x)"
    eval' ctx "m" expr `shouldBe` ("-42", "_1", [])

  it "☯ Tao.Call.2" $ do
    let ctx = [("m", [def "x" "40", def "y" "2"])]
    let expr = loc 1 1 1 9 (Call "int_add" [x 1 10, y 1 13])
    syntax "%int_add(x, y)" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "%int_add(x, y)"
    eval' ctx "m" expr `shouldBe` ("42", "_1", [])

  it "☯ Tao.Match.empty" $ do
    let ctx = [("m", [def "x" "42"])]
    let expr = match 1 1 (x 1 7) []
    syntax "match x {}" `shouldBe` Right expr
    core ctx "m" expr `shouldBe` "!cannot-apply((), ()) (x : !error(NotAFunction !cannot-apply((), ()) _))"
    eval' ctx "m" expr
      `shouldBe` ( "!cannot-apply(!cannot-apply((), ()), @[ctx.x = 42:1:1,1:3](42) : !error(NotAFunction (Err (RuntimeError (CannotApply (Tuple []) (Tuple [])))) Any))",
                   "Int",
                   [(x 1 7, notAFunction (Err (cannotApply (Tuple []) (Tuple []))) Any)]
                 )

  -- it "☯ Tao.Match.error" $ do
  --   let ctx = [("m", [def "x" "42"])]
  --   let expr = match 1 1 (x 1 7) [fun 2 5 (y 2 3) (z 2 8)]
  --   syntax "match x {\n| y -> z\n}" `shouldBe` Right expr
  --   core ctx "m" expr `shouldBe` "^let y : ^Int = x : ^Int; z"
  --   eval' ctx "m" expr
  --     `shouldBe` ( "z",
  --                  "!undefined-var(z)",
  --                  [()]
  --                )

  -- it "☯ Tao.Match.2" $ do
  --   let ctx = [("m", [def "x" "42"])]
  --   let match' arg (a, b) (c, d) = match 1 1 arg [fun 1 14 a b, fun 1 23 c d]
  --   let expr = match' (x 1 7) (a 1 12, int 1 17 1) (b 1 21, int 1 26 2)
  --   let expr = match 1 1 (x 1 7)[fun 1 14 (a 1 1) (b 1 1), fun 1 23 ()]
  --   syntax "match x {\n| a -> 1\n| b -> 2\n}" `shouldBe` Right expr
  --   core ctx "m" expr `shouldBe` ""
  --   eval' ctx "m" expr `shouldBe` ("", "", [])

  -- it "☯ Tao.Let" $ do
  --   let ctx = [("m", [def "y" "42"])]
  --   let expr = let' 1 3 (x 1 1, y 1 5) (x 1 8)
  --   let (_, expr') = compile ctx "m" expr
  --   syntax "x = y; x" `shouldBe` Right expr
  --   format 80 expr `shouldBe` "x = y\nx"
  --   C.dropMeta expr' `shouldBe` C.Ann (C.App (C.For "x" $ C.Fun (C.Ann x' C.IntT) (C.Ann x' C.IntT)) (C.Ann y' C.IntT)) C.IntT
  --   lift expr' `shouldBe` Ann (let' 1 3 (Ann (x 1 1) IntT, Ann (y 1 5) IntT) (loc 1 8 1 9 (Ann (Var "x") IntT))) IntT
  --   dropMeta (eval ctx "m" expr) `shouldBe` Int 42

  -- it "☯ Tao.TODO" $ do
  --   let ctx = [("m", [def "x" "42"])]
  --   let expr = Any
  --   let (_, expr') = compile ctx "m" expr
  --   syntax "TODO" `shouldBe` Right expr
  --   format 80 expr `shouldBe` "TODO"
  --   C.dropMeta expr' `shouldBe` C.Ann C.Any C.IntT
  --   lift expr' `shouldBe` Ann expr IntT
  --   dropMeta (eval ctx "m" expr) `shouldBe` Any

  -- Bind (Pattern, Expr) Expr
  -- Record [(String, Expr)]
  -- Select Expr [(String, Expr)]
  -- With Expr [(String, Expr)]
  -- Record type definitions
  -- Record default values
  -- Record var shortcut
  -- App named arguments
  -- App default values
  -- Spread
  -- TODO
  -- Deprecated

  -- let if' r c x y z = loc r c r (c + 2) (If x y z)
  -- it "☯ Tao.If" $ do
  --   let ctx =
  --         [ ( "m",
  --             [ def "Bool" (Or (Fun true bool) (Fun true bool)),
  --               def "a" (tag 10 10 "True" []),
  --               def "b" "1",
  --               def "c" "2"
  --             ]
  --           )
  --         ]
  --   let (bool', true', false') = (C.Tag "Bool", C.Tag "True", C.Tag "False")
  --   let expr = if' 1 1 (a 1 4) (b 1 11) (c 1 18)
  --   let (_, expr') = compile ctx "m" expr
  --   syntax "if a then b else c" `shouldBe` Right expr
  --   format 80 expr `shouldBe` "if a then b else c"
  --   -- TODO: fix this
  --   C.dropMeta expr' `shouldBe` C.Ann (C.App (C.Or (C.Fun (C.Ann true' bool') b') (C.Fun (C.Ann false' bool') c')) (C.Ann a' bool')) C.IntT
  --   lift expr' `shouldBe` Ann expr IntT
  --   dropMeta (eval ctx "m" expr) `shouldBe` Int 1

  -- it "☯ Tao.Err" $ do
  --   syntax "!error _" `shouldBe` Right (loc 1 1 1 7 (Err (customError $ any 1 8)), "")
  --   format 80 (Err (customError Any)) `shouldBe` "!error _"

  --   let ctx = []
  --   let expr = loc 1 1 1 7 (Err (customError $ any 1 8))
  --   let (_, expr') = compile ctx "m" expr
  --   syntax "!error _" `shouldBe` Right expr
  --   format 80 expr `shouldBe` "!error _"
  --   C.dropMeta expr' `shouldBe` C.Ann (C.Err (customError C.Any)) C.Any
  --   lift expr' `shouldBe` Ann expr Any
  --   dropMeta (eval ctx "m" expr) `shouldBe` Err (customError $ any 1 8)

  it "☯ TODO" $ do
    "" `shouldBe` ""
