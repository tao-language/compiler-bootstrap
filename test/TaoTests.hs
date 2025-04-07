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
filename = "<test>"

fmt :: Expr -> String
fmt = format 80 . dropLocations

core :: C.Expr -> String
core = C.format 80 . C.dropMeta

def' :: String -> String -> Stmt
def' a b = case (parse ("ctx." ++ a) a, parse ("ctx." ++ a) b) of
  (Right (a, _), Right (b, _)) -> def (a, b)
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

compile' :: Context -> FilePath -> Expr -> (C.Env, (C.Expr, C.Type))
compile' ctx path expr = do
  let (env, a) = compile ctx path expr
  (env, C.typedOf a)

check' :: C.Expr -> [(Maybe (Int, Int, Int, Int), Error Expr)]
check' a = do
  let f (Just (Location _ (Range start end)), err) = (Just (start.row, start.col, end.row, end.col), err)
      f (Nothing, err) = (Nothing, err)
  map f (check (lift a))

eval' :: C.Env -> C.Expr -> C.Type -> (String, String)
eval' env expr type' =
  bimap (fmt . dropTypes) (fmt . dropTypes) (eval env (C.Ann expr type'))

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
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
  let let' r c (x, y) z = loc r c r (c + 3) (Let (x, y) z)

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
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "_" `shouldBe` Right expr
    core a `shouldBe` "_"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("_", "_")

  it "☯ Tao.Meta.Location" $ do
    let ctx = []
    let expr = Meta (C.Loc $ Location "file" (Range (Pos 1 2) (Pos 3 4))) (any 1 20)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "^loc[:1:2,3:4](_)" `shouldBe` Left "syntax error, remaining: :1:2,3:4](_)"
    syntax' "^loc[file:1:2,3:4](_)" "_" `shouldBe` Right expr
    core a `shouldBe` "_"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("_", "_")

  it "☯ Tao.Meta.Comments.1" $ do
    let ctx = []
    let expr = Meta (C.Comments ["c1"]) (any 2 1)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "# c1\n_" `shouldBe` Right expr
    core a `shouldBe` "_"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("# c1\n_", "_")

  it "☯ Tao.Meta.Comments.2" $ do
    let ctx = []
    let expr = Meta (C.Comments ["c1", "c2"]) (any 3 1)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "# c1\n# c2\n_" `shouldBe` Right expr
    core a `shouldBe` "_"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("# c1\n# c2\n_", "_")

  it "☯ Tao.Meta.TrailingComment" $ do
    let ctx = []
    let expr = Meta (C.TrailingComment "c") (any 1 1)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "_  # c\n" `shouldBe` Right expr
    core a `shouldBe` "_"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("_  # c\n", "_")

  -- TODO: multi-line comments

  it "☯ Tao.IntT" $ do
    let ctx = []
    let expr = intT 1 1
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "Int" `shouldBe` Right expr
    core a `shouldBe` "^Int"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("Int", "Int")

  it "☯ Tao.NumT" $ do
    let ctx = []
    let expr = numT 1 1
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "Num" `shouldBe` Right expr
    core a `shouldBe` "^Num"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("Num", "Num")

  it "☯ Tao.Int" $ do
    let ctx = []
    let expr = int 1 1 42
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "42" `shouldBe` Right expr
    core a `shouldBe` "42"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.Num" $ do
    let ctx = []
    let expr = num 1 1 3.14
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "3.14" `shouldBe` Right expr
    fmt expr `shouldBe` "3.14"
    core a `shouldBe` "3.14"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("3.14", "Num")

  it "☯ Tao.Char" $ do
    let ctx = []
    let expr = char 1 1 'x'
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "c'x'" `shouldBe` Right expr
    core a `shouldBe` "(Char, 120)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("c'x'", "Char(Int)")

  it "☯ Tao.Var.undefined" $ do
    let ctx = []
    let expr = x 1 1
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x" `shouldBe` Right expr
    core a `shouldBe` "x"
    core t `shouldBe` "!undefined-var(x)"
    check' (C.Ann a t) `shouldBe` [(Just (1, 1, 1, 2), undefinedVar "x")]
    eval' env a t `shouldBe` ("x", "!undefined-var(x)")

  it "☯ Tao.Var.direct" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = x 1 1
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x" `shouldBe` Right expr
    core a `shouldBe` "x"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.Var.indirect" $ do
    let ctx = [("m", [def' "y" "42", def' "x" "y"])]
    let expr = x 1 1
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x" `shouldBe` Right expr
    core a `shouldBe` "x"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.Tag.0" $ do
    let ctx = []
    let expr = tag 1 1 "A" []
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "A" `shouldBe` Right expr
    core a `shouldBe` "A"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("A", "A")

  it "☯ Tao.Tag.1" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = tag 1 1 "A" [x 1 3]
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "A(x)" `shouldBe` Right expr
    core a `shouldBe` "(A, x)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("A(42)", "A(Int)")

  it "☯ Tao.Tag.2" $ do
    let ctx = [("m", [def' "x" "42", def' "y" "3.14"])]
    let expr = tag 1 1 "A" [x 1 3, y 1 6]
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "A(x, y)" `shouldBe` Right expr
    core a `shouldBe` "(A, x, y)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("A(42, 3.14)", "A(Int, Num)")

  it "☯ Tao.Tag.error" $ do
    let ctx = [("m", [])]
    let expr = tag 1 1 "A" [x 1 3]
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "A(x)" `shouldBe` Right expr
    core a `shouldBe` "(A, x : !undefined-var(x))"
    check' (C.Ann a t) `shouldBe` [(Just (1, 3, 1, 4), undefinedVar "x")]
    eval' env a t `shouldBe` ("A(x)", "A(!undefined-var(x))")

  it "☯ Tao.Ann.ok" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = ann 1 3 (x 1 1) (intT 1 5)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x : Int" `shouldBe` Right expr
    core a `shouldBe` "x"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.Ann.type-mismatch" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = ann 1 3 (x 1 1) (numT 1 5)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x : Num" `shouldBe` Right expr
    core a `shouldBe` "x"
    core t `shouldBe` "!type-mismatch(^Int, ^Num)"
    check' (C.Ann a t) `shouldBe` [(Just (1, 1, 1, 2), typeMismatch IntT (numT 1 5))]
    eval' env a t `shouldBe` ("42", "!type-mismatch(Int, ^loc[<test>:1:5,1:8](Num))")

  it "☯ Tao.Tuple.0" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (Tuple [])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "()" `shouldBe` Right expr
    core a `shouldBe` "()"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("()", "()")

  it "☯ Tao.Tuple.1" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = loc 1 1 1 3 (Tuple [x 1 2])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax' "(x)" "x" `shouldBe` Right (x 1 2)
    core a `shouldBe` "x"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.Tuple.2" $ do
    let ctx = [("m", [def' "x" "42", def' "y" "3.14"])]
    let expr = loc 1 1 1 7 (Tuple [x 1 2, y 1 5])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "(x, y)" `shouldBe` Right expr
    core a `shouldBe` "(x, y)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("(42, 3.14)", "(Int, Num)")

  it "☯ Tao.Tuple.error" $ do
    let ctx = [("m", [def' "x" "42", def' "y" "3.14"])]
    let expr = loc 1 1 1 7 (Tuple [x 1 2, z 1 5])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "(x, z)" `shouldBe` Right expr
    core a `shouldBe` "(x, z : !undefined-var(z))"
    check' (C.Ann a t) `shouldBe` [(Just (1, 5, 1, 6), undefinedVar "z")]
    eval' env a t `shouldBe` ("(42, z)", "(Int, !undefined-var(z))")

  it "☯ Tao.List.0" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (List [])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "[]" `shouldBe` Right expr
    core a `shouldBe` "[]"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("[]", "[]")

  it "☯ Tao.List.1" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = loc 1 1 1 4 (List [x 1 2])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "[x]" `shouldBe` Right expr
    core a `shouldBe` "(::, x, [])"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("[42]", "[Int]")

  it "☯ Tao.List.2" $ do
    let ctx = [("m", [def' "x" "42", def' "y" "9"])]
    let expr = loc 1 1 1 7 (List [x 1 2, y 1 5])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "[x, y]" `shouldBe` Right expr
    core a `shouldBe` "(::, x, ::, y, [])"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("[42, 9]", "[Int, Int]")

  it "☯ Tao.String.empty" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (String [])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "''" `shouldBe` Right expr
    core a `shouldBe` "''"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("''", "''")

  -- it "☯ Tao.String literal" $ do
  -- it "☯ Tao.String interpolation" $ do

  it "☯ Tao.Or.different" $ do
    let ctx = [("m", [def' "x" "42", def' "y" "3.14"])]
    let expr = or' 1 3 (x 1 1) (y 1 5)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x | y" `shouldBe` Right expr
    core a `shouldBe` "x | y"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42 | 3.14", "Int | Num")

  it "☯ Tao.Or.same" $ do
    let ctx = [("m", [def' "x" "42", def' "y" "9"])]
    let expr = or' 1 3 (x 1 1) (y 1 5)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x | y" `shouldBe` Right expr
    core a `shouldBe` "x | y"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42 | 9", "Int")

  it "☯ Tao.For.0" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = loc 1 1 1 2 (For [] (x 1 4))
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "@. x" `shouldBe` Right expr
    core a `shouldBe` "x"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.For.1" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = loc 1 1 1 3 (For ["a"] (x 1 5))
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "@a. x" `shouldBe` Right expr
    core a `shouldBe` "@a. x"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.For.2" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = loc 1 1 1 5 (For ["a", "b"] (x 1 7))
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "@a b. x" `shouldBe` Right expr
    core a `shouldBe` "@a b. x"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.Fun.unbound" $ do
    let ctx = [("m", [def' "x" "42", def' "y" "3.14"])]
    let expr = fun 1 3 (x 1 1) (y 1 6)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x -> y" `shouldBe` Right expr
    core a `shouldBe` "@x. (x : x1T) -> (y : ^Num)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("@. (x : x1T) -> 3.14", "@. x1T -> Num")

  it "☯ Tao.Fun.bound" $ do
    let ctx = [("m", [def' "x" "42", def' "y" "3.14"])]
    let expr = loc 1 1 1 2 (For [] $ fun 1 6 (x 1 4) (y 1 9))
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "@. x -> y" `shouldBe` Right expr
    core a `shouldBe` "(x : ^Int) -> (y : ^Num)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("(42 : Int) -> 3.14", "Int -> Num")

  it "☯ Tao.App.empty" $ do
    let ctx = [("m", [def' "x" "() -> 42"])]
    let expr = loc 1 2 1 4 (app (x 1 1) [])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x()" `shouldBe` Right expr
    core a `shouldBe` "x (() : ())"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.App.args1" $ do
    let ctx = [("m", [def' "x" "a -> a", def' "y" "42"])]
    let expr = loc 1 2 1 5 (app (x 1 1) [y 1 3])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x(y)" `shouldBe` Right expr
    core a `shouldBe` "x (y : ^Int)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  it "☯ Tao.App.args2" $ do
    let ctx = [("m", [def' "x" "(a, b) -> b", def' "y" "42", def' "z" "3.14"])]
    let expr = loc 1 2 1 8 (app (x 1 1) [y 1 3, z 1 6])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x(y, z)" `shouldBe` Right expr
    core a `shouldBe` "x ((y, z) : (^Int, ^Num))"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("3.14", "Num")

  it "☯ Tao.App.Fun" $ do
    let ctx = [("m", [def' "x" "A -> B", def' "y" "A"])]
    let expr = loc 1 2 1 5 (app (x 1 1) [y 1 3])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x(y)" `shouldBe` Right expr
    core a `shouldBe` "x (y : A)"
    core t `shouldBe` "B"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("B", "B")

  it "☯ Tao.App.Or.first" $ do
    let ctx = [("m", [def' "x" "A -> B | B -> A", def' "y" "A"])]
    let expr = loc 1 2 1 5 (app (x 1 1) [y 1 3])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x(y)" `shouldBe` Right expr
    core a `shouldBe` "x (y : A)"
    core t `shouldBe` "B"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("B", "B")

  it "☯ Tao.App.Or.second" $ do
    let ctx = [("m", [def' "x" "A -> B | B -> A", def' "y" "B"])]
    let expr = loc 1 2 1 5 (app (x 1 1) [y 1 3])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x(y)" `shouldBe` Right expr
    core a `shouldBe` "x (y : B)"
    core t `shouldBe` "A"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("A", "A")

  it "☯ Tao.App.Or.both" $ do
    let ctx = [("m", [def' "x" "A -> B | B -> A", def (Var "y", Var "y")])]
    let expr = loc 1 2 1 5 (app (x 1 1) [y 1 3])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "x(y)" `shouldBe` Right expr
    core a `shouldBe` "x (y : (A | B))"
    core t `shouldBe` "B | A"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("let A = y\nB | let B = y\nA", "B | A")

  -- TODO: App named arguments
  -- TODO: App default values

  it "☯ Tao.Call.0" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (Call "f" [])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "%f" `shouldBe` Right expr
    syntax' "%f()" "%f" `shouldBe` Right expr
    core a `shouldBe` "%f()"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("%f", "_")

  it "☯ Tao.Call.1" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = loc 1 1 1 9 (Call "int_neg" [x 1 10])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "%int_neg(x)" `shouldBe` Right expr
    core a `shouldBe` "%int_neg(x)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("-42", "_")

  it "☯ Tao.Call.2" $ do
    let ctx = [("m", [def' "x" "40", def' "y" "2"])]
    let expr = loc 1 1 1 9 (Call "int_add" [x 1 10, y 1 13])
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "%int_add(x, y)" `shouldBe` Right expr
    core a `shouldBe` "%int_add(x, y)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "_")

  it "☯ Tao.Match.error.empty" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = match 1 1 (x 1 7) []
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "match x {}" `shouldBe` Right expr
    core a `shouldBe` "!cannot-apply((), ()) (x : ^Int)"
    check' (C.Ann a t) `shouldBe` [(Just (1, 7, 1, 8), notAFunction (Err (cannotApply (Tuple []) (Tuple []))) Any)]
    eval' env a t `shouldBe` ("!cannot-apply(!cannot-apply((), ()), ^loc[<test>:1:7,1:8](^loc[ctx.x:1:1,1:3](42)))", "Int")

  it "☯ Tao.Match.error.arg" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = match 1 1 (z 1 7) [fun 2 5 (y 2 3) (x 2 8)]
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "match z {\n| y -> x\n}" `shouldBe` Right expr
    core a `shouldBe` "^let<y> y : yT = z : !undefined-var(z); x : ^Int"
    check' (C.Ann a t) `shouldBe` [(Just (1, 7, 1, 8), undefinedVar "z")]
    -- Undefined since there are errors (should this be removed?)
    -- eval' env a t `shouldBe` ("match z {\n| (y : !undefined-var(z)) -> 42\n}", "Int")
    eval' env a t `shouldBe` ("42", "_")

  it "☯ Tao.Match.error.case" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = match 1 1 (x 1 7) [fun 2 5 (y 2 3) (z 2 8)]
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "match x {\n| y -> z\n}" `shouldBe` Right expr
    core a `shouldBe` "^let<y> y : yT = x : ^Int; z : !undefined-var(z)"
    check' (C.Ann a t) `shouldBe` [(Just (2, 8, 2, 9), undefinedVar "z")]
    eval' env a t `shouldBe` ("z", "_")

  it "☯ Tao.Match.1" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = match 1 1 (x 1 7) [fun 2 5 (a 2 3) (int 2 8 1)]
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "match x {\n| a -> 1\n}" `shouldBe` Right expr
    core a `shouldBe` "^let a : ^Int = x : ^Int; 1 : ^Int"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("1", "Int")

  it "☯ Tao.Match.2" $ do
    let ctx = [("m", [def' "x" "42"])]
    let expr = match 1 1 (x 1 7) [fun 2 5 (a 2 3) (int 2 8 1), fun 3 5 (b 3 3) (int 3 8 2)]
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "match x {\n| a -> 1\n| b -> 2\n}" `shouldBe` Right expr
    core a `shouldBe` "(@a. (a : ^Int) -> (1 : ^Int) | @b. (b : ^Int) -> (2 : ^Int)) (x : ^Int)"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("1", "Int")

  it "☯ Tao.Let" $ do
    let ctx = [("m", [def' "y" "42"])]
    let expr = let' 1 1 (x 1 5, y 1 9) (x 2 1)
    let (env, (a, t)) = compile' ctx "m" expr
    syntax "let x = y\nx" `shouldBe` Right expr
    core a `shouldBe` "^let x : ^Int = y : ^Int; x : ^Int"
    check' (C.Ann a t) `shouldBe` []
    eval' env a t `shouldBe` ("42", "Int")

  -- it "☯ Tao.TODO" $ do
  --   let ctx = [("m", [def' "x" "42"])]
  --   let expr = Any
  --   let (env, (a, t)) = compile' ctx "m" expr
  --   syntax "TODO" `shouldBe` Right expr
  --   core a `shouldBe` ""
  --   check' (C.Ann a t) `shouldBe` []
  --   eval' env a t `shouldBe` ("", "")

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
  --             [ def' "Bool" (Or (Fun true bool) (Fun true bool)),
  --               def' "a" (tag 10 10 "True" []),
  --               def' "b" "1",
  --               def' "c" "2"
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
