module CoreTests where

import Core
import Data.Bifunctor (Bifunctor (first))
import Data.Char (toLower)
import Error (Error (..), TypeError (..), cannotApply, customError, typeMismatch)
import Location (Location (Location), Position (Pos), Range (Range))
import Parser (State (..))
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯️ Core language ☯️==--" $ do
  let (i0, i1, i2) = (Int 0, Int 1, Int 2)
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (f, g, h) = (Var "f", Var "g", Var "h")
  let err = Err (customError Any)

  let add a b = Call "int_add" [a, b]
  let sub a b = Call "int_sub" [a, b]
  let mul a b = Call "int_mul" [a, b]
  let ops =
        [ ( "null",
            \eval args -> case map (dropTypes . eval) args of
              [] -> Just (Tag "Null")
              _ -> Nothing
          ),
          ( "int_neg",
            \eval args -> case map (dropTypes . eval) args of
              [Int x] -> Just (Int (-x))
              _ -> Nothing
          ),
          ( "int_add",
            \eval args -> case map (dropTypes . eval) args of
              [Int x, Int y] -> Just (Int (x + y))
              _ -> Nothing
          ),
          ( "int_sub",
            \eval args -> case map (dropTypes . eval) args of
              [Int x, Int y] -> Just (Int (x - y))
              _ -> Nothing
          ),
          ( "int_mul",
            \eval args -> case map (dropTypes . eval) args of
              [Int x, Int y] -> Just (Int (x * y))
              _ -> Nothing
          )
        ]

  let factorial f = Fix f (case0 `Or` caseN f)
        where
          case0 = Fun i0 i1
          caseN f = For "x" (Fun x (x `mul` App (Var f) (x `sub` i1)))

  let filename = "<CoreTests>"
  let parse' :: String -> Either ([String], String) (Expr, String)
      parse' text = case parse 0 filename text of
        Right (a, s) -> Right (a, s.remaining)
        Left s -> Left (s.context, s.remaining)
  let run env src = case parse' src of
        Right (a, "") -> Right (format 80 $ eval ops (Let env a))
        Right (_, rem) -> Left ("remaining: " ++ rem)
        Left (_, rem) -> Left ("syntax error: " ++ rem)

  it "☯ Core.Any" $ do
    let env = []
    let expr = Any
    parse' "_ " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "_"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, Var "_1", [("_1", Var "_1")])
    eval ops (Let env expr') `shouldBe` expr

  it "☯ Core.Unit" $ do
    let env = []
    let expr = Unit
    parse' "() " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "()"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, expr, [])
    eval ops (Let env expr') `shouldBe` expr

  it "☯ Core.IntT" $ do
    let env = []
    let expr = IntT
    parse' "!Int " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "!Int"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, expr, [])
    eval ops (Let env expr') `shouldBe` expr

  it "☯ Core.NumT" $ do
    let env = []
    let expr = NumT
    parse' "!Num " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "!Num"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, expr, [])
    eval ops (Let env expr') `shouldBe` expr

  it "☯ Core.Int" $ do
    let env = []
    let expr = Int 42
    parse' "42 " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "42"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, IntT, [])
    eval ops (Let env expr') `shouldBe` expr

  it "☯ Core.Num" $ do
    let env = []
    let expr = Num 3.14
    parse' "3.14 " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "3.14"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, NumT, [])
    eval ops (Let env expr') `shouldBe` expr

  it "☯ Core.Tag" $ do
    let env = []
    let expr = Tag "A"
    parse' "A " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "A"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, expr, [])
    eval ops (Let env expr') `shouldBe` expr

  it "☯ Core.Var" $ do
    let env = [("x", Int 42)]
    let expr = Var "x"
    parse' "x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, IntT, [])
    eval ops (Let env expr') `shouldBe` Int 42

  it "☯ Core.Ann" $ do
    let env = [("x", Int 42), ("y", IntT)]
    let expr = Ann x y
    parse' "x : y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x : y"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (Ann x IntT, IntT, [("y", IntT)])
    eval ops (Let env expr') `shouldBe` Ann (Int 42) IntT

  it "☯ Core.And 2" $ do
    let env = [("x", Int 42), ("y", Num 3.14)]
    let expr = And x y
    parse' "(x, y) " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "(x, y)"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, And IntT NumT, [])
    eval ops (Let env expr') `shouldBe` And (Int 42) (Num 3.14)

  it "☯ Core.And 3" $ do
    let env = [("x", Int 42), ("y", Num 3.14), ("z", Unit)]
    let expr = and' [x, y, z]
    parse' "(x, y, z) " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "(x, y, z)"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, and' [IntT, NumT, Unit], [])
    eval ops (Let env expr') `shouldBe` and' [Int 42, Num 3.14, Unit]

  it "☯ Core.Or" $ do
    let env = [("x", Int 42), ("y", Num 3.14)]
    let expr = Or x y
    parse' "x | y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x | y"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, Or IntT NumT, [])
    eval ops (Let env expr') `shouldBe` Or (Int 42) (Num 3.14)

  it "☯ Core.For" $ do
    let env = [("y", Int 42)]
    let expr = For "x" y
    parse' "@x. y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "@x. y"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, IntT, [("x", x)])
    eval ops (Let env expr') `shouldBe` For "x" (Int 42)

  it "☯ Core.Fix" $ do
    let env = [("y", Int 42)]
    let expr = Fix "x" y
    parse' "&x. y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "&x. y"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, IntT, [("x", x)])
    eval ops (Let env expr') `shouldBe` Fix "x" (Int 42)

  it "☯ Core.Fun" $ do
    let env = [("x", Int 42), ("y", Num 3.14)]
    let expr = Fun x y
    parse' "x -> y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x -> y"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (Fun (Ann x IntT) y, Fun IntT NumT, [])
    eval ops (Let env expr') `shouldBe` Fun (Ann (Int 42) IntT) (Num 3.14)

  it "☯ Core.App" $ do
    let env = [("x", Fun (Int 1) (Num 3.14)), ("y", Int 1)]
    let expr = App x y
    parse' "x y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x y"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (App x (Ann y IntT), NumT, [])
    eval ops (Let env expr') `shouldBe` Num 3.14

  it "☯ Core.Call 0" $ do
    let env = []
    let expr = Call "null" []
    parse' "%null() " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "%null()"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (Call "null" [], Var "_1", [])
    eval ops (Let env expr') `shouldBe` Tag "Null"

  it "☯ Core.Call 1" $ do
    let env = [("x", Int 1)]
    let expr = Call "int_neg" [x]
    parse' "%int_neg(x) " `shouldBe` Right (expr, "")
    parse' "%int_neg x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "%int_neg(x)"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (Call "int_neg" [x], Var "_1", [])
    eval ops (Let env expr') `shouldBe` Int (-1)

  it "☯ Core.Call 2" $ do
    let env = [("x", Int 1), ("y", Int 2)]
    let expr = Call "int_add" [x, y]
    parse' "%int_add(x, y) " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "%int_add(x, y)"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (Call "int_add" [x, y], Var "_1", [])
    eval ops (Let env expr') `shouldBe` Int 3

  it "☯ Core.Let 0" $ do
    let env = [("x", Int 1)]
    let expr = Let [] x
    parse' "@{} x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "@{} x"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, IntT, [])
    eval ops (Let env expr') `shouldBe` Int 1

  it "☯ Core.Let 1" $ do
    let env = [("x", Num 3.14)]
    let expr = Let [("x", Int 1)] x
    parse' "@{x = 1} x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "@{x = 1} x"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, IntT, [])
    eval ops expr' `shouldBe` Int 1

  it "☯ Core.Let 2" $ do
    let env = [("x", Num 3.14), ("y", Num 2.71)]
    let expr = Let [("x", Int 1), ("y", Int 2)] y
    parse' "@{x = 1, y = 2} y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "@{x = 1, y = 2} y"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, IntT, [])
    eval ops expr' `shouldBe` Int 2

  it "☯ Core.Meta.Location" $ do
    let env = [("x", Int 1)]
    let expr = Meta (Loc $ Location "file" (Range (Pos 1 2) (Pos 3 4)))
    parse' "![file:1:2,3:4] x" `shouldBe` Right (expr x, "")
    format 80 (expr x) `shouldBe` "![file:1:2,3:4] x"
    let ((expr', typ), s) = infer ops env (expr x)
    (expr', typ, s) `shouldBe` (expr x, IntT, [])
    eval ops (Let env expr') `shouldBe` expr (Int 1)

  it "☯ Core.Meta.Comments 1" $ do
    let env = [("x", Int 1)]
    let expr = Meta (Comments ["c1"])
    parse' "# c1\nx " `shouldBe` Right (expr x, "")
    format 80 (expr x) `shouldBe` "# c1\nx"
    let ((expr', typ), s) = infer ops env (expr x)
    (expr', typ, s) `shouldBe` (expr x, IntT, [])
    eval ops (Let env expr') `shouldBe` expr (Int 1)

  it "☯ Core.Meta.Comments 2" $ do
    let env = [("x", Int 1)]
    let expr = Meta (Comments ["c1", "c2"])
    parse' "# c1\n# c2\nx " `shouldBe` Right (expr x, "")
    format 80 (expr x) `shouldBe` "# c1\n# c2\nx"
    let ((expr', typ), s) = infer ops env (expr x)
    (expr', typ, s) `shouldBe` (expr x, IntT, [])
    eval ops (Let env expr') `shouldBe` expr (Int 1)

  -- TODO: multi-line comments

  it "☯ Core.Meta.TrailingComment" $ do
    let env = [("x", Int 1)]
    let expr = Meta (TrailingComment "c")
    parse' "x # c" `shouldBe` Right (expr x, "")
    format 80 (expr x) `shouldBe` "x  # c\n"
    let ((expr', typ), s) = infer ops env (expr x)
    (expr', typ, s) `shouldBe` (expr x, IntT, [])
    eval ops (Let env expr') `shouldBe` expr (Int 1)

  it "☯ Core.Err" $ do
    let env = [("x", Int 1)]
    let expr = Err (customError x)
    parse' "!error x" `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "!error x"
    let ((expr', typ), s) = infer ops env expr
    (expr', typ, s) `shouldBe` (expr, Any, [])
    eval ops (Let env expr') `shouldBe` expr

  it "☯ Core.run.App" $ do
    let env = [("x", Int 42), ("y", Num 3.14), ("a", Any)]
    run env "_ x" `shouldBe` Right "_"
    run env "() x" `shouldBe` Right "!cannot-apply((), 42)"
    run env "^Int x" `shouldBe` Right "!cannot-apply(^Int, 42)"
    run env "^Num x" `shouldBe` Right "!cannot-apply(^Num, 42)"
    run env "1 x" `shouldBe` Right "!cannot-apply(1, 42)"
    run env "1.1 x" `shouldBe` Right "!cannot-apply(1.1, 42)"
    run env "A x" `shouldBe` Right "!cannot-apply(A, 42)"
    run env "y x" `shouldBe` Right "!cannot-apply(3.14, 42)"
    run env "a x" `shouldBe` Right "_"
    run env "z x" `shouldBe` Right "z 42"
    run env "(1, 2) x" `shouldBe` Right "!cannot-apply((1, 2), 42)"
    run env "(a | 2) x" `shouldBe` Right "_"
    run env "(1 | a) x" `shouldBe` Right "_"
    run env "(1 | 2) x" `shouldBe` Right "!cannot-apply(2, 42)"
    run env "(1 : ^Int) x" `shouldBe` Right "!cannot-apply(1, 42)"
    run env "(a : ^Int) x" `shouldBe` Right "_"
    run env "(@y. y) x" `shouldBe` Right "y 42"
    run env "(&y. a) x" `shouldBe` Right "_"
    run env "(_ -> Ok) x" `shouldBe` Right "Ok"
    run env "(() -> Ok) x" `shouldBe` Right "!unhandled-case(42)"
    run env "(() -> Ok) ()" `shouldBe` Right "Ok"
    run env "(^Int -> Ok) x" `shouldBe` Right "!unhandled-case(42)"
    run env "(^Int -> Ok) ^Int" `shouldBe` Right "Ok"
    run env "(^Num -> Ok) x" `shouldBe` Right "!unhandled-case(42)"
    run env "(^Num -> Ok) ^Num" `shouldBe` Right "Ok"
    run env "(1 -> Ok) x" `shouldBe` Right "!unhandled-case(42)"
    run env "(42 -> Ok) x" `shouldBe` Right "Ok"
    run env "(3.14 -> Ok) x" `shouldBe` Right "!unhandled-case(42)"
    run env "(3.14 -> Ok) 3.14" `shouldBe` Right "Ok"
    run env "(A -> Ok) x" `shouldBe` Right "!unhandled-case(42)"
    run env "(A -> Ok) A" `shouldBe` Right "Ok"
    run env "(y -> y) x" `shouldBe` Right "!unhandled-case(42)"
    run env "(y -> y) 3.14" `shouldBe` Right "3.14"
    run env "(@y. y -> y) x" `shouldBe` Right "42"
    run env "(&y. x -> y) x" `shouldBe` Right "&y. 42 -> y"
    run env "((A, 42) -> Ok) (B, x)" `shouldBe` Right "!unhandled-case((B, 42))"
    run env "((A, 42) -> Ok) (A, x)" `shouldBe` Right "Ok"
    run env "((A | 42) -> Ok) B" `shouldBe` Right "!unhandled-case(B)"
    run env "((A | 42) -> Ok) A" `shouldBe` Right "Ok"
    run env "((A | 42) -> Ok) x" `shouldBe` Right "Ok"
    run env "((_ : ^Int) -> Ok) (x : ^Int)" `shouldBe` Right "Ok"
    run env "((_ : ^Num) -> Ok) (x : ^Int)" `shouldBe` Right "!unhandled-case(42 : ^Int)"
    run env "((_ : ^Num) -> Ok) (x : _)" `shouldBe` Right "Ok"
    run env "((_ : ^Num) -> Ok) (x : !error(_))" `shouldBe` Right "Ok"
    run env "((_ : ^Num) -> Ok) x" `shouldBe` Right "!unhandled-case(42)"
  -- Fun Expr Expr
  -- App Expr Expr
  -- Call String [Expr]
  -- Let [(String, Expr)] Expr
  -- Meta Metadata Expr
  -- Err (Error Expr)

  -- it "☯ format" $ do
  --   format err `shouldBe` "!RuntimeError"
  --   format IntT `shouldBe` "!IntT"
  --   format NumT `shouldBe` "!NumT"
  --   format (Int 1) `shouldBe` "1"
  --   format (Num 1.1) `shouldBe` "1.1"
  --   -- format (Typ "T") `shouldBe` "$T"
  --   -- format (Ctr "T" "A") `shouldBe` "$T.A"
  --   format (Var "x") `shouldBe` "x"

  -- format (pow (pow x y) z) `shouldBe` "(x^y)^z"
  -- format (pow x (pow y z)) `shouldBe` "x^y^z"
  -- format (pow (App x y) z) `shouldBe` "(x y)^z"
  -- format (pow x (App y z)) `shouldBe` "x^(y z)"

  -- format (App x (pow y z)) `shouldBe` "x y^z"
  -- format (App (pow x y) z) `shouldBe` "x^y z"
  -- format (App (App x y) z) `shouldBe` "x y z"
  -- format (App x (App y z)) `shouldBe` "x (y z)"
  -- format (App (mul x y) z) `shouldBe` "(x * y) z"
  -- format (App x (mul y z)) `shouldBe` "x (y * z)"

  -- format (isInt (App x y)) `shouldBe` "@isInt (x y)"
  -- format (isInt (pow x y)) `shouldBe` "@isInt x^y"
  -- format (pow (isInt x) y) `shouldBe` "(@isInt x)^y"
  -- format (App (isInt x) y) `shouldBe` "@isInt x y"
  -- format (App x (isInt y)) `shouldBe` "x (@isInt y)"

  -- format (isNum (App x y)) `shouldBe` "@isNum (x y)"
  -- format (isNum (pow x y)) `shouldBe` "@isNum x^y"
  -- format (pow (isNum x) y) `shouldBe` "(@isNum x)^y"
  -- format (App (isNum x) y) `shouldBe` "@isNum x y"
  -- format (App x (isNum y)) `shouldBe` "x (@isNum y)"

  -- format (int2num (App x y)) `shouldBe` "$i2n (x y)"
  -- format (int2num (pow x y)) `shouldBe` "$i2n x^y"
  -- format (pow (int2num x) y) `shouldBe` "($i2n x)^y"
  -- format (App (int2num x) y) `shouldBe` "$i2n x y"
  -- format (App x (int2num y)) `shouldBe` "x ($i2n y)"

  -- format (mul x (App y z)) `shouldBe` "x * y z"
  -- format (mul (App x y) z) `shouldBe` "x y * z"
  -- format (mul (mul x y) z) `shouldBe` "x * y * z"
  -- format (mul x (mul y z)) `shouldBe` "x * (y * z)"
  -- format (mul (add x y) z) `shouldBe` "(x + y) * z"
  -- format (mul x (add y z)) `shouldBe` "x * (y + z)"

  -- format (add x (mul y z)) `shouldBe` "x + y * z"
  -- format (add (mul x y) z) `shouldBe` "x * y + z"
  -- format (add (add x y) z) `shouldBe` "x + y + z"
  -- format (add x (add y z)) `shouldBe` "x + (y + z)"
  -- format (sub (add x y) z) `shouldBe` "x + y - z"
  -- format (sub x (add y z)) `shouldBe` "x - (y + z)"
  -- format (sub (sub x y) z) `shouldBe` "x - y - z"
  -- format (sub x (sub y z)) `shouldBe` "x - (y - z)"
  -- format (sub (fun [x] y) z) `shouldBe` "(x -> y) - z"
  -- format (sub x (fun [y] z)) `shouldBe` "x - (y -> z)"

  -- format (fun [x] (add y z)) `shouldBe` "x -> y + z"
  -- format (fun [add x y] z) `shouldBe` "x + y -> z"
  -- format (fun [fun [x] y] z) `shouldBe` "(x -> y) -> z"
  -- format (fun [x] (fun [y] z)) `shouldBe` "x -> y -> z"
  -- format (fun [x] (lt y z)) `shouldBe` "x -> (y < z)"
  -- format (fun [lt x y] z) `shouldBe` "(x < y) -> z"

  -- format (lt x (fun [y] z)) `shouldBe` "x < y -> z"
  -- format (lt (fun [x] y) z) `shouldBe` "x -> y < z"
  -- format (lt (lt x y) z) `shouldBe` "(x < y) < z"
  -- format (lt x (lt y z)) `shouldBe` "x < y < z"
  -- format (lt (eq x y) z) `shouldBe` "(x == y) < z"
  -- format (lt x (eq y z)) `shouldBe` "x < (y == z)"

  -- format (eq x (lt y z)) `shouldBe` "x == y < z"
  -- format (eq (lt x y) z) `shouldBe` "x < y == z"
  -- format (eq (eq x y) z) `shouldBe` "x == y == z"
  -- format (eq x (eq y z)) `shouldBe` "x == (y == z)"
  -- format (eq (Ann x y) z) `shouldBe` "(x : y) == z"
  -- format (eq x (Ann y z)) `shouldBe` "x == (y : z)"

  -- format (Ann x (eq y z)) `shouldBe` "x : y == z"
  -- format (Ann (eq x y) z) `shouldBe` "x == y : z"
  -- format (Ann x (Ann y z)) `shouldBe` "x : y : z"
  -- format (Ann (Ann x y) z) `shouldBe` "(x : y) : z"
  -- format (Ann (Or x y) z) `shouldBe` "(x | y) : z"
  -- format (Ann x (Or y z)) `shouldBe` "x : (y | z)"

  -- format (For "x" (Ann y z)) `shouldBe` "@x. (y : z)"
  -- format (For "x" (eq y z)) `shouldBe` "@x. y == z"
  -- format (Ann (For "x" y) z) `shouldBe` "(@x. y) : z"
  -- format (Or (For "x" y) z) `shouldBe` "@x. y | z"
  -- format (Or x (For "y" z)) `shouldBe` "x | @y. z"

  -- format (Or x (Ann y z)) `shouldBe` "x | y : z"
  -- format (Or (Ann x y) z) `shouldBe` "x : y | z"
  -- format (Or x (Or y z)) `shouldBe` "x | y | z"
  -- format (Or (Or x y) z) `shouldBe` "(x | y) | z"

  -- format (If x (Ann y z)) `shouldBe` "x ? y : z"
  -- format (If (Ann x y) z) `shouldBe` "x : y ? z"
  -- format (If x (If y z)) `shouldBe` "x ? y ? z"
  -- format (If (If x y) z) `shouldBe` "(x ? y) ? z"

  it "☯ syntax sugar" $ do
    -- let' [] x `shouldBe` x
    -- let' [(y', z)] x `shouldBe` App (Fun y' x) z

    -- lam [] x `shouldBe` x
    -- lam [y'] x `shouldBe` Fun y' x

    and' [] `shouldBe` Unit
    and' [x] `shouldBe` x
    and' [x, y] `shouldBe` x `And` y

    tag "A" [] `shouldBe` Tag "A"
    tag "A" [x] `shouldBe` Tag "A" `And` x
    tag "A" [x, y] `shouldBe` Tag "A" `And` (x `And` y)

    app x [] `shouldBe` App x Unit
    app x [y, z] `shouldBe` App x (And y z)

  it "☯ reduce" $ do
    let env =
          [ ("a", IntT),
            ("x", Int 42),
            ("y", Num 3.14),
            ("z", Var "z"),
            ("f", For "y" (Fun y y))
          ]

    let reduce' x = reduce ops (Let env x)
    reduce' IntT `shouldBe` IntT
    reduce' NumT `shouldBe` NumT
    reduce' (Int 1) `shouldBe` Int 1
    reduce' (Num 1.1) `shouldBe` Num 1.1
    reduce' (Tag "x") `shouldBe` Tag "x"
    reduce' (Var "x") `shouldBe` Int 42
    reduce' (Var "y") `shouldBe` Num 3.14
    reduce' (Var "z") `shouldBe` Var "z"
    reduce' (Var "w") `shouldBe` Var "w"
    -- reduce' (For "x" x) `shouldBe` For "x" x
    -- reduce' (For "x" y) `shouldBe` For "x" (Num 3.14)
    -- reduce' (Fix "x" x) `shouldBe` Fix "x" x
    -- reduce' (Fix "x" y) `shouldBe` Fix "x" (Num 3.14)
    reduce' (Ann x y) `shouldBe` Ann (Let env x) (Let env y)
    reduce' (And x y) `shouldBe` And (Let env x) (Let env y)
    reduce' (Or x y) `shouldBe` Or (Let env x) (Let env y)
    reduce' (Fun x y) `shouldBe` Fun (Let env x) (Let env y)
    reduce' (App IntT y) `shouldBe` Err (cannotApply IntT (Num 3.14))
    reduce' (App NumT y) `shouldBe` Err (cannotApply NumT (Num 3.14))
    -- reduce' (App (Int 1) y) `shouldBe` err
    -- reduce' (App (Num 1.1) y) `shouldBe` err
    -- reduce' (App (Tag "x") y) `shouldBe` err
    -- reduce' (App (Var "x") y) `shouldBe` err
    reduce' (App (Var "z") y) `shouldBe` App z (Num 3.14)
    reduce' (App (App (Var "z") y) x) `shouldBe` App (App z (Num 3.14)) (Int 42)
    -- reduce' (App (For "x" x) y) `shouldBe` App x (Num 3.14)
    -- reduce' (App (Fix "x" x) y) `shouldBe` App (Fix "x" x) x
    reduce' (App (Fun IntT NumT) IntT) `shouldBe` NumT
    -- reduce' (App (Fun NumT IntT) IntT) `shouldBe` err
    reduce' (App (Fun NumT IntT) NumT) `shouldBe` IntT
    reduce' (App (Fun (Int 42) z) (Int 42)) `shouldBe` z
    -- reduce' (App (Fun (Int 42) z) (Int 0)) `shouldBe` err
    reduce' (App (Fun (Num 3.14) z) (Num 3.14)) `shouldBe` z
    -- reduce' (App (Fun (Num 3.14) z) (Num 0.0)) `shouldBe` err
    reduce' (App (Fun (Tag "A") z) (Tag "A")) `shouldBe` z
    -- reduce' (App (Fun (Tag "A") z) (Tag "B")) `shouldBe` err
    reduce' (App (Fun (Var "x") z) (Int 42)) `shouldBe` z
    -- reduce' (App (Fun (Var "x") z) (Int 0)) `shouldBe` err
    reduce' (App (Fun (Var "x") z) x) `shouldBe` z
    -- reduce' (App (Fun (Var "x") z) y) `shouldBe` err
    -- TODO: reduce App Fun App
    reduce' (App (Fun (And IntT NumT) z) (And IntT NumT)) `shouldBe` z
    -- reduce' (App (Fun (And IntT NumT) z) (And IntT IntT)) `shouldBe` err
    -- reduce' (App (Fun (And IntT NumT) z) (And NumT NumT)) `shouldBe` err
    reduce' (App (Fun (Or IntT NumT) z) IntT) `shouldBe` z
    reduce' (App (Fun (Or IntT NumT) z) NumT) `shouldBe` z
    -- reduce' (App (Fun (Or IntT IntT) z) x) `shouldBe` err
    reduce' (App (Fun (Ann x err) z) x) `shouldBe` z
    -- reduce' (App (Fun (Ann x err) z) y) `shouldBe` err
    reduce' (App (Fun (Call "f" []) z) (Call "f" [])) `shouldBe` z
    reduce' (App (Fun err IntT) err) `shouldBe` IntT
    reduce' (App (For "y" (Fun y y)) x) `shouldBe` Int 42
    reduce' (App (Var "f") x) `shouldBe` Int 42
    reduce' (App (Or (Var "f") err) x) `shouldBe` Int 42
    reduce' (App (Or err (Var "f")) x) `shouldBe` Int 42
    -- reduce' (App (Or err err) x) `shouldBe` err
    reduce' (Call "f" [x, y]) `shouldBe` Call "f" [Let env x, Let env y]
    reduce' err `shouldBe` err

  it "☯ eval" $ do
    let env =
          [ ("x", Int 42),
            ("y", Num 3.14),
            ("f", For "z" (Fun z z))
          ]

    let eval' x = eval ops (Let env x)
    eval' (Fun x y) `shouldBe` Fun (Int 42) (Num 3.14)
    eval' (And x y) `shouldBe` And (Int 42) (Num 3.14)
    eval' (Or x y) `shouldBe` Or (Int 42) (Num 3.14)
    eval' (Call "f" [x, y]) `shouldBe` Call "f" [Int 42, Num 3.14]
    eval' (Call "int_add" [i1, i1]) `shouldBe` i2
    -- eval' (For "x" (And x y)) `shouldBe` For "x" (And x (Num 3.14))
    -- eval' (Fix "x" (And x y)) `shouldBe` Fix "x" (And x (Num 3.14))
    eval' (App z (And x y)) `shouldBe` App z (And (Int 42) (Num 3.14))

  it "☯ eval eq" $ do
    let eq a b = app (For "x" (fun [x, x] i1) `Or` fun [Any, Any] i0) [a, b]
    eval ops (eq i2 i2) `shouldBe` i1
    eval ops (eq i1 i2) `shouldBe` i0

  it "☯ eval factorial" $ do
    let env = [("f", factorial "f")]
    let eval' x = eval ops (Let env x)

    -- eval' (Var "f") `shouldBe` factorial "f"
    -- eval' (App f x) `shouldBe` App (factorial "f") x
    eval' (App f (Int 0)) `shouldBe` Int 1
    eval' (App f (Int 1)) `shouldBe` Int 1
    eval' (App f (Int 2)) `shouldBe` Int 2
    eval' (App f (Int 3)) `shouldBe` Int 6
    eval' (App f (Int 4)) `shouldBe` Int 24
    eval' (App f (Int 5)) `shouldBe` Int 120

  -- it "☯ eval fibonacci" $ do
  --   let fib f = Fix f (case0 `Or` case1 `Or` caseN f)
  --         where
  --           case0 = Fun i0 i0
  --           case1 = Fun i1 i1
  --           caseN f = For "x" (Fun x (App (Var f) (x `sub` i1) `add` App (Var f) (x `sub` i2)))
  --           add x y = Call "+" [x, y]
  --           sub x y = Call "-" [x, y]
  --   let env = [("f", fib "f")]
  --   let eval' x = eval ops (Let env x)
  --   eval' (App f (Int 0)) `shouldBe` Int 0
  --   eval' (App f (Int 1)) `shouldBe` Int 1
  --   eval' (App f (Int 2)) `shouldBe` Int 1
  --   eval' (App f (Int 3)) `shouldBe` Int 2
  --   eval' (App f (Int 4)) `shouldBe` Int 3
  --   eval' (App f (Int 5)) `shouldBe` Int 5

  -- it "☯ eval type alias" $ do
  --   let env = [("T0", Fun (Int 0) NumT), ("T1", lam [x] (Fun (Int 1) x))]
  --   let eval' x = eval ops (Let env x)
  --   eval' (App (Tag "A") (Tag "A")) `shouldBe` Tag "A"
  --   eval' (App (And (Tag "A") IntT) (And (Tag "A") IntT)) `shouldBe` And (Tag "A") IntT
  --   eval' (App (Tag "T0") (Int 0)) `shouldBe` NumT
  --   eval' (App (And (Tag "T1") NumT) (Int 1)) `shouldBe` NumT

  it "☯ eval type safety" $ do
    let eval' = eval ops
    eval' (App (For "x" $ Fun x x) i1) `shouldBe` i1
    eval' (App (For "x" $ Fun x x) (Ann i1 IntT)) `shouldBe` Ann i1 IntT
    eval' (App (For "x" $ Fun (Ann x IntT) x) i1) `shouldBe` i1
    eval' (App (For "x" $ Fun (Ann x IntT) x) (Ann i1 IntT)) `shouldBe` i1
    eval' (App (For "x" $ Fun (Ann x NumT) x) (Ann i1 IntT)) `shouldBe` err
    let a' = Fun (Ann err err) (Tag "Ok") `Or` Fun (Ann x a) x
    let b' = Ann (App Unit (Ann i1 IntT)) Unit
    eval' (for ["x", "a"] $ App a' b') `shouldBe` err

  it "☯ eval alpha equivalence" $ do
    let eval' = eval ops
    let a' = for ["x", "a"] (Fun (Ann x a) x)
    let b' = for ["y", "b"] (Fun (Ann y b) y)
    eval' (App (Fun a' i1) b') `shouldBe` i1

  it "☯ -- unify" $ do
    True `shouldBe` True

  it "☯ infer const" $ do
    infer [] [] IntT `shouldBe` ((IntT, IntT), [])
    infer [] [] NumT `shouldBe` ((NumT, NumT), [])
    infer [] [] (Int 1) `shouldBe` ((Int 1, IntT), [])
    infer [] [] (Num 1.1) `shouldBe` ((Num 1.1, NumT), [])
    infer [] [] err `shouldBe` ((err, Any), [])

  it "☯ infer Var" $ do
    let (a1, yT) = (Var "a1", Var "yT")
    let env = [("x", i1), ("y", y), ("b", Ann b IntT), ("a", b), ("c", Ann c (for ["a"] a))]
    infer [] env (Var "x") `shouldBe` ((x, IntT), [])
    infer [] env (Var "y") `shouldBe` ((y, yT), [("yT", yT), ("y", Ann y yT)])
    infer [] env (Var "z") `shouldBe` ((z, Err $ TypeError $ UndefinedVar "z"), [])
    infer [] env (Var "a") `shouldBe` ((a, IntT), [])
    infer [] env (Var "c") `shouldBe` ((c, a1), [("a1", a1)])

  it "☯ infer Ann" $ do
    let env = []
    infer [] env (Ann i1 IntT) `shouldBe` ((i1, IntT), [])
    infer [] env (Ann i1 NumT) `shouldBe` ((i1, Err $ typeMismatch IntT NumT), [])
    infer [] env (Ann i1 (For "a" a)) `shouldBe` ((i1, IntT), [("a", IntT)])

  it "☯ infer Ann Tag" $ do
    let env = [("T", Tag "A" `Or` Tag "B")]
    -- infer [] env (Tag "T" []) `shouldBe` Right (Tag "A" [] `Or` Tag "B" [], [])
    -- infer [] env (Ann (Tag "A" []) (Tag "A" [])) `shouldBe` Right (Tag "A" [], [])
    -- infer [] env (Ann (Tag "A") (Tag "T")) `shouldBe` Right (Tag "T", [])
    -- infer [] env (Ann (Tag "B []) (Tag "T" [])) `shouldBe` Right (Tag "T" [], [])
    -- infer [] env (Ann (Tag "C" []) (Tag "T" [])) `shouldBe` Left (TypeMismatch (Ann (Tag "C" []) (Tag "T" [])) (Tag "A" [] `Or` Tag "B" []))
    True `shouldBe` True

  it "☯ infer Fun" $ do
    let (t, xT, _T) = (Var "t", Var "xT", Var "_T")
    let env =
          [ ("x", Ann x a),
            ("y", Int 1),
            ("a", a)
          ]
    infer [] env (Fun x x) `shouldBe` ((Fun (Ann x a) x, Fun a a), [])

  it "☯ infer Fun" $ do
    let env = [("a", Ann a IntT), ("b", Ann b NumT)]
    infer [] env (Fun a b) `shouldBe` ((Fun (Ann a IntT) b, Fun IntT NumT), [])

  it "☯ infer App" $ do
    let env =
          [ ("x", i1),
            ("y", y),
            ("f", Ann f (Fun IntT NumT))
          ]
    infer [] env (App f x) `shouldBe` ((App f (Ann x IntT), NumT), [])
    infer [] env (App (Fun y y) x) `shouldBe` ((App (Fun (Ann y IntT) y) (Ann x IntT), IntT), [("yT", IntT), ("y", Ann y IntT)])
    infer [] env (App y x) `shouldBe` ((App y (Ann x IntT), Var "yT$2"), [("yT$1", IntT), ("yT", Fun IntT (Var "yT$2")), ("yT$2", Var "yT$2"), ("y", Ann y (Fun IntT (Var "yT$2")))])

  it "☯ infer Or" $ do
    let env = [("x", Int 42), ("y", Num 3.14)]
    infer [] env (Or x x) `shouldBe` ((Or x x, Or IntT IntT), [])
    infer [] env (Or x y) `shouldBe` ((Or x y, Or IntT NumT), [])

  it "☯ infer For" $ do
    let xT = Var "xT"
    infer [] [] (For "x" x) `shouldBe` ((For "x" x, xT), [("xT", xT), ("x", Ann x xT)])

  it "☯ infer Op2" $ do
    True `shouldBe` True

  it "☯ infer factorial" $ do
    let env = [("f", Ann (factorial "f") (Fun IntT IntT))]
    let infer' = fst . infer ops env
    infer' (Var "f") `shouldBe` (f, Fun IntT IntT)
    infer' (Ann f (Fun IntT IntT)) `shouldBe` (f, Fun IntT IntT)

  it "☯ infer Bool" $ do
    let (bool, true, false) = (Tag "Bool", Tag "True", Tag "False")
    let env = [("Bool", Fun true bool `Or` Fun false bool)]

    eval ops (Let env (App (Fun bool Unit) true)) `shouldBe` Unit
    eval ops (Let env (App (Fun bool Unit) (Tag "X"))) `shouldBe` err
    eval ops (Let env (App (Fun bool Unit) bool)) `shouldBe` Unit

    let infer' = infer ops env
    infer' (Tag "True") `shouldBe` ((true, true), [])
    infer' (Ann true bool) `shouldBe` ((true, bool), env)
    infer' (Ann false (Tag "X")) `shouldBe` ((false, Err $ typeMismatch false (Tag "X")), [])
    infer' (Ann (Tag "X") bool) `shouldBe` ((Tag "X", Err $ typeMismatch err bool), env)

  -- it "☯ infer Maybe" $ do
  --   let (maybe, just, nothing) = (App (Tag "Maybe"), \a -> tag "Just" [a], Tag "Nothing")
  --   let env = [("Maybe", lam [PVar "a"] (nothing `Or` just a))]

  --   let infer' a = fmap fst (infer env a)
  --   infer' (Tag "Nothing") `shouldBe` Right (Tag "Nothing")
  --   infer' (Tag "Just") `shouldBe` Right (Tag "Just")
  --   infer' (just i1) `shouldBe` Right (just (Or (Int 1) IntT))
  --   infer' (Ann nothing (maybe IntT)) `shouldBe` Right (maybe IntT)
  --   infer' (Ann (just i1) (maybe IntT)) `shouldBe` Right (maybe IntT)
  --   infer' (Ann (just i1) (maybe NumT)) `shouldBe` Left (TypeMismatch (just (Int 1 `Or` IntT)) (nothing `Or` just NumT))
  --   infer' (Ann (Tag "X") (maybe IntT)) `shouldBe` Left (TypeMismatch (Ann (Tag "X") (maybe IntT)) (nothing `Or` just IntT))

  it "☯ infer Vec" $ do
    let (n, a) = (Var "n", Var "a")
    let nil = Tag "Nil"
    let cons x xs = tag "Cons" [x, xs]
    let vec n a = tag "Vec" [n, a]
    let vecDef a =
          or'
            [ For "n" (Fun (cons a (vec n a)) (vec (n `add` i1) a)),
              Fun nil (vec i0 a)
            ]
    let env = [("Vec", lam [And n a] (vecDef a))]

    eval ops (Let env (App (Fun (vec i0 NumT) Unit) nil)) `shouldBe` Unit
    eval ops (Let env (App (Fun (vec i0 NumT) Unit) (Tag "X"))) `shouldBe` err
    eval ops (Let env (App (Fun (vec i0 NumT) Unit) (vec i0 NumT))) `shouldBe` Unit

    let infer' = infer ops env
    infer' (Tag "Nil") `shouldBe` ((Tag "Nil", Tag "Nil"), [])
    infer' (cons (Num 1.1) nil) `shouldBe` ((cons (Num 1.1) nil, cons NumT nil), [])
    infer' (Ann nil (vec i0 NumT)) `shouldBe` ((nil, vec i0 NumT), env)
    infer' (Ann nil (vec i1 NumT)) `shouldBe` ((nil, vec (Err $ typeMismatch i0 i1) NumT), env)
    infer' (Ann (cons (Num 1.1) nil) (vec i1 NumT)) `shouldBe` ((cons (Num 1.1) nil, vec i1 NumT), env)
    infer' (Ann (cons (Num 1.1) (cons (Num 2.2) nil)) (vec i0 NumT)) `shouldBe` ((cons (Num 1.1) (cons (Num 2.2) nil), vec (Err $ typeMismatch i2 i0) NumT), env)

-- it "☯ checkTypes" $ do
--   let env =
--         [ ("f", Ann f (Fun IntT NumT)),
--           ("x", Ann (Int 42) NumT),
--           ("y", App f (Int 42)),
--           ("z", App f (Tag "A"))
--         ]
--   checkTypes env `shouldBe` [TypeMismatch (Int 42 `Or` IntT) NumT, TypeMismatch (Tag "A") IntT]

-- it "☯ rename simple" $ do
--   let env = [("A", x), ("B", y)]
--   let f t xs x = case map toLower x of
--         y | y `elem` xs -> f t xs (y ++ "_")
--         y -> y
--   rename f [] env env `shouldBe` [("a", x), ("b", y)]

-- it "☯ rename name clashes" $ do
--   let env = [("a_", x), ("A", y), ("a", z)]
--   let f t xs x = case map toLower x of
--         y | y `elem` xs -> f t xs (y ++ "_")
--         y -> y
--   rename f [] env env `shouldBe` [("a_", x), ("a__", y), ("a", z)]

-- it "☯ load Module" $ do
--   let mod =
--         Module
--           { values = [("x", Int 1), ("y", Int 2)],
--             types = [],
--             tests = []
--           }
--   load "examples/core-package/core-module" `shouldReturn` mod
