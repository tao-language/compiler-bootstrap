module CoreTests where

import Core
import Data.Bifunctor (Bifunctor (first))
import Data.Char (toLower)
import Error
import Location
import Parser (State (..))
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯️ Core language ☯️==--" $ do
  let (i0, i1, i2) = (Int 0, Int 1, Int 2)
  let (n0, n1, n2) = (Num 0.0, Num 1.1, Num 2.2)
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (f, g, h) = (Var "f", Var "g", Var "h")
  let loc0= Location "null" (Range (Pos 0 0) (Pos 0 0))
  let loc = Loc $ Location "file" (Range (Pos 1 2) (Pos 3 4))

  let add a b = Call "int_add" (And a b)
  let sub a b = Call "int_sub" (And a b)
  let mul a b = Call "int_mul" (And a b)
  let env = []
  let ops =
        [ ( "null",
            \eval a -> case (dropTypes . eval) a of
              Unit -> Just (tag' "Null")
              _ -> Nothing
          ),
          ( "int_neg",
            \eval a -> case (dropTypes . eval) a of
              Int x -> Just (Int (-x))
              _ -> Nothing
          ),
          ( "int_add",
            \eval a -> case (dropTypes . eval) a of
              And (Int x) (Int y) -> Just (Int (x + y))
              _ -> Nothing
          ),
          ( "int_sub",
            \eval a -> case (dropTypes . eval) a of
              And (Int x) (Int y) -> Just (Int (x - y))
              _ -> Nothing
          ),
          ( "int_mul",
            \eval a -> case (dropTypes . eval) a of
              And (Int x) (Int y) -> Just (Int (x * y))
              _ -> Nothing
          )
        ]

  let factorial f = Fix f (case0 `Or` caseN f)
        where
          case0 = Fun i0 i1
          caseN f = For "x" (Fun x (x `mul` App (Var f) (x `sub` i1)))

  let filename = "<CoreTests>"
  let parse' :: String -> Either (String, String) (Expr, String)
      parse' text = case parse 0 filename text of
        Right (a, s) -> Right (a, s.remaining)
        Left s -> Left (s.expected, s.remaining)
  let parseWith :: [(String, String)] -> String -> Either String (Env, Expr)
      parseWith envSrc src = do
        let p src = case parse' src of
              Right (a, "") -> Right a
              Right (_, rem) -> Left ("remaining: " ++ rem)
              Left (_, rem) -> Left ("syntax error: " ++ rem)
        env <- mapM (\(x, src) -> fmap (x,) (p src)) envSrc
        expr <- p src
        Right (env, expr)
  let run envSrc src = do
        (env, a) <- parseWith envSrc src
        Right (show $ eval ops (Let env a))

  it "☯ Core.freeVars" $ do
    freeVars Any `shouldBe` []
    freeVars Unit `shouldBe` []
    freeVars IntT `shouldBe` []
    freeVars NumT `shouldBe` []
    freeVars (Int 1) `shouldBe` []
    freeVars (Num 1.1) `shouldBe` []
    freeVars (Var "x") `shouldBe` ["x"]
    freeVars (Tag "A" x) `shouldBe` ["x"]
    freeVars (And x y) `shouldBe` ["x", "y"]
    freeVars (Or x y) `shouldBe` ["x", "y"]
    freeVars (Ann x y) `shouldBe` ["x", "y"]
    freeVars (For "x" x) `shouldBe` []
    freeVars (For "x" y) `shouldBe` ["y"]
    freeVars (Fix "x" x) `shouldBe` []
    freeVars (Fix "x" y) `shouldBe` ["y"]
    freeVars (Fun x y) `shouldBe` ["x", "y"]
    freeVars (App x y) `shouldBe` ["x", "y"]
    freeVars (Call "f" x) `shouldBe` ["x"]
    freeVars (Let [] x) `shouldBe` ["x"]
    freeVars (Let [("y", z)] x) `shouldBe` ["x"]
    freeVars (Let [("x", y)] x) `shouldBe` ["y"]
    freeVars (Let [("x", y), ("y", z)] x) `shouldBe` ["z"]
    freeVars (Meta (Loc $ Location "file" (Range (Pos 1 2) (Pos 3 4))) x) `shouldBe` ["x"]
    freeVars Err `shouldBe` []

  it "☯ Core.freeTags" $ do
    let (a, b, c) = (tag' "A", tag' "B", tag' "C")
    freeTags Any `shouldBe` []
    freeTags Unit `shouldBe` []
    freeTags IntT `shouldBe` []
    freeTags NumT `shouldBe` []
    freeTags (Int 1) `shouldBe` []
    freeTags (Num 1.1) `shouldBe` []
    freeTags (Var "x") `shouldBe` []
    freeTags (Tag "A" x) `shouldBe` ["A"]
    freeTags (Tag "A" (Tag "B" x)) `shouldBe` ["A", "B"]
    freeTags (And a b) `shouldBe` ["A", "B"]
    freeTags (Or a b) `shouldBe` ["A", "B"]
    freeTags (Ann a b) `shouldBe` ["A", "B"]
    freeTags (For "A" a) `shouldBe` []
    freeTags (For "A" b) `shouldBe` ["B"]
    freeTags (Fix "A" a) `shouldBe` []
    freeTags (Fix "A" b) `shouldBe` ["B"]
    freeTags (Fun a b) `shouldBe` ["A", "B"]
    freeTags (App a b) `shouldBe` ["A", "B"]
    freeTags (Call "f" a) `shouldBe` ["A"]
    freeTags (Let [] a) `shouldBe` ["A"]
    freeTags (Let [("B", c)] a) `shouldBe` ["A"]
    freeTags (Let [("A", b)] a) `shouldBe` ["B"]
    freeTags (Let [("A", b)] x) `shouldBe` []
    freeTags (Let [("x", b)] x) `shouldBe` ["B"]
    freeTags (Let [("A", b), ("B", c)] a) `shouldBe` ["C"]
    freeTags (Meta (Loc $ Location "file" (Range (Pos 1 2) (Pos 3 4))) a) `shouldBe` ["A"]
    freeTags Err `shouldBe` []

  it "☯ Core.grammar.parser" $ do
    parse' "_ \n" `shouldBe` Right (Any, "\n")
    parse' "() \n" `shouldBe` Right (Unit, "\n")
    parse' "( \n ) \n" `shouldBe` Right (Unit, "\n")
    parse' "!Int \n" `shouldBe` Right (IntT, "\n")
    parse' "!Num \n" `shouldBe` Right (NumT, "\n")
    parse' "42 \n" `shouldBe` Right (Int 42, "\n")
    parse' "-42 \n" `shouldBe` Right (Int (-42), "\n")
    parse' "- 42 \n" `shouldBe` Right (Int (-42), "\n")
    parse' "3.14 \n" `shouldBe` Right (Num 3.14, "\n")
    parse' "-3.14 \n" `shouldBe` Right (Num (-3.14), "\n")
    parse' "- 3.14 \n" `shouldBe` Right (Num (-3.14), "\n")
    parse' "x \n" `shouldBe` Right (Var "x", "\n")
    parse' "A \n" `shouldBe` Right (tag "A" [], "\n")
    parse' "A() \n" `shouldBe` Right (tag "A" [], "\n")
    parse' "A(x) \n" `shouldBe` Right (tag "A" [x], "\n")
    parse' "A(x,y) \n" `shouldBe` Right (tag "A" [x, y], "\n")
    parse' "A(x, y, z) \n" `shouldBe` Right (tag "A" [x, y, z], "\n")
    parse' "A(\nx\n,\ny\n,\n) \n" `shouldBe` Right (tag "A" [x, y], "\n")
    parse' "@x.y \n" `shouldBe` Right (For "x" y, "\n")
    parse' "@ x .\ny \n" `shouldBe` Right (For "x" y, "\n")
    parse' "@ x y \nz \n" `shouldBe` Right (for ["x", "y"] z, "\n")
    parse' "@\nx. y \n" `shouldBe` Left ([], "@\nx. y \n")
    parse' "&x.y \n" `shouldBe` Right (Fix "x" y, "\n")
    parse' "& x .\ny \n" `shouldBe` Right (Fix "x" y, "\n")
    parse' "& x y \nz \n" `shouldBe` Right (fix ["x", "y"] z, "\n")
    parse' "&\nx. y \n" `shouldBe` Left ([], "&\nx. y \n")
    parse' "x:y \n" `shouldBe` Right (Ann x y, "\n")
    parse' "x :\ny \n" `shouldBe` Right (Ann x y, "\n")
    parse' "x\n:\ny \n" `shouldBe` Right (Ann x y, "\n")
    parse' "x : y : z \n" `shouldBe` Right (Ann x (Ann y z), "\n")
    parse' "(x) \n" `shouldBe` Right (x, "\n")
    parse' "(\nx\n) \n" `shouldBe` Right (x, "\n")
    parse' "(x,y) \n" `shouldBe` Right (and' [x, y], "\n")
    parse' "(x, y, z) \n" `shouldBe` Right (and' [x, y, z], "\n")
    parse' "(\nx\n,\ny\n,\n) \n" `shouldBe` Right (and' [x, y], "\n")
    parse' "x|y \n" `shouldBe` Right (Or x y, "\n")
    parse' "x | y | z \n" `shouldBe` Right (Or x (Or y z), "\n")
    parse' "x\n|\ny \n" `shouldBe` Right (Or x y, "\n")
    parse' "x->y \n" `shouldBe` Right (Fun x y, "\n")
    parse' "x -> y -> z \n" `shouldBe` Right (Fun x (Fun y z), "\n")
    parse' "x\n->\ny\n->\nz \n" `shouldBe` Right (Fun x (Fun y z), "\n")
    parse' "a() \n" `shouldBe` Right (app a [], "\n")
    parse' "a(x) \n" `shouldBe` Right (app a [x], "\n")
    parse' "a(x,y) \n" `shouldBe` Right (app a [x, y], "\n")
    parse' "a (x, y, z) \n" `shouldBe` Right (app a [x, y, z], "\n")
    parse' "a(\nx\n,\ny\n,\n) \n" `shouldBe` Right (app a [x, y], "\n")
    parse' "%f \n" `shouldBe` Right (call "f" [], "\n")
    parse' "%f() \n" `shouldBe` Right (call "f" [], "\n")
    parse' "%f(x) \n" `shouldBe` Right (call "f" [x], "\n")
    parse' "%f(x,y) \n" `shouldBe` Right (call "f" [x, y], "\n")
    parse' "%f (x, y, z) \n" `shouldBe` Right (call "f" [x, y, z], "\n")
    parse' "%f(\nx\n,\ny\n,\n) \n" `shouldBe` Right (call "f" [x, y], "\n")
    parse' "^{}y \n" `shouldBe` Right (Let [] y, "\n")
    parse' "^ { } y \n" `shouldBe` Right (Let [] y, "\n")
    parse' "^\n{\n}\ny \n" `shouldBe` Right (Let [] y, "\n")
    parse' "^x=a;y \n" `shouldBe` Right (Let [("x", a)] y, "\n")
    parse' "^ x = a ; ^ y = b ; z \n" `shouldBe` Right (Let [("x", a), ("y", b)] z, "\n")
    parse' "^\nx\n=\na \n^\ny\n=\nb \nz \n" `shouldBe` Right (Let [("x", a), ("y", b)] z, "\n")
  -- Meta (Metadata Expr) Expr
  -- Err

  it "☯ Core.grammar.layout" $ do
    format 0 "" Any `shouldBe` "_"
    format 0 "" Unit `shouldBe` "()"
    format 0 "" IntT `shouldBe` "!Int"
    format 0 "" NumT `shouldBe` "!Num"
    format 0 "" (Int 1) `shouldBe` "1"
    format 0 "" (Num 1.1) `shouldBe` "1.1"
    format 0 "" (Var "x") `shouldBe` "x"
    format 0 "" (tag "A" []) `shouldBe` "A"
    format 4 "" (tag "A" [x]) `shouldBe` "A(x)"
    format 3 "" (tag "A" [x]) `shouldBe` "A(\n  x,\n)"
    format 7 "" (tag "A" [x, y]) `shouldBe` "A(x, y)"
    format 6 "" (tag "A" [x, y]) `shouldBe` "A(\n  x,\n  y,\n)"
    format 4 "" (tag "A" [x, y]) `shouldBe` "A(\n  x,\n  y,\n)"
    format 5 "" (For "x" y) `shouldBe` "@x. y"
    format 4 "" (For "x" y) `shouldBe` "@x\ny"
    format 5 "" (Ann x y) `shouldBe` "x : y"
    format 4 "" (Ann x y) `shouldBe` "x\n: y"
    format 9 "" (Ann x (Ann y z)) `shouldBe` "x : y : z"
    format 8 "" (Ann x (Ann y z)) `shouldBe` "x : y\n: z"
    format 4 "" (Ann x (Ann y z)) `shouldBe` "x\n: y\n  : z"
    format 6 "" (and' [x, y]) `shouldBe` "(x, y)"
    format 5 "" (and' [x, y]) `shouldBe` "( x,\n  y,\n)"
    format 9 "" (and' [x, y, z]) `shouldBe` "(x, y, z)"
    format 8 "" (and' [x, y, z]) `shouldBe` "( x,\n  y,\n  z,\n)"
    format 5 "" (Or x y) `shouldBe` "x | y"
    format 4 "" (Or x y) `shouldBe` "| x\n| y"
    format 9 "" (Or x (Or y z)) `shouldBe` "x | y | z"
    -- format 8 "" (Or x (Or y z)) `shouldBe` "| x\n| y\n| z"
    -- format 4 "" (Or x (Or y z)) `shouldBe` "| x\n| y\n| z"
    format 6 "" (Fun x y) `shouldBe` "x -> y"
    format 5 "" (Fun x y) `shouldBe` "x ->\n  y"
    format 11 "" (Fun x (And y z)) `shouldBe` "x -> (y, z)"
    format 12 "" (Fun (And x y) (And y z)) `shouldBe` "(x, y) -> (y, z)"
    format 11 "" (Fun (And x y) (And y z)) `shouldBe` "(x, y) -> ( y,\n  z,\n)"
    format 9 "" (Fun (And x y) (And y z)) `shouldBe` "(x, y) ->\n  (y, z)"
    format 0 "" (app x []) `shouldBe` "x()"
    format 4 "" (app x [y]) `shouldBe` "x(y)"
    format 3 "" (app x [y]) `shouldBe` "x(\n  y,\n)"
    format 7 "" (app x [y, z]) `shouldBe` "x(y, z)"
    format 6 "" (app x [y, z]) `shouldBe` "x(\n  y,\n  z,\n)"
    format 0 "" (call "f" []) `shouldBe` "%f"
    format 5 "" (call "f" [x]) `shouldBe` "%f(x)"
    format 4 "" (call "f" [x]) `shouldBe` "%f(\n  x,\n)"
    format 8 "" (call "f" [x, y]) `shouldBe` "%f(x, y)"
    format 7 "" (call "f" [x, y]) `shouldBe` "%f(\n  x,\n  y,\n)"
    format 5 "" (Let [] x) `shouldBe` "^{}\nx"
    format 10 "" (Let [("x", a)] y) `shouldBe` "^x = a\ny"
    format 6 "" (Let [("x", a)] y) `shouldBe` "^x = a\ny"
    format 5 "" (Let [("x", a)] y) `shouldBe` "^x =\n  a\ny"
  -- Meta (Metadata Expr) Expr
  -- Err

  -- it "☯ Core.run.App" $ do
  --   let env = [("x", "42"), ("y", "3.14"), ("a", "a")]
  --   run env "_(x)" `shouldBe` Right "_"
  --   run env "()(x)" `shouldBe` Right "!cannot-apply<(), 42>(!Err)"
  --   run env "!Int(x)" `shouldBe` Right "!cannot-apply<!Int, 42>(!Err)"
  --   run env "!Num(x)" `shouldBe` Right "!cannot-apply<!Num, 42>(!Err)"
  --   run env "1(x)" `shouldBe` Right "!cannot-apply<1, 42>(!Err)"
  --   run env "1.1(x)" `shouldBe` Right "!cannot-apply<1.1, 42>(!Err)"
  --   run env "A(x)" `shouldBe` Right "!cannot-apply<A, 42>(!Err)"
  --   run env "y(x)" `shouldBe` Right "!cannot-apply<3.14, 42>(!Err)"
  --   run env "a(x)" `shouldBe` Right "a 42"
  --   run env "z(x)" `shouldBe` Right "z 42"
  --   run env "(1, 2)(x)" `shouldBe` Right "!cannot-apply<(1, 2), 42>(!Err)"
  --   run env "(a | 2)(x)" `shouldBe` Right "a 42 | !cannot-apply<2, 42>(!Err)"
  --   run env "(1 | a)(x)" `shouldBe` Right "a 42"
  --   run env "(1 | 2)(x)" `shouldBe` Right "!cannot-apply<2, 42>(!Err)"
  --   run env "(1 : !Int)(x)" `shouldBe` Right "!cannot-apply<1, 42>(!Err)"
  --   run env "(a : !Int)(x)" `shouldBe` Right "a 42"
  --   run env "(@y. y)(x)" `shouldBe` Right "y 42"
  --   run env "(&y. a)(x)" `shouldBe` Right "a 42"
  --   run env "(a -> a)(x)" `shouldBe` Right "42"
  --   run env "(a y) x" `shouldBe` Right "a 3.14 42"
  --   run env "%call() x" `shouldBe` Right "%call() 42"
  --   run env "@{f = f}(f) x" `shouldBe` Right "f 42"
  --   run env "^[file:1:2,3:4](a) x" `shouldBe` Right "^[file:1:2,3:4](a) 42"
  --   run env "!error(a) x" `shouldBe` Right "!cannot-apply<!Err, 42>(!Err)"

  -- it "☯ Core.run.match" $ do
  --   let env = [("x", "42"), ("y", "3.14"), ("a", "a")]
  --   run env "(_ -> Ok)(x)" `shouldBe` Right "Ok"
  --   run env "(() -> Ok)(x)" `shouldBe` Right "!unhandled-case<(), 42>(!error)"
  --   run env "(() -> Ok)()" `shouldBe` Right "Ok"
  --   run env "(!Int -> Ok)(x)" `shouldBe` Right "!unhandled-case<!Int, 42>(!error)"
  --   run env "(!Int -> Ok)(!Int)" `shouldBe` Right "Ok"
  --   run env "(!Num -> Ok)(x)" `shouldBe` Right "!unhandled-case<!Num, 42>(!error)"
  --   run env "(!Num -> Ok)(!Num)" `shouldBe` Right "Ok"
  --   run env "(1 -> Ok)(x)" `shouldBe` Right "!unhandled-case<1, 42>(!error)"
  --   run env "(42 -> Ok)(x)" `shouldBe` Right "Ok"
  --   run env "(3.14 -> Ok)(x)" `shouldBe` Right "!unhandled-case<3.14, 42>(!error)"
  --   run env "(3.14 -> Ok)(3.14)" `shouldBe` Right "Ok"
  --   run env "(A -> Ok)(x)" `shouldBe` Right "!unhandled-case<A, 42>(!error)"
  --   run env "(A -> Ok)(A)" `shouldBe` Right "Ok"
  --   run env "(a -> a)(x)" `shouldBe` Right "42"
  --   run env "(y -> y)(x)" `shouldBe` Right "!unhandled-case<3.14, 42>(!error)"
  --   run env "(y -> y)(3.14)" `shouldBe` Right "3.14"
  --   run env "(@y. y -> y)(x)" `shouldBe` Right "42"
  --   run env "(&y. x -> y)(x)" `shouldBe` Right "&y. 42 -> y"
  --   run env "((A, a) -> a)(B, x)" `shouldBe` Right "!unhandled-case<A, B>(!error)"
  --   run env "((A, a) -> a)(A, x)" `shouldBe` Right "42"
  --   run env "((A | x) -> x)(B)" `shouldBe` Right "!unhandled-case<A, B>(!error)"
  --   run env "((A | x) -> x)(A)" `shouldBe` Right "42"
  --   run env "((A | x) -> x)(x)" `shouldBe` Right "42"
  --   run env "((A | a) -> a)(x)" `shouldBe` Right "42"
  --   run env "((A | B) -> x)(A)" `shouldBe` Right "42"
  --   run env "((A | B) -> x)(B)" `shouldBe` Right "42"
  --   run env "((A | B) -> x)(A | B)" `shouldBe` Right "42"
  --   run env "((A | B) -> x)(B | A)" `shouldBe` Right "42"
  --   run env "((a : !Int) -> a)(x)" `shouldBe` Right "42"
  --   run env "((a : !Int) -> a)(x : !Int)" `shouldBe` Right "42"
  --   run env "((a : !Num) -> a)(x : !Int)" `shouldBe` Right "!unhandled-case<!Num, !Int>(!error)"
  --   run env "((x : a) -> a)(x : !Int)" `shouldBe` Right "!Int"
  --   run env "((a : !Num) -> a)(x : _)" `shouldBe` Right "42"
  --   run env "((a : !Num) -> a)(x : !error(_))" `shouldBe` Right "!unhandled-case<!Num, !Err>(!error)"
  --   run env "((a : !Num) -> a)(x)" `shouldBe` Right "42"
  --   run env "((A : A) -> B)(a : A)" `shouldBe` Right "!let<> A = a; B"
  --   run env "((@y. y) -> y)(x)" `shouldBe` Right "42"
  --   run env "((&y. x -> y) -> y)(x)" `shouldBe` Right "!unhandled-case<&y. 42 -> y, 42>(!error)"
  --   run env "((&y. x -> y) -> y)(&y. x -> y)" `shouldBe` Right "&y. 42 -> y"
  --   run env "((&y. x -> y) -> y)(&z. x -> z)" `shouldBe` Right "&y. 42 -> y"
  --   run env "((a x) -> a)(z x)" `shouldBe` Right "z" -- undefined
  --   run env "(%call() -> Ok)(%call())" `shouldBe` Right "Ok"
  --   run env "(%call() -> Ok)(%other())" `shouldBe` Right "!unhandled-case<%call(), %other()>(!error)"
  --   run env "(%call(a) -> a)(%call(x))" `shouldBe` Right "42"
  --   run env "(@{z = 5} z -> z)(5)" `shouldBe` Right "5"
  --   run env "(@{z = 5} z -> z)(x)" `shouldBe` Right "!unhandled-case<5, 42>(!error)"
  --   run env "(^[file:1:2,3:4](z) -> z)(x)" `shouldBe` Right "42"
  --   run env "(z -> z)(^[file:1:2,3:4](x))" `shouldBe` Right "^[file:1:2,3:4](42)"
  --   run env "(!error(x) -> Ok)(!error)" `shouldBe` Right "Ok"
  --   run env "(!error(x) -> Ok)(x)" `shouldBe` Right "!unhandled-case<!Err, 42>(!error)"
  --   run env "(x -> Ok)(!error)" `shouldBe` Right "!unhandled-case<42, !Err>(!error)"

  it "☯ syntax sugar" $ do
    -- let' [] x `shouldBe` x
    -- let' [(y', z)] x `shouldBe` App (Fun y' x) z

    -- lam [] x `shouldBe` x
    -- lam [y'] x `shouldBe` Fun y' x

    and' [] `shouldBe` Unit
    and' [x] `shouldBe` x
    and' [x, y] `shouldBe` And x y

    tag "A" [] `shouldBe` Tag "A" Unit
    tag "A" [x] `shouldBe` Tag "A" x
    tag "A" [x, y] `shouldBe` Tag "A" (And x y)

    app x [] `shouldBe` App x Unit
    app x [y, z] `shouldBe` App x (And y z)

  -- it "☯ reduce" $ do
  --   let env =
  --         [ ("a", IntT),
  --           ("x", Int 42),
  --           ("y", Num 3.14),
  --           ("z", Var "z"),
  --           ("f", For "y" (Fun y y))
  --         ]

  --   let reduce' x = reduce ops (Let env x)
  --   reduce' IntT `shouldBe` IntT
  --   reduce' NumT `shouldBe` NumT
  --   reduce' (Int 1) `shouldBe` Int 1
  --   reduce' (Num 1.1) `shouldBe` Num 1.1
  --   reduce' (Tag "x") `shouldBe` Tag "x"
  --   reduce' (Var "x") `shouldBe` Int 42
  --   reduce' (Var "y") `shouldBe` Num 3.14
  --   reduce' (Var "z") `shouldBe` Var "z"
  --   reduce' (Var "w") `shouldBe` Var "w"
  --   -- reduce' (For "x" x) `shouldBe` For "x" x
  --   -- reduce' (For "x" y) `shouldBe` For "x" (Num 3.14)
  --   -- reduce' (Fix "x" x) `shouldBe` Fix "x" x
  --   -- reduce' (Fix "x" y) `shouldBe` Fix "x" (Num 3.14)
  --   reduce' (Ann x y) `shouldBe` Ann (Let env x) (Let env y)
  --   reduce' (And x y) `shouldBe` And (Let env x) (Let env y)
  --   reduce' (Or x y) `shouldBe` Or (Let env x) (Let env y)
  --   reduce' (Fun x y) `shouldBe` Fun (Let env x) (Let env y)
  --   reduce' (App IntT y) `shouldBe` Err (cannotApply IntT (Num 3.14))
  --   reduce' (App NumT y) `shouldBe` Err (cannotApply NumT (Num 3.14))
  --   -- reduce' (App (Int 1) y) `shouldBe` err
  --   -- reduce' (App (Num 1.1) y) `shouldBe` err
  --   -- reduce' (App (Tag "x") y) `shouldBe` err
  --   -- reduce' (App (Var "x") y) `shouldBe` err
  --   reduce' (App (Var "z") y) `shouldBe` App z (Num 3.14)
  --   reduce' (App (App (Var "z") y) x) `shouldBe` App (App z (Num 3.14)) (Int 42)
  --   -- reduce' (App (For "x" x) y) `shouldBe` App x (Num 3.14)
  --   -- reduce' (App (Fix "x" x) y) `shouldBe` App (Fix "x" x) x
  --   reduce' (App (Fun IntT NumT) IntT) `shouldBe` NumT
  --   -- reduce' (App (Fun NumT IntT) IntT) `shouldBe` err
  --   reduce' (App (Fun NumT IntT) NumT) `shouldBe` IntT
  --   reduce' (App (Fun (Int 42) z) (Int 42)) `shouldBe` z
  --   -- reduce' (App (Fun (Int 42) z) (Int 0)) `shouldBe` err
  --   reduce' (App (Fun (Num 3.14) z) (Num 3.14)) `shouldBe` z
  --   -- reduce' (App (Fun (Num 3.14) z) (Num 0.0)) `shouldBe` err
  --   reduce' (App (Fun (Tag "A") z) (Tag "A")) `shouldBe` z
  --   -- reduce' (App (Fun (Tag "A") z) (Tag "B")) `shouldBe` err
  --   reduce' (App (Fun (Var "x") z) (Int 42)) `shouldBe` z
  --   -- reduce' (App (Fun (Var "x") z) (Int 0)) `shouldBe` err
  --   reduce' (App (Fun (Var "x") z) x) `shouldBe` z
  --   -- reduce' (App (Fun (Var "x") z) y) `shouldBe` err
  --   -- TODO: reduce App Fun App
  --   reduce' (App (Fun (And IntT NumT) z) (And IntT NumT)) `shouldBe` z
  --   -- reduce' (App (Fun (And IntT NumT) z) (And IntT IntT)) `shouldBe` err
  --   -- reduce' (App (Fun (And IntT NumT) z) (And NumT NumT)) `shouldBe` err
  --   reduce' (App (Fun (Or IntT NumT) z) IntT) `shouldBe` z
  --   reduce' (App (Fun (Or IntT NumT) z) NumT) `shouldBe` z
  --   -- reduce' (App (Fun (Or IntT IntT) z) x) `shouldBe` err
  --   reduce' (App (Fun (Ann x err) z) x) `shouldBe` z
  --   -- reduce' (App (Fun (Ann x err) z) y) `shouldBe` err
  --   reduce' (App (Fun (Call "f" []) z) (Call "f" [])) `shouldBe` z
  --   reduce' (App (Fun err IntT) err) `shouldBe` IntT
  --   reduce' (App (For "y" (Fun y y)) x) `shouldBe` Int 42
  --   reduce' (App (Var "f") x) `shouldBe` Int 42
  --   reduce' (App (Or (Var "f") err) x) `shouldBe` Int 42
  --   reduce' (App (Or err (Var "f")) x) `shouldBe` Int 42
  --   -- reduce' (App (Or err err) x) `shouldBe` err
  --   reduce' (Call "f" [x, y]) `shouldBe` Call "f" [Let env x, Let env y]
  --   reduce' err `shouldBe` err

  -- it "☯ eval" $ do
  --   let env =
  --         [ ("x", Int 42),
  --           ("y", Num 3.14),
  --           ("f", For "z" (Fun z z))
  --         ]

  --   let eval' x = eval ops (Let env x)
  --   eval' (Fun x y) `shouldBe` Fun (Int 42) (Num 3.14)
  --   eval' (And x y) `shouldBe` And (Int 42) (Num 3.14)
  --   eval' (Or x y) `shouldBe` Or (Int 42) (Num 3.14)
  --   eval' (Call "f" [x, y]) `shouldBe` Call "f" [Int 42, Num 3.14]
  --   eval' (Call "int_add" [i1, i1]) `shouldBe` i2
  --   -- eval' (For "x" (And x y)) `shouldBe` For "x" (And x (Num 3.14))
  --   -- eval' (Fix "x" (And x y)) `shouldBe` Fix "x" (And x (Num 3.14))
  --   eval' (App z (And x y)) `shouldBe` App z (And (Int 42) (Num 3.14))

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

  it "☯ eval alpha equivalence" $ do
    let eval' = eval ops
    let a' = for ["x", "a"] (Fun (Ann x a) x)
    let b' = for ["y", "b"] (Fun (Ann y b) y)
    eval' (App (Fun a' i1) b') `shouldBe` i1

  it "☯ -- unify" $ do
    True `shouldBe` True

  -- it "☯ infer const" $ do
  --   infer [] [] IntT `shouldBe` ((IntT, IntT), [])
  --   infer [] [] NumT `shouldBe` ((NumT, NumT), [])
  --   infer [] [] (Int 1) `shouldBe` ((Int 1, IntT), [])
  --   infer [] [] (Num 1.1) `shouldBe` ((Num 1.1, NumT), [])
  --   infer [] [] err `shouldBe` ((err, Any), [])

  -- it "☯ infer Var" $ do
  --   let (a1, yT) = (Var "a1", Var "yT")
  --   let env = [("x", i1), ("y", y), ("b", Ann b IntT), ("a", b), ("c", Ann c (for ["a"] a))]
  --   infer [] env (Var "x") `shouldBe` ((x, IntT), [])
  --   infer [] env (Var "y") `shouldBe` ((y, yT), [("yT", yT), ("y", Ann y yT)])
  --   infer [] env (Var "z") `shouldBe` ((z, Err $ TypeError $ UndefinedVar "z"), [])
  --   infer [] env (Var "a") `shouldBe` ((a, IntT), [])
  --   infer [] env (Var "c") `shouldBe` ((c, a1), [("a1", a1)])

  -- it "☯ infer Ann" $ do
  --   let env = []
  --   infer [] env (Ann i1 IntT) `shouldBe` ((i1, IntT), [])
  --   infer [] env (Ann i1 NumT) `shouldBe` ((i1, Err $ typeMismatch IntT NumT), [])
  --   infer [] env (Ann i1 (For "a" a)) `shouldBe` ((i1, IntT), [("a", IntT)])

  -- it "☯ infer Ann Tag" $ do
  --   let env = [("T", Tag "A" `Or` Tag "B")]
  --   -- infer [] env (Tag "T" []) `shouldBe` Right (Tag "A" [] `Or` Tag "B" [], [])
  --   -- infer [] env (Ann (Tag "A" []) (Tag "A" [])) `shouldBe` Right (Tag "A" [], [])
  --   -- infer [] env (Ann (Tag "A") (Tag "T")) `shouldBe` Right (Tag "T", [])
  --   -- infer [] env (Ann (Tag "B []) (Tag "T" [])) `shouldBe` Right (Tag "T" [], [])
  --   -- infer [] env (Ann (Tag "C" []) (Tag "T" [])) `shouldBe` Left (TypeMismatch (Ann (Tag "C" []) (Tag "T" [])) (Tag "A" [] `Or` Tag "B" []))
  --   True `shouldBe` True

  -- it "☯ infer Fun" $ do
  --   let (t, xT, _T) = (Var "t", Var "xT", Var "_T")
  --   let env =
  --         [ ("x", Ann x a),
  --           ("y", Int 1),
  --           ("a", a)
  --         ]
  --   infer [] env (Fun x x) `shouldBe` ((Fun (Ann x a) x, Fun a a), [])

  -- it "☯ infer Fun" $ do
  --   let env = [("a", Ann a IntT), ("b", Ann b NumT)]
  --   infer [] env (Fun a b) `shouldBe` ((Fun (Ann a IntT) b, Fun IntT NumT), [])

  -- it "☯ infer App" $ do
  --   let env =
  --         [ ("x", i1),
  --           ("y", y),
  --           ("f", Ann f (Fun IntT NumT))
  --         ]
  --   infer [] env (App f x) `shouldBe` ((App f (Ann x IntT), NumT), [])
  --   infer [] env (App (Fun y y) x) `shouldBe` ((App (Fun (Ann y IntT) y) (Ann x IntT), IntT), [("yT", IntT), ("y", Ann y IntT)])
  --   infer [] env (App y x) `shouldBe` ((App y (Ann x IntT), Var "yT$2"), [("yT$1", IntT), ("yT", Fun IntT (Var "yT$2")), ("yT$2", Var "yT$2"), ("y", Ann y (Fun IntT (Var "yT$2")))])

  -- it "☯ infer Or" $ do
  --   let env = [("x", Int 42), ("y", Num 3.14)]
  --   infer [] env (Or x x) `shouldBe` ((Or x x, Or IntT IntT), [])
  --   infer [] env (Or x y) `shouldBe` ((Or x y, Or IntT NumT), [])

  -- it "☯ infer For" $ do
  --   let xT = Var "xT"
  --   infer [] [] (For "x" x) `shouldBe` ((For "x" x, xT), [("xT", xT), ("x", Ann x xT)])

  -- it "☯ infer Op2" $ do
  --   True `shouldBe` True

  -- it "☯ infer factorial" $ do
  --   let env = [("f", Ann (factorial "f") (Fun IntT IntT))]
  --   let infer' = infer ops env
  --   infer' (Var "f") `shouldBe` Right [((f, Fun IntT IntT), [])]
  --   infer' (Ann f (Fun IntT IntT)) `shouldBe` Right [((f, Fun IntT IntT), [])]

  -- it "☯ Core.Bool" $ do
  --   let (bool, true, false) = (tag' "Bool", tag' "True", tag' "False")
  --   let env = [("Bool", Fun Unit (Fun true bool `Or` Fun false bool))]

  --   eval ops (Let env (App (Fun bool Unit) true)) `shouldBe` Unit
  --   eval ops (Let env (App (Fun bool Unit) (tag' "X"))) `shouldBe` err (unhandledCase bool (tag' "X"))
  --   eval ops (Let env (App (Fun bool Unit) bool)) `shouldBe` Unit

  -- let infer' = infer ops env
  -- infer' true `shouldBe` Right [((true, true), [])]
  -- infer' (Ann true bool) `shouldBe` Right [((true, bool), [])]
  -- infer' (Ann false (tag' "X")) `shouldBe` Right [((false, err (typeMismatch false (tag' "X"))), [])]
  -- infer' (Ann (tag' "X") bool) `shouldBe` Right [((tag' "X", err $ typeMismatch (err $ unhandledCase false (tag' "X")) bool), [])]

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

  -- it "☯ Core.Vec" $ do
  --   let (n, a) = (Var "n", Var "a")
  --   let nil = tag' "Nil"
  --   let cons x xs = tag "Cons" [x, xs]
  --   let vec n a = tag "Vec" [n, a]
  --   let alts a =
  --         [ For "n" $ fun [cons a (vec n a)] (vec (n `add` i1) a),
  --           fun [nil] (vec i0 a)
  --         ]
  --   let env = [("Vec", lam [n, a] (or' $ alts a))]

  --   eval ops (Let env (App (Fun (vec i0 NumT) Unit) nil)) `shouldBe` Unit
  --   eval ops (Let env (App (Fun (vec i0 NumT) Unit) (tag' "X"))) `shouldBe` err (unhandledCase (vec i0 NumT) (tag' "X"))
  --   eval ops (Let env (App (Fun (vec i0 NumT) Unit) (vec i0 NumT))) `shouldBe` Unit
  --   eval ops (Let env (App (Fun (vec i1 NumT) Unit) (cons NumT nil))) `shouldBe` Unit
  --   eval ops (Let env (App (Fun (vec i1 NumT) Unit) (vec i1 NumT))) `shouldBe` Unit

  -- unify ops env (vec i0 NumT) nil `shouldBe` Right [(vec i0 NumT, [])]
  -- unify ops env nil (vec i0 NumT) `shouldBe` Right [(vec i0 NumT, [])]
  -- unify ops env (vec i1 NumT) nil `shouldBe` Right [(Tag "Vec" (And (err $ typeMismatch i1 i0) NumT), [])]
  -- unify ops env (vec i1 NumT) (cons NumT nil) `shouldBe` Right [(vec i1 NumT, [])]
  -- unify ops env (cons NumT nil) (vec i1 NumT) `shouldBe` Right [(vec i1 NumT, [])]
  -- unify ops env (vec i0 NumT) (cons NumT nil) `shouldBe` Right [(Tag "Vec" (And (err $ typeMismatch i0 i1) NumT), [])]

  -- let infer' = infer ops env
  -- infer' nil `shouldBe` Right [((nil, nil), [])]
  -- infer' (cons (Num 1.1) nil) `shouldBe` Right [((cons (Num 1.1) nil, cons NumT nil), [])]
  -- infer' (Ann nil (vec i0 NumT)) `shouldBe` Right [((nil, vec i0 NumT), [])]
  -- infer' (Ann nil (vec i1 NumT)) `shouldBe` Right [((nil, Tag "Vec" (And (err $ typeMismatch i0 i1) NumT)), [])]
  -- infer' (Ann (cons (Num 1.1) nil) (vec i1 NumT)) `shouldBe` Right [((cons (Num 1.1) nil, vec i1 NumT), [])]
  -- infer' (Ann (cons (Num 1.1) (cons (Num 2.2) nil)) (vec i0 NumT)) `shouldBe` Right [((cons (Num 1.1) (cons (Num 2.2) nil), Tag "Vec" (And (err $ typeMismatch i2 i0) NumT)), [])]

  -- it "☯ Core.choice" $ do
  --   let env =
  --         [ ("a", a),
  --           ("b", b),
  --           ("x", i1),
  --           ("y", n1),
  --           ("f", Ann f (Fun a a)),
  --           ("g", Ann g (Fun (And a a) a))
  --         ]
  --   let infer' = infer ops env
  --   let check' = check ops env
  --   let e = err (typeMismatch NumT IntT)
  --   infer' (Fun (Ann x IntT) (Ann y NumT)) `shouldBe` Right [((Fun (Ann x IntT) (Ann y NumT), Fun IntT NumT), [])]
  --   check' (Fun x y) (Fun IntT NumT) `shouldBe` Right [((Fun (Ann x IntT) (Ann y NumT), Fun IntT NumT), [])]
  --   infer' (Fun (Ann x IntT) (Ann y IntT)) `shouldBe` Right [((Fun (Ann x IntT) (Ann y e), Fun IntT e), [])]
  --   check' (Fun x y) (Fun IntT IntT) `shouldBe` Right [((Fun (Ann x IntT) (Ann y e), Fun IntT e), [])]
  --   infer' (Fun (Ann x IntT) (Ann y NumT) `Or` Fun e e) `shouldBe` Right [((Fun (Ann x IntT) (Ann y NumT), Fun IntT NumT), [])]
  --   check' (Fun x y `Or` Fun e e) (Fun IntT NumT) `shouldBe` Right [((Fun (Ann x IntT) (Ann y NumT), Fun IntT NumT), [])]
  --   infer' (Fun e e `Or` Fun (Ann x IntT) (Ann y NumT)) `shouldBe` Right [((Fun (Ann x IntT) (Ann y NumT), Fun IntT NumT), [])]
  --   check' (Fun e e `Or` Fun x y) (Fun IntT NumT) `shouldBe` Right [((Fun (Ann x IntT) (Ann y NumT), Fun IntT NumT), [])]
  --   infer' (App (Fun x y) i1) `shouldBe` Right [((App (Fun (Ann x IntT) (Ann y NumT)) (Ann i1 IntT), NumT), [("$1", NumT)])]
  --   check' (App (Fun x y) i1) NumT `shouldBe` Right [((App (Fun (Ann x IntT) (Ann y NumT)) (Ann i1 IntT), NumT), [])]
  --   -- f : a -> a
  --   -- g : (a, a) -> a
  --   () `shouldBe` ()

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

  it "☯ Core.overload.fixed" $ do
    let f1 = Ann (Fun (Ann i1 IntT) i2) (Fun IntT IntT)
    let f2 = Ann (Fun (Ann n1 NumT) n2) (Fun NumT NumT)
    let env = [("f", Or f1 f2)]
    eval ops (Let env f) `shouldBe` Or f1 f2
    eval ops (Let env (App f (Ann i1 IntT))) `shouldBe` i2
    eval ops (Let env (App f (Ann i2 IntT))) `shouldBe` err (unhandledCase loc0 NumT IntT)
    eval ops (Let env (App f (Ann n1 NumT))) `shouldBe` n2
  -- infer ops env f `shouldBe` Right [((f, Fun IntT IntT `Or` Fun NumT NumT), [])]
  -- infer ops env (App f i1) `shouldBe` Right [((App f (Ann i1 IntT), IntT), [("$1", IntT)])]
  -- infer ops env (App f n1) `shouldBe` Right [((App f (Ann n1 NumT), NumT), [("$1", NumT)])]
  -- infer ops env (App f Unit) `shouldBe` Right [((Err, Or (Fun (err $ typeMismatch IntT Unit) IntT) (Fun (err $ typeMismatch NumT Unit) NumT)), [])]
  -- -- TODO: This should give a type error, that case is unreachable
  -- infer ops env (App f i2) `shouldBe` Right [((App f (Ann i2 IntT), IntT), [("$1", IntT)])]

  it "☯ Core.overload.bind" $ do
    let f1 = Ann (For "x" $ Fun (Ann x IntT) i2) (Fun IntT IntT)
    let f2 = Ann (For "x" $ Fun (Ann x NumT) n2) (Fun NumT NumT)
    let env = [("f", Or f1 f2)]
    eval ops (Let env f) `shouldBe` Or f1 f2
    eval ops (Let env (App f (Ann i1 IntT))) `shouldBe` i2
    eval ops (Let env (App f (Ann n1 NumT))) `shouldBe` n2
  -- infer ops env f `shouldBe` Right [((f, Fun IntT IntT `Or` Fun NumT NumT), [("x", Ann x (Or IntT NumT))])]
  -- infer ops env (App f i1) `shouldBe` Right [((App f (Ann i1 IntT), IntT), [("$1", IntT), ("x", Ann x IntT)])]
  -- infer ops env (App f n1) `shouldBe` Right [((App f (Ann n1 NumT), NumT), [("$1", NumT), ("x", Ann x NumT)])]
  -- infer ops env (App f Unit) `shouldBe` Right [((Err, Or (Fun (err $ typeMismatch IntT Unit) IntT) (Fun (err $ typeMismatch NumT Unit) NumT)), [])]
  -- -- TODO: This should give a type error, that case is unreachable
  -- infer ops env (App f i2) `shouldBe` Right [((App f (Ann i2 IntT), IntT), [("$1", IntT), ("x", Ann x IntT)])]

  it "☯ Core.unpack" $ do
    let (x, y, z, w) = (Var "x", Var "y", Var "z", Var "w")

    -- Basic cases
    unpack (Any, z) `shouldBe` []
    unpack (Unit, z) `shouldBe` []
    unpack (IntT, z) `shouldBe` []
    unpack (NumT, z) `shouldBe` []
    unpack (Int 1, z) `shouldBe` []
    unpack (Num 1.1, z) `shouldBe` []
    unpack (Var "x", z) `shouldBe` [("x", z)]
    unpack (Tag "A" x, z) `shouldBe` [("x", letP (For "x" $ Tag "A" x, z) x)]
    unpack (And x y, z) `shouldBe` [("x", letP (for ["x", "y"] $ And x y, z) x), ("y", letP (for ["x", "y"] $ And x y, z) y)]
    unpack (Or x y, z) `shouldBe` [("x", letP (for ["x", "y"] $ Or x y, z) x), ("y", letP (for ["x", "y"] $ Or x y, z) y)]
    unpack (Ann x y, z) `shouldBe` [("x", Ann z y)]
    unpack (For "x" x, z) `shouldBe` [("x", z)]
    unpack (For "x" y, z) `shouldBe` [("x", letP (y, z) x)]
    unpack (For "x" (And x y), z) `shouldBe` [("x", letP (For "x" (And x y), z) x)]
    unpack (Fix "x" y, z) `shouldBe` [("x", letP (Fix "x" y, z) x)]
    unpack (Fun x y, z) `shouldBe` [("x", letP (for ["x", "y"] $ Fun x y, z) x), ("y", letP (for ["x", "y"] $ Fun x y, z) y)]
    unpack (App x y, z) `shouldBe` [("x", Fun y z)]
    unpack (Call "f" x, z) `shouldBe` [("x", letP (For "x" $ Call "f" x, z) x)]
    -- unpack (Let [] x, z) `shouldBe` [("x", letP (For "x" $ Let [] x, z) x)]
    -- unpack (Let [("x", y)] x, z) `shouldBe` []
    unpack (Meta loc x, z) `shouldBe` [("x", z)]
    unpack (Err, z) `shouldBe` []

    -- Special cases
    unpack (Ann (App x y) z, w) `shouldBe` [("x", Ann (Fun y w) z)]

  it "☯ Core.bind" $ do
    let (x, y, z) = (Var "x", Var "y", Var "z")
    bind [] x `shouldBe` x
    bind [] (Ann x x) `shouldBe` For "x" (Ann x x)
    bind [] (Ann x y) `shouldBe` For "y" (Ann x y)
    bind ["y"] (Ann x y) `shouldBe` Ann x y
    bind [] (For "x" (Ann x y)) `shouldBe` For "x" (Ann x y)
    bind [] (For "y" (Ann x y)) `shouldBe` For "y" (Ann x y)
    bind [] (For "z" (Ann x y)) `shouldBe` Ann x y
    bind [] (Ann x (For "x" y)) `shouldBe` For "x" (Ann x y)
    bind [] (Ann x (For "y" y)) `shouldBe` For "y" (Ann x y)
    bind [] (Ann x (For "z" y)) `shouldBe` Ann x y
    bind [] (Fun x y) `shouldBe` For "x" (Fun x y)
    bind ["x"] (Fun x y) `shouldBe` Fun x y
    bind [] (For "x" (Fun x y)) `shouldBe` For "x" (Fun x y)
    bind [] (For "y" (Fun x y)) `shouldBe` For "y" (Fun x y)
    bind [] (For "z" (Fun x y)) `shouldBe` Fun x y
    bind [] (Fun (For "x" x) y) `shouldBe` For "x" (Fun x y)
    bind [] (Fun (For "y" x) y) `shouldBe` For "y" (Fun x y)
    bind [] (Fun (For "z" x) y) `shouldBe` Fun x y
    bind [] (Fun (And x y) z) `shouldBe` for ["x", "y"] (Fun (And x y) z)
    bind [] (Fun (And x (Fun x y)) z) `shouldBe` for ["x", "y"] (Fun (And x (Fun x y)) z)
    bind [] (Fun x (Fun y z)) `shouldBe` For "x" (Fun x (for ["y"] (Fun y z)))
    bind [] (Fun x (Fun x y)) `shouldBe` For "x" (Fun x (for ["x"] (Fun x y)))

  it "☯ Core.substitute" $ do
    let s = [("x", i1), ("y", i2)]
    substitute s Any `shouldBe` Any
    substitute s Unit `shouldBe` Unit
    substitute s IntT `shouldBe` IntT
    substitute s NumT `shouldBe` NumT
    substitute s (Int 0) `shouldBe` Int 0
    substitute s (Num 0.0) `shouldBe` Num 0.0
    substitute s (Var "x") `shouldBe` i1
    substitute s (Var "y") `shouldBe` i2
    substitute s (Var "z") `shouldBe` Var "z"
    substitute s (Tag "A" x) `shouldBe` Tag "A" i1
    substitute s (Ann x y) `shouldBe` Ann i1 i2
    substitute s (And x y) `shouldBe` And i1 i2
    substitute s (Or x y) `shouldBe` Or i1 i2
    substitute s (For "x" x) `shouldBe` For "x" x
    substitute s (For "x" y) `shouldBe` For "x" i2
    substitute s (Fix "x" x) `shouldBe` Fix "x" x
    substitute s (Fix "x" y) `shouldBe` Fix "x" i2
    substitute s (Fun x y) `shouldBe` Fun i1 i2
    substitute s (App x y) `shouldBe` App i1 i2
    substitute s (Call "f" x) `shouldBe` Call "f" i1
    substitute s (Let [] x) `shouldBe` Let [] i1
    substitute s (Let [("x", y)] x) `shouldBe` Let [("x", i2)] x
    substitute s (Let [("y", x)] x) `shouldBe` Let [("y", i1)] i1
    substitute s Err `shouldBe` Err

  it "☯ Core.compose" $ do
    compose [] [("x", i1)] `shouldBe` [("x", i1)]
    compose [("x", i1)] [] `shouldBe` [("x", i1)]
    compose [("x", i1)] [("x", i2)] `shouldBe` [("x", i1)]
    compose [("x", i1)] [("y", i2)] `shouldBe` [("x", i1), ("y", i2)]
    compose [("x", i1)] [("y", x)] `shouldBe` [("x", i1), ("y", i1)]
    compose [("x", y)] [("y", i1)] `shouldBe` [("x", y), ("y", i1)]
    compose [("x", i1)] [("x", For "x" x)] `shouldBe` [("x", i1)]
    compose [("x", i1)] [("x", For "x" i2)] `shouldBe` [("x", i1)]

  it "☯ Core.reduce" $ do
    reduce [] Any `shouldBe` Any
    reduce [] Unit `shouldBe` Unit
    reduce [] IntT `shouldBe` IntT
    reduce [] NumT `shouldBe` NumT
    reduce [] (Int 0) `shouldBe` (Int 0)
    reduce [] (Num 0.0) `shouldBe` (Num 0.0)
    reduce [] (Var "x") `shouldBe` (Var "x")
    reduce [] (Tag "A" x) `shouldBe` (Tag "A" x)
    reduce [] (For "x" x) `shouldBe` (For "x" x)
    reduce [] (Fix "x" x) `shouldBe` (Fix "x" x)
    reduce [] (Ann x y) `shouldBe` (Ann x y)
    reduce [] (And x y) `shouldBe` (And x y)
    reduce [] (Or x y) `shouldBe` (Or x y)
    reduce [] (Fun x y) `shouldBe` (Fun x y)
    reduce [] (App x y) `shouldBe` (App x y)
    reduce [] (Call "f" x) `shouldBe` (Call "f" x)
    reduce [] (Let [] x) `shouldBe` x
    reduce [] (Meta (Comments []) x) `shouldBe` x
    reduce [] Err `shouldBe` Err

  it "☯ Core.reduce.Let" $ do
    let env = [("x", a), ("y", b)]
    reduce [] (Let env Any) `shouldBe` Any
    reduce [] (Let env Unit) `shouldBe` Unit
    reduce [] (Let env IntT) `shouldBe` IntT
    reduce [] (Let env NumT) `shouldBe` NumT
    reduce [] (Let env $ Int 0) `shouldBe` (Int 0)
    reduce [] (Let env $ Num 0.0) `shouldBe` (Num 0.0)
    reduce [] (Let env $ Var "x") `shouldBe` a
    reduce [] (Let env $ Tag "A" x) `shouldBe` Tag "A" (Let env x)
    reduce [] (Let env $ For "x" x) `shouldBe` (For "x" (Let env x))
    reduce [] (Let env $ Fix "x" x) `shouldBe` (Fix "x" (Let env x))
    reduce [] (Let env $ Ann x y) `shouldBe` (Ann (Let env x) (Let env y))
    reduce [] (Let env $ And x y) `shouldBe` (And (Let env x) (Let env y))
    reduce [] (Let env $ Or x y) `shouldBe` (Or (Let env x) (Let env y))
    reduce [] (Let env $ Fun x y) `shouldBe` (Fun (Let env x) (Let env y))
    reduce [] (Let env $ App x y) `shouldBe` (App a (Let env y))
    reduce [] (Let env $ Call "f" x) `shouldBe` (Call "f" (Let env x))
    reduce [] (Let env $ Let [] x) `shouldBe` a
    reduce [] (Let env $ Let [("x", c)] x) `shouldBe` c
    reduce [] (Let env $ Meta (Comments []) x) `shouldBe` a
    reduce [] (Let env Err) `shouldBe` Err

  it "☯ Core.reduce.Call" $ do
    let ops =
          [ ("f", \eval a -> Just i0),
            ("g", \eval a -> Nothing)
          ]
    -- TODO: ("h", \eval args -> Just $ and' (map eval args))
    reduce ops (Call "undefined" x) `shouldBe` Call "undefined" x
    reduce ops (Call "f" x) `shouldBe` i0
    reduce ops (Call "g" x) `shouldBe` Call "g" x

  it "☯ Core.reduce.App" $ do
    let x1 = Var "x1"
    reduce [] (App Any x) `shouldBe` Any
    reduce [] (App Unit x) `shouldBe` err (cannotApply loc0 Unit x)
    reduce [] (App IntT x) `shouldBe` err (cannotApply loc0 IntT x)
    reduce [] (App NumT x) `shouldBe` err (cannotApply loc0 NumT x)
    reduce [] (App i0 x) `shouldBe` err (cannotApply loc0 i0 x)
    reduce [] (App n0 x) `shouldBe` err (cannotApply loc0 n0 x)
    reduce [] (App x y) `shouldBe` App x y
    reduce [] (App (Tag "A" x) y) `shouldBe` err (cannotApply loc0 (Tag "A" x) y)
    reduce [] (App (For "x" x) x) `shouldBe` App (For "x1" x1) x
    reduce [] (App (For "x" x) y) `shouldBe` App (For "x" x) y
    reduce [] (App (For "x" y) x) `shouldBe` App y x
    reduce [] (App (For "x" y) y) `shouldBe` App y y
    reduce [] (App (Fix "x" y) z) `shouldBe` App y z
    reduce [] (App (Ann x y) z) `shouldBe` App x z
    reduce [] (App (And x y) z) `shouldBe` err (cannotApply loc0 (And x y) z)
    reduce [] (App (Or x y) z) `shouldBe` Or (App x z) (App y z)
    reduce [] (App (Fun x y) z) `shouldBe` y
    reduce [] (App (App x y) z) `shouldBe` App (App x y) z
    reduce [] (App (Call "f" x) y) `shouldBe` App (Call "f" x) y
    reduce [("f", \_ _ -> Just x)] (App (Call "f" y) z) `shouldBe` App x z
    reduce [] (App (Let [] x) y) `shouldBe` App x y
    reduce [] (App (Let [("x", y)] x) z) `shouldBe` App y z
    reduce [] (App (Meta (Comments []) x) y) `shouldBe` App x y
    reduce [] (App Err x) `shouldBe` err (cannotApply loc0 Err x)

  it "☯ Core.reduce.App.Fun -- pattern matching direct" $ do
    let reduce' a b c = reduce [] (App (Fun a c) b)
    reduce' Any Any x `shouldBe` x
    reduce' Any Unit x `shouldBe` x
    reduce' Any IntT x `shouldBe` x
    reduce' Any x x `shouldBe` x
    reduce' Any y x `shouldBe` x
    reduce' Unit Any x `shouldBe` x
    reduce' Unit Unit x `shouldBe` x
    reduce' Unit IntT x `shouldBe` err (unhandledCase loc0 Unit IntT)
    reduce' Unit x x `shouldBe` Unit
    reduce' Unit b x `shouldBe` x
    reduce' IntT Unit x `shouldBe` err (unhandledCase loc0 IntT Unit)
    reduce' IntT IntT x `shouldBe` x
    reduce' IntT x x `shouldBe` IntT
    reduce' IntT b x `shouldBe` x
    reduce' NumT Unit x `shouldBe` err (unhandledCase loc0 NumT Unit)
    reduce' NumT NumT x `shouldBe` x
    reduce' NumT x x `shouldBe` NumT
    reduce' NumT b x `shouldBe` x
    reduce' (Int 0) i0 x `shouldBe` x
    reduce' (Int 0) i1 x `shouldBe` err (unhandledCase loc0 i0 i1)
    reduce' (Int 0) x x `shouldBe` (Int 0)
    reduce' (Int 0) b x `shouldBe` x
    reduce' (Num 0.0) n0 x `shouldBe` x
    reduce' (Num 0.0) n1 x `shouldBe` err (unhandledCase loc0 n0 n1)
    reduce' (Num 0.0) x x `shouldBe` (Num 0.0)
    reduce' (Num 0.0) b x `shouldBe` x
    reduce' (Var "x") i1 x `shouldBe` i1
    reduce' (Var "x") a x `shouldBe` a
    reduce' (Var "x") b x `shouldBe` b
    reduce' (Var "x") a a `shouldBe` a
    reduce' (Var "x") b a `shouldBe` a
    reduce' (Tag "A" x) i1 x `shouldBe` err (unhandledCase loc0 (Tag "A" x) i1)
    reduce' (Tag "A" x) a x `shouldBe` x
    reduce' (Tag "A" x) a a `shouldBe` Tag "A" x
    reduce' (Tag "A" x) (Tag "B" a) x `shouldBe` err (unhandledCase loc0 (Tag "A" x) (Tag "B" a))
    reduce' (Tag "A" x) (Tag "A" a) x `shouldBe` a
    reduce' (Tag "A" x) (Tag "A" i1) x `shouldBe` i1
    reduce' (Tag "A" i0) (Tag "A" i1) x `shouldBe` err (unhandledCase loc0 i0 i1)
    reduce' (For "x" x) i1 x `shouldBe` i1
    reduce' (For "x" x) a x `shouldBe` a
    reduce' (For "x" x) a a `shouldBe` a
    reduce' (Fix "x" x) i1 x `shouldBe` err (unhandledCase loc0 (Fix "x" x) i1)
    reduce' (Fix "x" x) a x `shouldBe` x
    reduce' (Fix "x" x) a a `shouldBe` Fix "x" x
    reduce' (Fix "x" x) (Fix "a" a) x `shouldBe` a
    reduce' (Ann x y) i1 x `shouldBe` i1
    reduce' i1 (Ann x y) x `shouldBe` i1
    reduce' (Ann x y) a x `shouldBe` x
    reduce' (Ann x y) a a `shouldBe` Ann x y
    reduce' (Ann x y) (Ann a IntT) x `shouldBe` a
    reduce' (Ann x y) (Ann a IntT) y `shouldBe` IntT
    reduce' (Ann x IntT) (Ann a IntT) x `shouldBe` a
    reduce' (Ann x IntT) (Ann a NumT) x `shouldBe` err (unhandledCase loc0 IntT NumT)
    reduce' (And x y) i1 x `shouldBe` err (unhandledCase loc0 (And x y) i1)
    reduce' (And x y) a x `shouldBe` x
    reduce' (And x y) a a `shouldBe` And x y
    reduce' (And x y) (And i1 i2) x `shouldBe` i1
    reduce' (And x y) (And i1 i2) y `shouldBe` i2
    reduce' (Or x y) i1 x `shouldBe` i1
    reduce' (Or i0 y) i1 y `shouldBe` i1
    reduce' (Or x i0) i1 x `shouldBe` i1
    reduce' (Or i1 i2) i0 x `shouldBe` err (unhandledCase loc0 i2 i0)
    reduce' (Or x y) (Fun a b) x `shouldBe` Or (Fun a b) (letP (y, Fun a b) x)
    reduce' (Or x y) z x `shouldBe` Or z (letP (y, z) x)
    reduce' (Or x y) z z `shouldBe` Or z (letP (y, z) z)
    reduce' i1 (Or x y) x `shouldBe` i1
    reduce' i1 (Or i0 y) y `shouldBe` i1
    reduce' i1 (Or x i0) x `shouldBe` i1
    reduce' i0 (Or i1 i2) x `shouldBe` err (unhandledCase loc0 i0 i2)
    reduce' (Fun a b) (Or x y) x `shouldBe` Or (Fun a b) (letP (Fun a b, y) x)
    reduce' z (Or x y) x `shouldBe` Or x (letP (z, y) x)
    reduce' z (Or x y) z `shouldBe` Or x (letP (z, y) z)
    reduce' (Fun x y) i1 x `shouldBe` err (unhandledCase loc0 (Fun x y) i1)
    reduce' (Fun x y) a x `shouldBe` x
    reduce' (Fun x y) a a `shouldBe` Fun x y
    reduce' (Fun x y) (Fun a b) x `shouldBe` a
    reduce' (Fun x y) (Fun a b) y `shouldBe` b
    reduce' (App x y) i1 x `shouldBe` err (unhandledCase loc0 (App x y) i1)
    reduce' (App x y) a x `shouldBe` x
    reduce' (App x y) a a `shouldBe` App x y
    reduce' (App x y) (App a b) x `shouldBe` a
    reduce' (App x y) (App a b) y `shouldBe` b
    reduce' (Call "f" x) i1 x `shouldBe` err (unhandledCase loc0 (Call "f" x) i1)
    reduce' (Call "f" x) a x `shouldBe` x
    reduce' (Call "f" x) a a `shouldBe` Call "f" x
    reduce' (Call "f" x) (Call "f" a) x `shouldBe` a
    -- TODO: Is this a reasonable behavior? Should this fail?
    --       A real world example would help to clarify this.
    -- reduce' (Call "f" x) (Call "g" a) x `shouldBe` err (unhandledCase (Call "f" x) (Call "g" a))
    reduce' (Call "f" x) (Call "g" a) x `shouldBe` letP (Call "f" x, Call "g" a) x
    reduce' (Let [] x) i1 x `shouldBe` i1
    reduce' (Let [("x", i0)] x) i1 x `shouldBe` err (unhandledCase loc0 i0 i1)
    reduce' (Let [] x) a x `shouldBe` a
    reduce' (Let [] x) a a `shouldBe` a
    reduce' (Meta (Comments []) x) i1 x `shouldBe` i1
    reduce' (Meta (Comments []) x) a x `shouldBe` a
    reduce' (Meta (Comments []) x) a a `shouldBe` a
    reduce' Err i1 x `shouldBe` err (unhandledCase loc0 Err i1)
    reduce' Err a x `shouldBe` x
    reduce' Err a a `shouldBe` Err
    reduce' Err Err x `shouldBe` x

  it "☯ Core.reduce.App.Fun -- pattern matching lazy reduce" $ do
    let ops = [("and", \_ a -> Just (And a a))]
    let reduce' a b c = reduce ops (App (Fun a c) b)
    reduce' (And x x) (App a b) x `shouldBe` letP (And x x, App a b) x
    reduce' (And x x) (App (Fun a (And a a)) b) x `shouldBe` b
    reduce' (And x x) (Call "f" b) x `shouldBe` letP (And x x, Call "f" b) x
    reduce' (And x x) (Call "and" b) x `shouldBe` b
    reduce' (And x x) (Let [("a", b)] (And a a)) x `shouldBe` b
    reduce' (And x x) (Meta (Comments []) (And b b)) x `shouldBe` b

  it "☯ Core.reduce.App.For -- generics" $ do
    let env = [("f", For "x" (Fun (Ann x IntT) Unit))]
    let reduce' a = reduce ops (Let env a)
    reduce' (Var "f") `shouldBe` For "x" (Fun (Ann x IntT) Unit)
    reduce' (App f (Ann y IntT)) `shouldBe` Unit
    reduce' (App f (Ann y NumT)) `shouldBe` err (unhandledCase loc0 IntT NumT)

  it "☯ Core.reduce.App.Fix -- recursion" $ do
    let appFix x a b = reduce [] (App (Fix x a) b)
    "" `shouldBe` ""

  it "☯ Core.reduce.overload" $ do
    reduce ops (App (Fun (Int 3 `Ann` IntT) Unit `Or` Any) (Call "int_add" (And i1 i2 `Ann` And IntT IntT) `Ann` IntT)) `shouldBe` Unit

  it "☯ Core.eval.swap" $ do
    eval ops (letP (And x y, And i1 i2) (And y x)) `shouldBe` And i2 i1

  it "☯ Core.eval.add" $ do
    eval ops (Call "int_add" (And i1 i2)) `shouldBe` Int 3
    eval ops (letP (And x y, And i1 i2) (Call "int_add" (And x y))) `shouldBe` Int 3

  -- it "☯ Core.unify" $ do
  --   let unify' = unify [] [("x", Any), ("a", a)]
  --   unify' Any Any `shouldBe` Right (Any, [])
  --   unify' Any Unit `shouldBe` Right (Unit, [])
  --   unify' Unit Any `shouldBe` Right (Unit, [])
  --   unify' Unit Unit `shouldBe` Right (Unit, [])
  --   unify' Unit IntT `shouldBe` Left (typeMismatch Unit IntT)
  --   unify' IntT IntT `shouldBe` Right (IntT, [])
  --   unify' NumT NumT `shouldBe` Right (NumT, [])
  --   unify' (Int 1) (Int 1) `shouldBe` Right (Int 1, [])
  --   unify' (Int 1) (Int 2) `shouldBe` Left (typeMismatch i1 i2)
  --   unify' (Num 1.1) (Num 1.1) `shouldBe` Right (Num 1.1, [])
  --   unify' (Num 1.1) (Num 2.2) `shouldBe` Left (typeMismatch (Num 1.1) (Num 2.2))
  --   unify' (Var "x") (Var "x") `shouldBe` Right (x, [])
  --   unify' (Var "x") (Var "y") `shouldBe` Right (y, [("x", y)])
  --   unify' (Var "x") (Var "a") `shouldBe` Right (a, [("x", a)])
  --   unify' (Var "y") (Var "x") `shouldBe` Right (x, [("y", x)])
  --   unify' (Var "a") (Var "x") `shouldBe` Right (a, [("x", a)])
  --   unify' (Var "x") (Int 1) `shouldBe` Right (i1, [("x", i1)])
  --   unify' (Var "a") (Int 1) `shouldBe` Right (a, [])
  --   unify' (Int 1) (Var "x") `shouldBe` Right (i1, [("x", i1)])
  --   unify' (Int 1) (Var "a") `shouldBe` Right (a, [])
  --   unify' (Tag "A" x) (Tag "A" i1) `shouldBe` Right (Tag "A" i1, [("x", i1)])
  --   unify' (Tag "A" x) (Tag "B" i1) `shouldBe` Left (typeMismatch (Tag "A" x) (Tag "B" i1))
  --   unify' (For "b" x) i1 `shouldBe` Right (i1, [("x", i1), ("b", b)])
  --   unify' (For "b" a) i1 `shouldBe` Right (a, [("b", b)])
  --   unify' (For "b" b) i1 `shouldBe` Right (For "b" b, [("b", b)])
  --   unify' i1 (For "b" x) `shouldBe` Right (i1, [("x", i1), ("b", b)])
  --   unify' i1 (For "b" a) `shouldBe` Right (a, [("b", b)])
  --   unify' i1 (For "b" b) `shouldBe` Right (For "b" b, [("b", b)])
  --   unify' (For "y" y) (For "z" z) `shouldBe` Right (For "z" z, [("z", z)])
  --   -- TODO: Fix
  --   -- TODO: Ann
  --   unify' (And x a) (And i1 i2) `shouldBe` Right (And i1 a, [("x", i1)])
  --   -- TODO: Or
  --   unify' (Fun x a) (Fun i1 i2) `shouldBe` Right (Fun i1 a, [("x", i1)])
  --   -- TODO: App
  --   -- TODO: Call
  --   -- TODO: Let
  --   -- TODO: Meta
  --   unify' Err Err `shouldBe` Right (Err, [])

  -- it "☯ Core.unify.GADT" $ do
  --   "" `shouldBe` ""

  -- it "☯ Core.infer" $ do
  --   let (xT, aT) = (Var "xT", Var "aT")
  --   let (x1, y2) = (("x", i1), ("y", n2))
  --   let infer' = infer []
  --   infer' [] Any `shouldBe` Right ((Any, Var "_1"), [("_1", Any)])
  --   infer' [] Unit `shouldBe` Right ((Unit, Unit), [])
  --   infer' [] IntT `shouldBe` Right ((IntT, IntT), [])
  --   infer' [] NumT `shouldBe` Right ((NumT, NumT), [])
  --   infer' [] (Int 1) `shouldBe` Right ((Int 1, IntT), [])
  --   infer' [] (Num 1.1) `shouldBe` Right ((Num 1.1, NumT), [])
  --   infer' [] (Var "x") `shouldBe` Left (undefinedVar "x")
  --   infer' [("x", i1)] (Var "x") `shouldBe` Right ((x, IntT), [])
  --   infer' [("x", Any)] (Var "x") `shouldBe` Right ((x, xT), [("xT", Any), ("x", Ann x xT)])
  --   infer' [("a", a)] (Var "a") `shouldBe` Right ((a, aT), [("aT", aT), ("a", Ann a aT)])
  --   infer' [x1] (Tag "A" x) `shouldBe` Right ((Tag "A" x, Tag "A" IntT), [])
  --   infer' [] (For "a" a) `shouldBe` Right ((For "a" a, aT), [("aT", aT), ("a", Ann a aT)])
  --   infer' [x1] (For "a" x) `shouldBe` Right ((x, IntT), [("a", a)])
  --   -- TODO: Fix
  --   infer' [x1] (Ann x y) `shouldBe` Right ((x, IntT), [("y", IntT)])
  --   infer' [x1, y2] (And x y) `shouldBe` Right ((And x y, And IntT NumT), [])
  --   infer' [x1, y2] (Or x y) `shouldBe` Right ((Or x y, Or IntT NumT), [])
  --   infer' [x1] (Or x x) `shouldBe` Right ((x, IntT), [])
  --   infer' [x1] (Or x y) `shouldBe` Right ((x, IntT), [])
  --   infer' [x1] (Or y x) `shouldBe` Right ((x, IntT), [])
  --   infer' [x1] (Or y z) `shouldBe` Left (undefinedVar "z")
  --   infer' [x1, y2] (Fun x y) `shouldBe` Right ((Fun (Ann x IntT) (Ann y NumT), Fun IntT NumT), [])
  --   infer' [] (For "x" (Fun x x)) `shouldBe` Right ((for ["x", "xT"] (Fun (Ann x xT) (Ann x xT)), Fun xT xT), [("xT", xT), ("x", Ann x xT)])
  --   infer' [("x", Any), y2] (App x y) `shouldBe` Right ((App x (Ann y NumT), Any), [("x", Ann x (Fun NumT Any))])
  --   infer' [("x", x), y2] (App x y) `shouldBe` Right ((App x (Ann y NumT), Any), [("x", Ann x (Fun NumT Any))])
  --   infer' [x1] (App (Fun i1 n1) x) `shouldBe` Right ((App (Fun (Ann i1 IntT) (Ann n1 NumT)) (Ann x IntT), NumT), [])
  --   infer' [x1] (App (Fun n1 i1) x) `shouldBe` Left (typeMismatch NumT IntT)
  --   infer' [x1] (App (For "a" $ Fun a a) x) `shouldBe` Right ((App (For "a" $ Fun (Ann a IntT) (Ann a IntT)) (Ann x IntT), IntT), [("a", Ann a IntT)])
  --   -- @x y. (x, y) -> (<) (y, x) : @a. (a, a) -> Bool
  --   -- TODO: App
  --   -- TODO: Call
  --   infer' [] (Let [x1] x) `shouldBe` Right ((Let [x1] x, IntT), [])
  --   infer' [("x", n1)] (Let [x1] x) `shouldBe` Right ((Let [x1] x, IntT), [])
  --   -- TODO: Meta
  --   infer' [] Err `shouldBe` Right ((Err, Err), [])

  -- it "☯ Core.check" $ do
  --   let check' = check []
  --   -- Any
  --   -- Unit
  --   -- IntT
  --   -- NumT
  --   -- Int Int
  --   -- Num Double
  --   check' [("x", Any)] x IntT `shouldBe` Right ((x, IntT), [("x", Ann x IntT)])
  --   check' [("x", x)] x IntT `shouldBe` Right ((x, IntT), [("x", Ann x IntT)])
  --   -- Tag String Expr
  --   check' [("a", a)] (Fun a a) (Fun IntT IntT) `shouldBe` Right ((Fun (Ann a IntT) (Ann a IntT), Fun IntT IntT), [("a", Ann a IntT)])
  --   check' [("a", a)] (Fun a a) (Fun IntT Any) `shouldBe` Right ((Fun (Ann a IntT) (Ann a IntT), Fun IntT IntT), [("a", Ann a IntT)])
  --   -- check' [("a", a)] (Fun a a) (Fun Any IntT) `shouldBe` Right ((Fun (Ann a IntT) (Ann a IntT), Fun IntT IntT), [("a", Ann a IntT)])
  --   -- For String Expr
  --   -- Fix String Expr
  --   -- Ann Expr Type
  --   check' [] (Or i1 i2) IntT `shouldBe` Right ((Or (Ann i1 IntT) (Ann i2 IntT), IntT), [])
  --   check' [] (Or i1 n2) IntT `shouldBe` Right ((i1, IntT), [])
  --   check' [] (Or n1 i2) IntT `shouldBe` Right ((i2, IntT), [])
  --   check' [("x", x), ("y", y)] (Or x y) IntT `shouldBe` Right ((Or (Ann x IntT) (Ann y IntT), IntT), [])
  --   check' [("x", x)] x (Or IntT NumT) `shouldBe` Right ((x, Or IntT NumT), [])
  --   -- check' [("x", x)] (Or n1 i2) IntT `shouldBe` Right ((i2, IntT), [])
  --   -- Or Expr Expr
  --   -- Fun Expr Expr
  --   -- App Expr Expr
  --   -- Call String [Expr]
  --   -- Let [(String, Expr)] Expr
  --   -- Meta (Metadata Expr) Expr
  --   -- Err
  --   "" `shouldBe` ""

  -- it "☯ Core.check.GADT" $ do
  --   "" `shouldBe` ""

  it "☯ Core.type.unify" $ do
    unify loc0 [] [] (Any, Any) `shouldBe` Ok [(Any, [])]
    unify loc0 [] [] (Any, Unit) `shouldBe` Ok [(Unit, [])]
    unify loc0 [] [] (Unit, Any) `shouldBe` Ok [(Unit, [])]
    unify loc0 [] [] (Unit, Unit) `shouldBe` Ok [(Unit, [])]
    unify loc0 [] [] (Unit, IntT) `shouldBe` Fail [typeMismatch loc0 Unit IntT]
    unify loc0 [] [] (IntT, IntT) `shouldBe` Ok [(IntT, [])]
    unify loc0 [] [] (NumT, NumT) `shouldBe` Ok [(NumT, [])]
    unify loc0 [] [] (Int 1, Int 1) `shouldBe` Ok [(Int 1, [])]
    unify loc0 [] [] (Int 1, Int 2) `shouldBe` Fail [typeMismatch loc0 i1 i2]
    unify loc0 [] [] (Num 1.1, Num 1.1) `shouldBe` Ok [(Num 1.1, [])]
    unify loc0 [] [] (Num 1.1, Num 2.2) `shouldBe` Fail [typeMismatch loc0 (Num 1.1) (Num 2.2)]
    let env = [("x", Any), ("a", a)]
    unify loc0 [] env (Var "x", Var "x") `shouldBe` Ok [(x, [])]
    unify loc0 [] env (Var "x", Var "y") `shouldBe` Ok [(y, [("x", y)])]
    unify loc0 [] env (Var "x", Var "a") `shouldBe` Ok [(a, [("x", a)])]
    unify loc0 [] env (Var "y", Var "x") `shouldBe` Ok [(x, [("y", x)])]
    -- unify loc0 [] env (Var "a", Var "x") `shouldBe` Ok [(a, [("x", a)])]
    unify loc0 [] env (Var "x", Int 1) `shouldBe` Ok [(i1, [("x", i1)])]
    -- unify loc0 [] env (Var "a", Int 1) `shouldBe` Ok [(a, [])]
    unify loc0 [] env (Var "x", And x x) `shouldBe` Fail [occursError loc0 "x" (And x x)]
    unify loc0 [] env (Int 1, Var "x") `shouldBe` Ok [(i1, [("x", i1)])]
    -- unify loc0 [] env (Int 1, Var "a") `shouldBe` Ok [(a, [])]
    unify loc0 [] [] (Tag "A" x, Tag "A" i1) `shouldBe` Ok [(Tag "A" i1, [("x", i1)])]
    unify loc0 [] [] (Tag "A" x, Tag "B" i1) `shouldBe` Fail [typeMismatch loc0 (Tag "A" x) (Tag "B" i1)]
    let tdef = For "x" $ Fun x $ Or (For "y" $ Fun (Tag "A" y) (Tag "T1" (And x y))) (For "z" $ Fun (Tag "B" z) (Tag "T2" (And x z)))
    let env = [("T", tdef)]
    unify loc0 [] env (Tag "A" i1, Tag "T" i2) `shouldBe` Ok [(Tag "T1" (And i2 i1), [("T$1", Tag "T1" (And (Ann i2 IntT) i1)), ("y", i1), ("x", Ann i2 IntT), ("T", tdef)])]
    unify loc0 [] env (Tag "B" i1, Tag "T" i2) `shouldBe` Ok [(Tag "T2" (And i2 i1), [("T$1", Tag "T2" (And (Ann i2 IntT) i1)), ("z", i1), ("x", Ann i2 IntT), ("T", tdef)])]
    unify loc0 [] env (Tag "T" i1, Tag "A" i2) `shouldBe` Ok [(Tag "T1" (And i1 i2), [("T$1", Tag "T1" (And (Ann i1 IntT) i2)), ("y", i2), ("x", Ann i1 IntT), ("T", tdef)])]
    unify loc0 [] env (Tag "T" i1, Tag "B" i2) `shouldBe` Ok [(Tag "T2" (And i1 i2), [("T$1", Tag "T2" (And (Ann i1 IntT) i2)), ("z", i2), ("x", Ann i1 IntT), ("T", tdef)])]
    unify loc0 [] [] (For "a" x, i1) `shouldBe` Ok [(i1, [("x", i1)])]
    -- unify loc0 [] [] (For "a" a, i1) `shouldBe` Ok [(For "a" a, [])]
    unify loc0 [] [] (For "a" a, i1) `shouldBe` Ok [(i1, [("a", i1)])]
    unify loc0 [] [] (i1, For "a" x) `shouldBe` Ok [(i1, [("x", i1)])]
    -- unify loc0 [] [] (i1, For "a" a) `shouldBe` Ok [(For "a" a, [])]
    unify loc0 [] [] (For "a" a, For "b" b) `shouldBe` Ok [(For "b" b, [("a", For "b" b)])]
    -- TODO: test Fix
    -- unify loc0 [] [] (Fix "a" x, i1) `shouldBe` Ok [(i1, [("x", i1)])]
    -- unify loc0 [] [] (Fix "a" a, i1) `shouldBe` Ok [(Fix "a" a, [])]
    -- unify loc0 [] [] (i1, Fix "a" x) `shouldBe` Ok [(i1, [("x", i1)])]
    -- unify loc0 [] [] (i1, Fix "a" a) `shouldBe` Ok [(Fix "a" a, [])]
    -- unify loc0 [] [] (i1, Fix "a" a) `shouldBe` Ok [(i1, [("a", i1)])]
    -- unify loc0 [] [] (Fix "a" a, Fix "a" i1) `shouldBe` Ok [(i1, [("a", i1)])]
    -- unify loc0 [] [] (Fix "a" a, Fix "a" a) `shouldBe` Ok [(Fix "a" a, [])]
    -- unify loc0 [] [] (Fix "a" a, Fix "b" b) `shouldBe` Ok [(Fix "b" b, [])]
    unify loc0 [] [] (Ann x y, Ann i1 IntT) `shouldBe` Ok [(Ann i1 IntT, [("y", IntT), ("x", i1)])]
    unify loc0 [] [] (Ann i1 IntT, x) `shouldBe` Ok [(Ann i1 IntT, [("x", Ann i1 IntT)])]
    unify loc0 [] [] (Ann x IntT, i1) `shouldBe` Ok [(i1, [("x", i1)])]
    unify loc0 [] [] (x, Ann i1 IntT) `shouldBe` Ok [(Ann i1 IntT, [("x", Ann i1 IntT)])]
    unify loc0 [] [] (i1, Ann x IntT) `shouldBe` Ok [(i1, [("x", i1)])]
    unify loc0 [] [] (And x y, And i1 i2) `shouldBe` Ok [(And i1 i2, [("y", i2), ("x", i1)])]
    unify loc0 [] [] (Or i1 i2, Any) `shouldBe` Ok [(i1, []), (i2, [])]
    unify loc0 [] [] (Or i1 i2, x) `shouldBe` Ok [(i1, [("x", i1)]), (i2, [("x", i2)])]
    unify loc0 [] [] (Or i1 i1, x) `shouldBe` Ok [(i1, [("x", i1)])]
    unify loc0 [] [] (Or i1 i2, i0) `shouldBe` Fail [typeMismatch loc0 i1 i0, typeMismatch loc0 i2 i0]
    unify loc0 [] [] (Any, Or i1 i2) `shouldBe` Ok [(i1, []), (i2, [])]
    unify loc0 [] [] (x, Or i1 i2) `shouldBe` Ok [(i1, [("x", i1)]), (i2, [("x", i2)])]
    unify loc0 [] [] (x, Or i1 i1) `shouldBe` Ok [(i1, [("x", i1)])]
    unify loc0 [] [] (i0, Or i1 i2) `shouldBe` Fail [typeMismatch loc0 i0 i1, typeMismatch loc0 i0 i2]
    unify loc0 [] [] (Fun x y, Fun i1 i2) `shouldBe` Ok [(Fun i1 i2, [("y", i2), ("x", i1)])]
    unify loc0 [] [] (App x y, App z i2) `shouldBe` Ok [(App z i2, [("y", i2), ("x", z)])]
    unify loc0 [] [] (Call "f" x, Call "f" i1) `shouldBe` Ok [(Call "f" i1, [("x", i1)])]
    unify loc0 [] [] (Call "f" x, Call "g" i1) `shouldBe` Fail [typeMismatch loc0 (Call "f" x) (Call "g" i1)]
    -- TODO: Let
    unify loc0 [] [] (Meta (Comments []) i1, x) `shouldBe` Ok [(i1, [("x", i1)])]
    unify loc0 [] [] (x, Meta (Comments []) i1) `shouldBe` Ok [(i1, [("x", i1)])]
    unify loc0 [] [] (Err, Err) `shouldBe` Ok [(Err, [])]

  it "☯ Core.type.infer" $ do
    let (xT, aT) = (Var "xT", Var "aT")
    infer loc0 [] [] Any `shouldBe` Ok [((Any, Var "_1"), [("_1", Var "_1")])]
    infer loc0 [] [] Unit `shouldBe` Ok [((Unit, Unit), [])]
    infer loc0 [] [] IntT `shouldBe` Ok [((IntT, IntT), [])]
    infer loc0 [] [] NumT `shouldBe` Ok [((NumT, NumT), [])]
    infer loc0 [] [] (Int 1) `shouldBe` Ok [((Int 1, IntT), [])]
    infer loc0 [] [] (Num 1.1) `shouldBe` Ok [((Num 1.1, NumT), [])]
    infer loc0 [] [] (Var "x") `shouldBe` Fail [undefinedVar loc0 "x"]
    -- TODO: does this work when inferring generic functions?
    -- infer' [] [("x", i1)] (Var "x") `shouldBe` Ok [((x, IntT), [("x", Ann x IntT)])]
    infer loc0 [] [("x", i1)] (Var "x") `shouldBe` Ok [((x, IntT), [])]
    infer loc0 [] [("a", a)] (Var "a") `shouldBe` Ok [((a, aT), [("aT", aT), ("a", Ann a aT)])]
    infer loc0 [] [] (Tag "A" i1) `shouldBe` Ok [((Tag "A" i1, Tag "A" IntT), [])]
    infer loc0 [] [] (For "a" a) `shouldBe` Ok [((For "a" a, aT), [("aT", aT), ("a", Ann a aT)])]
    infer loc0 [] [] (For "a" i1) `shouldBe` Ok [((i1, IntT), [("aT", aT), ("a", Ann a aT)])]
    infer loc0 [] [] (Fix "a" a) `shouldBe` Ok [((Fix "a" a, aT), [("aT", aT), ("a", Ann a aT)])]
    infer loc0 [] [] (Fix "a" i1) `shouldBe` Ok [((i1, IntT), [])]
    infer loc0 [] [] (Ann i1 IntT) `shouldBe` Ok [((i1, IntT), [])]
    infer loc0 [] [] (And i1 n2) `shouldBe` Ok [((And i1 n2, And IntT NumT), [])]
    infer loc0 [] [] (Or i1 n2) `shouldBe` Ok [((i1, IntT), []), ((n2, NumT), [])]
    infer loc0 [] [] (Or i1 i1) `shouldBe` Ok [((i1, IntT), [])]
    infer loc0 [] [] (Or x i1) `shouldBe` Ok [((i1, IntT), [])]
    infer loc0 [] [] (Or i1 y) `shouldBe` Ok [((i1, IntT), [])]
    infer loc0 [] [] (Or x y) `shouldBe` Fail [undefinedVar loc0 "x", undefinedVar loc0 "y"]
    infer loc0 [] [] (Fun i1 n2) `shouldBe` Ok [((Fun (Ann i1 IntT) (Ann n2 NumT), Fun IntT NumT), [])]
    infer loc0 [] [("f", f)] (App f i1) `shouldBe` Ok [((App f (Ann i1 IntT), Any), [("f", Ann f (Fun IntT Any))])]
    infer loc0 [] [] (App (Fun i1 n2) i2) `shouldBe` Ok [((App (Fun (Ann i1 IntT) (Ann n2 NumT)) (Ann i2 IntT), NumT), [])]
    infer loc0 [] [] (App (Fun n1 i2) i1) `shouldBe` Fail [typeMismatch loc0 NumT IntT]
    -- infer loc0 [] [("x", i1)] (App (For "a" $ Fun a a) x) `shouldBe` Ok [((App (For "a" $ Fun (Ann a IntT) (Ann a IntT)) (Ann x IntT), IntT), [("a", Ann a IntT), ("aT", IntT)])]
    -- @x y. (x, y) -> (<) (y, x) : @a. (a, a) -> Bool
    -- TODO: App
    -- TODO: Call
    -- infer loc0 [] [] (Let [x1] x) `shouldBe` Ok ((Let [x1] x, IntT), [])
    -- infer loc0 [] [("x", n1)] (Let [x1] x) `shouldBe` Ok ((Let [x1] x, IntT), [])
    -- TODO: Meta
    infer loc0 [] [] Err `shouldBe` Ok [((Err, Err), [])]

  it "☯ Core.type.check" $ do
    let xT = Var "xT"
    check loc0 [] [] (Any, IntT) `shouldBe` Ok [((Any, IntT), [("_1", IntT)])]
    check loc0 [] [] (i1, Any) `shouldBe` Ok [((i1, IntT), [])]
    check loc0 [] [] (Unit, Unit) `shouldBe` Ok [((Unit, Unit), [])]
    check loc0 [] [] (Unit, IntT) `shouldBe` Fail [typeMismatch loc0 Unit IntT]
    check loc0 [] [] (IntT, IntT) `shouldBe` Ok [((IntT, IntT), [])]
    check loc0 [] [] (NumT, NumT) `shouldBe` Ok [((NumT, NumT), [])]
    check loc0 [] [] (Int 1, IntT) `shouldBe` Ok [((i1, IntT), [])]
    check loc0 [] [] (Num 1.1, NumT) `shouldBe` Ok [((n1, NumT), [])]
    check loc0 [] [] (Var "x", IntT) `shouldBe` Fail [undefinedVar loc0 "x"]
    check loc0 [] [("x", i1)] (Var "x", Any) `shouldBe` Ok [((x, IntT), [])]
    check loc0 [] [("x", x)] (Var "x", Any) `shouldBe` Ok [((x, xT), [("xT", xT), ("x", Ann x xT)])]
    check loc0 [] [("x", x)] (Var "x", IntT) `shouldBe` Ok [((x, IntT), [("x", Ann x IntT)])]
    check loc0 [] [("x", Ann x Any)] (Var "x", IntT) `shouldBe` Ok [((x, IntT), [("x", Ann x IntT)])]
    let tdef = For "x" $ Fun x $ Or (For "y" $ Fun (Tag "A" y) (Tag "T1" (And x y))) (For "z" $ Fun (Tag "B" z) (Tag "T2" (And x z)))
    let env = [("T", tdef)]
    check loc0 [] env (Tag "A" i1, Tag "A" Any) `shouldBe` Ok [((Tag "A" i1, Tag "A" IntT), [])]
    check loc0 [] env (Tag "A" i1, Tag "B" Any) `shouldBe` Fail [typeMismatch loc0 (Tag "A" IntT) (Tag "B" Any)]
    check loc0 [] env (Tag "A" i1, Tag "T" i2) `shouldBe` Ok [((Tag "A" i1, Tag "T1" (And i2 IntT)), [("T$1", Tag "T1" (And (Ann i2 IntT) IntT)), ("y", IntT), ("x", Ann i2 IntT), ("T", tdef)])]
    check loc0 [] env (Tag "B" i1, Tag "T" i2) `shouldBe` Ok [((Tag "B" i1, Tag "T2" (And i2 IntT)), [("T$1", Tag "T2" (And (Ann i2 IntT) IntT)), ("z", IntT), ("x", Ann i2 IntT), ("T", tdef)])]
    check loc0 [] env (Tag "C" i1, Tag "T" i2) `shouldBe` Fail [typeMismatch loc0 (Tag "A" y) (Tag "C" IntT), typeMismatch loc0 (Tag "B" z) (Tag "C" IntT)]
    check loc0 [] env (Tag "T" i1, Tag "T" i2) `shouldBe` Fail [typeMismatch loc0 IntT i2]
    check loc0 [] env (Tag "T" i1, Tag "T" IntT) `shouldBe` Ok [((Tag "T" i1, Tag "T" IntT), [])]
    -- TODO: Does this make sense? Should it not be allowed?
    check loc0 [] env (Tag "T" i1, Tag "A" i2) `shouldBe` Ok [((Tag "T" i1, Tag "T1" (And IntT i2)), [("T$1", Tag "T1" (And (Ann IntT IntT) i2)), ("y", i2), ("x", Ann IntT IntT), ("T", tdef)])]
    -- For String Expr
    -- Fix String Expr
    -- Ann Expr Type
    check loc0 [] [] (And i1 n2, And a b) `shouldBe` Ok [((And i1 n2, And IntT NumT), [("b", NumT), ("a", IntT)])]
    -- check loc0 [] (Or i1 i2) IntT `shouldBe` Ok ((Or (Ann i1 IntT) (Ann i2 IntT), IntT), [])
    -- check loc0 [] (Or i1 n2) IntT `shouldBe` Ok ((i1, IntT), [])
    -- check loc0 [] (Or n1 i2) IntT `shouldBe` Ok ((i2, IntT), [])
    -- check loc0 [("x", x), ("y", y)] (Or x y) IntT `shouldBe` Ok ((Or (Ann x IntT) (Ann y IntT), IntT), [])
    -- check loc0 [("x", x)] x (Or IntT NumT) `shouldBe` Ok ((x, Or IntT NumT), [])
    -- check loc0 [("x", x)] (Or n1 i2) IntT `shouldBe` Ok ((i2, IntT), [])
    check loc0 [] [] (Fun i1 n2, Fun a b) `shouldBe` Ok [((Fun (Ann i1 IntT) (Ann n2 NumT), Fun IntT NumT), [("b", NumT), ("a", IntT)])]
    -- let env = [("x", x), ("y", y), ("a", a), ("b", b)]
    -- check loc0 [] env (for ["x", "y"] $ Fun x y, for ["a", "b"] $ Fun a b) `shouldBe` Ok []
    check loc0 [] [("f", f)] (App f i1, NumT) `shouldBe` Ok [((App f (Ann i1 IntT), NumT), [("f", Ann f (Fun IntT NumT))])]
    -- App Expr Expr
    -- Call String [Expr]
    -- Let [(String, Expr)] Expr
    -- Meta (Metadata Expr) Expr
    check loc0 [] [] (Err, Err) `shouldBe` Ok [((Err, Err), [])]
