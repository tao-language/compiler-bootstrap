module TaoLangTests where

import Parser
import Tao
import TaoLang
import Test.Hspec

taoLangTests :: SpecWith ()
taoLangTests = describe "--==☯ Tao language ☯==--" $ do
  -- let (a, b) = (Var "a", Var "b")
  -- let (x, y, z) = (Var "x", Var "y", Var "z")
  -- let (x', y', z') = (VarP "x", VarP "y", VarP "z")
  -- let indent = "  "
  -- let parse' src parser = case Parser.parse src parser of
  --       Right x -> Just x
  --       Left _ -> Nothing

  -- it "☯ keyword" $ do
  --   let keyword' src = parse' src (keyword True "A")
  --   keyword' "A" `shouldBe` Just True
  --   keyword' "ABC" `shouldBe` Nothing
  --   keyword' "A2" `shouldBe` Nothing
  --   keyword' "A_" `shouldBe` Nothing
  --   keyword' "A'" `shouldBe` Nothing

  -- it "☯ identifier" $ do
  --   parse' "" (identifier lowercase) `shouldBe` Nothing
  --   parse' "a" (identifier lowercase) `shouldBe` Just "a"
  --   parse' "a1" (identifier lowercase) `shouldBe` Just "a1"
  --   parse' "_a1" (identifier lowercase) `shouldBe` Just "_a1"

  -- it "☯ comment" $ do
  --   let comment' src = parse' src comment
  --   comment' "" `shouldBe` Nothing
  --   comment' "--my comment" `shouldBe` Just "my comment"
  --   comment' "-- my comment" `shouldBe` Just "my comment"
  --   comment' "--   my  comment  " `shouldBe` Just "  my  comment  "

  -- it "☯ emptyLine" $ do
  --   let emptyLine' src = parse' src emptyLine
  --   emptyLine' "" `shouldBe` Nothing
  --   emptyLine' "\n" `shouldBe` Just ""
  --   emptyLine' "  \n" `shouldBe` Just ""
  --   emptyLine' "  --my comment\n" `shouldBe` Just "my comment"
  --   emptyLine' "  -- my comment\n" `shouldBe` Just "my comment"
  --   emptyLine' "  --   my  comment  \n" `shouldBe` Just "  my  comment  "

  -- it "☯ newLine" $ do
  --   let newLine' src = parse' src (do _ <- newLine "  "; letter)
  --   newLine' "" `shouldBe` Nothing
  --   newLine' "   " `shouldBe` Nothing
  --   newLine' "\nx" `shouldBe` Nothing
  --   newLine' "\n x" `shouldBe` Nothing
  --   newLine' "\n  x" `shouldBe` Just 'x'
  --   newLine' "\n   x" `shouldBe` Nothing
  --   newLine' "\n\n   \n  x" `shouldBe` Just 'x'
  --   newLine' "\n -- comment\n  x" `shouldBe` Just 'x'

  -- it "☯ maybeNewLine" $ do
  --   let maybeNewLine' src = parse' src (maybeNewLine "  ")
  --   maybeNewLine' "" `shouldBe` Just "  "
  --   maybeNewLine' "\n" `shouldBe` Just "  "
  --   maybeNewLine' "\n  " `shouldBe` Just "  "
  --   maybeNewLine' "\n   " `shouldBe` Just "   "
  --   maybeNewLine' "\n    " `shouldBe` Just "    "

  -- it "☯ token" $ do
  --   let tokens src = parse' src (zeroOrMore (token letter))
  --   tokens "abc.d" `shouldBe` Just "abc"
  --   tokens "a b c . d" `shouldBe` Just "abc"

  -- it "☯ err" $ do
  --   let err' src = parse' src err
  --   err' "@error" `shouldBe` Just (Err "")

  -- it "☯ typT" $ do
  --   let typT' src = parse' src typT
  --   typT' "Type" `shouldBe` Just TypT

  -- it "☯ nilT" $ do
  --   let nilT' src = parse' src nilT
  --   nilT' "Nil" `shouldBe` Just NilT

  -- it "☯ nil" $ do
  --   let nil' src = parse' src nil
  --   nil' "()" `shouldBe` Just Nil
  --   nil' "( )" `shouldBe` Just Nil

  -- it "☯ intT" $ do
  --   let intT' src = parse' src intT
  --   intT' "Int" `shouldBe` Just IntT

  -- it "☯ int" $ do
  --   let int' src = parse' src int
  --   int' "42" `shouldBe` Just (Int 42)
  --   int' "-1" `shouldBe` Nothing

  -- it "☯ numT" $ do
  --   let numT' src = parse' src numT
  --   numT' "Num" `shouldBe` Just NumT

  -- it "☯ num" $ do
  --   let num' src = parse' src num
  --   num' "1.1" `shouldBe` Just (Num 1.1)
  --   num' "-1.1" `shouldBe` Nothing

  -- it "☯ sumT" $ do
  --   let sumT' src = parse' src (sumT indent)
  --   sumT' "@type T {}" `shouldBe` Just (SumT "T" [])
  --   sumT' "@type T {A:Int}" `shouldBe` Just (SumT "T" [("A", IntT)])
  --   sumT' "@type T {A:Int,}" `shouldBe` Just (SumT "T" [("A", IntT)])
  --   sumT' "@type T {A:Int,B:Num}" `shouldBe` Just (SumT "T" [("A", IntT), ("B", NumT)])
  --   sumT' "@type T {A:Int,B:Num,}" `shouldBe` Just (SumT "T" [("A", IntT), ("B", NumT)])
  --   sumT' "@type T { A : Int , B : Num , }" `shouldBe` Just (SumT "T" [("A", IntT), ("B", NumT)])

  -- it "☯ ctr" $ do
  --   let ctr' src = parse' src ctr
  --   ctr' "T.A" `shouldBe` Just (Ctr "T" "A")
  --   ctr' "T. A" `shouldBe` Nothing
  --   ctr' "T . A" `shouldBe` Nothing

  -- it "☯ var" $ do
  --   let var' src = parse' src var
  --   var' "x" `shouldBe` Just (Var "x")
  --   var' "A" `shouldBe` Just (Var "A")

  -- it "☯ for'" $ do
  --   let for_ src = parse' src for'
  --   for_ "@forall." `shouldBe` Nothing
  --   for_ "@forall x." `shouldBe` Just ["x"]
  --   for_ "@forall x y ." `shouldBe` Just ["x", "y"]

  -- it "☯ and_" $ do
  --   let and src = parse' src (and_ indent)
  --   and "()" `shouldBe` Just Nil
  --   and "(x)" `shouldBe` Just x
  --   and "(x,)" `shouldBe` Just x
  --   and "(x, y)" `shouldBe` Just (And x y)
  --   and "(x, y, z,)" `shouldBe` Just (and' [x, y, z])

  -- it "☯ term" $ do
  --   let term' src = parse' src term
  --   term' "@error" `shouldBe` Just (Err "")
  --   term' "Type" `shouldBe` Just TypT
  --   term' "Nil" `shouldBe` Just NilT
  --   term' "()" `shouldBe` Just Nil
  --   term' "Int" `shouldBe` Just IntT
  --   term' "42" `shouldBe` Just (Int 42)
  --   term' "Num" `shouldBe` Just NumT
  --   term' "3.14" `shouldBe` Just (Num 3.14)
  --   term' "x" `shouldBe` Just x

  -- it "☯ expression" $ do
  --   let expr src = parse' src (expression 0 indent)
  --   expr "@error" `shouldBe` Just (Err "")
  --   expr "Type" `shouldBe` Just TypT
  --   expr "Nil" `shouldBe` Just NilT
  --   expr "()" `shouldBe` Just Nil
  --   expr "Int" `shouldBe` Just IntT
  --   expr "42" `shouldBe` Just (Int 42)
  --   expr "Num" `shouldBe` Just NumT
  --   expr "3.14" `shouldBe` Just (Num 3.14)
  --   expr "T.A" `shouldBe` Just (Ctr "T" "A")
  --   expr "x" `shouldBe` Just x
  --   expr "@forall x. y" `shouldBe` Just (For "x" y)
  --   expr "@type T {}" `shouldBe` Just (SumT "T" [])
  --   expr "x -> y" `shouldBe` Just (FunT x y)
  --   expr "\\x -> y" `shouldBe` Just (Lam x' y)
  --   expr "x y" `shouldBe` Just (App x y)
  --   expr "(x)" `shouldBe` Just x
  --   expr "(x, y)" `shouldBe` Just (And x y)
  --   expr "x | y" `shouldBe` Just (Or x y)
  --   expr "if x then y else z" `shouldBe` Just (IfElse x y z)
  --   expr "x : y" `shouldBe` Just (Ann x y)
  --   expr "x < y" `shouldBe` Just (Lt x y)
  --   expr "x + y" `shouldBe` Just (Add x y)
  --   expr "x - y" `shouldBe` Just (Sub x y)
  --   expr "x * y" `shouldBe` Just (Mul x y)
  --   expr "@typeOf x" `shouldBe` Just (TypeOf x)

  --   -- Operator precedence.
  --   expr "x | y | z" `shouldBe` Just (Or x (Or y z))
  --   expr "x | y : z" `shouldBe` Just (Or x (Ann y z))

  --   expr "x : y | z" `shouldBe` Just (Or (Ann x y) z)
  --   expr "x : y : z" `shouldBe` Just (Ann x (Ann y z))
  --   expr "x : @forall y. z" `shouldBe` Just (Ann x (For "y" z))
  --   expr "x : \\y -> z" `shouldBe` Just (Ann x (Lam y' z))
  --   expr "x : if y then z else a" `shouldBe` Just (Ann x (IfElse y z a))

  --   expr "@forall x. y : z" `shouldBe` Just (Ann (For "x" y) z)
  --   expr "@forall x. @forall y. z" `shouldBe` Just (For "x" (For "y" z))
  --   expr "@forall x. \\y -> z" `shouldBe` Just (For "x" (Lam y' z))
  --   expr "@forall x. if y then z else a" `shouldBe` Just (For "x" (IfElse y z a))
  --   expr "@forall x. y -> z" `shouldBe` Just (For "x" (FunT y z))

  --   expr "\\x -> y : z" `shouldBe` Just (Ann (Lam x' y) z)
  --   expr "\\x -> @forall y. z" `shouldBe` Just (Lam x' (For "y" z))
  --   expr "\\x -> \\y -> z" `shouldBe` Just (Lam x' (Lam y' z))
  --   expr "\\x -> if y then z else a" `shouldBe` Just (Lam x' (IfElse y z a))
  --   expr "\\x -> y -> z" `shouldBe` Just (Lam x' (FunT y z))

  --   expr "if x then y else z : a" `shouldBe` Just (Ann (IfElse x y z) a)
  --   expr "if x then y else @forall z. a" `shouldBe` Just (IfElse x y (For "z" a))
  --   expr "if x then y else \\z -> a" `shouldBe` Just (IfElse x y (Lam z' a))
  --   expr "if x then y else if z then a else b" `shouldBe` Just (IfElse x y (IfElse z a b))
  --   expr "if x then y else z -> a" `shouldBe` Just (IfElse x y (FunT z a))

  --   expr "x -> y : z" `shouldBe` Just (Ann (FunT x y) z)
  --   expr "x -> @forall y. z" `shouldBe` Just (FunT x (For "y" z))
  --   expr "x -> \\y -> z" `shouldBe` Just (FunT x (Lam y' z))
  --   expr "x -> y -> z" `shouldBe` Just (FunT x (FunT y z))
  --   expr "x -> y < z" `shouldBe` Just (FunT x (Lt y z))

  --   expr "x < y -> z" `shouldBe` Just (FunT (Lt x y) z)
  --   expr "x < y < z" `shouldBe` Just (Lt (Lt x y) z)
  --   expr "x < y + z" `shouldBe` Just (Lt x (Add y z))
  --   expr "x < y - z" `shouldBe` Just (Lt x (Sub y z))

  --   expr "x + y < z" `shouldBe` Just (Lt (Add x y) z)
  --   expr "x + y + z" `shouldBe` Just (Add (Add x y) z)
  --   expr "x + y - z" `shouldBe` Just (Sub (Add x y) z)
  --   expr "x + y * z" `shouldBe` Just (Add x (Mul y z))

  --   expr "x - y < z" `shouldBe` Just (Lt (Sub x y) z)
  --   expr "x - y + z" `shouldBe` Just (Add (Sub x y) z)
  --   expr "x - y - z" `shouldBe` Just (Sub (Sub x y) z)
  --   expr "x - y * z" `shouldBe` Just (Sub x (Mul y z))

  --   expr "x * y + z" `shouldBe` Just (Add (Mul x y) z)
  --   expr "x * y - z" `shouldBe` Just (Sub (Mul x y) z)
  --   expr "x * y * z" `shouldBe` Just (Mul (Mul x y) z)
  --   expr "x * y z" `shouldBe` Just (Mul x (App y z))

  --   expr "x y * z" `shouldBe` Just (Mul (App x y) z)
  --   expr "x y z" `shouldBe` Just (App (App x y) z)

  --   expr "@typeOf x y" `shouldBe` Just (App (TypeOf x) y)
  --   expr "@typeOf @typeOf x" `shouldBe` Just (TypeOf (TypeOf x))

  -- it "☯ anyP" $ do
  --   let anyP' src = parse' src anyP
  --   anyP' "_" `shouldBe` Just AnyP

  -- it "☯ varP" $ do
  --   let varP' src = parse' src varP
  --   varP' "x" `shouldBe` Just x'
  --   varP' "x'" `shouldBe` Just (EqP x)

  -- it "☯ asP" $ do
  --   let asP' src = parse' src asP
  --   asP' "as x" `shouldBe` Just "x"

  -- it "☯ andP" $ do
  --   let andP_ src = parse' src (andP' indent)
  --   andP_ "()" `shouldBe` Just (EqP Nil)
  --   andP_ "(x)" `shouldBe` Just x'
  --   andP_ "(x,)" `shouldBe` Just x'
  --   andP_ "(x, y)" `shouldBe` Just (AndP x' y')
  --   andP_ "(x, y, z,)" `shouldBe` Just (andP [x', y', z'])

  -- it "☯ termP" $ do
  --   let termP' src = parse' src (termP indent)
  --   termP' "_" `shouldBe` Just AnyP
  --   termP' "@error" `shouldBe` Just (EqP (Err ""))
  --   termP' "Type" `shouldBe` Just (EqP TypT)
  --   termP' "Nil" `shouldBe` Just (EqP NilT)
  --   termP' "()" `shouldBe` Just (EqP Nil)
  --   termP' "Int" `shouldBe` Just (EqP IntT)
  --   termP' "42" `shouldBe` Just (EqP (Int 42))
  --   termP' "Num" `shouldBe` Just (EqP NumT)
  --   termP' "3.14" `shouldBe` Just (EqP (Num 3.14))
  --   termP' "x" `shouldBe` Just x'
  --   termP' "x'" `shouldBe` Just (EqP x)
  --   termP' "A" `shouldBe` Just (EqP (Var "A"))
  --   termP' "T.A" `shouldBe` Just (EqP (Ctr "T" "A"))
  --   termP' "(x)" `shouldBe` Just x'
  --   termP' "(x, y)" `shouldBe` Just (AndP x' y')

  -- it "☯ pattern'" $ do
  --   let pattern_ src = parse' src (pattern' 0 indent)
  --   pattern_ "_" `shouldBe` Just AnyP
  --   pattern_ "42" `shouldBe` Just (EqP (Int 42))
  --   pattern_ "x" `shouldBe` Just x'
  --   pattern_ "x'" `shouldBe` Just (EqP x)
  --   pattern_ "(x)" `shouldBe` Just x'
  --   pattern_ "(x, y)" `shouldBe` Just (AndP x' y')
  --   pattern_ "x | y" `shouldBe` Just (OrP x' y')
  --   pattern_ "x : y" `shouldBe` Just (AnnP x' y')
  --   pattern_ "x y" `shouldBe` Just (AppP x' y')
  --   pattern_ "x as y" `shouldBe` Just (AsP x' "y")
  --   pattern_ "x if y" `shouldBe` Just (IfP x' y)

  --   -- Operator precedence.
  --   pattern_ "x | y | z" `shouldBe` Just (OrP x' (OrP y' z'))
  --   pattern_ "x | y : z" `shouldBe` Just (OrP x' (AnnP y' z'))

  --   pattern_ "x : y | z" `shouldBe` Just (OrP (AnnP x' y') z')
  --   pattern_ "x : y : z" `shouldBe` Just (AnnP x' (AnnP y' z'))
  --   pattern_ "x : y as z" `shouldBe` Just (AnnP x' (AsP y' "z"))
  --   pattern_ "x : y if z" `shouldBe` Just (AnnP x' (IfP y' z))

  --   pattern_ "x as y : z" `shouldBe` Just (AnnP (AsP x' "y") z')
  --   pattern_ "x as y as z" `shouldBe` Just (AsP (AsP x' "y") "z")
  --   pattern_ "x as y if z" `shouldBe` Just (IfP (AsP x' "y") z)
  --   pattern_ "x as y z" `shouldBe` Just (AppP (AsP x' "y") z')

  --   pattern_ "x if y : z" `shouldBe` Just (IfP x' (Ann y z))
  --   pattern_ "x if y as z" `shouldBe` Just (AsP (IfP x' y) "z")
  --   pattern_ "x if y if z" `shouldBe` Just (IfP (IfP x' y) z)
  --   pattern_ "x if y z" `shouldBe` Just (IfP x' (App y z))

  --   pattern_ "x y as z" `shouldBe` Just (AsP (AppP x' y') "z")
  --   pattern_ "x y if z" `shouldBe` Just (IfP (AppP x' y') z)
  --   pattern_ "x y z" `shouldBe` Just (AppP (AppP x' y') z')

  -- it "☯ definition" $ do
  --   let definition' src = parse' src (definition indent)
  --   definition' "x y = a" `shouldBe` Just ([], x', Match [([y'], a)])
  --   definition' "x y = a\n x z = b" `shouldBe` Nothing
  --   definition' "x y = a\n  x z = b" `shouldBe` Just ([], x', Match [([y'], a), ([z'], b)])
  --   definition' "x y = a\n   x z = b" `shouldBe` Just ([], x', Match [([y'], a)])
  --   definition' "_ = a" `shouldBe` Just ([], AnyP, a)
  --   definition' "42 = a" `shouldBe` Just ([], EqP (Int 42), a)
  --   definition' "x = a" `shouldBe` Just ([], x', a)
  --   definition' "x' = a" `shouldBe` Just ([], EqP x, a)
  --   definition' "T.A = a" `shouldBe` Just ([], EqP (Ctr "T" "A"), a)
  --   definition' "(x) = a" `shouldBe` Just ([], x', a)
  --   definition' "(x, y) = a" `shouldBe` Just ([], AndP x' y', a)
  --   definition' "(x | y) = a" `shouldBe` Just ([], OrP x' y', a)
  --   definition' "(x : y) = a" `shouldBe` Just ([], AnnP x' y', a)
  --   definition' "(x y) = a" `shouldBe` Just ([], AppP x' y', a)
  --   definition' "(x if y) = a" `shouldBe` Just ([], IfP x' y, a)
  --   definition' "(x as y) = a" `shouldBe` Just ([], AsP x' "y", a)
  --   definition' "x : Int = a" `shouldBe` Just ([("x", IntT)], x', a)
  --   definition' "x : Int\n x = a" `shouldBe` Nothing
  --   definition' "x : Int\n  x = a" `shouldBe` Just ([("x", IntT)], x', a)
  --   definition' "x : Int\n   x = a" `shouldBe` Nothing
  --   definition' "x : Int\n  y : Num\n  (x, y) = a" `shouldBe` Just ([("x", IntT), ("y", NumT)], AndP x' y', a)

  -- it "☯ block" $ do
  --   let block' src = parse' src (block indent)
  --   block' "42" `shouldBe` Just ([], Int 42)
  --   block' "x = a; 42" `shouldBe` Just ([([], x', a)], Int 42)
  --   block' "x = a\n 42" `shouldBe` Just ([], x)
  --   block' "x = a\n  42" `shouldBe` Just ([([], x', a)], Int 42)
  --   block' "x = a\n   42" `shouldBe` Nothing
  --   block' "(x, y) = a; 42" `shouldBe` Just ([([], AndP x' y', a)], Int 42)
  --   block' "x y = a; 42" `shouldBe` Just ([([], x', Match [([y'], a)])], Int 42)
  --   block' "x = a; y = b; 42" `shouldBe` Just ([([], x', a), ([], y', b)], Int 42)
  --   block' "x : Int = a; 42" `shouldBe` Just ([([("x", IntT)], x', a)], Int 42)
  --   block' "x : Int\n  x = a; 42" `shouldBe` Just ([([("x", IntT)], x', a)], Int 42)

  -- it "☯ parseExpr" $ do
  --   parseExpr "42" `shouldBe` Right (Int 42)

  -- it "☯ parseDefinitions" $ do
  --   parseDefinitions "x = a" `shouldBe` Right [([], x', a)]
  --   parseDefinitions "x = a; y = b" `shouldBe` Right [([], x', a), ([], y', b)]
  --   parseDefinitions "x = a\ny = b" `shouldBe` Right [([], x', a), ([], y', b)]

  -- it "☯ loadBlock" $ do
  --   loadBlock "42" `shouldReturn` ([], Int 42)
  --   loadBlock "x = 1; 42" `shouldReturn` ([([], x', Int 1)], Int 42)

  -- let untypedDefs =
  --       [ ("au", Int 0),
  --         ("bu", Match [([x'], x)]),
  --         ("cu", Match [([EqP (Int 0)], Int 1), ([x'], x)]),
  --         ("du", Let ([], AndP (VarP "du") (VarP "eu"), And (Int 1) (Int 2)) (Var "du")),
  --         ("eu", Let ([], AndP (VarP "du") (VarP "eu"), And (Int 1) (Int 2)) (Var "eu"))
  --       ]
  -- let typedDefs =
  --       [ ("at", Ann (Int 0) IntT),
  --         ("bt", Ann (Match [([x'], x)]) (FunT a a)),
  --         ("ct", Ann (Match [([EqP (Int 0)], Int 1), ([x'], x)]) (FunT IntT IntT)),
  --         ("dt", Ann (Let ([("dt", IntT), ("et", IntT)], AndP (VarP "dt") (VarP "et"), And (Int 1) (Int 2)) (Var "dt")) IntT),
  --         ("et", Ann (Let ([("dt", IntT), ("et", IntT)], AndP (VarP "dt") (VarP "et"), And (Int 1) (Int 2)) (Var "et")) IntT)
  --       ]
  -- it "☯ loadFile" $ do
  --   loadFile "example/basic" "untyped.tao" `shouldReturn` untypedDefs
  --   loadFile "example/basic" "typed.tao" `shouldReturn` typedDefs

  -- it "☯ loadModule" $ do
  --   loadModule "example/basic" `shouldReturn` typedDefs ++ untypedDefs

  it "☯ TODO" $ do
    True `shouldBe` True