module TaoGrammarTests where

import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import Error
import Location (Location (Location), Position (Pos), Range (Range))
import qualified Parser as P
import TaoGrammar
import Test.Hspec

filename :: String
filename = "<TaoGrammarTests>"

parse' :: String -> Either ([String], String) (Expr, String)
parse' text = case parse 0 filename text of
  Right (a, s) -> Right (a, s.remaining)
  Left s -> Left (s.context, s.remaining)

run :: SpecWith ()
run = describe "--==☯ TaoGrammar ☯==--" $ do
  let loc r1 c1 r2 c2 = Meta (C.Loc $ Location filename (Range (Pos r1 c1) (Pos r2 c2)))
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

  let x r c = var r c "x"
  let y r c = var r c "y"
  let z r c = var r c "z"

  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")

  let def x a = Def (Var x, a)

  it "☯ Tao.Any" $ do
    let ctx = []
    let expr = any 1 1
    let (_, expr') = compile ctx "m" expr
    parse' "_ " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "_"
    C.dropMeta expr' `shouldBe` C.Ann C.Any (C.Var "_1")
    liftExpr expr' `shouldBe` Ann expr (Var "_1")
    eval ctx "m" expr `shouldBe` Any

  it "☯ Tao.Meta.Location" $ do
    let ctx = []
    let expr = Meta (C.Loc $ Location "file" (Range (Pos 1 2) (Pos 3 4))) (any 1 17)
    let (_, expr') = compile ctx "m" expr
    parse' "![:1:2,3:4] _" `shouldBe` Left (["Metadata location"], ":1:2,3:4] _")
    parse' "![file:1:2,3:4] _" `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "_"
    C.dropMeta expr' `shouldBe` C.Ann C.Any (C.Var "_1")
    liftExpr expr' `shouldBe` Ann (any 1 17) (Var "_1")
    eval ctx "m" expr `shouldBe` Any

  it "☯ Tao.Meta.Comments 1" $ do
    let ctx = []
    let expr = Meta (C.Comments ["c1"]) (any 2 1)
    let (_, expr') = compile ctx "m" expr
    parse' "# c1\n_ " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "# c1\n_"
    C.dropMeta expr' `shouldBe` C.Ann C.Any (C.Var "_1")
    liftExpr expr' `shouldBe` Ann expr (Var "_1")
    eval ctx "m" expr `shouldBe` Any

  it "☯ Tao.Meta.Comments 2" $ do
    let ctx = []
    let expr = Meta (C.Comments ["c1", "c2"]) (any 3 1)
    let (_, expr') = compile ctx "m" expr
    parse' "# c1\n# c2\n_ " `shouldBe` Right (Meta (C.Comments ["c1", "c2"]) (any 3 1), "")
    format 80 expr `shouldBe` "# c1\n# c2\n_"
    C.dropMeta expr' `shouldBe` C.Ann C.Any (C.Var "_1")
    liftExpr expr' `shouldBe` Ann expr (Var "_1")
    eval ctx "m" expr `shouldBe` Any

  -- TODO: multi-line comments

  it "☯ Tao.Meta.TrailingComment" $ do
    let ctx = []
    let expr = Meta (C.TrailingComment "c") (any 1 1)
    let (_, expr') = compile ctx "m" expr
    parse' "_ # c" `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "_  # c\n"
    C.dropMeta expr' `shouldBe` C.Ann C.Any (C.Var "_1")
    liftExpr expr' `shouldBe` Ann expr (Var "_1")
    eval ctx "m" expr `shouldBe` Any

  it "☯ Tao.IntT" $ do
    let ctx = []
    let expr = intT 1 1
    let (_, expr') = compile ctx "m" expr
    parse' "Int " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "Int"
    C.dropMeta expr' `shouldBe` C.Ann C.IntT C.IntT
    liftExpr expr' `shouldBe` Ann expr IntT
    eval ctx "m" expr `shouldBe` IntT

  it "☯ Tao.NumT" $ do
    let ctx = []
    let expr = numT 1 1
    let (_, expr') = compile ctx "m" expr
    parse' "Num " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "Num"
    C.dropMeta expr' `shouldBe` C.Ann C.NumT C.NumT
    liftExpr expr' `shouldBe` Ann expr NumT
    eval ctx "m" expr `shouldBe` NumT

  it "☯ Tao.Int" $ do
    let ctx = []
    let expr = int 1 1 42
    let (_, expr') = compile ctx "m" expr
    parse' "42 " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "42"
    C.dropMeta expr' `shouldBe` C.Ann (C.Int 42) C.IntT
    liftExpr expr' `shouldBe` Ann expr IntT
    eval ctx "m" expr `shouldBe` Int 42

  it "☯ Tao.Num" $ do
    let ctx = []
    let expr = num 1 1 3.14
    let (_, expr') = compile ctx "m" expr
    parse' "3.14 " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "3.14"
    C.dropMeta expr' `shouldBe` C.Ann (C.Num 3.14) C.NumT
    liftExpr expr' `shouldBe` Ann expr NumT
    eval ctx "m" expr `shouldBe` Num 3.14

  it "☯ Tao.Char" $ do
    let ctx = []
    let expr = char 1 1 'x'
    let (_, expr') = compile ctx "m" expr
    parse' "c'x' " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "c'x'"
    C.dropMeta expr' `shouldBe` C.Ann (C.tag "Char" [C.Int 120]) (C.tag "Char" [C.IntT])
    liftExpr expr' `shouldBe` Ann expr (Tag "Char" [IntT])
    eval ctx "m" expr `shouldBe` Char 'x'

  it "☯ Tao.Var undefined" $ do
    let ctx = []
    let expr = x 1 1
    let (_, expr') = compile ctx "m" expr
    parse' "x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x"
    C.dropMeta expr' `shouldBe` C.Ann x' (C.Err (undefinedVar "x"))
    liftExpr expr' `shouldBe` Ann expr (Err (undefinedVar "x"))
    eval ctx "m" expr `shouldBe` Var "x"

  it "☯ Tao.Var defined direct" $ do
    let ctx = [("m", [def "x" (int 10 10 42)])]
    let expr = x 1 1
    let (_, expr') = compile ctx "m" expr
    parse' "x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x"
    C.dropMeta expr' `shouldBe` C.Ann x' C.IntT
    liftExpr expr' `shouldBe` Ann expr IntT
    eval ctx "m" expr `shouldBe` Int 42

  it "☯ Tao.Var defined indirect" $ do
    let ctx = [("m", [def "y" (int 10 10 42), def "x" (y 20 20)])]
    let expr = x 1 1
    let (_, expr') = compile ctx "m" expr
    parse' "x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x"
    C.dropMeta expr' `shouldBe` C.Ann x' C.IntT
    liftExpr expr' `shouldBe` Ann expr IntT
    eval ctx "m" expr `shouldBe` Int 42

  it "☯ Tao.Tag 0" $ do
    let ctx = []
    let expr = tag 1 1 "A" []
    let (_, expr') = compile ctx "m" expr
    parse' "A " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "A"
    C.dropMeta expr' `shouldBe` C.Ann (C.Tag "A") (C.Tag "A")
    liftExpr expr' `shouldBe` Ann expr (Tag "A" [])
    eval ctx "m" expr `shouldBe` Tag "A" []

  it "☯ Tao.Tag 1" $ do
    let ctx = [("m", [def "x" (int 10 10 42)])]
    let expr = tag 1 1 "A" [x 1 3]
    let (_, expr') = compile ctx "m" expr
    parse' "A x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "A x"
    C.dropMeta expr' `shouldBe` C.Ann (C.and' [C.Tag "A", x']) (C.and' [C.Tag "A", C.IntT])
    liftExpr expr' `shouldBe` Ann expr (Tag "A" [IntT])
    eval ctx "m" expr `shouldBe` Tag "A" [Int 42]

  it "☯ Tao.Tag 2" $ do
    let ctx = [("m", [def "x" (int 10 10 42), def "y" (num 20 20 3.14)])]
    let expr = tag 1 1 "A" [x 1 3, y 1 5]
    let (_, expr') = compile ctx "m" expr
    parse' "A x y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "A x y"
    C.dropMeta expr' `shouldBe` C.Ann (C.and' [C.Tag "A", x', y']) (C.and' [C.Tag "A", C.IntT, C.NumT])
    liftExpr expr' `shouldBe` Ann expr (Tag "A" [IntT, NumT])
    eval ctx "m" expr `shouldBe` Tag "A" [Int 42, Num 3.14]

  it "☯ Tao.Ann type checks" $ do
    let ctx = [("m", [def "x" (int 10 10 42)])]
    let expr = ann 1 3 (x 1 1) (intT 1 5)
    let (_, expr') = compile ctx "m" expr
    parse' "x : Int " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x : Int"
    C.dropMeta expr' `shouldBe` C.Ann (C.Ann x' C.IntT) C.IntT
    liftExpr expr' `shouldBe` Ann expr (intT 1 5)
    eval ctx "m" expr `shouldBe` Int 42

  it "☯ Tao.Ann type mismatch" $ do
    let ctx = [("m", [def "x" (int 10 10 42)])]
    let expr = ann 1 3 (x 1 1) (numT 1 5)
    let (_, expr') = compile ctx "m" expr
    parse' "x : Num " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x : Num"
    C.dropMeta expr' `shouldBe` let err = C.Err $ typeMismatch C.IntT C.NumT in C.Ann (C.Ann x' err) err
    liftExpr expr' `shouldBe` let err = loc 1 5 1 8 $ Err $ typeMismatch IntT NumT in Ann (ann 1 3 (x 1 1) err) err
    eval ctx "m" expr `shouldBe` Int 42

  it "☯ Tao.Tuple 0" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (Tuple [])
    let (_, expr') = compile ctx "m" expr
    parse' "() " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "()"
    C.dropMeta expr' `shouldBe` C.Ann C.Unit C.Unit
    liftExpr expr' `shouldBe` Ann expr (Tuple [])
    eval ctx "m" expr `shouldBe` Tuple []

  it "☯ Tao.Tuple 1" $ do
    let ctx = [("m", [def "x" (int 10 10 42)])]
    let expr = loc 1 1 1 3 (Tuple [x 1 2])
    let (_, expr') = compile ctx "m" expr
    parse' "(x) " `shouldBe` Right (x 1 2, "")
    format 80 expr `shouldBe` "(x)"
    C.dropMeta expr' `shouldBe` C.Ann x' C.IntT
    liftExpr expr' `shouldBe` Ann (x 1 2) IntT
    eval ctx "m" expr `shouldBe` Int 42

  it "☯ Tao.Tuple 2" $ do
    let ctx = [("m", [def "x" (int 10 10 42), def "y" (num 20 20 3.14)])]
    let expr = loc 1 1 1 7 (Tuple [x 1 2, y 1 5])
    let (_, expr') = compile ctx "m" expr
    parse' "(x, y) " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "(x, y)"
    C.dropMeta expr' `shouldBe` C.Ann (C.And x' y') (C.And C.IntT C.NumT)
    liftExpr expr' `shouldBe` Ann expr (Tuple [IntT, NumT])
    eval ctx "m" expr `shouldBe` Tuple [Int 42, Num 3.14]

  it "☯ Tao.List 0" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (List [])
    let (_, expr') = compile ctx "m" expr
    parse' "[] " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "[]"
    C.dropMeta expr' `shouldBe` C.Ann (C.Tag "[]") (C.Tag "[]")
    liftExpr expr' `shouldBe` Ann expr (List [])
    eval ctx "m" expr `shouldBe` List []

  it "☯ Tao.List 1" $ do
    let ctx = [("m", [def "x" (int 10 10 42)])]
    let expr = loc 1 1 1 4 (List [x 1 2])
    let (_, expr') = compile ctx "m" expr
    parse' "[x] " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "[x]"
    C.dropMeta expr' `shouldBe` C.Ann (C.tag "::" [x', C.Tag "[]"]) (C.tag "::" [C.IntT, C.Tag "[]"])
    liftExpr expr' `shouldBe` Ann expr (List [IntT])
    eval ctx "m" expr `shouldBe` List [Int 42]

  it "☯ Tao.List 2" $ do
    let ctx = [("m", [def "x" (int 10 10 42), def "y" (int 20 20 9)])]
    let expr = loc 1 1 1 7 (List [x 1 2, y 1 5])
    let (_, expr') = compile ctx "m" expr
    parse' "[x, y] " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "[x, y]"
    C.dropMeta expr' `shouldBe` C.Ann (C.tag "::" [x', C.tag "::" [y', C.Tag "[]"]]) (C.tag "::" [C.IntT, C.tag "::" [C.IntT, C.Tag "[]"]])
    liftExpr expr' `shouldBe` Ann expr (List [IntT, IntT])
    eval ctx "m" expr `shouldBe` List [Int 42, Int 9]

  it "☯ Tao.String empty" $ do
    let ctx = []
    let expr = loc 1 1 1 3 (String [])
    let (_, expr') = compile ctx "m" expr
    parse' "'' " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "''"
    C.dropMeta expr' `shouldBe` C.Ann (C.Tag "''") (C.Tag "''")
    liftExpr expr' `shouldBe` Ann expr (String [])
    eval ctx "m" expr `shouldBe` String []

  -- it "☯ Tao.String literal" $ do
  -- it "☯ Tao.String interpolation" $ do

  it "☯ Tao.Or" $ do
    let ctx = [("m", [def "x" (int 10 10 42), def "y" (num 20 20 3.14)])]
    let expr = or' 1 3 (x 1 1) (y 1 5)
    let (_, expr') = compile ctx "m" expr
    parse' "x | y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x | y"
    C.dropMeta expr' `shouldBe` C.Ann (C.Or x' y') (C.Or C.IntT C.NumT)
    liftExpr expr' `shouldBe` Ann expr (Or IntT NumT)
    eval ctx "m" expr `shouldBe` Or (Int 42) (Num 3.14)

  it "☯ Tao.For 0" $ do
    let ctx = [("m", [def "x" (int 10 10 42)])]
    let expr = loc 1 1 1 2 (For [] (x 1 4))
    let (_, expr') = compile ctx "m" expr
    parse' "@; x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "@; x"
    C.dropMeta expr' `shouldBe` C.Ann x' C.IntT
    liftExpr expr' `shouldBe` Ann (x 1 4) IntT
    eval ctx "m" expr `shouldBe` Int 42

  it "☯ Tao.For 1" $ do
    let ctx = [("m", [def "x" (int 10 10 42)])]
    let expr = loc 1 1 1 3 (For ["a"] (x 1 5))
    let (_, expr') = compile ctx "m" expr
    parse' "@a; x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "@a; x"
    C.dropMeta expr' `shouldBe` C.Ann x' C.IntT
    liftExpr expr' `shouldBe` Ann (x 1 5) IntT
    eval ctx "m" expr `shouldBe` Int 42

  it "☯ Tao.For 2" $ do
    let ctx = [("m", [def "x" (int 10 10 42)])]
    let expr = loc 1 1 1 5 (For ["a", "b"] (x 1 7))
    let (_, expr') = compile ctx "m" expr
    parse' "@a b; x " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "@a b; x"
    C.dropMeta expr' `shouldBe` C.Ann x' C.IntT
    liftExpr expr' `shouldBe` Ann (x 1 7) IntT
    eval ctx "m" expr `shouldBe` Int 42

  it "☯ Tao.Fun" $ do
    let ctx = [("m", [def "x" (int 10 10 42), def "y" (num 20 20 3.14)])]
    let expr = fun 1 3 (x 1 1) (y 1 6)
    let (_, expr') = compile ctx "m" expr
    parse' "x -> y " `shouldBe` Right (expr, "")
    format 80 expr `shouldBe` "x -> y"
    C.dropMeta expr' `shouldBe` C.Ann (C.for ["x1T", "x"] $ C.Fun (C.Ann x' (C.Var "x1T")) y') (C.Fun (C.Var "x1T") C.NumT)
    liftExpr expr' `shouldBe` Ann (For ["x1T"] $ loc 1 3 1 5 $ For ["x"] $ Fun (Ann (x 1 1) (Var "x1T")) (y 1 6)) (Fun (Var "x1T") NumT)
    eval ctx "m" expr `shouldBe` For ["x"] (Fun (Var "x") (Num 3.14))

  -- App Expr [Expr]
  -- Call String [(String, Expr)]
  -- Spread Expr
  -- Op1 Op1 Expr
  -- Op2 Op2 Expr Expr
  -- Match [Expr] [Case]
  -- If Expr Expr Expr
  -- Let (Pattern, Expr) Expr
  -- Bind (Pattern, Expr) Expr
  -- Record [(String, Expr)]
  -- Select Expr [(String, Expr)]
  -- With Expr [(String, Expr)]
  -- Meta C.Metadata Expr
  it "☯ Tao.Err" $ do
    parse' "!error _" `shouldBe` Right (loc 1 1 1 7 (Err (customError $ any 1 8)), "")
    format 80 (Err (customError Any)) `shouldBe` "!error _"
