{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ TaoTests ☯==--" $ do
  let err = C.TODO "error"
  let loc = C.Location "TaoTests" (1, 2)
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
  let (f, f') = (Var "f", C.Var "f")

  it "☯ lower/lift Any" $ do
    let expr = Any
    let term = C.Var "_"
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Kind" $ do
    let expr = Kind
    let term = C.Knd
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift IntType" $ do
    let expr = IntType
    let term = C.IntT
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift NumType" $ do
    let expr = NumType
    let term = C.NumT
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Int" $ do
    let expr = Int 42
    let term = C.Int 42
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Num" $ do
    let expr = Num 3.14
    let term = C.Num 3.14
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Var" $ do
    let expr = Var "x"
    let term = C.Var "x"
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Tag" $ do
    let expr = Tag "A" []
    let term = C.Tag "A"
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

    let expr = Tag "A" [x, y]
    let term = C.app (C.Tag "A") [x', y']
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Tuple" $ do
    let expr = Tuple []
    let term = C.Tag "()"
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

    let expr = Tuple [x, y]
    let term = C.app (C.Tag "()") [x', y']
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Record" $ do
    let expr = Record []
    let term = C.Rec []
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

    let expr = Record [("a", x), ("b", y)]
    let term = C.Rec [("a", x'), ("b", y')]
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Trait" $ do
    let expr = Trait (Int 1) "y"
    let term = C.app (C.Var ".y") [C.IntT, C.Int 1]
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

    let expr = Trait x "y"
    let term = C.app (C.Var ".y") [C.IntT, x']
    lowerExpr [("x", Int 1)] expr `shouldBe` term
    liftExpr term `shouldBe` expr

    let expr = Trait x "y"
    let term = C.app (C.Var ".y") [C.Err (C.UndefinedVar "x"), C.Var "x"]
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift ListNil" $ do
    let expr = ListNil
    let term = C.Tag "[]"
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift ListCons" $ do
    let expr = ListCons
    let term = C.Tag "[..]"
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift TextNil" $ do
    let expr = TextNil
    let term = C.Tag "\"\""
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift TextCons" $ do
    let expr = TextCons
    let term = C.Tag "\"..\""
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Fun" $ do
    let expr = Fun x y
    let term = C.Fun x' y'
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift App" $ do
    let expr = App x y
    let term = C.App x' y'
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Let" $ do
    let expr = Let (x, y) z
    let term = C.let' (x', y') z'
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Let recursive" $ do
    let expr = Let (f, App f x) z
    let term = C.let' (f', C.Fix "f" $ C.App f' x') z'
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Bind" $ do
    let expr = Bind (x, y) z
    let term = C.app (C.Var ".<-") [C.IntT, y', C.Fun x' z']
    lowerExpr [("y", Int 1)] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  -- it "☯ lower/lift TypeDef" $ do
  --   let expr = TODO
  --   let term = TODO
  --   lowerExpr [] expr `shouldBe` term
  --   liftExpr term `shouldBe` expr

  -- it "☯ lower/lift MatchFun" $ do
  --   let expr = TODO
  --   let term = TODO
  --   lowerExpr [] expr `shouldBe` term
  --   liftExpr term `shouldBe` expr

  -- it "☯ lower/lift Match" $ do
  --   let expr = TODO
  --   let term = TODO
  --   lowerExpr [] expr `shouldBe` term
  --   liftExpr term `shouldBe` expr

  it "☯ lower/lift Or" $ do
    let expr = Or x y
    let term = C.Or x' y'
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Ann" $ do
    let expr = Ann x y
    let term = C.Ann x' y'
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Op1" $ do
    let expr = Op1 C.Int2Num x
    let term = C.Op1 C.Int2Num x'
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Op2" $ do
    let expr = Op2 C.Add x y
    let term = C.Op2 C.Add x' y'
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Meta" $ do
    let expr = Meta loc x
    let term = C.Meta loc x'
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Err" $ do
    let expr = Err err
    let term = C.Err err
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ stmtDefs" $ do
    stmtDefs (Def (Int 42) z) `shouldBe` []
    stmtDefs (Def (Num 3.14) z) `shouldBe` []
    stmtDefs (Def (Var "x") z) `shouldBe` [("x", z)]
    stmtDefs (Def (Tag "A" []) z) `shouldBe` []
    stmtDefs (Def (Tag "A" [x, y]) z) `shouldBe` [("x", Match [z] [Fun (Tag "A" [x, y]) x]), ("y", Match [z] [Fun (Tag "A" [x, y]) y])]
    stmtDefs (Def (Tuple []) z) `shouldBe` []
    stmtDefs (Def (Tuple [x, y]) z) `shouldBe` [("x", Match [z] [Fun (Tuple [x, y]) x]), ("y", Match [z] [Fun (Tuple [x, y]) y])]
    stmtDefs (Def (Record []) z) `shouldBe` []
    stmtDefs (Def (Record [("a", x), ("b", y)]) z) `shouldBe` [("x", Match [z] [Fun (Record [("a", x), ("b", y)]) x]), ("y", Match [z] [Fun (Record [("a", x), ("b", y)]) y])]
    stmtDefs (Def (Trait y "x") z) `shouldBe` [(".x", fun [Any, y] z)]
    stmtDefs (Def (Trait (Ann y IntType) "x") z) `shouldBe` [(".x", fun [IntType, y] z)]
    -- TODO: List
    -- TODO: Text
    stmtDefs (Def (Fun x y) z) `shouldBe` [("x", Match [z] [Fun (Fun x y) x]), ("y", Match [z] [Fun (Fun x y) y])]
    stmtDefs (Def (App x y) z) `shouldBe` [("x", Fun y z)]
    stmtDefs (Def (Let (x, y) x) z) `shouldBe` [("y", Match [z] [Fun (Let (x, y) x) y])]
    stmtDefs (Def (Let (x, Int 1) x) z) `shouldBe` []
    stmtDefs (Def (Let (x, Int 1) y) z) `shouldBe` [("y", Match [z] [Fun (Let (x, Int 1) y) y])]
    -- TODO: Bind
    -- TODO: TypeDef
    -- TODO: MatchFun
    -- TODO: Match
    stmtDefs (Def (Or x y) z) `shouldBe` [("x", Match [z] [Fun (Or x y) x]), ("y", Match [z] [Fun (Or x y) y])]
    stmtDefs (Def (Ann x y) z) `shouldBe` [("x", Ann z y)]
    stmtDefs (Def (Op1 C.Int2Num x) z) `shouldBe` []
    stmtDefs (Def (Op2 C.Add x y) z) `shouldBe` []
    stmtDefs (Def (Meta loc x) z) `shouldBe` [("x", Meta loc z)]
    stmtDefs (Def (Err err) y) `shouldBe` []

  it "☯ lowerModule" $ do
    let mod defs = Module {name = "lowerModule", files = [File "f" defs]}
    lowerModule (mod []) `shouldBe` []
    lowerModule (mod [Def x y]) `shouldBe` [("x", y')]

  it "☯ eval" $ do
    let defs =
          [ Def x (Int 42),
            Def (Trait (Ann Any IntType) "y") (Num 3.14),
            Def f (Fun (Int 1) (Int 2))
          ]
    let mod = Module {name = "run", files = [File "f" defs]}

    eval mod Any `shouldBe` Any
    eval mod Kind `shouldBe` Kind
    eval mod IntType `shouldBe` IntType
    eval mod (Int 42) `shouldBe` Int 42
    eval mod (Num 3.14) `shouldBe` Num 3.14
    eval mod (Var "x") `shouldBe` Int 42
    eval mod (Var "y") `shouldBe` Var "y"
    eval mod (Tag "A" [x]) `shouldBe` Tag "A" [Int 42]
    eval mod (Tuple [x]) `shouldBe` Tuple [Int 42]
    eval mod (Record [("a", x)]) `shouldBe` Record [("a", Int 42)]
    eval mod (Trait x "y") `shouldBe` Num 3.14
    eval mod ListNil `shouldBe` ListNil
    eval mod ListCons `shouldBe` ListCons
    eval mod TextNil `shouldBe` TextNil
    eval mod TextCons `shouldBe` TextCons
    eval mod (Fun x y) `shouldBe` Fun (Int 42) y
    eval mod (App (Tag "A" []) x) `shouldBe` Tag "A" [Int 42]
    eval mod (App f (Int 1)) `shouldBe` Int 2
    eval mod (App f (Int 2)) `shouldBe` Err (C.PatternMatchError (C.Int 1) (C.Int 2))
    -- eval mod (Let (Expr, Expr) Expr) `shouldBe` Any
    -- eval mod (Bind (Expr, Expr) Expr) `shouldBe` Any
    -- eval mod (TypeDef String [Expr] Expr) `shouldBe` Any
    -- eval mod (MatchFun [Expr]) `shouldBe` Any
    -- eval mod (Match [Expr] [Expr]) `shouldBe` Any
    eval mod (Or x (Err err)) `shouldBe` Int 42
    eval mod (Or (Err err) x) `shouldBe` Int 42
    eval mod (Or (Err err) (Err err)) `shouldBe` Err err
    eval mod (Ann x IntType) `shouldBe` Int 42
    eval mod (Op1 C.Int2Num x) `shouldBe` Num 42.0
    eval mod (Op2 C.Add x (Int 1)) `shouldBe` Int 43
    eval mod (Meta loc x) `shouldBe` Meta loc (Int 42)
    eval mod (Err err) `shouldBe` Err err