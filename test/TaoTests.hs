module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ TaoTests ☯==--" $ do
  let run = Tao.run
  let loc = C.Location "TaoTests" (1, 2)
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
  let (f, f') = (Var "f", C.Var "f")

  it "☯ lower/lift Any" $ do
    let expr = Any
    let term = C.Var "_"
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift Type" $ do
    let expr = Type ["A"]
    let term = C.Typ ["A"]
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift IntType" $ do
    let expr = Tag "Int"
    let term = C.IntT
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ lower/lift NumType" $ do
    let expr = Tag "Num"
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
    let expr = Tag "A"
    let term = C.Tag "A"
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

  -- it "☯ lower/lift Record" $ do
  --   let expr = Record []
  --   let term = C.Rec []
  --   lowerExpr [] expr `shouldBe` term
  --   liftExpr term `shouldBe` expr

  --   let expr = Record [("a", x), ("b", y)]
  --   let term = C.Rec [("a", x'), ("b", y')]
  --   lowerExpr [] expr `shouldBe` term
  --   liftExpr term `shouldBe` expr

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
    let term = C.app (C.Var ".y") [C.Err, C.Var "x"]
    lowerExpr [] expr `shouldBe` C.Err
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

  -- it "☯ lower/lift Let" $ do
  --   let expr = Let (x, y) z
  --   let term = C.let' (x', y') z'
  --   lowerExpr [] expr `shouldBe` term
  --   liftExpr term `shouldBe` expr

  -- it "☯ lower/lift Let recursive" $ do
  --   let expr = Let (f, App f x) z
  --   let term = C.let' (f', C.Fix "f" $ C.App f' x') z'
  --   lowerExpr [] expr `shouldBe` term
  --   liftExpr term `shouldBe` expr

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
    let expr = Err
    let term = C.Err
    lowerExpr [] expr `shouldBe` term
    liftExpr term `shouldBe` expr

  it "☯ stmtDefs" $ do
    -- stmtDefs (Def (Int 42) z) `shouldBe` []
    -- stmtDefs (Def (Num 3.14) z) `shouldBe` []
    -- stmtDefs (Def (Var "x") z) `shouldBe` [("x", z)]
    -- stmtDefs (Def (Tag "A" []) z) `shouldBe` []
    -- stmtDefs (Def (Tag "A" [x, y]) z) `shouldBe` [("x", Match [z] [Fun (Tag "A" [x, y]) x]), ("y", Match [z] [Fun (Tag "A" [x, y]) y])]
    -- stmtDefs (Def (Tuple []) z) `shouldBe` []
    -- stmtDefs (Def (Tuple [x, y]) z) `shouldBe` [("x", Match [z] [Fun (Tuple [x, y]) x]), ("y", Match [z] [Fun (Tuple [x, y]) y])]
    -- stmtDefs (Def (Record []) z) `shouldBe` []
    -- stmtDefs (Def (Record [("a", x), ("b", y)]) z) `shouldBe` [("x", Match [z] [Fun (Record [("a", x), ("b", y)]) x]), ("y", Match [z] [Fun (Record [("a", x), ("b", y)]) y])]
    -- stmtDefs (Def (Trait y "x") z) `shouldBe` [(".x", fun [Any, y] z)]
    -- stmtDefs (Def (Trait (Ann y IntType) "x") z) `shouldBe` [(".x", fun [IntType, y] z)]
    -- -- TODO: List
    -- -- TODO: Text
    -- stmtDefs (Def (Fun x y) z) `shouldBe` [("x", Match [z] [Fun (Fun x y) x]), ("y", Match [z] [Fun (Fun x y) y])]
    -- stmtDefs (Def (App x y) z) `shouldBe` [("x", Fun y z)]
    -- -- stmtDefs (Def (Let (x, y) x) z) `shouldBe` [("y", Match [z] [Fun (Let (x, y) x) y])]
    -- -- stmtDefs (Def (Let (x, Int 1) x) z) `shouldBe` []
    -- -- stmtDefs (Def (Let (x, Int 1) y) z) `shouldBe` [("y", Match [z] [Fun (Let (x, Int 1) y) y])]
    -- -- TODO: Bind
    -- -- TODO: TypeDef
    -- -- TODO: MatchFun
    -- -- TODO: Match
    -- stmtDefs (Def (Or x y) z) `shouldBe` [("x", Match [z] [Fun (Or x y) x]), ("y", Match [z] [Fun (Or x y) y])]
    -- stmtDefs (Def (Ann x y) z) `shouldBe` [("x", Ann z y)]
    -- stmtDefs (Def (Op1 C.Int2Num x) z) `shouldBe` []
    -- stmtDefs (Def (Op2 C.Add x y) z) `shouldBe` []
    -- stmtDefs (Def (Meta loc x) z) `shouldBe` [("x", Meta loc z)]
    -- stmtDefs (Def Err y) `shouldBe` []
    True `shouldBe` True

  it "☯ moduleDefs" $ do
    let defs stmts = do
          let mod = Module "mod" stmts
          moduleDefs "pkg" mod
    defs [] `shouldBe` []
    defs [Import "mod2" "m2" []] `shouldBe` []
    defs [Import "mod2" "m2" [("x", "y")]] `shouldBe` [("pkg:mod#y", Var "pkg:mod2#x")]
    defs [Import "pkg2:mod2" "m2" [("x", "y")]] `shouldBe` [("pkg:mod#y", Var "pkg2:mod2#x")]
    defs [defName "x" y] `shouldBe` [("pkg:mod#x", Var "y")]
    defs [defName "x" y, defName "y" z] `shouldBe` [("pkg:mod#x", Var "pkg:mod#y"), ("pkg:mod#y", Var "z")]

  it "☯ packageDefs" $ do
    let defs stmts = do
          let mod = Module "mod" stmts
          let pkg = Package "pkg" [mod]
          packageDefs pkg
    defs [] `shouldBe` []
    defs [defName "x" y] `shouldBe` [("pkg:mod#x", Var "y")]

  -- it "☯ lowerPackage" $ do
  --   let mod defs = Package {name = "lowerPackage", modules = [Module "f" defs]}
  --   lowerPackage (mod []) `shouldBe` []
  --   lowerPackage (mod [Def (NameDef "x" [] y)]) `shouldBe` [("x", y')]

  -- it "☯ run" $ do
  --   let defs =
  --         [ Def (NameDef "x" [] (Int 42)),
  --           Def (DefTrait (Ann Any IntType) "y" [] (Num 3.14)),
  --           Def (NameDef "f" [Int 1] (Int 2))
  --         ]
  --   let mod = Package {name = "run", modules = [Module "f" defs]}

  --   run mod Any `shouldBe` Any
  --   run mod (Type ["A"]) `shouldBe` Type ["A"]
  --   run mod IntType `shouldBe` IntType
  --   run mod (Int 42) `shouldBe` Int 42
  --   run mod (Num 3.14) `shouldBe` Num 3.14
  --   run mod (Var "x") `shouldBe` Int 42
  --   run mod (Var "y") `shouldBe` Var "y"
  --   run mod (Tag "A" [x]) `shouldBe` Tag "A" [Int 42]
  --   run mod (Tuple [x]) `shouldBe` Tuple [Int 42]
  --   run mod (Record [("a", x)]) `shouldBe` Record [("a", Int 42)]
  --   run mod (Trait x "y") `shouldBe` Num 3.14
  --   run mod ListNil `shouldBe` ListNil
  --   run mod ListCons `shouldBe` ListCons
  --   run mod TextNil `shouldBe` TextNil
  --   run mod TextCons `shouldBe` TextCons
  --   run mod (Fun x y) `shouldBe` Fun (Int 42) y
  --   run mod (App (Tag "A" []) x) `shouldBe` Tag "A" [Int 42]
  --   run mod (App f (Int 1)) `shouldBe` Int 2
  --   run mod (App f (Int 2)) `shouldBe` Err
  --   -- run mod (Let (Expr, Expr) Expr) `shouldBe` Any
  --   -- run mod (Bind (Expr, Expr) Expr) `shouldBe` Any
  --   -- run mod (TypeDef String [Expr] Expr) `shouldBe` Any
  --   -- run mod (MatchFun [Expr]) `shouldBe` Any
  --   -- run mod (Match [Expr] [Expr]) `shouldBe` Any
  --   run mod (Or x Err) `shouldBe` Int 42
  --   run mod (Or Err x) `shouldBe` Int 42
  --   run mod (Or Err Err) `shouldBe` Err
  --   run mod (Ann x IntType) `shouldBe` Int 42
  --   run mod (Op1 C.Int2Num x) `shouldBe` Num 42.0
  --   run mod (Op2 C.Add x (Int 1)) `shouldBe` Int 43
  --   run mod (Meta loc x) `shouldBe` Int 42
  --   run mod Err `shouldBe` Err

  it "☯ packageTests" $ do
    let defs =
          [ defName "x" (Int 1),
            Test x y,
            defName "y" (Int 2)
          ]
    let mod = Package {name = "pkg", modules = [Module "mod" defs]}
    packageTests mod `shouldBe` [(Var "pkg:mod#x", Var "pkg:mod#y")]

  it "☯ test" $ do
    let defs =
          [ defName "x" (Int 1),
            Test x y,
            defName "y" (Int 2)
          ]
    let mod = Package {name = "pkg", modules = [Module "mod" defs]}
    test mod `shouldBe` [TestEqError (Var "pkg:mod#x") (Int 1) (Int 2)]

  it "☯ splitCamelCase" $ do
    splitCamelCase "" `shouldBe` []
    splitCamelCase "Camel" `shouldBe` ["Camel"]
    splitCamelCase "CamelCase" `shouldBe` ["Camel", "Case"]
    splitCamelCase "CamelCaseABC" `shouldBe` ["Camel", "Case", "ABC"]
    splitCamelCase "CamelABCCase" `shouldBe` ["Camel", "ABC", "Case"]
    splitCamelCase "ABCCamelCase" `shouldBe` ["ABC", "Camel", "Case"]

  it "☯ nameSplit" $ do
    nameSplit "" `shouldBe` []
    nameSplit "camelCase" `shouldBe` ["camel", "case"]
    nameSplit "CamelCase" `shouldBe` ["camel", "case"]
    nameSplit "snake_case" `shouldBe` ["snake", "case"]
    nameSplit "dash-case" `shouldBe` ["dash", "case"]
    nameSplit "dot.name" `shouldBe` ["dot", "name"]
    nameSplit "/path/name" `shouldBe` ["path", "name"]
    nameSplit "multisymbol/.name" `shouldBe` ["multisymbol", "name"]

  it "☯ nameCamelCaseUpper" $ do
    nameCamelCaseUpper "my-name" `shouldBe` "MyName"

  it "☯ nameCamelCaseLower" $ do
    nameCamelCaseLower "my-name" `shouldBe` "myName"

  it "☯ nameSnakeCase" $ do
    nameSnakeCase "my-name" `shouldBe` "my_name"

  it "☯ nameDashCase" $ do
    nameDashCase "my_name" `shouldBe` "my-name"

  -- it "☯ rename Expr" $ do
  --   let f _ "x" = "y"
  --       f _ x = x
  --   rename f [] Any `shouldBe` Any
  --   rename f [] x `shouldBe` y
  --   rename f [] z `shouldBe` z

  -- it "☯ rename Module" $ do
  --   let mod1 x = Module "mod1" [Def (NameDef [] x [] z)]
  --   let mod2 x = Module "mod2" [Import "path/mod1" "mod1" [(x, x)], Test (Var x) z]
  --   let sub "x" = "y"
  --       sub z = z
  --   -- rename [] "mod1" sub [mod1 "x", mod2 "x"] `shouldBe` [mod1 "x", mod2 "x"]
  --   -- rename ["path"] "mod1" sub [mod1 "x", mod2 "x"] `shouldBe` [mod1 "y", mod2 "y"]
  --   True `shouldBe` True

  it "☯ renameExpr" $ do
    True `shouldBe` True

  it "☯ renameStmt" $ do
    True `shouldBe` True

  it "☯ renameImport" $ do
    True `shouldBe` True

  it "☯ renameModule" $ do
    True `shouldBe` True

  it "☯ rename Package" $ do
    let m1 x = Module "m1" [Def (NameDef [] x [] $ Int 42), Def (NameDef [] "y" [] $ Var x)]
    let m2 _ = Module "m2" [Def (NameDef [] "x" [] $ Int 42), Def (NameDef [] "y" [] $ Var "x")]
    let m3 x = Module "m3" [Import "m1" x [], Def (NameDef [] "y" [] $ Var x)]
    let m4 x = Module "m4" [Import "m1" "m" [(x, x)], Def (NameDef [] "y" [] $ Var x)]
    let pkg = Package "pkg" [m1 "x", m2 "x", m3 "x", m4 "x"]
    rename "m1" "x" "z" pkg `shouldBe` pkg {modules = [m1 "z", m2 "z", m3 "z", m4 "z"]}
