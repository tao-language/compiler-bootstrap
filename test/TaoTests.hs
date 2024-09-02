module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ TaoTests ☯==--" $ do
  let loc = C.Location "TaoTests" (1, 2)
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (xP, yP, zP) = (PVar "x", PVar "y", PVar "z")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
  let (xP', yP', zP') = (C.PVar "x", C.PVar "y", C.PVar "z")
  let (a, a') = (Var "a", C.Var "a")
  let (f, f') = (Var "f", C.Var "f")
  let (i0, i1, i2) = (Int 0, Int 1, Int 2)

  it "☯ lambda" $ do
    lambda [] x `shouldBe` x
    lambda ["x"] y `shouldBe` Match [Case [xP] Nothing y]
    lambda ["x", "y"] z `shouldBe` Match [Case [xP, yP] Nothing z]

  it "☯ lambdaOf" $ do
    lambdaOf "$" x `shouldBe` ([], x)
    lambdaOf "$" (Meta (C.Comment "") x) `shouldBe` ([], Meta (C.Comment "") x)
    lambdaOf "$" (Match []) `shouldBe` ([], Err)
    lambdaOf "$" (Match [Case [] Nothing x]) `shouldBe` ([], x)
    lambdaOf "$" (Match [Case [xP] Nothing i1]) `shouldBe` (["x"], i1)
    lambdaOf "$" (Match [Case [xP] Nothing i1, Case [xP] Nothing i2]) `shouldBe` (["x"], Int 1)
    lambdaOf "$" (Match [Case [xP] Nothing i1, Case [yP] Nothing i2]) `shouldBe` (["$1"], app (Match [Case [xP] Nothing i1, Case [yP] Nothing i2]) [Var "$1"])
    lambdaOf "$" (Match [Case [xP, yP] Nothing i1, Case [xP, zP] Nothing i2]) `shouldBe` (["x", "$1"], app (Match [Case [yP] Nothing i1, Case [zP] Nothing i2]) [Var "$1"])

  it "☯ lower/lift/eval Type" $ do
    let expr = Tag "Type" []
    let term = C.Knd
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift IntType" $ do
    let expr = Tag "Int" []
    let term = C.IntT
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift NumType" $ do
    let expr = Tag "Num" []
    let term = C.NumT
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Int" $ do
    let expr = Int 42
    let term = C.Int 42
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Num" $ do
    let expr = Num 3.14
    let term = C.Num 3.14
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Var" $ do
    let expr = Var "x"
    let term = C.Var "x"
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Tag" $ do
    let expr = Tag "A" []
    let term = C.Tag "A" []
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Tuple" $ do
    let expr = tuple []
    let term = C.Tag "" []
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

    let expr = tuple [x, y]
    let term = C.Tag "" [x', y']
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Record" $ do
    let expr = record []
    let term = C.Tag "" []
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

    let expr = record [("a", x), ("b", y)]
    let term = C.Tag "" [C.Fix "a" x', C.Fix "b" y']
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Trait" $ do
    let expr = Trait (Int 1) "y"
    let term = C.app (C.Var ".y") [C.intT 1, C.Int 1]
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

    let expr = Trait x "y"
    let term = C.app (C.Var ".y") [C.intT 1, x']
    lower [("x", C.Int 1)] expr `shouldBe` term
    lift term `shouldBe` expr

    let expr = Trait x "y"
    let term = C.app (C.Var ".y") [C.Err, C.Var "x"]
    lower [] expr `shouldBe` C.Err
    lift term `shouldBe` expr

  it "☯ lower/lift Fun" $ do
    let expr = Fun x y
    let term = C.Fun x' y'
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift App" $ do
    let expr = App x y
    let term = C.App x' y'
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  -- it "☯ lower/lift Let" $ do
  --   let expr = Let (x, y) z
  --   let term = C.let' (x', y') z'
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift Let recursive" $ do
  --   let expr = Let (f, App f x) z
  --   let term = C.let' (f', C.Fix "f" $ C.App f' x') z'
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  it "☯ lower/lift Bind" $ do
    let expr = Bind (xP, y) z
    let term = C.app (C.Var ".<-") [C.intT 1, y', C.Lam xP' z']
    lower [("y", C.Int 1)] expr `shouldBe` term
    lift term `shouldBe` expr

  -- it "☯ lower/lift TypeDef" $ do
  --   let expr = TODO
  --   let term = TODO
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift MatchFun" $ do
  --   let expr = TODO
  --   let term = TODO
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift Match" $ do
  --   let expr = TODO
  --   let term = TODO
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  it "☯ lower/lift Or" $ do
    let expr = Or x y
    let term = C.Or x' y'
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Ann" $ do
    let expr = Ann x y
    let term = C.Ann x' y'
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Op" $ do
    let expr = Op "+" [x, y]
    let term = C.Op "+" [x', y']
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Meta" $ do
    let expr = Meta loc x
    let term = C.Meta loc x'
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Err" $ do
    let expr = Err
    let term = C.Err
    lower [] expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Package" $ do
    let pkg = Package "pkg" [Module "mod" [var "x" y]]
    let env :: C.Env
        env = [("mod", C.Tag "mod" [C.Fix "x" (C.Var "mod.x")]), ("x", C.Var "y")]
    lower [] pkg `shouldBe` env
  -- TODO: lift env `shouldBe` pkg

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
          [ var "x" (Int 1),
            Test x (PInt 2)
          ]
    let mod = Package {name = "pkg", modules = [Module "mod" defs]}
    packageTests mod `shouldBe` [(x, PInt 2)]

  it "☯ test" $ do
    let defs =
          [ var "x" (Int 1),
            Test x (PInt 2),
            var "y" (Int 3),
            Test y (PInt 3)
          ]
    let pkg = Package {name = "pkg", modules = [Module "mod" defs]}
    test pkg `shouldBe` [TestEqError (Var "mod.x") (Int 1) (PInt 2)]

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

  it "☯ rename String" $ do
    rename "m" [] "x" `shouldBe` "x"
    rename "m" [(("m", "x"), "y")] "x" `shouldBe` "y"

  it "☯ rename Expr" $ do
    True `shouldBe` True

  it "☯ rename Definition" $ do
    rename "m" [(("m", "x"), "y")] (Def [("x", x)] xP x) `shouldBe` Def [("y", y)] yP y

  it "☯ rename Stmt" $ do
    rename "m" [(("m", "x"), "y")] (Import "m" "x" [("x", "x")]) `shouldBe` Import "m" "y" [("y", "y")]
    rename "m" [(("m", "x"), "y")] (Import "n" "x" [("x", "x")]) `shouldBe` Import "n" "y" [("x", "y")]
    rename "m" [(("n", "x"), "y")] (Import "m" "x" [("x", "x")]) `shouldBe` Import "m" "x" [("x", "x")]
    rename "n" [(("m", "x"), "y")] (Import "m" "x" [("x", "x")]) `shouldBe` Import "m" "x" [("y", "x")]
    rename "m" [(("m", "x"), "y")] (var "x" z) `shouldBe` var "y" z

  it "☯ rename Module" $ do
    True `shouldBe` True

  it "☯ rename Package" $ do
    -- let m1 x = Module "m1" [Define (Def [] (PVar x) $ Int 42), Define (Def [] yP (Var x))]
    -- let m2 _ = Module "m2" [Define (Def [] xP $ Int 42), Define (Def [] yP x)]
    -- let m3 x = Module "m3" [Import "pkg" "m1" x [], Define (Def [] yP (Var x))]
    -- let m4 x = Module "m4" [Import "pkg" "m1" "m" [(x, x)], Define (Def [] yP (Var x))]
    -- let pkg = Package "pkg" [m1 "x", m2 "x", m3 "x", m4 "x"]
    -- rename "x" "z" pkg `shouldBe` pkg {modules = [m1 "z", m2 "z", m3 "z", m4 "z"]}
    True `shouldBe` True

  it "☯ resolveNames Def" $ do
    let f = resolveNames "mod"
    f (Def [] xP y) `shouldBe` [("mod", "x")]
    f (TraitDef [] (Err, Err) "x" y) `shouldBe` []

  it "☯ resolveNames Stmt" $ do
    let f = resolveNames "mod"
    f (Import "m" "n" [("x", "y")]) `shouldBe` [("mod", "y"), ("mod", "n")]
    f (var "x" y) `shouldBe` [("mod", "x")]

  it "☯ resolveNames Module" $ do
    let f stmts = resolveNames () (Module "mod" stmts)
    f [] `shouldBe` []
    f [Import "m" "n" []] `shouldBe` [("mod", "n")]

  it "☯ link Package" $ do
    let pkg stmts = Package "pkg" [Module "mod" stmts]
    let f stmts = link (pkg stmts)
    f [] `shouldBe` pkg []
    f [Import "m" "n" [("x", "y")]] `shouldBe` pkg [Import "m" "mod.n" [("x", "mod.y")]]
    f [var "x" y] `shouldBe` pkg [var "mod.x" y]
    f [var "x" y, var "y" z] `shouldBe` pkg [var "mod.x" (Var "mod.y"), var "mod.y" z]

  -- it "☯ getContext Stmt" $ do
  --   let f = getContext ("pkg", "mod")
  --   f (Import "m" "n" [("x", "y")]) `shouldBe` [("@pkg:mod.y", Var "@p:m.x"), ("@pkg:mod.n", Var "@p:m")]
  --   f (Import "m" "" [("x", "")]) `shouldBe` [("@pkg:mod.x", Var "@p:m.x"), ("@pkg:mod.m", Var "@p:m")]
  --   f (Import "m" "n" [("x", "")]) `shouldBe` [("@pkg:mod.x", Var "@pkg:m.x"), ("@pkg:mod.n", Var "@pkg:m")]
  --   f (Import "m" "" [("x", "")]) `shouldBe` [("@pkg:mod.x", Var "@pkg:m.x"), ("@pkg:mod.m", Var "@pkg:m")]

  -- it "☯ getContext Module" $ do
  --   let f stmts = do
  --         let mod = Module "mod" stmts
  --         getContext "pkg" mod
  --   f [] `shouldBe` [("@pkg:mod", Tag "@pkg:mod" [])]
  --   f [Import "m" "n" []] `shouldBe` [("@pkg:mod", Tag "@pkg:mod" [("n", Var "@pkg:mod.n")]), ("@pkg:mod.n", Var "@p:m")]
  --   f [Import "m" "n" [("x", "y")]] `shouldBe` [("@pkg:mod", Tag "@pkg:mod" [("y", Var "@pkg:mod.y"), ("n", Var "@pkg:mod.n")]), ("@pkg:mod.y", Var "@p:m.x"), ("@pkg:mod.n", Var "@p:m")]
  --   f [var "x" y] `shouldBe` [("@pkg:mod", Tag "@pkg:mod" [("x", Var "@pkg:mod.x")]), ("@pkg:mod.x", y)]

  -- it "☯ getContext Package" $ do
  --   let f stmts = do
  --         let mod = Module "mod" stmts
  --         let pkg = Package "pkg" [mod]
  --         getContext () pkg
  --   f [] `shouldBe` [("@pkg:mod", Tag "@pkg:mod" [])]
  --   f [Import "m" "n" []] `shouldBe` [("@pkg:mod", Tag "@pkg:mod" [("n", Var "@pkg:mod.n")]), ("@pkg:mod.n", Var "@p:m")]

  -- it "☯ fullNames Stmt" $ do
  --   let names = fullNames ("pkg", "mod")
  --   names (Import "@p:m" "n" [("x", "y")]) `shouldBe` [("n", "@p:m"), ("y", "@pkg:mod.x")]
  --   names (Import "@p:m" "" [("x", "y")]) `shouldBe` [("m", "@p:m"), ("y", "@pkg:mod.x")]
  --   names (Import "m" "n" [("x", "y")]) `shouldBe` [("n", "@pkg:m"), ("y", "@pkg:mod.x")]
  --   names (Import "m" "" [("x", "y")]) `shouldBe` [("m", "@pkg:m"), ("y", "@pkg:mod.x")]
  --   names (Import "m" "" [("x", "")]) `shouldBe` [("m", "@pkg:m"), ("x", "@pkg:mod.x")]
  --   names (var "x" y) `shouldBe` [("x", "@pkg:mod.x")]

  -- it "☯ fullNames Module" $ do
  --   let names stmts = fullNames "pkg" (Module "mod" stmts)
  --   names [Import "@p:m" "n" [("x", "y")]] `shouldBe` [("n", "@p:m"), ("y", "@pkg:mod.x")]
  --   names [var "x" y] `shouldBe` [("x", "@pkg:mod.x")]

  it "☯ eval" $ do
    let pkg = Package "pkg" [Module "mod" [var "x" (Int 42)]]
    let eval' = eval pkg "mod"
    let x = Var "mod.x"
    eval' (Int 42) `shouldBe` Right (Int 42, intT' 42)
    eval' (Num 3.14) `shouldBe` Right (Num 3.14, numT' 3.14)
    eval' (Var "x") `shouldBe` Right (Int 42, intT' 42)
    eval' (Var "y") `shouldBe` Left (Var "y", C.UndefinedVar "y")
    eval' (Var "mod.x") `shouldBe` Right (Int 42, intT' 42)
    eval' (Tag "A" []) `shouldBe` Right (Tag "A" [], Tag "A" [])
    eval' (Tag "A" [("", x)]) `shouldBe` Right (Tag "A" [("", Int 42)], Tag "A" [("", intT' 42)])
    eval' (Tag "A" [("x", x)]) `shouldBe` Right (Tag "A" [("x", Int 42)], Tag "A" [("x", intT' 42)])
    eval' (Trait (Tag "A" [("a", x)]) "a") `shouldBe` Right (Int 42, intT' 42)
    -- Trait Expr String
    -- TraitFun String
    -- Fun Expr Expr
    -- App Expr Expr
    -- Or Expr Expr
    -- Let Definition Expr
    -- Bind (Pattern, Expr) Expr
    -- Match [Case]
    -- If Expr Expr Expr
    -- Ann Expr Expr
    -- Op String [Expr]
    -- Meta C.Metadata Expr
    -- Err
    True `shouldBe` True
