module TaoTests where

import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ TaoTests ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (C.Var "x", C.Var "y", C.Var "z")
  let (xT, xT') = (Var "xT", C.Var "xT")
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (a', b', c') = (C.Var "a", C.Var "b", C.Var "c")
  let (f, f') = (Var "f", C.Var "f")
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  let (i1', i2', i3') = (C.Int 1, C.Int 2, C.Int 3)

  it "☯ lambda" $ do
    lambda [] x `shouldBe` x
    lambda ["x"] y `shouldBe` Fun x y
    lambda ["x", "y"] z `shouldBe` fun [x, y] z

  it "☯ lambdaOf" $ do
    -- lambdaOf "$" x `shouldBe` ([], x)
    -- lambdaOf "$" (Meta (C.Comment "") x) `shouldBe` ([], Meta (C.Comment "") x)
    -- lambdaOf "$" (Match [] []) `shouldBe` ([], Err)
    -- lambdaOf "$" (Match [] [([], x)]) `shouldBe` ([], x)
    -- lambdaOf "$" (Match [] [([x], i1)]) `shouldBe` (["x"], i1)
    -- lambdaOf "$" (Match [] [([x], i1), ([x], i2)]) `shouldBe` (["x"], i1)
    -- lambdaOf "$" (Match [] [([x], i1), ([y], i2)]) `shouldBe` (["$1"], Match [Var "$1"] [([x], i1), ([y], i2)])
    -- lambdaOf "$" (Match [] [([x, y], i1), ([x, z], i2)]) `shouldBe` (["x", "$1"], Match [Var "$1"] [([y], i1), ([z], i2)])
    True `shouldBe` True

  it "☯ lower/lift Expr Any" $ do
    let expr = Any
    let term = C.Any
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Unit" $ do
    let expr = Unit
    let term = C.Unit
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr IntT" $ do
    let expr = IntT
    let term = C.IntT
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr NumT" $ do
    let expr = NumT
    let term = C.NumT
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Int" $ do
    let expr = Int 42
    let term = C.Int 42
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Num" $ do
    let expr = Num 3.14
    let term = C.Num 3.14
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Var" $ do
    let expr = Var "x"
    let term = C.Var "x"
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Tag" $ do
    let expr = Tag "A"
    let term = C.Tag "A"
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Ann" $ do
    let expr = Ann x y
    let term = C.Ann x' y'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr And" $ do
    let expr = And x y
    let term = C.And x' y'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Or" $ do
    let expr = Or x y
    let term = C.Or x' y'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr For -- empty" $ do
    let expr = For [] x
    let term = C.Var "x"
    lower expr `shouldBe` term
    lift term `shouldBe` x

  it "☯ lower/lift Expr For -- unbound" $ do
    let expr = For ["y"] x
    let term = C.Var "x"
    lower expr `shouldBe` term
    lift term `shouldBe` x

  it "☯ lower/lift Expr For -- bound" $ do
    let expr = For ["x"] x
    let term = C.For "x" x'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr For -- Fun explicit bindings" $ do
    let expr = For [] (fun [x, y] z)
    let term = C.fun [x', y'] z'
    lower expr `shouldBe` term
    lift term `shouldBe` fun [x, y] z

  it "☯ lower/lift Expr Fun -- implicit bindings" $ do
    let expr = fun [x, y] z
    let term = C.for ["x", "y"] (C.fun [x', y'] z')
    lower expr `shouldBe` term
    lift term `shouldBe` for ["x", "y"] expr

  it "☯ lower/lift Expr App -- type match" $ do
    let expr = App x y
    let term = C.App x' y'
    lower expr `shouldBe` term
    lift term `shouldBe` App x y

  it "☯ lower/lift Expr Call" $ do
    let expr = Call "+" [x, y]
    let term = C.Call "+" [x', y']
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Op1" $ do
    let expr = Op1 Neg x
    let term = C.App (C.Var "-") x'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Op2 ==" $ do
    let expr = Op2 Eq x y
    let term = C.App (C.Var "==") (C.And x' y')
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Op2 <" $ do
    let expr = Op2 Lt x y
    let term = C.App (C.Var "<") (C.And x' y')
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Op2 >" $ do
    let expr = Op2 Gt x y
    let term = C.App (C.Var ">") (C.And x' y')
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Op2 +" $ do
    let expr = Op2 Add x y
    let term = C.App (C.Var "+") (C.And x' y')
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Op2 -" $ do
    let expr = Op2 Sub x y
    let term = C.App (C.Var "-") (C.And x' y')
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Op2 *" $ do
    let expr = Op2 Mul x y
    let term = C.App (C.Var "*") (C.And x' y')
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Op2 /" $ do
    let expr = Op2 Div x y
    let term = C.App (C.Var "/") (C.And x' y')
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Op2 ^" $ do
    let expr = Op2 Pow x y
    let term = C.App (C.Var "^") (C.And x' y')
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Let atom" $ do
    let expr = Let (Unit, y) z
    let term = C.def [] (C.Unit, y') z'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Let Var" $ do
    let expr = Let (x, y) a
    let term = C.Let [("x", y')] a'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Let Ann" $ do
    let expr = Let (Ann x y, z) a
    let term = C.def ["x", "y"] (C.Ann x' y', z') a'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Let And" $ do
    let expr = Let (And x y, z) a
    let term = C.def ["x", "y"] (C.And x' y', z') a'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Let Or" $ do
    let expr = Let (Or x y, z) a
    let term = C.Let [("x", z')] (C.Let [("y", z')] a')
    lower expr `shouldBe` term
    lift term `shouldBe` lets [(x, z), (y, z)] a

  it "☯ lower/lift Expr Let For empty" $ do
    let expr = Let (For [] x, y) a
    let term = C.def [] (x', y') a'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Let For bound" $ do
    let expr = Let (For ["x", "y"] (And x y), z) a
    let term = C.def ["x", "y"] (C.And x' y', z') a'
    lower expr `shouldBe` term
    lift term `shouldBe` Let (And x y, z) a

  it "☯ lower/lift Expr Let For unbound" $ do
    let expr = Let (For ["x"] (And x y), z) a
    let term = C.def ["x"] (C.And x' y', z') a'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  it "☯ lower/lift Expr Let Fun" $ do
    let expr = Let (Fun x y, z) a
    let term = C.def ["x", "y"] (C.Fun x' y', z') a'
    lower expr `shouldBe` term
    lift term `shouldBe` expr

  -- Bind (Expr, Expr) Expr

  -- If Expr Expr Expr

  it "☯ lower/lift Expr Match -- empty" $ do
    let expr = Match [] []
    let term = C.Err
    lower expr `shouldBe` term
    lift term `shouldBe` Err

  it "☯ lower/lift Expr Match -- no args, one case" $ do
    let expr = Match [] [x]
    let term = x'
    lower expr `shouldBe` term
    lift term `shouldBe` x

  it "☯ lower/lift Expr Match -- no args, many cases" $ do
    let expr = Match [] [x, y]
    let term = C.Or x' y'
    lower expr `shouldBe` term
    lift term `shouldBe` Or x y

  it "☯ lower/lift Expr Match -- args, with function" $ do
    let expr = Match [y] [Fun x z]
    let term = C.App (C.For "x" (C.Fun x' z')) y'
    lower expr `shouldBe` term
    lift term `shouldBe` Let (x, y) z

  -- it "☯ lower/lift Expr Record" $ do
  --   let expr = Record []
  --   let term = C.tag "~" []
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  --   let expr = Record [("a", x), ("b", y)]
  --   let term = C.tag "~a,b" [x', y']
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift Expr Trait -- property" $ do
  --   let env = [(".id", Trait x x)]
  --   let expr = Trait i1 "y"
  --   let term = C.app (C.Var ".y") [C.IntT, i1']
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift Expr Trait -- literal" $ do
  --   let expr = Trait i1 "y"
  --   let term = C.app (C.Var ".y") [C.IntT, i1']
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift Expr Trait -- variable" $ do
  --   let expr = Trait x "y"
  --   let term = C.app (C.Var ".y") [C.IntT, x']
  --   lower [("x", i1')] expr `shouldBe` term
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift Expr Trait -- property" $ do
  --   let expr = Trait x "y"
  --   let term = C.app (C.Var ".y") [C.tag "~y,z" [C.IntT, C.IntT], x']
  --   lower [("x", C.tag "~y,z" [i1', i2'])] expr `shouldBe` term
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift Expr Trait -- undefined" $ do
  --   let expr = Trait x "y"
  --   let term = C.app (C.Var ".y") [C.Err, C.Var "x"]
  --   lower [] expr `shouldBe` C.Err
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift Expr Trait -- function" $ do
  --   let env = [(".id", Trait x x)]
  --   let expr =
  --   let term = C.def ["a"] (C.Var "a", i1') (C.app (C.Var ".y") [C.Ann C.IntT C.IntT, C.Var "a"])
  --   lower env expr `shouldBe` (term, C.Unit, [("aT", C.Ann C.IntT C.IntT), ("a", C.Ann (C.Var "a") C.IntT), ("aTT", C.IntT), ("aT", C.IntT)])
  --   lift term `shouldBe` Match [i1] [For ["a"] $ Fun a (Trait a "y")]

  -- it "☯ lower/lift Expr Select -- empty" $ do
  --   let expr = select (Record [("x", i1), ("y", i2)]) []
  --   let term = C.tag "~" []
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` Record []

  -- it "☯ lower/lift Expr Select -- undefined" $ do
  --   let expr = select (Record [("x", i1), ("y", i2)]) ["z"]
  --   let term = C.tag "~" []
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` Record []

  -- it "☯ lower/lift Expr Select -- reorder" $ do
  --   let expr = select (Record [("x", i1), ("y", i2)]) ["y", "x"]
  --   let term = C.tag "~y,x" [i2', i1']
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` Record [("y", i2), ("x", i1)]

  -- it "☯ lower/lift Expr Select -- remapping" $ do
  --   let expr = Select (Record [("x", i1), ("y", i2)]) [("x", y), ("y", x)]
  --   let term = C.tag "~x,y" [i2', i1']
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` Record [("x", i2), ("y", i1)]

  -- it "☯ lower/lift Expr Select -- application" $ do
  --   let env = [("f", C.Ann (C.Var "f") (C.Fun (C.tag "~x" [C.IntT]) C.NumT))]
  --   let expr = App f (Record [("x", Int 42), ("y", Num 3.14)])
  --   let term = C.App (C.Var "f") (C.tag "~x" [C.Int 42])
  --   lower env expr `shouldBe` term
  --   lift term `shouldBe` App f (Record [("x", Int 42)])

  -- -- Select Expr [(String, Expr)]

  -- it "☯ lower/lift Expr Err" $ do
  --   let expr = Err
  --   let term = C.Err
  --   lower [] expr `shouldBe` term
  --   lift term `shouldBe` expr

  -- it "☯ lower/lift Stmt Import" $ do
  --   let stmt = Import "@pkg/mod" "mod" []
  --   let env = [] :: C.Env
  --   lower [] stmt `shouldBe` env
  --   -- TODO: lift

  --   let stmt = Import "@pkg/mod" "mod" [("x", "y")]
  --   let env = [("y", C.Var "x")] :: C.Env
  --   lower [] stmt `shouldBe` env
  -- -- TODO: lift

  -- it "☯ lower/lift Module" $ do
  --   let mod = Module "mod" [Def $ defVar "x" y]
  --   let env = [("x", C.Var "y")] :: C.Env
  --   lower [] mod `shouldBe` env
  -- -- TODO: lift

  -- it "☯ lower/lift Package" $ do
  --   let pkg = Package "pkg" [Module "mod" [Def $ defVar "x" y]]
  --   let env :: C.Env
  --       env = [("x", C.Var "y")]
  --   lower [] pkg `shouldBe` env
  -- -- TODO: lift env `shouldBe` pkg

  -- it "☯ resolve Stmt" $ do
  --   resolve ("@pkg", "mod") (Def $ defVar "x" y) `shouldBe` [(("@pkg", "mod", "x"), Name "@pkg" "mod" "x")]

  -- it "☯ resolve Module" $ do
  --   let mod =
  --         Module
  --           "mod"
  --           [ Def $ defVar "x" y,
  --             Def $ defVar "y" z
  --           ]
  --   resolve "@pkg" mod `shouldBe` [(("@pkg", "mod", "x"), Name "@pkg" "mod" "x"), (("@pkg", "mod", "y"), Name "@pkg" "mod" "y")]

  -- it "☯ resolve Package" $ do
  --   let pkg =
  --         Package
  --           "@pkg"
  --           [ Module
  --               "mod"
  --               [ Def $ defVar "x" y,
  --                 Def $ defVar "y" z
  --               ]
  --           ]
  --   resolve () pkg `shouldBe` [(("@pkg", "mod", "x"), Name "@pkg" "mod" "x"), (("@pkg", "mod", "y"), Name "@pkg" "mod" "y")]

  -- it "☯ replace Expr" $ do
  --   let f = replace ("@pkg", "mod") [(("@pkg", "mod", "x"), Name "@pkg" "mod" "x")]
  --   -- Int Int
  --   -- Num Double
  --   f (Var "x") `shouldBe` Name "@pkg" "mod" "x"
  --   f (Var "y") `shouldBe` Var "y"
  --   f (Name "@pkg" "mod" "x") `shouldBe` Name "@pkg" "mod" "x"
  --   -- Tag String [Expr]
  --   -- Tuple [Expr]
  --   -- Record [(String, Expr)]
  --   -- Fun Expr Expr
  --   -- App Expr Expr
  --   -- Or Expr Expr
  --   -- Ann Expr Type
  --   -- Call String [Expr]
  --   -- Let Definition Expr
  --   -- Bind Definition Expr
  --   -- Function [Pattern] Expr
  --   -- Match [Expr] [Case]
  --   -- MatchFun [Case]
  --   -- Trait Expr String
  --   -- TraitFun String
  --   -- Select Expr [(String, Expr)]
  --   -- SelectFun [(String, Expr)]
  --   -- With Expr [(String, Expr)]
  --   -- WithFun [(String, Expr)]
  --   -- IfElse Expr Expr Expr
  --   -- Meta C.Metadata Expr
  --   f Err `shouldBe` Err

  -- it "☯ replace Stmt" $ do
  --   let f = replace ("@pkg", "mod") [(("@pkg", "mod", "x"), Name "@pkg" "mod" "x")]
  --   f (Import "@pkg/mod" "mod" [("x", "x")]) `shouldBe` Import "@pkg/mod" "mod" [("x", "x")]
  --   f (Def $ defVar "x" y) `shouldBe` Def (defVar "x" (Var "y"))
  --   f (Def $ defVar "y" x) `shouldBe` Def (defVar "y" (Name "@pkg" "mod" "x"))
  --   f (Test "name" x xP) `shouldBe` Test ">@pkg/mod:name" (Name "@pkg" "mod" "x") (PVar "x")

  -- it "☯ run" $ do
  --   let defs =
  --         [ Def (NameDef "x" [] (Int 42)),
  --           Def (DefTrait (Ann Any IntT) "y" [] (Num 3.14)),
  --           Def (NameDef "f" [i1] i2)
  --         ]
  --   let mod = Package {name = "run", modules = [Module "f" defs]}

  --   run mod Any `shouldBe` Any
  --   run mod (Type ["A"]) `shouldBe` Type ["A"]
  --   run mod IntT `shouldBe` IntT
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
  --   run mod (App f i1) `shouldBe` i2
  --   run mod (App f i2) `shouldBe` Err
  --   -- run mod (Let (Expr, Expr) Expr) `shouldBe` Any
  --   -- run mod (Bind (Expr, Expr) Expr) `shouldBe` Any
  --   -- run mod (TypeDef String [Expr] Expr) `shouldBe` Any
  --   -- run mod (MatchFun [Expr]) `shouldBe` Any
  --   -- run mod (Match [Expr] [Expr]) `shouldBe` Any
  --   run mod (Or x Err) `shouldBe` Int 42
  --   run mod (Or Err x) `shouldBe` Int 42
  --   run mod (Or Err Err) `shouldBe` Err
  --   run mod (Ann x IntT) `shouldBe` Int 42
  --   run mod (Op1 C.Int2Num x) `shouldBe` Num 42.0
  --   run mod (Op2 C.Add x i1) `shouldBe` Int 43
  --   run mod (Meta loc x) `shouldBe` Int 42
  --   run mod Err `shouldBe` Err

  it "☯ splitCamelCase" $ do
    splitCamelCase "" `shouldBe` []
    splitCamelCase "Camel" `shouldBe` ["Camel"]
    splitCamelCase "CamelCase" `shouldBe` ["Camel", "Case"]
    splitCamelCase "CamelCaseABC" `shouldBe` ["Camel", "Case", "ABC"]
    splitCamelCase "CamelABCCase" `shouldBe` ["Camel", "ABC", "Case"]
    splitCamelCase "ABCCamelCase" `shouldBe` ["ABC", "Camel", "Case"]

  it "☯ nameWords" $ do
    nameWords "" `shouldBe` []
    nameWords "camelCase" `shouldBe` ["camel", "case"]
    nameWords "CamelCase" `shouldBe` ["camel", "case"]
    nameWords "snake_case" `shouldBe` ["snake", "case"]
    nameWords "dash-case" `shouldBe` ["dash", "case"]
    nameWords "dot.name" `shouldBe` ["dot", "name"]
    nameWords "/path/name" `shouldBe` ["path", "name"]
    nameWords "multisymbol/.name" `shouldBe` ["multisymbol", "name"]

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

  -- it "☯ rename String" $ do
  --   rename "m" [] "x" `shouldBe` "x"
  --   rename "m" [(("m", "x"), "y")] "x" `shouldBe` "y"

  -- it "☯ rename Expr" $ do
  --   True `shouldBe` True

  -- it "☯ rename Stmt" $ do
  --   rename "m" [(("m", "x"), "y")] (Import "m" "m" [("x", "x")]) `shouldBe` Import "m" "m" [("y", "y")]
  --   rename "m" [(("m", "x"), "y")] (Import "n" "n" [("x", "x")]) `shouldBe` Import "n" "n" [("x", "y")]
  --   rename "m" [(("n", "x"), "y")] (Import "m" "m" [("x", "x")]) `shouldBe` Import "m" "m" [("x", "x")]
  --   rename "n" [(("m", "x"), "y")] (Import "m" "m" [("x", "x")]) `shouldBe` Import "m" "m" [("y", "x")]
  --   rename "m" [(("m", "x"), "y")] (defVarT "x" x x) `shouldBe` defVarT "y" y y

  -- it "☯ rename Module" $ do
  --   True `shouldBe` True

  -- it "☯ rename Package" $ do
  --   -- let m1 x = Module "m1" [Define (Def [] (PVar x) $ Int 42), Define (Def [] yP (Var x))]
  --   -- let m2 _ = Module "m2" [Define (Def [] xP $ Int 42), Define (Def [] yP x)]
  --   -- let m3 x = Module "m3" [Import "pkg" "m1" x [], Define (Def [] yP (Var x))]
  --   -- let m4 x = Module "m4" [Import "pkg" "m1" "m" [(x, x)], Define (Def [] yP (Var x))]
  --   -- let pkg = Package "pkg" [m1 "x", m2 "x", m3 "x", m4 "x"]
  --   -- rename "x" "z" pkg `shouldBe` pkg {modules = [m1 "z", m2 "z", m3 "z", m4 "z"]}
  --   True `shouldBe` True

  -- it "☯ resolveNames Definition" $ do
  --   let ts = [] :: [(String, Type)]
  --   let f m p = resolveNames m (ts, p, Err)
  --   f "@pkg/mod" (PVar "x") `shouldBe` [("@pkg/mod", "x")]
  --   f "@pkg/@pkg" (PVar "x") `shouldBe` [("@pkg", "x")]
  --   f "@pkg/mod" (PVar "_x") `shouldBe` [("_@pkg/mod", "x")]
  --   f "@pkg/_mod" (PVar "x") `shouldBe` [("_@pkg/_mod", "x")]
  --   -- f "pkg/mod" (PTrait xP "y") de`shouldBe` [(".@pkg/mod:x", "y")]
  --   -- f "pkg/mod" (POp1 "+" xP) `shouldBe` [("$1@pkg/mod:x", "+")]
  --   -- f "pkg/mod" (POp2 "+" xP yP) `shouldBe` [("$2@pkg/mod:x:y", "+")]
  --   f "@pkg/mod" (PVar "@pkg/mod.x") `shouldBe` [("@pkg/mod", "x")]
  --   f "@pkg/mod" (PVar "@/mod2.x") `shouldBe` [("@pkg/mod2", "x")]

  -- it "☯ resolveNames Stmt" $ do
  --   let f = resolveNames "@pkg/mod"
  --   f (Import "m" "m" [("x", "y")]) `shouldBe` [("@pkg/mod", "y")]
  --   f (Def $ defVar "x" y) `shouldBe` [("@pkg/mod", "x")]

  -- it "☯ resolveNames Module" $ do
  --   let f stmts = resolveNames "@pkg" (Module "path/mod" stmts)
  --   f [] `shouldBe` []
  --   f [Def $ defVar "x" y] `shouldBe` [("@pkg/path/mod", "x")]

  -- it "☯ findName" $ do
  --   let ctx =
  --         [ ( "pkg/a",
  --             [Def (Var "x", Int 42)]
  --           ),
  --           ( "pkg/b",
  --             [ Import "pkg/a" "m" [("x", "y")],
  --               Def (Var "z", Var "y")
  --             ]
  --           )
  --         ]
  --   findName ctx "pkg/a" "x" `shouldBe` Just ("pkg/a", Int 42)
  --   findName ctx "pkg/a" "y" `shouldBe` (Nothing :: Maybe (String, Expr))
  --   findName ctx "pkg/b" "m" `shouldBe` Just ("pkg/b", Tag "pkg/a" [])
  --   findName ctx "pkg/b" "x" `shouldBe` (Nothing :: Maybe (String, Expr))
  --   findName ctx "pkg/b" "y" `shouldBe` Just ("pkg/a", Int 42)
  --   findName ctx "pkg/b" "z" `shouldBe` Just ("pkg/b", Var "y")

  it "☯ resolve Name" $ do
    let ctx =
          [ ( "pkg/a",
              [defVar ("x", Int 42)]
            ),
            ( "pkg/b",
              [ Import "pkg/a" "m" [("x", "y")],
                defVar ("z", Var "y")
              ]
            )
          ]

    resolve ctx "pkg/a" "x" `shouldBe` [("pkg/a", Let (x, Int 42) x)]
    resolve ctx "pkg/a" "y" `shouldBe` []
    resolve ctx "pkg/b" "m" `shouldBe` [("pkg/b", Tag "pkg/a")]
    resolve ctx "pkg/b" "x" `shouldBe` []
    resolve ctx "pkg/b" "y" `shouldBe` [("pkg/a", Let (x, Int 42) x)]
    resolve ctx "pkg/b" "z" `shouldBe` [("pkg/b", Let (z, y) z)]

  it "☯ resolve Stmt" $ do
    let ctx =
          [ ( "pkg/a",
              [defVar ("x", Int 42)]
            ),
            ( "pkg/b",
              [ Import "pkg/a" "m" [("x", "y")],
                defVar ("z", Var "y")
              ]
            )
          ]

    resolve ctx "pkg/a" ("x", Def (x, i1)) `shouldBe` [("pkg/a", Let (x, i1) x)]
    resolve ctx "pkg/a" ("y", Def (x, i1)) `shouldBe` []
    resolve ctx "pkg/a" ("x", Def (Or x y, i1)) `shouldBe` [("pkg/a", Let (Or x y, i1) x)]
    resolve ctx "pkg/a" ("x", Def (App x y, i1)) `shouldBe` [("pkg/a", Let (App x y, i1) x)]
    resolve ctx "pkg/a" ("y", Def (App x y, i1)) `shouldBe` []

  it "☯ compile Name" $ do
    let ctx =
          [ ( "pkg/a",
              [ defVar ("x", Int 42),
                defVar ("y", Var "y")
              ]
            ),
            ( "pkg/b",
              [ Import "pkg/a" "m" [("x", "y")],
                defVar ("z", Var "y")
              ]
            )
          ]

    compile ctx "pkg/a" "x" `shouldBe` ("x", C.Int 42)
    compile ctx "pkg/a" "y" `shouldBe` ("y", C.Var "y")
    compile ctx "pkg/a" "z" `shouldBe` ("z", C.Err)
    compile ctx "pkg/b" "m" `shouldBe` ("m", C.Tag "pkg/a")
    compile ctx "pkg/b" "x" `shouldBe` ("x", C.Err)
    compile ctx "pkg/b" "y" `shouldBe` ("y", C.Int 42)
    compile ctx "pkg/b" "z" `shouldBe` ("z", C.Let [("y", C.Int 42)] (C.Var "y"))

  it "☯ compile Expr" $ do
    let ctx =
          [ ( "pkg/a",
              [ defVar ("x", i1),
                defVar ("y", y),
                defVar ("f", Ann f (Fun IntT NumT))
              ]
            )
          ]

    compile ctx "pkg/a" Any `shouldBe` C.Any
    compile ctx "pkg/a" Unit `shouldBe` C.Unit
    compile ctx "pkg/a" IntT `shouldBe` C.IntT
    compile ctx "pkg/a" NumT `shouldBe` C.NumT
    compile ctx "pkg/a" (Int 1) `shouldBe` C.Int 1
    compile ctx "pkg/a" (Num 1.0) `shouldBe` C.Num 1.0
    compile ctx "pkg/a" (Var "x") `shouldBe` C.Let [("x", i1')] x'
    compile ctx "pkg/a" (Tag "A") `shouldBe` C.Tag "A"
    compile ctx "pkg/a" (Ann i1 IntT) `shouldBe` C.Ann i1' C.IntT
    compile ctx "pkg/a" (Ann i1 NumT) `shouldBe` C.Ann i1' C.NumT
    compile ctx "pkg/a" (Or i1 (Num 1.1)) `shouldBe` C.Or i1' (C.Num 1.1)
    compile ctx "pkg/a" (For [] x) `shouldBe` C.Let [("x", i1')] x'
    compile ctx "pkg/a" (For [] (Fun x x)) `shouldBe` C.Let [("x", i1')] (C.Fun (C.Ann x' C.IntT) x')
    compile ctx "pkg/a" (For ["x"] x) `shouldBe` C.For "x" x'
    compile ctx "pkg/a" (For ["x"] (Fun x x)) `shouldBe` C.for ["x", "xT"] (C.Fun (C.Ann x' xT') x')
    compile ctx "pkg/a" (Fun x x) `shouldBe` C.for ["x", "xT"] (C.Fun (C.Ann x' xT') x')
    compile ctx "pkg/a" (App f i1) `shouldBe` C.Let [("f", C.Ann (C.Var "f") (C.Fun (C.Ann C.IntT C.IntT) C.NumT))] (C.App (C.Var "f") (C.Ann i1' C.IntT))
    compile ctx "pkg/a" (Call "f" []) `shouldBe` C.Call "f" []
    compile ctx "pkg/a" (Call "f" [i1, Num 1.1]) `shouldBe` C.Call "f" [C.Ann i1' C.IntT, C.Ann (C.Num 1.1) C.NumT]
    -- Op1 Op1 Expr
    -- Op2 Op2 Expr Expr
    -- Let (Expr, Expr) Expr
    -- Bind (Expr, Expr) Expr
    -- If Expr Expr Expr
    -- Match [Expr] [Expr]
    -- Record [(String, Expr)]
    -- Select Expr [(String, Expr)]
    -- With Expr [(String, Expr)]
    compile ctx "pkg/a" Err `shouldBe` C.Err

  it "☯ eval" $ do
    let ctx =
          [ ( "pkg/a",
              [defVar ("x", Int 42)]
            ),
            ( "pkg/b",
              [ Import "pkg/a" "m" [("x", "y")],
                defVar ("z", y),
                defVar ("x", Int 9)
              ]
            )
          ]
    eval ctx "pkg/a" (Int 42) `shouldBe` Int 42
    eval ctx "pkg/a" (Num 3.14) `shouldBe` Num 3.14
    eval ctx "pkg/a" (Var "x") `shouldBe` Int 42
    eval ctx "pkg/b" (Var "x") `shouldBe` Int 9
    eval ctx "pkg/a" (Var "y") `shouldBe` Err
    eval ctx "pkg/a" (Tag "A") `shouldBe` Tag "A"
    -- Record [(String, Maybe Expr, Maybe Expr)]
    -- Fun Expr Expr
    -- App Expr Expr
    eval ctx "pkg/a" (tag "A" [x]) `shouldBe` tag "A" [Int 42]
    -- And Expr Expr
    -- Or Expr Expr
    -- Ann Expr Type
    -- Call String [Expr]
    -- Let [(String, Type)] Pattern Expr Expr
    -- Bind [(String, Type)] Pattern Expr Expr
    -- Match [Expr] [Case]
    -- MatchFun [Case]
    -- Trait Expr String
    -- TraitFun String
    -- Select Expr [(String, Expr)]
    -- SelectFun [(String, Expr)]
    -- With Expr [(String, Expr)]
    -- WithFun [(String, Expr)]
    -- IfElse Expr Expr Expr
    -- Meta C.Metadata Expr
    -- Err
    True `shouldBe` True

  it "☯ test" $ do
    let ctx =
          [ ( "pkg/a",
              [ defVar ("x", i1),
                defVar ("y", i2),
                Test ">x" x i1,
                Test ">y" y i3
              ]
            )
          ]
    let results =
          [ TestPass "pkg/a" ">x",
            TestFail "pkg/a" ">y" (y, i3) (C.Let [("y", i2')] y') i2
          ]
    testAll ctx ("pkg", ctx) `shouldBe` results
