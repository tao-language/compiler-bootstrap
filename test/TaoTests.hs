module TaoTests where

import qualified Core as C
import Tao
import qualified Tao as T
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

  it "☯ lower Expr atoms" $ do
    lower Any `shouldBe` C.Any
    lower Unit `shouldBe` C.Unit
    lower IntT `shouldBe` C.IntT
    lower NumT `shouldBe` C.NumT
    lower (Int 42) `shouldBe` C.Int 42
    lower (Num 3.14) `shouldBe` C.Num 3.14
    lower (Tag "A") `shouldBe` C.Tag "A"
    lower (Var "x") `shouldBe` C.Var "x"

  it "☯ lower Expr Ann" $ do
    lower (Ann x y) `shouldBe` C.Ann x' y'

  it "☯ lower Expr And" $ do
    lower (And x y) `shouldBe` C.And x' y'

  it "☯ lower Expr Or" $ do
    lower (Or x y) `shouldBe` C.Or x' y'

  it "☯ lower Expr For" $ do
    lower (For [] x) `shouldBe` x'
    lower (For ["y"] x) `shouldBe` x'
    lower (For ["x"] x) `shouldBe` C.For "x" x'
    lower (For [] (fun [x, y] z)) `shouldBe` C.fun [x', y'] z'

  it "☯ lower Expr Fun" $ do
    lower (fun [x, y] z) `shouldBe` C.for ["x", "y"] (C.fun [x', y'] z')

  it "☯ lower Expr App" $ do
    lower (App x y) `shouldBe` C.App x' y'

  it "☯ lower Expr Call" $ do
    lower (Call "f" [x, y]) `shouldBe` C.Call "f" [x', y']

  it "☯ lower Expr Op1" $ do
    lower (Op1 Neg x) `shouldBe` C.App (C.Var "-") x'

  it "☯ lower Expr Op2" $ do
    lower (Op2 Eq x y) `shouldBe` C.app (C.Var "==") [x', y']
    lower (Op2 Lt x y) `shouldBe` C.app (C.Var "<") [x', y']
    lower (Op2 Gt x y) `shouldBe` C.app (C.Var ">") [x', y']
    lower (Op2 Add x y) `shouldBe` C.app (C.Var "+") [x', y']
    lower (Op2 Sub x y) `shouldBe` C.app (C.Var "-") [x', y']
    lower (Op2 Mul x y) `shouldBe` C.app (C.Var "*") [x', y']
    lower (Op2 Div x y) `shouldBe` C.app (C.Var "/") [x', y']
    lower (Op2 Pow x y) `shouldBe` C.app (C.Var "^") [x', y']

  it "☯ lower Expr Match" $ do
    lower (Match [] []) `shouldBe` C.Err
    lower (Match [] [([], [], x)]) `shouldBe` x'
    lower (Match [] [(["x", "y"], [x, y], z)]) `shouldBe` C.for ["x", "y"] (C.fun [x', y'] z')
    lower (Match [] [([], [], x), ([], [], y)]) `shouldBe` C.Or x' y'
    lower (Match [a, b] [([], [x, y], z)]) `shouldBe` C.app (C.fun [x', y'] z') [a', b']
    lower (Match [a, b] [([], [x, y], z), ([], [], c)]) `shouldBe` C.app (C.fun [x', y'] z' `C.Or` C.fun [C.Any, C.Any] c') [a', b']

  it "☯ lower Expr If" $ do
    lower (If x y z) `shouldBe` C.App (C.Or (C.Fun (C.Tag "True") y') (C.Fun C.Any z')) x'

  it "☯ lower Expr Let atom" $ do
    lower (Let (Unit, y) a) `shouldBe` C.def [] (C.Unit, y') a'

  it "☯ lower Expr Let Var" $ do
    lower (Let (x, y) a) `shouldBe` C.def ["x"] (x', y') a'

  it "☯ lower Expr Let Ann" $ do
    lower (Let (Ann x y, z) a) `shouldBe` C.def ["x", "y"] (x', C.Ann z' y') a'

  it "☯ lower Expr Let And" $ do
    lower (Let (And x y, z) a) `shouldBe` C.def ["x", "y"] (C.And x' y', z') a'

  it "☯ lower Expr Let Or" $ do
    lower (Let (Or x y, z) a) `shouldBe` C.def ["x"] (x', z') (C.def ["y"] (y', z') a')

  it "☯ lower Expr Let For" $ do
    lower (Let (For [] x, y) a) `shouldBe` C.def [] (x', y') a'
    lower (Let (For ["x"] x, y) a) `shouldBe` C.def ["x"] (x', y') a'
    lower (Let (For ["y"] x, y) a) `shouldBe` C.def [] (x', y') a'

  it "☯ lower Expr Let Fun" $ do
    lower (Let (Fun x y, z) a) `shouldBe` C.def ["y"] (C.For "x" $ C.Fun x' y', z') a'

  it "☯ lower Expr Let App" $ do
    lower (Let (App x y, z) a) `shouldBe` C.def ["x"] (x', C.For "y" (C.Fun y' z')) a'

  it "☯ lower Expr Let Call" $ do
    lower (Let (Call "f" [x, y], z) a) `shouldBe` C.def ["x", "y"] (C.Call "f" [x', y'], z') a'

  it "☯ lower Expr Let Op1" $ do
    lower (Let (Op1 Neg x, z) a) `shouldBe` C.def ["-"] (C.Var "-", C.For "x" (C.Fun x' z')) a'

  it "☯ lower Expr Let Op2" $ do
    lower (Let (Op2 Add x y, z) a) `shouldBe` C.def ["+"] (C.Var "+", C.for ["x", "y"] (C.fun [x', y'] z')) a'

  -- it "☯ lower Expr Let Bind" $ do
  --   lower (Let (Bind (x, y) z, a) b) `shouldBe` C.def ["y", "z"] (C.def ["x"] (x', y') z', a') b'

  -- it "☯ lower Expr Let Match" $ do
  --   lower (Let (Match [x] [([], [], y)], a) b) `shouldBe` C.def ["x", "y"] (C.App y' x', a') b'
  --   lower (Let (Match [x] [([], [y], z)], a) b) `shouldBe` C.For "x" (C.def ["y", "z"] (y', x') (C.def [] (z', a') b'))

  it "☯ lower Expr Let If" $ do
    lower (Let (If x y z, a) b) `shouldBe` C.def ["x", "y", "z"] (C.App (C.Or (C.Fun (C.Tag "True") y') (C.Fun C.Any z')) x', a') b'

  it "☯ lower Expr Let Let" $ do
    lower (Let (Let (x, y) z, a) b) `shouldBe` C.def ["y", "z"] (C.def ["x"] (x', y') z', a') b'

  -- Record [(String, Expr)]
  -- Select Expr [(String, Expr)]
  -- With Expr [(String, Expr)]
  -- Err

  -- Bind (Expr, Expr) Expr

  it "☯ lower Expr Record" $ do
    lower (Record []) `shouldBe` C.Tag "~"
    lower (Record [("a", x), ("b", y)]) `shouldBe` C.tag "~a,b" [x', y']

  it "☯ lower Expr Select" $ do
    let record = Record [("x", i1), ("y", i2)]
    lower (select record []) `shouldBe` C.Tag "~"
    lower (select record ["z"]) `shouldBe` C.tag "~z" [z']
    lower (select record ["y", "x"]) `shouldBe` C.tag "~y,x" [i2', i1']
    lower (Select record [("x", y), ("y", x)]) `shouldBe` C.tag "~x,y" [i2', i1']
    lower (select a []) `shouldBe` C.Tag "~"
    lower (select a ["z"]) `shouldBe` C.tag "~z" [C.App z' a']
    lower (select a ["y", "x"]) `shouldBe` C.tag "~y,x" [C.App y' a', C.App x' a']
    lower (Select a [("x", y), ("y", x)]) `shouldBe` C.tag "~x,y" [C.App y' a', C.App x' a']

  -- it "☯ lower Expr Select -- application" $ do
  --   let env = [("f", C.Ann (C.Var "f") (C.Fun (C.tag "~x" [C.IntT]) C.NumT))]
  --   let expr = App f (Record [("x", Int 42), ("y", Num 3.14)])
  --   let term = C.App (C.Var "f") (C.tag "~x" [C.Int 42])
  --   lower expr `shouldBe` term
  --   lift term `shouldBe` App f (Record [("x", Int 42)])

  -- Select Expr [(String, Expr)]

  it "☯ lower Expr Err" $ do
    lower Err `shouldBe` C.Err

  -- it "☯ lower Stmt Import" $ do
  --   let stmt = Import "@pkg/mod" "mod" []
  --   let env = [] :: C.Env
  --   lower [] stmt `shouldBe` env
  --   -- TODO: lift

  --   let stmt = Import "@pkg/mod" "mod" [("x", "y")]
  --   let env = [("y", C.Var "x")] :: C.Env
  --   lower [] stmt `shouldBe` env
  -- -- TODO: lift

  -- it "☯ lower Module" $ do
  --   let mod = Module "mod" [Def $ defVar "x" y]
  --   let env = [("x", C.Var "y")] :: C.Env
  --   lower [] mod `shouldBe` env
  -- -- TODO: lift

  -- it "☯ lower Package" $ do
  --   let pkg = Package "pkg" [Module "mod" [Def $ defVar "x" y]]
  --   let env :: C.Env
  --       env = [("x", C.Var "y")]
  --   lower [] pkg `shouldBe` env
  -- -- TODO: lift env `shouldBe` pkg

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

  it "☯ resolve Name" $ do
    let ctx =
          [ ( "pkg/a",
              [Def (x, i1)]
            ),
            ("pkg/b", [Import "pkg/a" "m" [("x", "y")]]),
            ("pkg/b/@implicit1", [Def (x, i2)]),
            ("pkg/b/@implicit2", [Def (z, y)]),
            ("pkg/c", [Import "pkg/b" "m" [("", "")]])
          ]

    resolve ctx "pkg/a" "x" `shouldBe` [("pkg/a", Let (x, i1) x)]
    resolve ctx "pkg/a" "y" `shouldBe` []
    resolve ctx "pkg/b" "m" `shouldBe` [("pkg/b", Tag "pkg/a")]
    resolve ctx "pkg/b" "x" `shouldBe` [("pkg/b", Let (x, i2) x)]
    resolve ctx "pkg/b" "y" `shouldBe` [("pkg/a", Let (x, i1) x)]
    resolve ctx "pkg/b" "z" `shouldBe` [("pkg/b", Let (z, y) z)]
    resolve ctx "pkg/c" "x" `shouldBe` [("pkg/b", Let (x, i2) x)]
    resolve ctx "pkg/c" "y" `shouldBe` [("pkg/a", Let (x, i1) x)]
    resolve ctx "pkg/c" "z" `shouldBe` [("pkg/b", Let (z, y) z)]

  it "☯ resolve Stmt" $ do
    let ctx =
          [ ( "pkg/a",
              [Def (x, i1)]
            ),
            ( "pkg/b",
              [ Import "pkg/a" "m" [("x", "y")],
                Def (z, y)
              ]
            )
          ]

    resolve ctx "pkg/a" ("x", Def (x, i2)) `shouldBe` [("pkg/a", Let (x, i2) x)]
    resolve ctx "pkg/a" ("y", Def (x, i2)) `shouldBe` []
    resolve ctx "pkg/a" ("x", Def (Or x y, i2)) `shouldBe` [("pkg/a", Let (Or x y, i2) x)]
    resolve ctx "pkg/a" ("x", Def (App x y, i2)) `shouldBe` [("pkg/a", Let (App x y, i2) x)]
    resolve ctx "pkg/a" ("y", Def (App x y, i2)) `shouldBe` []

  it "☯ compile Name" $ do
    let ctx =
          [ ( "pkg/a",
              [ Def (x, i1),
                Def (y, y)
              ]
            ),
            ( "pkg/b",
              [ Import "pkg/a" "m" [("x", "y")],
                Def (z, y)
              ]
            )
          ]

    let compile' path x = compile ctx path x :: C.Env
    compile' "pkg/a" "x" `shouldBe` [("x", i1')]
    compile' "pkg/a" "y" `shouldBe` [("y", y')]
    compile' "pkg/a" "z" `shouldBe` []
    compile' "pkg/b" "m" `shouldBe` [("m", C.Tag "pkg/a")]
    compile' "pkg/b" "x" `shouldBe` []
    compile' "pkg/b" "y" `shouldBe` [("y", i1')]
    compile' "pkg/b" "z" `shouldBe` [("z", C.Let [("y", i1')] y'), ("y", i1')]

  it "☯ compile Expr" $ do
    let ctx =
          [ ( "pkg/a",
              [ Def (x, i1),
                Def (y, y),
                Def (f, Ann f (Fun IntT NumT))
              ]
            )
          ]

    let compile' a = compile ctx "pkg/a" a :: (C.Env, C.Expr)
    compile' Any `shouldBe` ([], C.Any)
    compile' Unit `shouldBe` ([], C.Unit)
    compile' IntT `shouldBe` ([], C.IntT)
    compile' NumT `shouldBe` ([], C.NumT)
    compile' (Int 1) `shouldBe` ([], C.Int 1)
    compile' (Num 1.0) `shouldBe` ([], C.Num 1.0)
    compile' (Var "x") `shouldBe` ([("x", i1')], x')
    compile' (Tag "A") `shouldBe` ([], C.Tag "A")
    compile' (Ann i1 IntT) `shouldBe` ([], i1')
    compile' (Ann i1 NumT) `shouldBe` ([], i1')
    compile' (Or i1 (Num 1.1)) `shouldBe` ([], C.Or i1' (C.Num 1.1))
    compile' (For [] x) `shouldBe` ([("x", i1')], x')
    compile' (For [] (Fun x x)) `shouldBe` ([("x", i1')], C.Fun (C.Ann x' C.IntT) x')
    compile' (For ["x"] x) `shouldBe` ([], C.For "x" x')
    compile' (For ["x"] (Fun x x)) `shouldBe` ([], C.for ["xT", "x"] (C.Fun (C.Ann x' xT') x'))
    compile' (Fun x x) `shouldBe` ([], C.for ["xT", "x"] (C.Fun (C.Ann x' xT') x'))
    compile' (App f i1) `shouldBe` ([("f", f')], C.App (C.Var "f") (C.Ann i1' C.IntT))
    compile' (Call "f" []) `shouldBe` ([], C.Call "f" [])
    compile' (Call "f" [i1, Num 1.1]) `shouldBe` ([], C.Call "f" [i1', C.Num 1.1])
    -- Op1 Op1 Expr
    -- Op2 Op2 Expr Expr
    -- Let (Expr, Expr) Expr
    -- Bind (Expr, Expr) Expr
    -- If Expr Expr Expr
    -- Match [Expr] [Expr]
    -- Record [(String, Expr)]
    -- Select Expr [(String, Expr)]
    -- With Expr [(String, Expr)]
    compile' Err `shouldBe` ([], C.Err)

  it "☯ run" $ do
    let ctx =
          [ ( "pkg/a",
              [Def (x, i1)]
            ),
            ( "pkg/b",
              [ Import "pkg/a" "m" [("x", "y")],
                Def (z, y),
                Def (x, i2)
              ]
            )
          ]
    T.run ctx "pkg/a" (Int 42) `shouldBe` Int 42
    T.run ctx "pkg/a" (Num 3.14) `shouldBe` Num 3.14
    T.run ctx "pkg/a" (Var "x") `shouldBe` Int 1
    T.run ctx "pkg/b" (Var "x") `shouldBe` Int 2
    T.run ctx "pkg/a" (Var "y") `shouldBe` Var "y"
    T.run ctx "pkg/a" (Tag "A") `shouldBe` Tag "A"
    -- Record [(String, Maybe Expr, Maybe Expr)]
    -- Fun Expr Expr
    -- App Expr Expr
    T.run ctx "pkg/a" (tag "A" [x]) `shouldBe` tag "A" [i1]
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
              [ Def (x, i1),
                Def (y, i2),
                Test (UnitTest "pkg/a" (1, 2) ">x" x i1),
                Test (UnitTest "pkg/a" (3, 4) ">y" y i3)
              ]
            )
          ]
    let results =
          [ TestPass "pkg/a" (1, 2) ">x",
            TestFail "pkg/a" (3, 4) ">y" y i3 i2
          ]
    testAll [] ("pkg", ctx) `shouldBe` results
