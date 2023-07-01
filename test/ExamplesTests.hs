module ExamplesTests where

import Tao
import TaoLang
import Test.Hspec

-- TODO: rename to EndToEndTests

examplesTests :: SpecWith ()
examplesTests = describe "--==☯ Examples ☯==--" $ do
  let ops = []

  it "☯ definitions" $ do
    {- examples/definitions.tao
        x = 42
        y = 3.14
    -}
    env <- loadFile "examples" "definitions.tao"
    eval ops env (Var "x") `shouldBe` Right (Int 42, IntT)
    eval ops env (Var "y") `shouldBe` Right (Num 3.14, NumT)

  it "☯ factorial" $ do
    {- examples/factorial.tao
        factorial 0 = 1
        factorial n = n * factorial (n - 1)
    -}
    let f = Var "factorial"
    env <- loadFile "examples" "factorial.tao"
    -- infer ops env f `shouldBe` Right (Fun IntT IntT, env)
    -- eval env (App f (Int 0)) `shouldBe` Int 1
    -- eval env (App f (Int 1)) `shouldBe` Int 1
    -- eval env (App f (Int 2)) `shouldBe` Int 2
    -- eval env (App f (Int 3)) `shouldBe` Int 6
    -- eval env (App f (Int 4)) `shouldBe` Int 24
    -- eval env (App f (Int 5)) `shouldBe` Int 120
    True `shouldBe` True

  -- it "☯ fibonacci" $ do
  --   let f = Var "fibonacci"
  --   env <- loadFile "example/e2e" "fibonacci.tao"
  --   infer' env f `shouldBe` Right (FunT IntT IntT)
  --   reduce env (App f (Int 0)) `shouldBe` Int 0
  --   reduce env (App f (Int 1)) `shouldBe` Int 1
  --   reduce env (App f (Int 2)) `shouldBe` Int 1
  --   reduce env (App f (Int 3)) `shouldBe` Int 2
  --   reduce env (App f (Int 4)) `shouldBe` Int 3
  --   reduce env (App f (Int 5)) `shouldBe` Int 5

  -- it "☯ Bool" $ do
  --   env <- loadFile "example/e2e" "bool.tao"
  --   let (bool, true, false) = (Var "Bool", Var "True", Var "False")
  --   let boolT = SumT "Bool" [("True", bool), ("False", bool)]
  --   infer' env bool `shouldBe` Right TypT
  --   infer' env true `shouldBe` Right boolT
  --   infer' env false `shouldBe` Right boolT
  -- -- it "☯ Bool" $ do
  -- --   -- f False = 0
  -- --   -- f True = 1
  -- --   let f = Var "f"
  -- --   let (i0, i1) = (Int 0, Int 1)
  -- --   let (bool, true, false) = (Var "Bool", Var "True", Var "False")
  -- --   let boolT = SumT "Bool" [("True", bool), ("False", bool)]
  -- --   let env =
  -- --         [ ("f", or' [Lam false i0, Lam true i1]),
  -- --           ("Bool", boolT),
  -- --           ("True", Ctr "Bool" "True"),
  -- --           ("False", Ctr "Bool" "False")
  -- --         ]
  -- --   reduce env (App f i0) `shouldBe` Err
  -- --   reduce env (App f false) `shouldBe` i0
  -- --   reduce env (App f true) `shouldBe` i1
  -- --   infer' env f `shouldBe` Right (FunT boolT IntT)

  -- --   it "☯ Maybe" $ do
  -- --     -- f Nothing = 0
  -- --     -- f (Just x) = x
  -- --     let f = Var "f"
  -- --     let (i0, i1) = (Int 0, Int 1)
  -- --     let (maybe, nothing, just) = (App (Var "Maybe"), Var "Nothing", App (Var "Just"))
  -- --     let maybeT = SumT "Maybe" [("Just", For "a" (FunT a (maybe a))), ("Nothing", For "a" (maybe a))]
  -- --     let env =
  -- --           [ ("f", or' [Lam nothing i0, For "x" (Lam (just x) x)]),
  -- --             ("Maybe", maybeT),
  -- --             ("Just", For "x" (Lam x $ App (Ctr "Just" (For "a" $ maybe a)) x)),
  -- --             ("Nothing", Ctr "Nothing" (For "a" $ maybe a))
  -- --           ]
  -- --     reduce env (App f i0) `shouldBe` Err
  -- --     reduce env (App f nothing) `shouldBe` i0
  -- --     reduce env (App f (just i1)) `shouldBe` i1
  -- --     -- infer' env f `shouldBe` Right (FunT (SumT "Bool" ["True", "False"]) IntT)
  -- --     True `shouldBe` True

  -- --   it "☯ List" $ do
  -- --     True `shouldBe` True

  -- --   it "☯ Vec" $ do
  -- --     True `shouldBe` True

  -- -- it "☯ parseExpr" $ do
  -- --   parseExpr "42" `shouldBe` Right (Int 42)

  -- -- it "☯ parseDef" $ do
  -- --   parseDef "x = y" `shouldBe` Right [("x", y)]
  -- --   parseDef "x : y\nx = z" `shouldBe` Right [("x", Ann z y)]
  -- --   parseDef "x y = 1" `shouldBe` Right [("x", Match [([y'], Int 1)])]
  -- --   parseDef "x y = 1\nx z = 2" `shouldBe` Right [("x", Match [([y'], Int 1), ([z'], Int 2)])]
  -- --   parseDef "x : y\nx z = 1" `shouldBe` Right [("x", Ann (Match [([z'], Int 1)]) y)]
  -- -- -- parseDef "_ = y" `shouldBe` Right []
  -- -- -- parseDef "(A x) = y" `shouldBe` [("x", App (Match [([PCtr "A" [x']], x)]) y)]
  -- -- -- parseDef "(A x y) = z" `shouldBe` [("x", App (Match [([PCtr "A" [x', y']], x)]) z), ("y", App (Match [([PCtr "A" [x', y']], y)]) z)]

  -- -- it "☯ loadEnv" $ do
  -- --   loadEnv "" `shouldReturn` []
  -- --   loadEnv "x = 1" `shouldReturn` [("x", Int 1)]
  -- --   loadEnv "x = 1\n" `shouldReturn` [("x", Int 1)]
  -- --   loadEnv "x = 1\ny = 2" `shouldReturn` [("x", Int 1), ("y", Int 2)]

  -- -- it "☯ loadBlock" $ do
  -- --   loadBlock "42" `shouldReturn` ([], Int 42)
  -- --   loadBlock "x = 1; 42" `shouldReturn` ([("x", Int 1)], Int 42)

  -- -- it "☯ loadFile" $ do
  -- --   loadFile "example/basic" "expr.tao" `shouldReturn` [("x", Int 42)]
  -- --   loadFile "example/basic" "func.tao" `shouldReturn` [("id", Match [([x'], x)])]

  -- -- it "☯ loadModule" $ do
  -- --   loadModule "example/basic" `shouldReturn` [("x", Int 42), ("id", Match [([x'], x)])]

  -- -- it "☯ eval" $ do
  -- --   let env =
  -- --         ("p", Rec [("y", Int 2), ("x", Int 1)]) :
  -- --         ("q", Ann (Var "q") (RecT [("y", IntT), ("x", IntT)])) :
  -- --         prelude
  -- --   let eval src = do (env', expr) <- parseBlock src; TaoLang.eval env (Let env' expr)
  -- --   eval "!error" `shouldBe` Right (Err, Err)
  -- --   eval "Type" `shouldBe` Right (TypT, TypT)
  -- --   eval "Int" `shouldBe` Right (IntT, TypT)
  -- --   eval "42" `shouldBe` Right (Int 42, IntT)
  -- --   eval "(() : Type)" `shouldBe` Right (TupT [], TypT)
  -- --   eval "((Int,) : Type)" `shouldBe` Right (TupT [IntT], TypT)
  -- --   -- eval "()" `shouldBe` Right (Tup [], TupT [])
  -- --   -- eval "(1,)" `shouldBe` Right (Tup [Int 1], TupT [IntT])
  -- --   -- eval "(1, Int)" `shouldBe` Right (Tup [Int 1, IntT], TupT [IntT, TypT])
  -- --   -- eval "(1, Int,)" `shouldBe` Right (Tup [Int 1, IntT], TupT [IntT, TypT])
  -- --   -- eval "(x : Int)" `shouldBe` Right (RecT [("x", IntT)], TypT)
  -- --   -- eval "(x : Int,)" `shouldBe` Right (RecT [("x", IntT)], TypT)
  -- --   -- eval "(x : Int, y : Type)" `shouldBe` Right (RecT [("x", IntT), ("y", TypT)], TypT)
  -- --   -- eval "(y : Type, x : Int,)" `shouldBe` Right (RecT [("x", IntT), ("y", TypT)], TypT)
  -- --   -- eval "(x = 1)" `shouldBe` Right (Rec [("x", Int 1)], RecT [("x", IntT)])
  -- --   -- eval "(x = 1,)" `shouldBe` Right (Rec [("x", Int 1)], RecT [("x", IntT)])
  -- --   -- eval "(x = 1, y = 2)" `shouldBe` Right (Rec [("x", Int 1), ("y", Int 2)], RecT [("x", IntT), ("y", IntT)])
  -- --   -- eval "(y = 2, x = 1,)" `shouldBe` Right (Rec [("x", Int 1), ("y", Int 2)], RecT [("x", IntT), ("y", IntT)])
  -- --   -- eval "(x = 1).x" `shouldBe` Right (Int 1, IntT)
  -- --   -- eval "p.x" `shouldBe` Right (Int 1, IntT)
  -- --   -- eval "p.y" `shouldBe` Right (Int 2, IntT)
  -- --   -- eval "q.x" `shouldBe` Right (Get (Var "q") "x", IntT)
  -- --   -- eval "q.y" `shouldBe` Right (Get (Var "q") "y", IntT)
  -- --   -- eval "(p | x = Int)" `shouldBe` Right (Rec [("x", IntT), ("y", Int 2)], RecT [("x", TypT), ("y", IntT)])
  -- --   -- eval "(p | x = Int,)" `shouldBe` Right (Rec [("x", IntT), ("y", Int 2)], RecT [("x", TypT), ("y", IntT)])
  -- --   -- eval "(p | x = Int, y = 0)" `shouldBe` Right (Rec [("x", IntT), ("y", Int 0)], RecT [("x", TypT), ("y", IntT)])
  -- --   -- eval "(q | x = Int)" `shouldBe` Right (Set (Var "q") [("x", IntT)], RecT [("x", TypT), ("y", IntT)])
  -- --   eval "T = A; A" `shouldBe` Right (Ctr "T" "A", SumT [("A", ([], Var "T"))])
  -- --   eval "x = 1; x" `shouldBe` Right (Int 1, IntT)
  -- -- -- TODO: ForT
  -- -- -- TODO: FunT
  -- -- -- TODO: Lam
  -- -- -- TODO: App
  -- -- -- TODO: Ann
  -- -- -- TODO: If
  -- -- -- TODO: Let
  -- -- -- TODO: Match
  -- -- -- TODO: TypeOf
  -- -- -- TODO: Op

  -- -- it "☯ factorial" $ do
  -- --   env <- loadFile "example/e2e" "factorial.tao"
  -- --   let f = Var "factorial"
  -- --   let factorial n = eval (env ++ prelude) (App f (Int n))
  -- --   factorial 0 `shouldBe` Right (Int 1, IntT)
  -- --   factorial 1 `shouldBe` Right (Int 1, IntT)
  -- --   factorial 5 `shouldBe` Right (Int 120, IntT)
  -- --   fmap snd (eval (env ++ prelude) f) `shouldBe` Right (FunT IntT IntT)

  -- -- it "☯ fibonacci" $ do
  -- --   env <- loadFile "example/e2e" "fibonacci.tao"
  -- --   let f = Var "fibonacci"
  -- --   let fibonacci n = eval (env ++ prelude) (App f (Int n))
  -- --   fibonacci 0 `shouldBe` Right (Int 0, IntT)
  -- --   fibonacci 1 `shouldBe` Right (Int 1, IntT)
  -- --   fibonacci 2 `shouldBe` Right (Int 1, IntT)
  -- --   fibonacci 3 `shouldBe` Right (Int 2, IntT)
  -- --   fibonacci 4 `shouldBe` Right (Int 3, IntT)
  -- --   fibonacci 5 `shouldBe` Right (Int 5, IntT)
  -- --   fmap snd (eval (env ++ prelude) f) `shouldBe` Right (FunT IntT IntT)

  it "☯ TODO" $ do
    True `shouldBe` True
