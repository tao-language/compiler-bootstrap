module PythonTests where

import PrettyPrint (pretty)
import Python
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Python ☯==--" $ do
  let ctx = PyCtx {globals = [], locals = [], nameIndex = 0}
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (PyName "x", PyName "y", PyName "z")
  let (a', b') = (PyName "a", PyName "b")

  it "☯ buildExpr" $ do
    buildExpr ctx Any `shouldBe` (ctx, PyName "_")
    buildExpr ctx IntType `shouldBe` (ctx, PyName "int")
    buildExpr ctx NumType `shouldBe` (ctx, PyName "float")
    buildExpr ctx (Int 42) `shouldBe` (ctx, PyInteger 42)
    buildExpr ctx (Num 3.14) `shouldBe` (ctx, PyFloat 3.14)
    buildExpr ctx (Var "x") `shouldBe` (ctx, PyName "x")
    buildExpr ctx (Tag "A" []) `shouldBe` (ctx, pyCall (PyName "A") [])
    buildExpr ctx (Tag "A" [x, y]) `shouldBe` (ctx, pyCall (PyName "A") [x', y'])
    buildExpr ctx (Tuple []) `shouldBe` (ctx, PyTuple [])
    buildExpr ctx (Tuple [x, y]) `shouldBe` (ctx, PyTuple [x', y'])
    -- buildExpr ctx (Record []) `shouldBe` (ctx, PyDict [])
    -- buildExpr ctx (Record [("a", x), ("b", y)]) `shouldBe` (ctx, PyDict [(a', x'), (b', y')])
    -- buildExpr ctx (Trait x "y") `shouldBe` (ctx, pyCall (PyAttribute x' "y") [])
    -- buildExpr ctx ListNil `shouldBe` (ctx, pyCall (PyName "_ListNil") [])
    -- buildExpr ctx ListCons `shouldBe` (ctx, pyCall (PyName "_ListCons") [])
    -- buildExpr ctx TextNil `shouldBe` (ctx, pyCall (PyName "_TextNil") [])
    -- buildExpr ctx TextCons `shouldBe` (ctx, pyCall (PyName "_TextCons") [])
    -- buildExpr ctx (Type []) `shouldBe` (ctx, pyCall (PyName "Type") [PyList []])
    -- buildExpr ctx (Type ["A", "B"]) `shouldBe` (ctx, pyCall (PyName "Type") [PyList [PyName "A", PyName "B"]])
    -- buildExpr ctx (Fun x y) `shouldBe`
    -- Fun Expr Expr
    -- App Expr Expr
    -- Let (Expr, Expr) Expr
    -- Bind (Expr, Expr) Expr
    -- TypeDef String [Expr] Expr
    -- MatchFun [Expr]
    -- Match [Expr] [Expr]
    -- Or Expr Expr
    -- Ann Expr Expr
    -- Op1 C.UnaryOp Expr
    -- Op2 C.BinaryOp Expr Expr
    -- Meta C.Metadata Expr
    -- Err
    True `shouldBe` True

  it "☯ buildStmt Import" $ do
    buildStmt (Import "mod" "mod" []) ctx `shouldBe` ctx {globals = [PyImport "mod" Nothing]}
    buildStmt (Import "mod" "alias" []) ctx `shouldBe` ctx {globals = [PyImport "mod" (Just "alias")]}
    buildStmt (Import "mod" "mod" [("a", "a"), ("b", "c")]) ctx `shouldBe` ctx {globals = [PyImport "mod" Nothing, PyImportFrom "mod" [("a", Nothing), ("b", Just "c")]]}

  it "☯ buildStmt Def" $ do
    buildStmt (Def (DefName "x" Any) [] y) ctx `shouldBe` ctx {locals = [PyAssign [x'] y']}

  it "☯ buildModule" $ do
    let stmts =
          [ Def (DefName "x" Any) [] (Int 1),
            Def (DefName "y" Any) [] (Int 2)
          ]
    let pyStmts =
          [ PyAssign [x'] (PyInteger 1),
            PyAssign [y'] (PyInteger 2)
          ]
    buildModule (Module {name = "mod", stmts = stmts}) `shouldBe` PyModule {name = "mod", body = pyStmts}

  -- it "☯ emitStmt" $ do
  --   let emitStmt' stmt stmts = fst $ apply (emitStmt target stmt stmts) newContext
  --   let prettyStmt stmt stmts = do
  --         let body = emitStmt' stmt stmts
  --         pretty 80 "    " (layoutModule $ newModule "m" body)
  --   emitStmt' (T.letDef "x" (T.Var "y")) [] `shouldBe` [Assign [Name "x"] (Name "y")]
  --   -- TODO: LetDef function
  --   -- TODO: LetPat
  --   emitStmt' (T.letTrait T.PIntT "x" (T.Var "y")) [] `shouldBe` []
  --   emitStmt' (T.letType "Void" [] []) []
  --     `shouldBe` [ ClassDef {decorators = [Name "dataclass"], name = "Void", typeParams = [], bases = [], body = []}
  --                ]
  --   -- emitStmt' (T.letType "Unit" [] [("A", T.For [] $ T.Tag "Unit")]) []
  --   --   `shouldBe` [ ClassDef {decorators = [Name "dataclass"], name = "Unit", typeParams = [], bases = [], body = []},
  --   --                ClassDef {decorators = [Name "dataclass"], name = "A", typeParams = [], bases = [], body = []}
  --   --              ]
  --   -- emitStmt' (T.letType "Unit" [] [("A", T.For [] $ T.Tag "Unit")]) [T.letTrait (T.PTag "Bool") "not" (T.Var "not_def")]
  --   --   `shouldBe` [ newClassDef "Unit" [] [newFunctionDef "not" [] [Return (Name "not_def")]],
  --   --                newClassDef "A" [TypeVar "Unit"] []
  --   --              ]
  --   -- TODO: Unbox
  --   -- TODO: Import
  --   emitStmt' (T.import' "m") [] `shouldBe` [Import "m" Nothing]
  --   -- TODO: Prompt
  --   True `shouldBe` True

  it "☯ emitDef" $ do
    True `shouldBe` True
