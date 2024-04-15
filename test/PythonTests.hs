{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module PythonTests where

import Core
import PrettyPrint (pretty)
import Python
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Python ☯==--" $ do
  -- let target =
  --       builtins
  --         { extern =
  --             [ ("True", targetDef $ Bool True),
  --               ("pi", (targetDef $ Attribute (Name "math") "pi") {globals = [import' "math"]})
  --             ]
  --         }

  -- it "☯ emitExpr" $ do
  --   let emitExpr' expr = apply (emitExpr target expr) newContext
  --   emitExpr' (Int 0) `shouldBe` (Integer 0, newContext)
  --   emitExpr' (Tag "True") `shouldBe` (Bool True, newContext)
  --   emitExpr' (Var "pi") `shouldBe` (Attribute (Name "math") "pi", newContext {globals = [import' "math"]})

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
