module Check where

import Compile (compile, liftTypeError, lower)
import qualified Core as C
import Data.List (intercalate)
import Error (Error (..), TypeError (..))
import Tao

class CheckTypes a where
  checkTypes :: Context -> FilePath -> a -> [Error Expr]

instance CheckTypes Context where
  checkTypes :: Context -> FilePath -> [Module] -> [Error Expr]
  checkTypes ctx path mods = do
    -- let (env, expr') = compile ctx path expr
    -- let (_, _, errors) = C.infer buildOps env expr'
    -- map liftTypeError errors
    -- error "TODO: checkTypes"
    concatMap (checkTypes ctx path) mods

instance CheckTypes Module where
  checkTypes :: Context -> FilePath -> Module -> [Error Expr]
  checkTypes ctx path (_, stmts) = do
    concatMap (checkTypes ctx path) stmts

instance CheckTypes Stmt where
  checkTypes :: Context -> FilePath -> Stmt -> [Error Expr]
  checkTypes ctx path = \case
    Import {} -> []
    Def (p, b) -> do
      let a = lower (Let (p, b) Unit)
      let env = concatMap (compile ctx path) (C.freeNames (True, True, False) a)
      let ((a', t), s, es) = C.infer buildOps env a
      -- case es of
      --   [] -> return ()
      --   _ ->
      --     (error . intercalate "\n")
      --       [ "",
      --         "def: " ++ show (p, b),
      --         "a: " ++ C.format a,
      --         "env: " ++ C.format (C.Let env C.Any),
      --         "a': " ++ C.format a',
      --         "t: " ++ C.format t,
      --         "e: " ++ show es
      --       ]
      map (TypeError . liftTypeError) es
    TypeDef {} -> []
    Test t -> do
      let a = lower (And t.expr t.expect)
      let env = concatMap (compile ctx path) (C.freeNames (True, True, False) a)
      let (_, _, es) = C.infer buildOps env a
      -- (error . intercalate "\n")
      --   [ "",
      --     "a: " ++ C.format a,
      --     "env: " ++ C.format (C.Let env C.Any),
      --     "a': " ++ C.format a',
      --     "t: " ++ C.format t,
      --     "e: " ++ show e
      --   ]
      map (TypeError . liftTypeError) es
