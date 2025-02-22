module Check where

import Compile (compile, liftTypeError, lower)
import qualified Core as C
import Data.List (intercalate)
import Error (TypeError (..))
import Tao

class CheckTypes a where
  checkTypes :: Context -> FilePath -> a -> [TypeError Expr]

instance CheckTypes Context where
  checkTypes :: Context -> FilePath -> [Module] -> [TypeError Expr]
  checkTypes ctx path mods = do
    -- let (env, expr') = compile ctx path expr
    -- let (_, _, errors) = C.infer buildOps env expr'
    -- map liftTypeError errors
    -- error "TODO: checkTypes"
    concatMap (checkTypes ctx path) mods

instance CheckTypes Module where
  checkTypes :: Context -> FilePath -> Module -> [TypeError Expr]
  checkTypes ctx path (_, stmts) = do
    concatMap (checkTypes ctx path) stmts

instance CheckTypes Stmt where
  checkTypes :: Context -> FilePath -> Stmt -> [TypeError Expr]
  checkTypes ctx path = \case
    Import {} -> []
    Def (p, b) -> do
      let a = lower (Let (p, b) Unit)
      let env = concatMap (compile ctx path) (C.freeNames (True, True, False) a)
      let ((a', t), s, e) = C.infer buildOps env a
      -- (error . intercalate "\n")
      --   [ "",
      --     "def: " ++ show (p, b),
      --     "a: " ++ C.format a,
      --     "env: " ++ C.format (C.Let env C.Any),
      --     "a': " ++ C.format a',
      --     "t: " ++ C.format t,
      --     "e: " ++ show e
      --   ]
      map liftTypeError e
    TypeDef {} -> []
    Test {} -> []
