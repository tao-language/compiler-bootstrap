module Check where

import qualified Core as C
import Data.List (intercalate)
import Error (Error (..), TypeError (..))
import Location
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

-- TODO: there's a lot of duplication here, maybe type classes for each case
instance CheckTypes Stmt where
  checkTypes :: Context -> FilePath -> Stmt -> [Error Expr]
  checkTypes ctx path = \case
    Import {} -> []
    -- LetDef (p, op, b) -> do
    --   let expr = (Let (p, op, b) (Tuple []))
    --   let (env, a) = compile ctx path expr
    --   check $ lift $ C.let' env a
    TypeDef {} -> []
    Test name expr expect -> do
      let (env, a) = compile ctx path (Tuple [expr, expect])
      check $ lift $ C.let' env a
    -- Run expr -> do
    --   let (env, a) = compile ctx path expr
    --   check $ lift $ C.let' env a
    Nop m -> check (Meta m Err)
