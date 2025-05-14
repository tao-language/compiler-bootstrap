module Check where

import qualified Core as C
import Data.List (intercalate)
import Error (Error (..), TypeError (..))
import Location
import Tao

class CheckTypes a where
  checkTypes :: Context -> FilePath -> a -> [(Maybe Location, Error Expr)]

instance CheckTypes Context where
  checkTypes :: Context -> FilePath -> [Module] -> [(Maybe Location, Error Expr)]
  checkTypes ctx path mods = do
    -- let (env, expr') = compile ctx path expr
    -- let (_, _, errors) = C.infer buildOps env expr'
    -- map liftTypeError errors
    -- error "TODO: checkTypes"
    concatMap (checkTypes ctx path) mods

instance CheckTypes Module where
  checkTypes :: Context -> FilePath -> Module -> [(Maybe Location, Error Expr)]
  checkTypes ctx path (_, stmts) = do
    concatMap (checkTypes ctx path) stmts

-- TODO: there's a lot of duplication here, maybe type classes for each case
instance CheckTypes Stmt where
  checkTypes :: Context -> FilePath -> Stmt -> [(Maybe Location, Error Expr)]
  checkTypes ctx path = \case
    Import {} -> []
    Def (p, b) -> do
      let expr = (Let (p, b) (Tuple []))
      check $ lift $ compile ctx path expr
    TypeDef {} -> []
    Test t -> do
      let expr = (Tuple [t.expr, t.expect])
      check $ lift $ compile ctx path expr
    Run expr -> do
      check $ lift $ compile ctx path expr
    Comment _ -> []
