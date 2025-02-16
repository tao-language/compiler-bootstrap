module Check where

import qualified Core as C
import Error (TypeError (..))
import Tao

checkTypes :: Context -> String -> Expr -> [TypeError Expr]
checkTypes ctx path expr = do
  let (env, expr') = compile ctx path expr
  let (_, _, errors) = C.infer buildOps env expr'
  map liftTypeError errors
