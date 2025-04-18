module Run where

import qualified Core as C
import Tao

run :: Context -> String -> Expr -> Expr
run ctx path expr = do
  let (env, expr') = compile ctx path expr
  lift (C.eval runtimeOps (C.Let env expr'))
