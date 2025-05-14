module Run where

import qualified Core as C
import Tao

run :: Context -> String -> Expr -> Expr
run ctx path expr = do
  lift $ C.eval runtimeOps $ compile ctx path expr
