module ObjectOriented where

import qualified Core as C
import Tao

data Class
  = Class
  {
  }
  deriving (Eq, Show)

typeDefAsClass :: String -> [Stmt] -> Class
typeDefAsClass name stmts =
  Class
    {
    }
