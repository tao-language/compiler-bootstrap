{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Check where

import qualified Core as C
import Tao

data Issue
  = MissingCases
  | UnreachableCase
  | Error C.Error
  deriving (Eq, Show)

data TestFailure = TestFailure
  { name :: String,
    expr :: Expr,
    expected :: Expr,
    actual :: Expr
  }
  deriving (Eq, Show)

checkTypes :: Module -> [Issue]
checkTypes mod = do
  let env = C.annotate (lowerModule mod)
  let errs = concatMap (C.errors . snd) env
  map Error errs

checkMissingCases :: Module -> [Issue]
checkMissingCases mod = error "TODO: checkMissingCases"

checkUnreachableCases :: Module -> [Issue]
checkUnreachableCases mod = error "TODO: checkUnreachableCases"

check :: Module -> [Issue]
check mod = error "TODO: check"

test :: Module -> [TestFailure]
test mod = error "TODO: test"
