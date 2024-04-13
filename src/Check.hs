{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Check where

import Core (Error (..))
import Tao

data Message
  = MissingCases
  | UnreachableCase
  | Error Error
  deriving (Eq, Show)

checkTypes :: Module -> [Message]
checkTypes = error "TODO: checkTypesModule"

checkMissingCases :: Module -> [Message]
checkMissingCases mod = error "TODO: checkMissingCasesModule"

checkUnreachableCases :: Module -> [Message]
checkUnreachableCases mod = error "TODO: checkUnreachableCasesModule"

check :: Module -> [Message]
check mod = error "TODO: check"

run :: Module -> Expr -> Expr
run = error "TODO: run"

test :: Module -> Either Error [TestFailure]
test mod = error "TODO: test"
