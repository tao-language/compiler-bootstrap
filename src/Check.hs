{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Check where

import Core
import Flow ((|>))
import Tao

data Message
  = MissingCases
  | UnreachableCase
  | Error Error
  deriving (Eq, Show)

data TestFailure = TestFailure
  { name :: String,
    expr :: TaoExpr,
    expected :: TaoExpr,
    actual :: TaoExpr
  }
  deriving (Eq, Show)

checkTypes :: TaoModule -> [Message]
checkTypes TaoModule {files} = concatMap checkTypesFile files

checkTypesFile :: (String, [TaoStmt]) -> [Message]
checkTypesFile (_, stmts) = concatMap checkTypesStmt stmts

checkTypesStmt :: TaoStmt -> [Message]
checkTypesStmt stmt = error "TODO: checkTypesStmt"

checkTypesExpr :: TaoExpr -> [Message]
checkTypesExpr expr = error "TODO: checkTypesExpr"

checkMissingCases :: TaoModule -> [Message]
checkMissingCases mod = error "TODO: checkMissingCasesTaoModule"

checkUnreachableCases :: TaoModule -> [Message]
checkUnreachableCases mod = error "TODO: checkUnreachableCasesTaoModule"

check :: TaoModule -> [Message]
check mod = error "TODO: check"

run :: TaoModule -> TaoExpr -> TaoExpr
run = error "TODO: run"

test :: TaoModule -> Either Error [TestFailure]
test mod = error "TODO: test"
