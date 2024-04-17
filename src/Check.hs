{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Check where

import qualified Core as C
import Flow ((|>))
import Tao

data Message
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

checkTypes :: Module -> [Message]
checkTypes Module {files} = concatMap checkTypesFile files

checkTypesFile :: (String, [Stmt]) -> [Message]
checkTypesFile (_, stmts) = concatMap checkTypesStmt stmts

checkTypesStmt :: Stmt -> [Message]
checkTypesStmt stmt = error "TODO: checkTypesStmt"

checkTypesExpr :: Expr -> [Message]
checkTypesExpr expr = error "TODO: checkTypesExpr"

checkMissingCases :: Module -> [Message]
checkMissingCases mod = error "TODO: checkMissingCasesModule"

checkUnreachableCases :: Module -> [Message]
checkUnreachableCases mod = error "TODO: checkUnreachableCasesModule"

check :: Module -> [Message]
check mod = error "TODO: check"

run :: Module -> Expr -> Expr
run = error "TODO: run"

test :: Module -> Either C.Error [TestFailure]
test mod = error "TODO: test"
