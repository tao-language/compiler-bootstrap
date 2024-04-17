{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Tao where

import Core

data TaoExpr
  = TaoInt Int
  | TaoNum Double
  | TaoVar String
  | TaoTag String [TaoExpr]
  | TaoTuple [TaoExpr]
  | TaoRecord [(String, TaoExpr)]
  | TaoFun TaoExpr TaoExpr
  | TaoApp TaoExpr TaoExpr
  | TaoOr TaoExpr TaoExpr
  | TaoAnn TaoExpr TaoExpr
  | TaoOp1 UnaryOp TaoExpr
  | TaoOp2 BinaryOp TaoExpr TaoExpr
  | TaoLet (TaoExpr, TaoExpr) TaoExpr
  | TaoMeta Metadata TaoExpr
  | TaoErr Error
  deriving (Eq, Show)

data TaoStmt
  = TaoDef TaoExpr TaoExpr
  | TaoTypeAnn String TaoExpr
  | TaoImport String String [String] -- import module as alias (a, b, c)
  | TaoTest TaoExpr TaoExpr
  | TaoDocString [Metadata] String
  | TaoComment [Metadata] String
  deriving (Eq, Show)

type TaoFile = (String, [TaoStmt])

data TaoModule = TaoModule
  { name :: String,
    files :: [TaoFile]
  }
  deriving (Eq, Show)

taoAdd :: TaoExpr -> TaoExpr -> TaoExpr
taoAdd = TaoOp2 Add

taoSub :: TaoExpr -> TaoExpr -> TaoExpr
taoSub = TaoOp2 Sub

taoMul :: TaoExpr -> TaoExpr -> TaoExpr
taoMul = TaoOp2 Mul

taoPow :: TaoExpr -> TaoExpr -> TaoExpr
taoPow = TaoOp2 Pow

taoEq :: TaoExpr -> TaoExpr -> TaoExpr
taoEq = TaoOp2 Eq

taoLt :: TaoExpr -> TaoExpr -> TaoExpr
taoLt = TaoOp2 Lt

taoGt :: TaoExpr -> TaoExpr -> TaoExpr
taoGt = TaoOp2 Gt

taoMeta :: [Metadata] -> TaoExpr -> TaoExpr
taoMeta ms a = foldr TaoMeta a ms

-- To/from Core
exprToCore :: Env -> TaoExpr -> Term
exprToCore _ (TaoInt i) = Int i
exprToCore _ (TaoNum n) = Num n
exprToCore _ (TaoVar x) = Var x
exprToCore env (TaoTag "Type" []) = Knd
exprToCore env (TaoTag "Int" []) = IntT
exprToCore env (TaoTag "Num" []) = NumT
exprToCore env (TaoTag k args) = app (Tag k) (exprToCore env <$> args)
exprToCore _ _ = error "TODO: exprToCore"

exprFromCore :: Term -> TaoExpr
exprFromCore _ = error "TODO: exprFromCore"

moduleToCore :: TaoModule -> Env
moduleToCore TaoModule {files} = error "TODO: moduleToCore"

moduleFromCore :: String -> Env -> TaoModule
moduleFromCore name _ = error "TODO: moduleFromCore"

unpackStmt :: TaoStmt -> [(String, TaoExpr)]
unpackStmt _ = error "TODO: unpackStmt"

unpackFile :: TaoFile -> [(String, TaoExpr)]
unpackFile _ = error "TODO: unpackFile"

unpackModule :: TaoModule -> [(String, TaoExpr)]
unpackModule _ = error "TODO: unpackModule"
