{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Tao where

import Core

data TaoExpr
  = TaoKind
  | TaoIntType
  | TaoNumType
  | TaoInt Int
  | TaoNum Double
  | TaoVar String
  | TaoTag String
  | TaoTuple [TaoExpr]
  | TaoRecord [(String, TaoExpr)]
  | TaoForAll String TaoExpr
  | TaoFun TaoExpr TaoExpr
  | TaoApp TaoExpr TaoExpr
  | TaoOr TaoExpr TaoExpr
  | TaoAnn TaoExpr TaoExpr
  | TaoOp1 UnaryOp TaoExpr
  | TaoOp2 BinaryOp TaoExpr TaoExpr
  | TaoMeta Metadata TaoExpr
  | TaoErr Error
  deriving (Eq, Show)

data TaoStmt
  = TaoDef [(String, TaoExpr)] TaoExpr TaoExpr
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

taoForAll :: [String] -> TaoExpr -> TaoExpr
taoForAll xs a = foldr TaoForAll a xs

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
taoMeta [] a = a
taoMeta (m : ms) a = TaoMeta m (taoMeta ms a)
