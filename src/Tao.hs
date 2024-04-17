{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Tao where

import qualified Core as C

data Expr
  = Int Int
  | Num Double
  | Var String
  | Tag String [Expr]
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Fun Expr Expr
  | App Expr Expr
  | Or Expr Expr
  | Ann Expr Expr
  | Op1 C.UnaryOp Expr
  | Op2 C.BinaryOp Expr Expr
  | Let (Expr, Expr) Expr
  | Meta C.Metadata Expr
  | Err C.Error
  deriving (Eq, Show)

data Stmt
  = Def Expr Expr
  | TypeAnn String Expr
  | Import String String [String] -- import module as alias (a, b, c)
  | Test Expr Expr
  | DocString [C.Metadata] String
  | Comment [C.Metadata] String
  deriving (Eq, Show)

type File = (String, [Stmt])

data Module = Module
  { name :: String,
    files :: [File]
  }
  deriving (Eq, Show)

taoAdd :: Expr -> Expr -> Expr
taoAdd = Op2 C.Add

taoSub :: Expr -> Expr -> Expr
taoSub = Op2 C.Sub

taoMul :: Expr -> Expr -> Expr
taoMul = Op2 C.Mul

taoPow :: Expr -> Expr -> Expr
taoPow = Op2 C.Pow

taoEq :: Expr -> Expr -> Expr
taoEq = Op2 C.Eq

taoLt :: Expr -> Expr -> Expr
taoLt = Op2 C.Lt

taoGt :: Expr -> Expr -> Expr
taoGt = Op2 C.Gt

taoMeta :: [C.Metadata] -> Expr -> Expr
taoMeta ms a = foldr Meta a ms

-- To/from Core
toCore :: C.Env -> Expr -> C.Term
toCore _ (Int i) = C.Int i
toCore _ (Num n) = C.Num n
toCore _ (Var x) = C.Var x
toCore _ (Tag "Type" []) = C.Knd
toCore _ (Tag "Int" []) = C.IntT
toCore _ (Tag "Num" []) = C.NumT
toCore env (Tag k args) = C.app (C.Tag k) (toCore env <$> args)
toCore _ _ = error "TODO: toCore"

fromCore :: C.Term -> Expr
fromCore _ = error "TODO: fromCore"

toEnv :: Module -> C.Env
toEnv Module {files} = error "TODO: toEnv"

fromEnv :: String -> C.Env -> Module
fromEnv name _ = error "TODO: fromEnv"

unpackStmt :: Stmt -> [(String, Expr)]
unpackStmt _ = error "TODO: unpackStmt"

unpackFile :: File -> [(String, Expr)]
unpackFile _ = error "TODO: unpackFile"

unpackModule :: Module -> [(String, Expr)]
unpackModule _ = error "TODO: unpackModule"
