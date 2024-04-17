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
  | Trait Expr String
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
toCore env (Tuple items) = toCore env (Tag "()" items)
toCore env (Record fields) = do
  let toCoreField (k, v) = (k, toCore env v)
  C.Rec (toCoreField <$> fields)
toCore env (Trait a x) = do
  let a' = toCore env a
  let (t, _) = C.infer env a'
  C.app (C.Var x) [t, a']
toCore env (Fun a b) = C.Fun (toCore env a) (toCore env b)
toCore env (App a b) = C.App (toCore env a) (toCore env b)
toCore env (Or a b) = C.Or (toCore env a) (toCore env b)
toCore env (Ann a b) = C.Ann (toCore env a) (toCore env b)
toCore env (Op1 op a) = C.Op1 op (toCore env a)
toCore env (Op2 op a b) = C.Op2 op (toCore env a) (toCore env b)
toCore env (Meta m a) = C.Meta m (toCore env a)
toCore _ (Err err) = C.Err err
toCore _ a = error $ "TODO: toCore " ++ show a

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
