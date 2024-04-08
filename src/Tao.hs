{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Tao where

import Core (BinaryOp (..), Env, Error (..), Metadata (..))
import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import Flow ((|>))

{- TODO: syntax sugar
- Match
- Let
- Do
- Char
- Maybe
- Tuple
- Record
- Text
- List
- Set
- Dict
- From
- Until
- Range
- IfElse
- Vector
- Matrix
- Tensor
- List comprehension
- Set comprehension
- Dict comprehension
-}

data Expr
  = Knd
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Tag String
  | Var String
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Trait Expr String
  | Fun Expr Expr
  | App Expr Expr
  | Let ([(String, Type)], Expr, Expr) Expr
  | Or Expr Expr
  | Op2 BinaryOp Expr Expr
  | Ann Expr Type
  | Meta Metadata Expr
  | Err Error
  deriving (Eq, Show)

data Type
  = For [String] Expr
  deriving (Eq, Show)

data Statement
  = Def [(String, Type)] Expr Expr
  | Import String String [String] -- import module as alias (a, b, c)
  | Test Expr Expr
  | DocString [Metadata] String
  | Comment [Metadata] String
  deriving (Eq, Show)

data Package = Package
  { name :: String,
    modules :: [(String, [Statement])]
  }
  deriving (Eq, Show)

data ParserContext
  = CModule
  | CDefinition
  | CImport
  | CTest
  | CComment
  | CCommentMultiLine
  | CDocString
  | CExpression
  | CLetDef
  | CLetDefTyped String
  | CLetDefTypedVar String
  | CLetDefUntyped String
  | COperator String
  | CPAny
  | CParentheses
  | CRecordField String
  | CTrait
  | CTuple
  | CLetType
  | CTODO -- TODO: REMOVE THIS
  deriving (Eq, Show)

fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

app :: Expr -> [Expr] -> Expr
app = foldl App

ann :: Expr -> Expr -> Expr
ann a t = Ann a (For [] t)

or' :: [Expr] -> Expr
or' [] = error "`or'` must have at least one expression"
or' [a] = a
or' (a : bs) = Or a (or' bs)

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

pow :: Expr -> Expr -> Expr
pow = Op2 Pow

eq :: Expr -> Expr -> Expr
eq = Op2 Eq

lt :: Expr -> Expr -> Expr
lt = Op2 Lt

gt :: Expr -> Expr -> Expr
gt a b = Op2 Gt b a

asFun :: Expr -> ([Expr], Expr)
asFun (Fun a1 a2) = let (bs, b) = asFun a2 in (a1 : bs, b)
asFun (Meta _ a) = asFun a
asFun a = ([], a)

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = let (a', bs) = asApp a in (a', bs ++ [b])
asApp a = (a, [])

meta :: [Metadata] -> Expr -> Expr
meta ms b = foldr Meta b ms

toCore :: Env -> Expr -> C.Expr
toCore _ Knd = C.Knd
toCore _ IntT = C.IntT
toCore _ NumT = C.NumT
toCore _ (Int i) = C.Int i
toCore _ (Num n) = C.Num n
toCore _ (Tag k) = C.Tag k
toCore _ (Var x) = C.Var x
-- toCore env (Lam p b) = do
--   let b' = toCore env b
--   C.Lam (toCoreP (C.freeVars b') p) b'
-- toCore env (LamMatch rules) = toCore env (or' $ map (uncurry lam) rules)
-- toCore env (Match args rules) = toCore env (app (LamMatch rules) args)
toCore env (Tuple items) = toCore env (app (Tag "()") items)
-- toCore (Record fields) = C.Rec (second toCore <$> fields)
-- toCore env (Block defs b) = error "TODO: toCore Block"
toCore env (Trait a x) = do
  let a' = toCore env a
  let (ta, _) = C.infer [] a'
  C.app (C.Var x) [ta, a']
toCore env (App a b) = C.App (toCore env a) (toCore env b)
-- toCore env (Fun a b) = C.Fun (toCore env a) (toCore env b)
toCore env (Or a b) = C.Or (toCore env a) (toCore env b)
toCore env (Op2 op a b) = C.Op2 op (toCore env a) (toCore env b)
-- toCore env (Ann a (For xs t)) = C.Ann (toCore env a) (C.For xs $ toCore env t)
toCore env (Meta m a) = C.Meta m (toCore env a)
toCore env (Err e) = C.Err e
toCore env a = error $ "TODO: toCore " ++ show a

fromCore :: C.Expr -> Expr
-- fromCore (Knd) = _
fromCore C.IntT = IntT
-- fromCore (NumT) = _
fromCore (C.Int i) = Int i
-- fromCore (Num Double) = _
-- fromCore (Tag String) = _
fromCore (C.Var x) = Var x
-- fromCore (Ann Expr Type) = _
-- fromCore (C.Lam p b) = Lam (fromCoreP p) (fromCore b)
-- fromCore (Fix String Expr) = _
-- fromCore (Fun Expr Expr) = _
-- fromCore (Or Expr Expr) = _
fromCore (C.App a b) = App (fromCore a) (fromCore b)
-- fromCore (Typ String [String]) = _
-- fromCore (Op1 UnaryOp Expr) = _
-- fromCore (Op2 BinaryOp Expr Expr) = _
fromCore (C.Meta meta a) = Meta meta (fromCore a)
-- fromCore (Err Error) = _
fromCore (C.Err e) = Err e
fromCore a = error $ "fromCore: not implemented: " ++ show a

dropMetadata :: Expr -> Expr
dropMetadata Knd = Knd
dropMetadata IntT = IntT
dropMetadata NumT = NumT
dropMetadata (Int i) = Int i
dropMetadata (Num n) = Num n
dropMetadata (Tag k) = Tag k
dropMetadata (Var x) = Var x
dropMetadata (Tuple items) = Tuple (map dropMetadata items)
dropMetadata (Record fields) = Record (map (second dropMetadata) fields)
dropMetadata (Trait a k) = Trait (dropMetadata a) k
dropMetadata (Fun a b) = Fun (dropMetadata a) (dropMetadata b)
dropMetadata (App a b) = App (dropMetadata a) (dropMetadata b)
dropMetadata (Let (types, p, a) b) = Let (map (second (\(For xs t) -> For xs (dropMetadata t))) types, dropMetadata p, dropMetadata a) (dropMetadata b)
dropMetadata (Or a b) = Or (dropMetadata a) (dropMetadata b)
dropMetadata (Op2 op a b) = Op2 op (dropMetadata a) (dropMetadata b)
dropMetadata (Ann a (For xs t)) = Ann (dropMetadata a) (For xs (dropMetadata t))
dropMetadata (Meta _ a) = dropMetadata a
dropMetadata (Err err) = Err err

dropMetadataStmt :: Statement -> Statement
dropMetadataStmt (Def types p a) = Def (map (second (\(For xs t) -> For xs (dropMetadata t))) types) (dropMetadata p) (dropMetadata a)
dropMetadataStmt (Import name alias vars) = Import name alias vars
dropMetadataStmt (Test a b) = Test (dropMetadata a) (dropMetadata b)
dropMetadataStmt (DocString _ txt) = DocString [] txt
dropMetadataStmt (Comment _ txt) = Comment [] txt

dropMetadataModule :: (String, [Statement]) -> (String, [Statement])
dropMetadataModule (name, stmts) = (name, map dropMetadataStmt stmts)

dropMetadataPackage :: Package -> Package
dropMetadataPackage pkg = pkg {modules = map dropMetadataModule pkg.modules}