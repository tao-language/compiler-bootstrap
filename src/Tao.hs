{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Tao where

import Core (BinaryOp (..), Env, Error (..), Metadata (..), UnaryOp (..))
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
  | Or Expr Expr
  | Ann Expr Type
  | Op1 UnaryOp Expr
  | Op2 BinaryOp Expr Expr
  | Typ String [String]
  | Let ([(String, Type)], Expr, Expr) Expr
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

data TestFailure = TestFailure
  { name :: String,
    expr :: Expr,
    expected :: Expr,
    actual :: Expr
  }

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

replace :: (String, Expr) -> Expr -> Expr
replace _ Knd = Knd
replace _ IntT = IntT
replace _ NumT = NumT
replace _ (Int i) = Int i
replace _ (Num n) = Num n
replace _ (Tag k) = Tag k
replace (x, a) (Var x') | x == x' = a
replace _ (Var x) = Var x
replace s (Tuple items) = Tuple (replace s <$> items)
replace s (Record fields) = Record (map (second (replace s)) fields)
replace s (Trait a x) = Trait (replace s a) x
replace s (Fun a b) = Fun (replace s a) (replace s b)
replace s (App a b) = App (replace s a) (replace s b)
replace s (Or a b) = Or (replace s a) (replace s b)
replace s (Let (ts, p, a) b) = Let (ts, replace s p, replace s a) (replace s b)
replace s (Op2 op a b) = Op2 op (replace s a) (replace s b)
replace s (Ann a (For xs t)) = Ann (replace s a) (For xs (replace s t))
replace s (Meta m a) = Meta m (replace s a)
replace _ (Err err) = Err err

toCore :: Env -> Expr -> C.Expr
toCore _ Knd = C.Knd
toCore _ IntT = C.IntT
toCore _ NumT = C.NumT
toCore _ (Int i) = C.Int i
toCore _ (Num n) = C.Num n
toCore _ (Tag k) = C.Tag k
toCore _ (Var x) = C.Var x
toCore env (Tuple items) = toCore env (app (Tag "()") items)
toCore env (Record fields) = toCore env (Tuple $ map snd fields)
toCore env (Trait a x) = do
  let a' = toCore env a
  let (ta, _) = C.infer [] a'
  C.app (C.Var x) [ta, a']
toCore env (Fun a b) = C.Fun (toCore env a) (toCore env b)
toCore env (App a b) = C.App (toCore env a) (toCore env b)
toCore env (Or a b) = C.Or (toCore env a) (toCore env b)
toCore env (Ann a (For xs t)) = C.Ann (toCore env a) (C.for xs $ toCore env t)
toCore env (Op1 op a) = C.Op1 op (toCore env a)
toCore env (Op2 op a b) = C.Op2 op (toCore env a) (toCore env b)
toCore _ (Typ k alts) = C.Typ k alts
toCore env (Let ([], p, a) b) = C.let' (toCore env p, toCore env a) (toCore env b)
toCore env (Let ((x, ty) : ts, p, a) b) = toCore env (Let (ts, replace (x, Ann (Var x) ty) p, a) b)
toCore env (Meta m a) = C.Meta m (toCore env a)
toCore _ (Err e) = C.Err e

fromCore :: C.Expr -> Expr
fromCore C.Knd = Knd
fromCore C.IntT = IntT
fromCore C.NumT = NumT
fromCore (C.Int i) = Int i
fromCore (C.Num n) = Num n
fromCore (C.Tag k) = Tag k
fromCore (C.Var x) = Var x
fromCore (C.Ann a b) = do
  let (xs, b') = C.asFor b
  Ann (fromCore a) (For xs $ fromCore b')
fromCore (C.For _ a) = fromCore a
fromCore (C.Fix _ a) = fromCore a
fromCore (C.Fun a b) = Fun (fromCore a) (fromCore b)
fromCore (C.App a b) = App (fromCore a) (fromCore b)
fromCore (C.Or a b) = Or (fromCore a) (fromCore b)
fromCore (C.Op1 op a) = Op1 op (fromCore a)
fromCore (C.Op2 op a b) = Op2 op (fromCore a) (fromCore b)
fromCore (C.Typ k alts) = Typ k alts
fromCore (C.Meta meta a) = Meta meta (fromCore a)
fromCore (C.Err e) = Err e

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
dropMetadata (Or a b) = Or (dropMetadata a) (dropMetadata b)
dropMetadata (Let (types, p, a) b) = Let (map (second (\(For xs t) -> For xs (dropMetadata t))) types, dropMetadata p, dropMetadata a) (dropMetadata b)
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

checkTypesPackage :: Package -> Either Error ()
checkTypesPackage = error "TODO: checkTypesPackage"

checkExhaustivePatternsPackage :: Package -> Either Error ()
checkExhaustivePatternsPackage pkg = error "TODO: checkExhaustivePatternsPackage"

checkRedundantPatternsPackage :: Package -> Either Error ()
checkRedundantPatternsPackage pkg = error "TODO: checkRedundantPatternsPackage"

run :: Package -> Expr -> Expr
run = error "TODO: run"

test :: Package -> Either Error [TestFailure]
test pkg = error "TODO: test"

data Target a = Target
  {
  }
  deriving (Eq, Show)

build :: Package -> Target a -> a
build pkg = error "TODO: build"