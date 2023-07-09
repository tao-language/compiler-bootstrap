module Tao where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (foldl')

{- TODO

Clean up toCore* functions
Infer type variables used in definitions (e.g. length of a vector)
Records on inferred type variables for function overloading

Patterns
- `IfP !Pattern !Expr` -- pattern guard
- `AnnP !Pattern !Pattern` -- get type information (TypeOf)
- `OrP !Pattern !Pattern`

-}

data Expr
  = Int !Int
  | Num !Double
  | Var !String
  | Lam !String !Expr
  | For !String !Expr
  | Fun !Expr !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Let ![Definition] !Expr
  | Ctr !String ![Expr]
  | Case !Expr ![(String, Expr)] !Expr
  | CaseI !Expr ![(Int, Expr)] !Expr
  | Match ![Branch]
  | Op !String ![Expr]
  | Op2 !BinaryOp !Expr !Expr
  deriving (Eq, Show)

data BinaryOp
  = Eq
  | Lt
  | Add
  | Sub
  | Mul
  deriving (Eq)

instance Show BinaryOp where
  show Eq = "=="
  show Lt = "<"
  show Add = "+"
  show Sub = "-"
  show Mul = "*"

data Pattern
  = AnyP
  | VarP !String
  | IntP !Int
  | CtrP !String ![Pattern]
  deriving (Eq, Show)

type Type = Expr

data Branch
  = Br ![Pattern] !Expr
  deriving (Eq, Show)

type Env = [(String, Expr)]

data Definition
  = Untyped !String !Expr
  | Typed !String !Type !Expr
  | Unpack !Pattern ![(String, Type)] !Expr
  deriving (Eq, Show)

data ContextDefinition
  = UnionType !String ![(String, Type)] ![(String, Type)]
  | Value !Definition
  deriving (Eq, Show)

type Context = [ContextDefinition]

data CompileError
  = EmptyMatch
  | MatchMissingArgs !Expr
  | NotAUnionAlt !String !Expr
  | TypeError !C.TypeError
  | UndefinedCtrField !String !String
  | UndefinedUnionAlt !String
  | UndefinedUnionType !String
  deriving (Eq, Show)

nameType :: String
nameType = "Type"

nameIntType :: String
nameIntType = "Int"

nameNumType :: String
nameNumType = "Num"

lam :: [String] -> Expr -> Expr
lam xs a = foldr Lam a xs

lamP :: [Pattern] -> Expr -> Expr
lamP [] a = a
lamP (VarP x : ps) a = Lam x (lamP ps a)
lamP ps a = Match [Br ps a]

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

fun :: [Expr] -> Expr -> Expr
fun args b = foldr Fun b args

match :: [Branch] -> Expr
match (Br [] a : _) = a
match [Br ps a] = lamP ps a
match brs = Match brs

toCore :: Expr -> Either CompileError C.Expr
toCore (Int i) = Right (C.Int i)
toCore (Num n) = Right (C.Num n)
toCore (Var x) = Right (C.Var x)
toCore (Lam x a) = do
  a <- toCore a
  Right (C.Lam x a)
toCore (For x a) = do
  a <- toCore a
  Right (C.For x a)
toCore (Fun a b) = do
  a <- toCore a
  b <- toCore b
  Right (C.Fun a b)
toCore (App a b) = do
  a <- toCore a
  b <- toCore b
  Right (C.App a b)
toCore (Ann a b) = do
  a <- toCore a
  b <- toCore b
  Right (C.Ann a b)
toCore (Let defs a) = do
  defs <- mapM toCoreDefs defs
  a <- toCore a
  Right (C.Let (concat defs) a)
toCore (Ctr k args) = do
  args <- mapM toCore args
  Right (C.Ctr k args)
toCore (Case a cases c) = do
  a <- toCore a
  cases <- mapM toCoreSecond cases
  c <- toCore c
  Right (C.Case a cases c)
toCore (CaseI a cases c) = do
  a <- toCore a
  cases <- mapM toCoreSecond cases
  c <- toCore c
  Right (C.CaseI a cases c)
toCore (Match branches) = do
  branches <- mapM toCoreBranch branches
  case C.match branches of
    Right expr -> Right expr
    Left err -> Left (TypeError err)
toCore (Op op args) = do
  args <- mapM toCore args
  Right (C.Op op args)
toCore (Op2 op a b) = do
  a <- toCore a
  b <- toCore b
  Right (C.Op (show op) [a, b])

toCoreSecond :: (a, Expr) -> Either CompileError (a, C.Expr)
toCoreSecond (k, b) = do
  b <- toCore b
  Right (k, b)

toCoreDefs :: Definition -> Either CompileError C.Env
toCoreDefs (Untyped x a) = do
  a <- toCore a
  Right [(x, a)]
toCoreDefs (Typed x t a) = do
  t <- toCore t
  a <- toCore a
  Right [(x, C.Ann a t)]
toCoreDefs (Unpack p ts a) = do
  let unpackVar x = do
        let value = App (match [Br [p] (Var x)]) a
        case lookup x ts of
          Just type' -> (x, Ann value type')
          Nothing -> (x, value)
  mapM (toCoreSecond . unpackVar) (bindings p)

bindings :: Pattern -> [String]
bindings AnyP = []
bindings (IntP _) = []
bindings (VarP x) = [x]
bindings (CtrP _ ps) = concatMap bindings ps

toCoreBranch :: Branch -> Either CompileError C.Branch
toCoreBranch (Br ps b) = do
  b <- toCore b
  Right (C.Br (map toCorePattern ps) b)

toCorePattern :: Pattern -> C.Pattern
toCorePattern AnyP = C.VarP ""
toCorePattern (VarP x) = C.VarP x
toCorePattern (IntP i) = C.IntP i
toCorePattern (CtrP k ps) = C.CtrP k (map toCorePattern ps)

fromCore :: C.Expr -> Expr
fromCore C.Typ = Var nameType
fromCore C.IntT = Var nameIntType
fromCore C.NumT = Var nameNumType
fromCore (C.Int i) = Int i
fromCore (C.Num n) = Num n
fromCore (C.Var x) = Var x
fromCore (C.Lam x a) = Lam x (fromCore a)
fromCore (C.For x a) = For x (fromCore a)
fromCore (C.Fun a b) = Fun (fromCore a) (fromCore b)
fromCore (C.App a b) = App (fromCore a) (fromCore b)
fromCore (C.Ann a b) = Ann (fromCore a) (fromCore b)
fromCore (C.Let defs a) = Let (map (\(x, b) -> Untyped x (fromCore b)) defs) (fromCore a)
fromCore (C.Fix x a) = Let [Untyped x (fromCore a)] (Var x)
fromCore (C.Ctr k args) = Ctr k (map fromCore args)
fromCore (C.Case a cases c) = Case (fromCore a) (map (second fromCore) cases) (fromCore c)
fromCore (C.CaseI a cases c) = CaseI (fromCore a) (map (second fromCore) cases) (fromCore c)
fromCore (C.Op "==" [a, b]) = Op2 Eq (fromCore a) (fromCore b)
fromCore (C.Op "<" [a, b]) = Op2 Lt (fromCore a) (fromCore b)
fromCore (C.Op "+" [a, b]) = Op2 Add (fromCore a) (fromCore b)
fromCore (C.Op "-" [a, b]) = Op2 Sub (fromCore a) (fromCore b)
fromCore (C.Op "*" [a, b]) = Op2 Mul (fromCore a) (fromCore b)
fromCore (C.Op op args) = Op op (map fromCore args)
