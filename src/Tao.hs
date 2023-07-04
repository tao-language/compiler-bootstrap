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
  | Let !Env !Expr
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
  = Value !String !(Maybe Type) !Expr
  | Unpack !Pattern ![(String, Type)] !Expr
  | UnionType !String ![(String, Type)] ![(String, Type)]
  deriving (Eq, Show)

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
  defs <- mapM toCoreSecond defs
  a <- toCore a
  Right (C.Let defs a)
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
fromCore (C.Let defs a) = Let (map (second fromCore) defs) (fromCore a)
fromCore (C.Fix x a) = Let [(x, fromCore a)] (Var x)
fromCore (C.Ctr k args) = Ctr k (map fromCore args)
fromCore (C.Case a cases c) = Case (fromCore a) (map (second fromCore) cases) (fromCore c)
fromCore (C.CaseI a cases c) = CaseI (fromCore a) (map (second fromCore) cases) (fromCore c)
fromCore (C.Op "==" [a, b]) = Op2 Eq (fromCore a) (fromCore b)
fromCore (C.Op "<" [a, b]) = Op2 Lt (fromCore a) (fromCore b)
fromCore (C.Op "+" [a, b]) = Op2 Add (fromCore a) (fromCore b)
fromCore (C.Op "-" [a, b]) = Op2 Sub (fromCore a) (fromCore b)
fromCore (C.Op "*" [a, b]) = Op2 Mul (fromCore a) (fromCore b)
fromCore (C.Op op args) = Op op (map fromCore args)

-- bindings :: Pattern -> [String]
-- bindings AnyP = []
-- bindings (IntP _) = []
-- bindings (VarP x) = [x]
-- bindings (CtrP _ ps) = concatMap bindings ps

-- unpack :: Definition -> Env
-- unpack (Def types p a) = do
--   let unpackVar x = do
--         let value = App (match [Br [p] (Var x)]) a
--         case lookup x types of
--           Just type' -> (x, Ann value type')
--           Nothing -> (x, value)
--   unpackVar <$> bindings p

-- unpack (DefT t args alts) = do
--   let unpackAlt (ctr, (ctrArgs, retT)) = do
--         let value = lam (map fst ctrArgs) (Ctr ctr (map (Var . fst) ctrArgs))
--         let type' = for (map fst args) (fun (snd <$> ctrArgs) retT)
--         (ctr, Ann value type')
--   (t, Typ t args (fst <$> alts)) : map unpackAlt alts

-- findTyped :: C.Ops -> Env -> String -> Either CompileError (Expr, Type)
-- findTyped ops env x = do
--   env <- toCoreEnv ops env env
--   case C.findTyped ops env x of
--     Right (a, t) -> Right (detoCore a, detoCore t)
--     Left err -> Left (TypeError err)

-- expandUnionAlt :: C.Ops -> Env -> String -> Either CompileError ([Type], Type)
-- expandUnionAlt ops env k = do
--   env <- toCoreEnv ops env env
--   case C.findTyped ops env k of
--     Right (_, ctrT) -> do
--       let (_, argsT, retT) = C.splitFun ctrT
--       Right (map detoCore argsT, detoCore retT)
--     Left err -> Left (TypeError err)

-- expandUnionType :: C.Ops -> Env -> String -> Either CompileError ([(String, Type)], [(String, ([Type], Type))])
-- expandUnionType ops env t = do
--   (_, typeArgs, ctrs) <- case lookup t env of
--     Just a -> do
--       term <- toCore ops env a
--       case C.asTypeDef term of
--         Right (t, args, ctrs) -> Right (t, map (second detoCore) args, ctrs)
--         Left err -> Left (TypeError err)
--     Nothing -> Left (UndefinedUnionType t)
--   altArgs <- mapM (expandUnionAlt ops env) ctrs
--   Right (typeArgs, zip ctrs altArgs)

-- toCoreEnv :: C.Ops -> Env -> Env -> Either CompileError C.Env
-- toCoreEnv ops env = mapM (toCoreNamed ops env)

-- toCoreNamed :: C.Ops -> Env -> (String, Expr) -> Either CompileError (String, C.Expr)
-- toCoreNamed ops env (x, a) = do
--   -- a <- toCore ops ((x, Var x) : env) a
--   a <- toCore ops env a
--   Right (x, a)

-- detoCore :: C.Expr -> Expr
-- detoCore C.Knd = Knd
-- detoCore C.IntT = IntT
-- detoCore C.NumT = NumT
-- detoCore (C.Int i) = Int i
-- detoCore (C.Num n) = Num n
-- detoCore (C.Var x) = Var x
-- detoCore (C.Lam x a) = Lam x (detoCore a)
-- detoCore (C.For x a) = For x (detoCore a)
-- detoCore (C.Fun a b) = Fun (detoCore a) (detoCore b)
-- detoCore (C.App a b) = App (detoCore a) (detoCore b)
-- detoCore (C.Ann a b) = Ann (detoCore a) (detoCore b)
-- detoCore (C.Let env b) = do
--   let detoCoreDef (x, a) = Def [] (VarP x) (detoCore a)
--   Let (detoCoreDef <$> env) (detoCore b)
-- detoCore (C.Fix x a) = letVar (x, detoCore a) (Var x)
-- detoCore (C.Ctr k args) = Ctr k (map detoCore args)
-- detoCore (C.Typ t args ctrs) = Typ t (map (second detoCore) args) ctrs
-- detoCore (C.Op op args) = Op op (detoCore <$> args)

-- detoCoreNamed :: (String, C.Expr) -> (String, Expr)
-- detoCoreNamed (x, a) = (x, detoCore a)

-- detoCoreEnv :: C.Env -> Env
-- detoCoreEnv = map detoCoreNamed

-- freeVars :: C.Ops -> Env -> Expr -> Either CompileError [String]
-- freeVars ops env a = do
--   a <- toCore ops env a
--   Right (C.freeVars a)

-- occurs :: C.Ops -> Env -> String -> Expr -> Either CompileError Bool
-- occurs ops env x a = do
--   vars <- freeVars ops env a
--   Right (x `elem` vars)

-- infer :: C.Ops -> Env -> Expr -> Either CompileError (Type, Env)
-- infer ops env expr = do
--   term <- toCore ops env expr
--   env <- toCoreEnv ops env env
--   case C.infer ops env term of
--     Right (type', env) -> Right (detoCore type', detoCoreEnv env)
--     Left err -> Left (TypeError err)

-- eval :: C.Ops -> Env -> Expr -> Either CompileError (Expr, Type)
-- eval ops env expr = do
--   term <- toCore ops env expr
--   env <- toCoreEnv ops env env
--   case C.infer ops env term of
--     Right (type', _) -> Right (detoCore (C.eval ops env term), detoCore type')
--     Left err -> Left (TypeError err)
