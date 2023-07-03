module Tao where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (foldl')

{- TODO

Clean up compile* functions
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

compile :: Expr -> Either CompileError C.Expr
compile (Int i) = Right (C.Int i)
compile (Num n) = Right (C.Num n)
compile (Var x) = Right (C.Var x)
compile (Lam x a) = do
  a <- compile a
  Right (C.Lam x a)
compile (For x a) = do
  a <- compile a
  Right (C.For x a)
compile (Fun a b) = do
  a <- compile a
  b <- compile b
  Right (C.Fun a b)
compile (App a b) = do
  a <- compile a
  b <- compile b
  Right (C.App a b)
compile (Ann a b) = do
  a <- compile a
  b <- compile b
  Right (C.Ann a b)
compile (Let defs a) = do
  defs <- mapM compileSecond defs
  a <- compile a
  Right (C.Let defs a)
compile (Ctr k args) = do
  args <- mapM compile args
  Right (C.Ctr k args)
compile (Case a cases c) = do
  a <- compile a
  cases <- mapM compileSecond cases
  c <- compile c
  Right (C.Case a cases c)
compile (CaseI a cases c) = do
  a <- compile a
  cases <- mapM compileSecond cases
  c <- compile c
  Right (C.CaseI a cases c)
compile (Match branches) = do
  branches <- mapM compileBranch branches
  case C.match branches of
    Right expr -> Right expr
    Left err -> Left (TypeError err)
compile (Op op args) = do
  args <- mapM compile args
  Right (C.Op op args)
compile (Op2 op a b) = do
  a <- compile a
  b <- compile b
  Right (C.Op (show op) [a, b])

compileSecond :: (a, Expr) -> Either CompileError (a, C.Expr)
compileSecond (k, b) = do
  b <- compile b
  Right (k, b)

compileBranch :: Branch -> Either CompileError C.Branch
compileBranch (Br ps b) = do
  b <- compile b
  Right (C.Br (map compilePattern ps) b)

compilePattern :: Pattern -> C.Pattern
compilePattern AnyP = C.VarP ""
compilePattern (VarP x) = C.VarP x
compilePattern (IntP i) = C.IntP i
compilePattern (CtrP k ps) = C.CtrP k (map compilePattern ps)

bindings :: Pattern -> [String]
bindings AnyP = []
bindings (IntP _) = []
bindings (VarP x) = [x]
bindings (CtrP _ ps) = concatMap bindings ps

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
--   env <- compileEnv ops env env
--   case C.findTyped ops env x of
--     Right (a, t) -> Right (decompile a, decompile t)
--     Left err -> Left (TypeError err)

-- expandUnionAlt :: C.Ops -> Env -> String -> Either CompileError ([Type], Type)
-- expandUnionAlt ops env k = do
--   env <- compileEnv ops env env
--   case C.findTyped ops env k of
--     Right (_, ctrT) -> do
--       let (_, argsT, retT) = C.splitFun ctrT
--       Right (map decompile argsT, decompile retT)
--     Left err -> Left (TypeError err)

-- expandUnionType :: C.Ops -> Env -> String -> Either CompileError ([(String, Type)], [(String, ([Type], Type))])
-- expandUnionType ops env t = do
--   (_, typeArgs, ctrs) <- case lookup t env of
--     Just a -> do
--       term <- compile ops env a
--       case C.asTypeDef term of
--         Right (t, args, ctrs) -> Right (t, map (second decompile) args, ctrs)
--         Left err -> Left (TypeError err)
--     Nothing -> Left (UndefinedUnionType t)
--   altArgs <- mapM (expandUnionAlt ops env) ctrs
--   Right (typeArgs, zip ctrs altArgs)

-- compileEnv :: C.Ops -> Env -> Env -> Either CompileError C.Env
-- compileEnv ops env = mapM (compileNamed ops env)

-- compileNamed :: C.Ops -> Env -> (String, Expr) -> Either CompileError (String, C.Expr)
-- compileNamed ops env (x, a) = do
--   -- a <- compile ops ((x, Var x) : env) a
--   a <- compile ops env a
--   Right (x, a)

-- decompile :: C.Expr -> Expr
-- decompile C.Knd = Knd
-- decompile C.IntT = IntT
-- decompile C.NumT = NumT
-- decompile (C.Int i) = Int i
-- decompile (C.Num n) = Num n
-- decompile (C.Var x) = Var x
-- decompile (C.Lam x a) = Lam x (decompile a)
-- decompile (C.For x a) = For x (decompile a)
-- decompile (C.Fun a b) = Fun (decompile a) (decompile b)
-- decompile (C.App a b) = App (decompile a) (decompile b)
-- decompile (C.Ann a b) = Ann (decompile a) (decompile b)
-- decompile (C.Let env b) = do
--   let decompileDef (x, a) = Def [] (VarP x) (decompile a)
--   Let (decompileDef <$> env) (decompile b)
-- decompile (C.Fix x a) = letVar (x, decompile a) (Var x)
-- decompile (C.Ctr k args) = Ctr k (map decompile args)
-- decompile (C.Typ t args ctrs) = Typ t (map (second decompile) args) ctrs
-- decompile (C.Op op args) = Op op (decompile <$> args)

-- decompileNamed :: (String, C.Expr) -> (String, Expr)
-- decompileNamed (x, a) = (x, decompile a)

-- decompileEnv :: C.Env -> Env
-- decompileEnv = map decompileNamed

-- freeVars :: C.Ops -> Env -> Expr -> Either CompileError [String]
-- freeVars ops env a = do
--   a <- compile ops env a
--   Right (C.freeVars a)

-- occurs :: C.Ops -> Env -> String -> Expr -> Either CompileError Bool
-- occurs ops env x a = do
--   vars <- freeVars ops env a
--   Right (x `elem` vars)

-- infer :: C.Ops -> Env -> Expr -> Either CompileError (Type, Env)
-- infer ops env expr = do
--   term <- compile ops env expr
--   env <- compileEnv ops env env
--   case C.infer ops env term of
--     Right (type', env) -> Right (decompile type', decompileEnv env)
--     Left err -> Left (TypeError err)

-- eval :: C.Ops -> Env -> Expr -> Either CompileError (Expr, Type)
-- eval ops env expr = do
--   term <- compile ops env expr
--   env <- compileEnv ops env env
--   case C.infer ops env term of
--     Right (type', _) -> Right (decompile (C.eval ops env term), decompile type')
--     Left err -> Left (TypeError err)
