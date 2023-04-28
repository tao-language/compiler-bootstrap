{-# LANGUAGE TupleSections #-}

module Tao where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (foldl', union)
import Data.Maybe (fromMaybe)

{- TODO

Patterns
- `IfP !Pattern !Expr` -- pattern guard
- `AnnP !Pattern !Pattern` -- get type information (TypeOf)
- `OrP !Pattern !Pattern`

-}

data Expr
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Var !String
  | Lam !String !Expr
  | For !String !Expr
  | Fun !Type !Type
  | App !Expr !Expr
  | Typ !String ![Expr]
  | Ctr !String ![Expr]
  | Get !String !Expr !String
  | Let ![Definition] !Expr
  | Case !Expr ![(Pattern, Expr)]
  | Match ![Expr] ![([Pattern], Expr)] !Expr
  | TypeOf !Expr
  | Eq !Expr !Expr
  | Lt !Expr !Expr
  | Add !Expr !Expr
  | Sub !Expr !Expr
  | Mul !Expr !Expr
  | Err
  deriving (Eq, Show)

data Pattern
  = AnyP
  | VarP !String
  | -- | AsP !Pattern !String
    CtrP !String ![Pattern]
  deriving (Eq, Show)

type Type = Expr

type Definition = ([(String, Type)], Pattern, Expr)

data Symbol
  = Val !Expr
  | Ann !Expr !Type
  | UnionType ![(String, Type)] ![String]
  | UnionAlt !String ![(String, Type)] !Type
  deriving (Eq, Show)

type Context = [(String, Symbol)]

data CompileError
  = CtrArgsMismatch !String ![String] ![Pattern]
  | EmptyCase
  | MissingCase !String
  | NotAUnionAlt !String !Symbol
  | NotAUnionType !String !Symbol
  | UndefinedCtrField !String !String
  | UndefinedUnionAlt !String
  | UndefinedUnionType !String
  deriving (Eq, Show)

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

fun :: [Type] -> Type -> Type
fun ts t = foldr Fun t ts

lam :: [String] -> Expr -> Expr
lam xs a = foldr Lam a xs

let' :: [(String, Expr)] -> Expr -> Expr
let' [] b = b
let' ((x, a) : defs) b = let' defs (App (Lam x b) a)

-- andP :: [Pattern] -> Pattern
-- andP [] = EqP Nil
-- andP (p : ps) = foldl' AndP p ps

-- let' :: [Definition] -> Expr -> Expr
-- let' defs a = foldr Let a defs

-- get :: key -> [(key, value)] -> Maybe value
-- get _ [] = Nothing
-- get k ((k', v) : _) | k == k' = Just v
-- get k (_ : env) = get k env

unpack :: Context -> Definition -> Either CompileError Context
unpack _ (_, AnyP, _) = Right []
unpack _ (types, VarP x, a) = case lookup x types of
  Just t -> Right [(x, Ann a t)]
  Nothing -> Right [(x, Val a)]
unpack _ (_, CtrP _ [], _) = Right []
unpack ctx (types, CtrP k ps, a) = do
  (_, args, _) <- getUnionAlt ctx k
  case fst <$> args of
    xs | length ps /= length xs -> Left (CtrArgsMismatch k xs ps)
    xs -> do
      ctxs <- mapM (\(p, x) -> unpack ctx (types, p, Get k a x)) (zip ps xs)
      Right (concat ctxs)

getUnionType :: Context -> String -> Either CompileError ([(String, Type)], [String])
getUnionType ctx t = case lookup t ctx of
  Just (UnionType args ks) -> Right (args, ks)
  Just a -> Left (NotAUnionType t a)
  Nothing -> Left (UndefinedUnionType t)

getUnionAlt :: Context -> String -> Either CompileError (String, [(String, Type)], Type)
getUnionAlt ctx k = case lookup k ctx of
  Just (UnionAlt t args retT) -> Right (t, args, retT)
  Just a -> Left (NotAUnionAlt k a)
  Nothing -> Left (UndefinedUnionAlt k)

expandUnionType :: Context -> String -> Either CompileError ([(String, Type)], [(String, ([(String, Type)], Type))])
expandUnionType ctx t = do
  (typeArgs, ks) <- getUnionType ctx t
  altDefs <- mapM (getUnionAlt ctx) ks
  let altArgs = map (\(_, args, retT) -> (args, retT)) altDefs
  Right (typeArgs, zip ks altArgs)

expandBranch :: Context -> Expr -> [(Pattern, Expr)] -> (String, [String]) -> Either CompileError Expr
expandBranch _ _ [] (k, _) = Left (MissingCase k)
expandBranch _ _ ((AnyP, branch) : _) (_, xs) = Right (lam xs branch)
expandBranch _ a ((VarP x, branch) : _) (_, xs) =
  Right (lam xs (Let [([], VarP x, a)] branch))
expandBranch ctx _ ((CtrP k ps, branch) : _) (k', xs) | k == k' = do
  (_, args, _) <- getUnionAlt ctx k
  let expandArg (x, p, field) a = Lam x (Let [([], p, Get k (Var x) field)] a)
  Right (foldr expandArg branch (zip3 xs ps (fst <$> args)))
expandBranch ctx a ((CtrP _ _, _) : branches) alt =
  expandBranch ctx a branches alt

findPatternsType :: Context -> [Pattern] -> Either CompileError (Maybe String)
findPatternsType _ [] = Right Nothing
findPatternsType ctx (CtrP k _ : _) = do
  (t, _, _) <- getUnionAlt ctx k
  Right (Just t)
findPatternsType ctx (_ : ps) = findPatternsType ctx ps

compile :: Context -> Expr -> Either CompileError C.Term
compile _ Knd = Right C.Knd
compile _ IntT = Right C.IntT
compile _ NumT = Right C.NumT
compile _ (Int i) = Right (C.Int i)
compile _ (Num n) = Right (C.Num n)
compile _ (Var x) = Right (C.Var x)
compile ctx (Lam x a) = do
  a <- compile ctx a
  Right (C.Lam x a)
compile ctx (For x a) = do
  a <- compile ctx a
  Right (C.For x a)
compile ctx (Fun a b) = do
  a <- compile ctx a
  b <- compile ctx b
  Right (C.Fun a b)
compile ctx (App a b) = do
  a <- compile ctx a
  b <- compile ctx b
  Right (C.App a b)
compile ctx (Typ t args) = do
  args <- mapM (compile ctx) args
  Right (C.Typ t args)
compile ctx (Ctr k args) = do
  (t, _, _) <- getUnionAlt ctx k
  (_, ks) <- getUnionType ctx t
  compile ctx (lam ks (app (Var k) args))
compile ctx (Get k a x) = do
  (_, args, _) <- getUnionAlt ctx k
  case fst <$> args of
    xs | x `elem` xs -> compile ctx (App a (lam xs (Var x)))
    _else -> Left (UndefinedCtrField k x)
compile ctx (Let defs a) = do
  a <- compile ctx a
  envs <- mapM (compileDef ctx) defs
  Right (C.let' (concat envs) a)
compile ctx (Case a branches) = do
  maybeTypeName <- findPatternsType ctx (fst <$> branches)
  case maybeTypeName of
    Just t -> do
      (_, typeAlts) <- expandUnionType ctx t
      let alts = map (\(k, (args, _)) -> (k, "*" <$ args)) typeAlts
      args <- mapM (expandBranch ctx a branches) alts
      compile ctx (app a args)
    Nothing -> case branches of
      [] -> Left EmptyCase
      (p, branch) : _ -> compile ctx (Let [([], p, a)] branch)
compile ctx (Match args branches default') = do
  error "TODO"
compile ctx a = error $ "TODO: " ++ show a

-- compile ctx (Eq a b) = C.Op "==" [compile ctx a, compile ctx b]
-- compile ctx (Lt a b) = C.Op "<" [compile ctx a, compile ctx b]
-- compile ctx (Add a b) = C.Op "+" [compile ctx a, compile ctx b]
-- compile ctx (Sub a b) = C.Op "-" [compile ctx a, compile ctx b]
-- compile ctx (Mul a b) = C.Op "*" [compile ctx a, compile ctx b]

compileSym :: Context -> Symbol -> Either CompileError C.Symbol
compileSym ctx (Val a) = do
  a <- compile ctx a
  Right (C.Val a)
compileSym ctx (Ann a b) = do
  a <- compile ctx a
  b <- compile ctx b
  Right (C.Ann a b)

compileDef :: Context -> Definition -> Either CompileError C.Env
compileDef ctx def = do
  defCtx <- unpack ctx def
  ctx <- mapM (\(x, sym) -> fmap (x,) (compileSym ctx sym)) defCtx
  Right (C.ctxToEnv ctx)

-- findCtr :: [Pattern] -> Maybe String
-- findCtr [] = Nothing
-- findCtr (AnyP : ps) = findCtr ps
-- findCtr (AsP p _ : ps) = findCtr (p : ps)
-- findCtr (VarP _ : ps) = findCtr ps
-- findCtr (CtrP _ k _ : _) = Just k

-- findType :: [Pattern] -> Maybe String
-- findType [] = Nothing
-- findType (CtrP t _ _ : _) = Just t
-- findType (_ : ps) = findType ps

-- compileT :: Env -> Type -> ([String], C.Expr)
-- compileT _ TypT = C.TypT
-- compileT _ NilT = C.NilT
-- compileT _ IntT = C.IntT
-- compileT _ NumT = C.NumT
-- compileT _ (Var x) = ([x], C.Var x)
-- compileT env (For x a) = do
--   let (xs, a') = compileT ((x, Var x) : env) a
--   ([x] `union` xs, a')
-- compileT env (FunT a b) = do
--   let (xs, a') = compileT env a
--   let (ys, b') = compileT env b
--   (xs `union` ys, C.FunT a' b')
-- compileT env (App a b) = do
--   let (xs, a') = compileT env a
--   (xs, C.App a' (compile env b))
-- compileT env (And a b) = do
--   let (xs, a') = compileT env a
--   let (ys, b') = compileT env b
--   (xs `union` ys, C.And a' b')
-- compileT env (Or a b) = do
--   let (xs, a') = compileT env a
--   let (ys, b') = compileT env b
--   (xs `union` ys, C.Or a' b')
-- compileT env (Ann a b) = do
--   let (xs, a') = compileT env a
--   let (ys, b') = compileT env b
--   (xs `union` ys, C.Ann a' b')
-- compileT env a = ([], compile env a)

-- compileP env () =

-- compilePattern :: Env -> Pattern -> ([String], C.Expr)
-- compilePattern _ AnyP = ([""], C.Var "")
-- compilePattern _ (VarP x) = ([x], C.Var x)
-- compilePattern env (AsP p x) = do
--   let (xs, a) = compilePattern env p
--   ([x] `union` xs, C.Eq (C.Var x) a)
-- compilePattern env (AppP p q) = do
--   let (xs, a) = compilePattern env p
--   let (ys, b) = compilePattern env q
--   (xs `union` ys, C.App a b)
-- compilePattern env (AndP p q) = do
--   let (xs, a) = compilePattern env p
--   let (ys, b) = compilePattern env q
--   (xs `union` ys, C.And a b)
-- compilePattern env (OrP p q) = do
--   let (xs, a) = compilePattern env p
--   let (ys, b) = compilePattern env q
--   (xs `union` ys, C.Or a b)
-- compilePattern env (IfP p a) = do
--   let (xs, b) = compilePattern env p
--   (xs, C.If (compile env a) b)
-- compilePattern env (AnnP p q) = do
--   let (xs, a) = compilePattern env p
--   let (ys, b) = compilePattern env q
--   (xs `union` ys, C.Ann a b)
-- compilePattern env (EqP a) = ([], compile env a)

-- compileEnv :: Env -> C.Env
-- compileEnv [] = []
-- compileEnv ((x, a) : env) = (x, compile ((x, Var x) : env) a) : compileEnv env

-- decompile :: C.Expr -> Expr
-- decompile (C.Err e) = Err e
-- decompile C.Nil = Nil
-- decompile (C.Int i) = Int i
-- decompile (C.Num n) = Num n
-- decompile (C.Ctr tc k) = Ctr tc k
-- decompile (C.Var x) = Var x
-- decompile (C.Lam a b) = Lam (EqP (decompile a)) (decompile b)
-- decompile (C.App a b) = App (decompile a) (decompile b)
-- decompile (C.And a b) = And (decompile a) (decompile b)
-- decompile (C.Or a b) = Or (decompile a) (decompile b)
-- decompile (C.If a b) = If (decompile a) (decompile b)
-- decompile (C.Ann a b) = Ann (decompile a) (decompileT b)
-- decompile (C.Op2 C.Eq a b) = Eq (decompile a) (decompile b)
-- decompile (C.Op2 C.Lt a b) = Lt (decompile a) (decompile b)
-- decompile (C.Op2 C.Add a b) = Add (decompile a) (decompile b)
-- decompile (C.Op2 C.Sub a b) = Sub (decompile a) (decompile b)
-- decompile (C.Op2 C.Mul a b) = Mul (decompile a) (decompile b)

-- decompileT :: C.Type -> Type
-- -- ErrT !String
-- -- TypT
-- -- NilT
-- -- IntT
-- -- NumT
-- -- VarT !String
-- -- ForT !String !Type
-- -- FunT !Type !Type
-- -- AppT !Type !TypeArg
-- -- AndT !Type !Type
-- -- OrT !Type !Type
-- -- SumT !String ![(String, Type)]
-- decompileT (C.ErrT e) = ErrT e
-- decompileT C.NilT = NilT

-- decompileEnv :: C.Env -> Env
-- decompileEnv [] = []
-- decompileEnv ((x, a) : env) = (x, decompile a) : decompileEnv env

-- occurs :: String -> Expr -> Bool
-- occurs x expr = C.occurs x (compile [] expr)

-- infer :: Env -> Expr -> Either C.TypeError (Expr, Env)
-- infer env expr = do
--   (expr', env') <- C.infer (compileEnv env) (compile env expr)
--   Right (decompile expr', decompileEnv env')

-- reduce :: Env -> Expr -> Expr
-- reduce env expr = do
--   let env' = compileEnv env
--   let expr' = compile env expr
--   decompile (C.reduce env' expr')
