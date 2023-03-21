module Tao where

import qualified Core
import Data.Bifunctor (second)
import Data.List (foldl', union)

-- data Expr
--   = Err !String
--   | Nil
--   | Int !Int
--   | Num !Double
--   | Ctr !String !String
--   | Var !String
--   | For !String !Expr
--   | Lam !Pattern !Expr
--   | App !Expr !Expr
--   | And !Expr !Expr
--   | Or !Expr !Expr
--   | If !Expr !Expr
--   | IfElse !Expr !Expr !Expr
--   | Ann !Expr !Type
--   | Eq !Expr !Expr
--   | Lt !Expr !Expr
--   | Add !Expr !Expr
--   | Sub !Expr !Expr
--   | Mul !Expr !Expr
--   | Let !Definition !Expr
--   | TypeOf !Expr
--   | Match ![([Pattern], Expr)]
--   deriving (Eq, Show)

-- data Type
--   = ErrT !String
--   | TypT
--   | NilT
--   | IntT
--   | NumT
--   | VarT !String
--   | ForT !String !Type
--   | FunT !Type !Type
--   | AppT !Type !TypeArg
--   | AndT !Type !Type
--   | OrT !Type !Type
--   | SumT !String ![(String, Type)]
--   deriving (Eq, Show)

-- data TypeArg
--   = ArgE !Expr
--   | ArgT !Type
--   deriving (Eq, Show)

-- data Pattern
--   = AnyP
--   | VarP !String
--   | AsP !Pattern !String
--   | AppP !Pattern !Pattern
--   | AndP !Pattern !Pattern
--   | OrP !Pattern !Pattern
--   | IfP !Pattern !Expr
--   | AnnP !Pattern !Pattern
--   | EqP !Expr
--   deriving (Eq, Show)

-- type Definition = ([(String, Type)], Pattern, Expr)

-- type Env = [(String, Expr)]

-- for :: [String] -> Expr -> Expr
-- for xs a = foldr For a xs

-- and' :: [Expr] -> Expr
-- and' [] = Nil
-- and' (a : bs) = foldl' And a bs

-- or' :: [Expr] -> Expr
-- or' [] = Nil
-- or' [a] = a
-- or' (a : bs) = Or a (or' bs)

-- app :: Expr -> [Expr] -> Expr
-- app = foldl' App

-- funT :: [Type] -> Type -> Type
-- funT ts t = foldr FunT t ts

-- appP :: Pattern -> [Pattern] -> Pattern
-- appP = foldl' AppP

-- lam :: [Pattern] -> Expr -> Expr
-- lam ps a = foldr Lam a ps

-- andP :: [Pattern] -> Pattern
-- andP [] = EqP Nil
-- andP (p : ps) = foldl' AndP p ps

-- let' :: [Definition] -> Expr -> Expr
-- let' defs a = foldr Let a defs

-- get :: key -> [(key, value)] -> Maybe value
-- get _ [] = Nothing
-- get k ((k', v) : _) | k == k' = Just v
-- get k (_ : env) = get k env

-- unpack :: Definition -> Env
-- unpack def@(types, p, a) = do
--   let annotate :: String -> Expr -> (String, Expr)
--       annotate x a = case get x types of
--         Just t -> (x, Ann a t)
--         Nothing -> (x, a)
--   let unpack' :: Pattern -> Env
--       unpack' (VarP x) | p == VarP x = [annotate x a]
--       unpack' (VarP x) = [annotate x (Let def (Var x))]
--       unpack' (AsP p x) = annotate x a : unpack (types, p, a)
--       unpack' (AppP p q) = unpack' p `union` unpack' q
--       unpack' (AndP p q) = unpack' p `union` unpack' q
--       unpack' (OrP p q) = unpack' p `union` unpack' q
--       unpack' (IfP p cond) = unpack (types, p, If cond a)
--       unpack' (AnnP p q) = unpack' p `union` unpack' q
--       unpack' _ = []
--   unpack' p

-- compile :: Env -> Expr -> Core.Expr
-- compile _ (Err e) = Core.Err e
-- compile _ Nil = Core.Nil
-- compile _ (Int i) = Core.Int i
-- compile _ (Num n) = Core.Num n
-- compile _ (Ctr tc k) = Core.Ctr tc k
-- compile env (Var x) = case get x env of
--   Just (Var x') | x == x' -> Core.Var x
--   Just (Ann (Var x') t) | x == x' -> Core.Ann (Core.Var x) (compile env t)
--   Just a -> compile ((x, Var x) : env) a
--   Nothing -> Core.Err ("undefined variable: " ++ x)
-- -- compile env (For x a) = Core.For x (compile ((x, Var x) : env) a)
-- compile env (FunT a b) = Core.FunT (compile env a) (compile env b)
-- compile env (Lam p a) = Core.Lam (compileP p) (compile env a)
-- compile env (App a b) = Core.App (compile env a) (compile env b)
-- compile env (And a b) = Core.And (compile env a) (compile env b)
-- compile env (Or a b) = Core.Or (compile env a) (compile env b)
-- compile env (If a b) = Core.If (compile env a) (compile env b)
-- compile env (IfElse a b c) = compile env (Or (If a b) c)
-- compile env (Ann a b) = Core.Ann (compile env a) (compileT b)
-- compile env (SumT ts alts) = Core.SumT ts (map (second (compile env)) alts)
-- compile env (Eq a b) = Core.eq (compile env a) (compile env b)
-- compile env (Lt a b) = Core.lt (compile env a) (compile env b)
-- compile env (Add a b) = Core.add (compile env a) (compile env b)
-- compile env (Sub a b) = Core.sub (compile env a) (compile env b)
-- compile env (Mul a b) = Core.mul (compile env a) (compile env b)
-- compile env (Let def a) = compile (env ++ unpack def) a
-- compile env (TypeOf a) = case infer env a of
--   Right (t, env) -> compile env t
--   Left err -> Core.Err (show err)
-- compile env (Match branches) = compile env (or' (map (uncurry lam) branches))

-- compileT :: Env -> Type -> ([String], Core.Expr)
-- compileT _ TypT = Core.TypT
-- compileT _ NilT = Core.NilT
-- compileT _ IntT = Core.IntT
-- compileT _ NumT = Core.NumT
-- compileT _ (Var x) = ([x], Core.Var x)
-- compileT env (For x a) = do
--   let (xs, a') = compileT ((x, Var x) : env) a
--   ([x] `union` xs, a')
-- compileT env (FunT a b) = do
--   let (xs, a') = compileT env a
--   let (ys, b') = compileT env b
--   (xs `union` ys, Core.FunT a' b')
-- compileT env (App a b) = do
--   let (xs, a') = compileT env a
--   (xs, Core.App a' (compile env b))
-- compileT env (And a b) = do
--   let (xs, a') = compileT env a
--   let (ys, b') = compileT env b
--   (xs `union` ys, Core.And a' b')
-- compileT env (Or a b) = do
--   let (xs, a') = compileT env a
--   let (ys, b') = compileT env b
--   (xs `union` ys, Core.Or a' b')
-- compileT env (Ann a b) = do
--   let (xs, a') = compileT env a
--   let (ys, b') = compileT env b
--   (xs `union` ys, Core.Ann a' b')
-- compileT env a = ([], compile env a)

-- compileP env () = 

-- compilePattern :: Env -> Pattern -> ([String], Core.Expr)
-- compilePattern _ AnyP = ([""], Core.Var "")
-- compilePattern _ (VarP x) = ([x], Core.Var x)
-- compilePattern env (AsP p x) = do
--   let (xs, a) = compilePattern env p
--   ([x] `union` xs, Core.Eq (Core.Var x) a)
-- compilePattern env (AppP p q) = do
--   let (xs, a) = compilePattern env p
--   let (ys, b) = compilePattern env q
--   (xs `union` ys, Core.App a b)
-- compilePattern env (AndP p q) = do
--   let (xs, a) = compilePattern env p
--   let (ys, b) = compilePattern env q
--   (xs `union` ys, Core.And a b)
-- compilePattern env (OrP p q) = do
--   let (xs, a) = compilePattern env p
--   let (ys, b) = compilePattern env q
--   (xs `union` ys, Core.Or a b)
-- compilePattern env (IfP p a) = do
--   let (xs, b) = compilePattern env p
--   (xs, Core.If (compile env a) b)
-- compilePattern env (AnnP p q) = do
--   let (xs, a) = compilePattern env p
--   let (ys, b) = compilePattern env q
--   (xs `union` ys, Core.Ann a b)
-- compilePattern env (EqP a) = ([], compile env a)

-- compileEnv :: Env -> Core.Env
-- compileEnv [] = []
-- compileEnv ((x, a) : env) = (x, compile ((x, Var x) : env) a) : compileEnv env

-- decompile :: Core.Expr -> Expr
-- decompile (Core.Err e) = Err e
-- decompile Core.Nil = Nil
-- decompile (Core.Int i) = Int i
-- decompile (Core.Num n) = Num n
-- decompile (Core.Ctr tc k) = Ctr tc k
-- decompile (Core.Var x) = Var x
-- decompile (Core.Lam a b) = Lam (EqP (decompile a)) (decompile b)
-- decompile (Core.App a b) = App (decompile a) (decompile b)
-- decompile (Core.And a b) = And (decompile a) (decompile b)
-- decompile (Core.Or a b) = Or (decompile a) (decompile b)
-- decompile (Core.If a b) = If (decompile a) (decompile b)
-- decompile (Core.Ann a b) = Ann (decompile a) (decompileT b)
-- decompile (Core.Op2 Core.Eq a b) = Eq (decompile a) (decompile b)
-- decompile (Core.Op2 Core.Lt a b) = Lt (decompile a) (decompile b)
-- decompile (Core.Op2 Core.Add a b) = Add (decompile a) (decompile b)
-- decompile (Core.Op2 Core.Sub a b) = Sub (decompile a) (decompile b)
-- decompile (Core.Op2 Core.Mul a b) = Mul (decompile a) (decompile b)

-- decompileT :: Core.Type -> Type
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
-- decompileT (Core.ErrT e) = ErrT e
-- decompileT Core.NilT = NilT

-- decompileEnv :: Core.Env -> Env
-- decompileEnv [] = []
-- decompileEnv ((x, a) : env) = (x, decompile a) : decompileEnv env

-- occurs :: String -> Expr -> Bool
-- occurs x expr = Core.occurs x (compile [] expr)

-- infer :: Env -> Expr -> Either Core.TypeError (Expr, Env)
-- infer env expr = do
--   (expr', env') <- Core.infer (compileEnv env) (compile env expr)
--   Right (decompile expr', decompileEnv env')

-- reduce :: Env -> Expr -> Expr
-- reduce env expr = do
--   let env' = compileEnv env
--   let expr' = compile env expr
--   decompile (Core.reduce env' expr')
