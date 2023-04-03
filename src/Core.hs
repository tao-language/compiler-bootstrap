{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (Foldable (foldl'))
import Data.List (intercalate)

{- TODO:

Exhaustive pattern checks
- Add `Ctr String String Term Type` in Context -- Ctr TypeName CtrName LambdaTerm Type
- Add `SumT String [String] Type` in Context -- SumT TypeName Alts Type
- Constructors and named types represented by Var

Clean up code
- Show Term with precedence

Exhaustive pattern checks (warnings, not errors)
- Find all available cases
  - Usually all the constructors on a union type
  - Can be filtered if a type says a constructor is not possible (e.g. `head`)

Function / operator overloading
- Via inferred type classes

Do notation
- Overload (<-) operator

-}

data Term
  = Knd
  | Typ !String
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Var !String
  | Lam !String !Term
  | For !String !Term
  | Fun !Type !Type
  | App !Term !Term
  | Fix !String !Term
  | Op !String ![Term]
  deriving (Eq)

showParen' :: Bool -> String -> String
showParen' True a = "(" ++ a ++ ")"
showParen' False a = a

showPrefix :: Int -> Int -> String -> Term -> String
showPrefix p q op a = showParen' (p > q) (op ++ showPrec (q + 1) a)

showInfixL :: Int -> Int -> Term -> String -> Term -> String
showInfixL p q a op b = showParen' (p > q) (showPrec q a ++ op ++ showPrec (q + 1) b)

showInfixR :: Int -> Int -> Term -> String -> Term -> String
showInfixR p q a op b = showParen' (p > q) (showPrec (q + 1) a ++ op ++ showPrec q b)

showPrec :: Int -> Term -> String
showPrec _ Knd = "%Type"
showPrec _ (Typ t) = "#" ++ t
showPrec _ IntT = "%Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "%Num"
showPrec _ (Num n) = show n
showPrec _ (Var x) = x
showPrec p (For x a) = showPrefix p 2 ("@" ++ x ++ ". ") a
showPrec p (Lam x a) = showPrefix p 2 ("\\" ++ x ++ " -> ") a
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (App a b) = showInfixL p 3 a " " b
showPrec p (Fix x a) = showPrefix p 2 ("%fix " ++ x ++ " -> ") a
showPrec _ (Op op args) = "%" ++ op ++ " (" ++ intercalate ", " (show <$> args) ++ ")"

instance Show Term where
  show :: Term -> String
  show a = showPrec 0 a

type Type = Term

type Ops = [(String, [Term] -> Maybe Term)]

type Env = [(String, Term)]

data Symbol
  = Val !Term
  | Ann !Term !Type
  | Ctr !(String, Term) !Type
  | Union ![String] !Type
  deriving (Eq, Show)

type Context = [(String, Symbol)]

data TypeError
  = EmptyCase
  | CtrMissingType !String !String
  | InfiniteType !String !Term
  | InvalidCtr !String !Symbol
  | InvalidOp !String !Symbol
  | Mismatch !Term !Term
  | NotASumType !Type
  | RuntimeError
  | UndefinedCtr !String
  | UndefinedOp !String
  | UndefinedVar !String
  deriving (Eq, Show)

fun :: [Type] -> Type -> Type
fun bs ret = foldr Fun ret bs

lam :: [String] -> Term -> Term
lam xs a = foldr Lam a xs

app :: Term -> [Term] -> Term
app = foldl' App

let' :: (String, Term) -> Term -> Term
let' (x, a) b = App (Lam x b) a

pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

set :: Eq k => k -> v -> [(k, v)] -> [(k, v)]
set _ _ [] = []
set x y ((x', _) : kvs) | x == x' = (x, y) : kvs
set x y (kv : kvs) = kv : set x y kvs

eval :: Ops -> Env -> Term -> Term
eval _ _ Knd = Knd
eval _ _ (Typ t) = Typ t
eval _ _ IntT = IntT
eval _ _ NumT = NumT
eval _ _ (Int i) = Int i
eval _ _ (Num n) = Num n
eval ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just a -> eval ops ((x, Var x) : env) a
  Nothing -> Var x
eval ops env (For x a) = For x (eval ops ((x, Var x) : env) a)
eval ops env (Lam x a) = Lam x (eval ops ((x, Var x) : env) a)
eval ops env (Fun a b) = Fun (eval ops env a) (eval ops env b)
eval ops env (App a b) = case (eval ops env a, eval ops env b) of
  (Lam x a, b) -> eval ops ((x, b) : env) a
  (Fix x a, b) -> eval ops ((x, Fix x a) : env) (App a b)
  (a, b) -> App a b
eval ops env (Fix x a) = Fix x (eval ops ((x, Var x) : env) a)
eval ops env (Op op args) = do
  let args' = eval ops env <$> args
  case lookup op ops of
    Just f -> case f args' of
      Just a -> eval ops env a
      Nothing -> Op op args'
    Nothing -> Op op args'

spine :: Term -> [Term]
spine (App a b) = spine a ++ [b]
spine a = [a]

ctxEnv :: Context -> Env
ctxEnv [] = []
ctxEnv ((x, Val a) : ctx) = (x, a) : ctxEnv ctx
ctxEnv ((x, Ann a _) : ctx) = (x, a) : ctxEnv ctx
ctxEnv ((x, Ctr (_, a) _) : ctx) = (x, a) : ctxEnv ctx
ctxEnv ((x, Union _ _) : ctx) = (x, Typ x) : ctxEnv ctx

solve :: Ops -> Context -> Term -> Term
solve ops ctx = eval ops (ctxEnv ctx)

occurs :: String -> Term -> Bool
occurs _ Knd = False
occurs _ (Typ _) = False
occurs _ IntT = False
occurs _ (Int _) = False
occurs _ NumT = False
occurs _ (Num _) = False
occurs x (Var y) = x == y
occurs x (For x' _) | x == x' = False
occurs x (For _ a) = occurs x a
occurs x (Lam x' _) | x == x' = False
occurs x (Lam _ a) = occurs x a
occurs x (Fun a b) = occurs x a || occurs x b
occurs x (App a b) = occurs x a || occurs x b
occurs x (Fix x' _) | x == x' = False
occurs x (Fix _ a) = occurs x a
occurs x (Op _ args) = any (occurs x) args

apply :: Ops -> (String, Term) -> Symbol -> Symbol
apply ops sub (Val a) = Val (eval ops [sub] a)
apply ops sub (Ann a b) = Ann (eval ops [sub] a) (eval ops [sub] b)
apply ops sub (Ctr (t, a) b) = Ctr (t, eval ops [sub] a) (eval ops [sub] b)
apply ops sub (Union alts b) = Union alts (eval ops [sub] b)

unify :: Ops -> Context -> Term -> Term -> Either TypeError Context
unify ops ctx a b = case (solve ops ctx a, solve ops ctx b) of
  (Knd, Knd) -> Right ctx
  (Typ t, Typ t') | t == t' -> Right ctx
  (IntT, IntT) -> Right ctx
  (Int i, Int i') | i == i' -> Right ctx
  (NumT, NumT) -> Right ctx
  (Num n, Num n') | n == n' -> Right ctx
  (Var x, Var x') | x == x' -> Right ctx
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> Right (set x (Val b) (second (apply ops (x, b)) <$> ctx))
  (a, Var y) -> unify ops ctx (Var y) a
  (For x a, b) -> do
    let xT = newName (x ++ "T") (map fst ctx)
    ctx <- unify ops ((xT, Ann (Var xT) Knd) : (x, Ann (Var x) (Var xT)) : ctx) a b
    Right (pop x ctx)
  (a, For x b) -> do
    let xT = newName (x ++ "T") (map fst ctx)
    ctx <- unify ops ((xT, Ann (Var xT) Knd) : (x, Ann (Var x) (Var xT)) : ctx) a b
    Right (pop x ctx)
  -- TODO: Lam
  (Fun a1 a2, Fun b1 b2) -> do
    ctx <- unify ops ctx a1 b1
    unify ops ctx a2 b2
  (App a1 a2, App b1 b2) -> do
    ctx <- unify ops ctx a1 b1
    unify ops ctx a2 b2
  -- TODO: Op
  (a, b) -> Left (Mismatch a b)

instantiate :: Ops -> Context -> Type -> (Type, Context)
instantiate ops ctx (For x a) = do
  let y = newName x (map fst ctx)
  let a' = eval ops [(x, Var y)] a
  instantiate ops ((y, Val (Var y)) : ctx) a'
instantiate ops ctx a = (solve ops ctx a, ctx)

inferType :: Ops -> Context -> Term -> Either TypeError (Type, Context)
inferType _ ctx Knd = Right (Knd, ctx)
inferType _ ctx (Typ _) = Right (Knd, ctx)
inferType _ ctx IntT = Right (Knd, ctx)
inferType _ ctx (Int _) = Right (IntT, ctx)
inferType _ ctx NumT = Right (Knd, ctx)
inferType _ ctx (Num _) = Right (NumT, ctx)
inferType ops ctx (Var x) = case lookup x ctx of
  Just (Val (Var x')) | x == x' -> do
    let xT = newName (x ++ "T") (map fst ctx)
    Right (Var xT, (xT, Val (Var xT)) : (x, Ann (Var x) (Var xT)) : ctx)
  Just (Val a) -> do
    (aT, ctx) <- inferType ops ((x, Val (Var x)) : ctx) a
    Right (aT, pop x ctx)
  Just (Ann (Var x') a) | x == x' -> Right (solve ops ctx a, ctx)
  Just (Ann a b) -> do
    ctx <- checkType ops ctx a b
    Right (solve ops ctx b, ctx)
  Just (Ctr _ b) -> Right (solve ops ctx b, ctx)
  Just (Union _ b) -> Right (solve ops ctx b, ctx)
  Nothing -> Left (UndefinedVar x)
inferType ops ctx (For x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (aT, ctx) <- inferType ops ((xT, Ann (Var xT) Knd) : (x, Ann (Var x) (Var xT)) : ctx) a
  case (aT, pop x ctx) of
    (Var xT', ctx) | xT == xT' -> Right (For xT $ Var xT, ctx)
    (aT, ctx) -> Right (aT, ctx)
inferType ops ctx (Lam x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (t2, ctx) <- inferType ops ((xT, Ann (Var xT) Knd) : (x, Ann (Var x) (Var xT)) : ctx) a
  case (solve ops ctx (Var xT), pop x ctx) of
    (t1, ctx) | xT `occurs` t1 -> Right (For xT $ Fun t1 t2, ctx)
    (t1, ctx) -> Right (Fun t1 t2, ctx)
inferType ops ctx (Fun a b) = do
  ctx <- checkType ops ctx a Knd
  ctx <- checkType ops ctx b Knd
  Right (Knd, ctx)
inferType ops ctx (App a b) = do
  let xT = newName "_app" (map fst ctx)
  (ta, ctx) <- inferType ops ((xT, Val (Var xT)) : ctx) a
  (tb, ctx) <- inferType ops ctx b
  ctx <- unify ops ctx (Fun tb (Var xT)) ta
  Right (solve ops ctx (Var xT), pop xT ctx)
inferType ops ctx (Fix x a) | x `occurs` a = do
  let xT = newName (x ++ "T") (map fst ctx)
  (_, ctx) <- inferType ops ((xT, Ann (Var xT) Knd) : (x, Ann (Var x) (Var xT)) : ctx) a
  Right (solve ops ctx (Var xT), pop x ctx)
inferType ops ctx (Fix _ a) = inferType ops ctx a
inferType ops ctx (Op op args) = case lookup op ctx of
  Just (Ann _ b) -> do
    (bT, ctx) <- inferType ops ((op, Ann (Var op) b) : ctx) (app (Var op) args)
    Right (bT, pop op ctx)
  Just sym -> Left (InvalidOp op sym)
  Nothing -> Left (UndefinedOp op)

checkType :: Ops -> Context -> Term -> Type -> Either TypeError Context
checkType ops ctx a b = do
  (ta, ctx) <- inferType ops ctx a
  unify ops ctx ta b

newName :: String -> [String] -> String
newName x xs = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` xs) names
