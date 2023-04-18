{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (Foldable (foldl'))
import Data.List (delete, intercalate, union)

{- TODO:

- Make Op behave similarly to Ctr
- Don't evaluate args in Op, but include an eval function

Clean up code
- Show Term with precedence

Function / operator overloading
- Via inferred type classes

Do notation
- Overload (<-) operator

-}

data Term
  = Typ
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Var !String
  | Let !Env !Term
  | Lam !String !Term
  | For !String !Term
  | Fun !Type !Type
  | App !Term !Term
  | Ctr !String !Int !Term
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
showPrec _ Typ = "%Type"
showPrec _ IntT = "%Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "%Num"
showPrec _ (Num n) = show n
showPrec _ (Var x) = x
showPrec _ (Let env a) = do
  let showDef (x, b) = x ++ " = " ++ show b
  "@let {" ++ intercalate "; " (showDef <$> env) ++ "} " ++ show a
showPrec p (Lam x a) = showPrefix p 2 ("\\" ++ x ++ " -> ") a
showPrec p (For x a) = showPrefix p 2 ("@" ++ x ++ ". ") a
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (App a b) = showInfixL p 3 a " " b
showPrec _ (Ctr k n a) = "#" ++ k ++ "/" ++ show n ++ " {" ++ show a ++ "}"
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
  deriving (Eq, Show)

type Context = [(String, Symbol)]

data TypeError
  = EmptyCase
  | CaseTooFewArguments !String
  | CtrNotInType !String !String ![String]
  | MissingType !String
  | InfiniteType !String !Term
  | InvalidCtr !String !Symbol
  | InvalidOp !String !Symbol
  | TypeMismatch !Term !Term
  | NotACtr !String !Symbol
  | NotAUnionType !String !Symbol
  | NotAFunction !Type
  | RuntimeError
  | UndefinedCtr !String
  | UndefinedOp !String
  | UndefinedVar !String
  | UndefinedType !String
  deriving (Eq, Show)

lam :: [String] -> Term -> Term
lam xs a = foldr Lam a xs

for :: [String] -> Term -> Term
for xs a = foldr (\x a -> if x `occurs` a then For x a else a) a xs

fun :: [Type] -> Type -> Type
fun bs ret = foldr Fun ret bs

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

freeVars :: Term -> [String]
freeVars Typ = []
freeVars IntT = []
freeVars (Int _) = []
freeVars NumT = []
freeVars (Num _) = []
freeVars (Var x) = [x]
freeVars (Let env a) = filter (`notElem` map fst env) (freeVars a)
freeVars (Lam x a) = delete x (freeVars a)
freeVars (For x a) = delete x (freeVars a)
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ctr k _ a) = delete k (freeVars a)
freeVars (Op _ args) = foldr (union . freeVars) [] args

occurs :: String -> Term -> Bool
occurs x a = x `elem` freeVars a

reduce :: Ops -> Env -> Term -> Term
reduce _ _ Typ = Typ
reduce _ _ IntT = IntT
reduce _ _ NumT = NumT
reduce _ _ (Int i) = Int i
reduce _ _ (Num n) = Num n
reduce ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Let env a) -> reduce ops env a
  Just a -> reduce ops env a
  Nothing -> Var x
reduce ops env (Let env' a) = reduce ops (env ++ env') a
reduce _ env (Lam x a) = Lam x (Let env a)
reduce _ env (For x a) = For x (Let env a)
reduce _ env (Fun a b) = Fun (Let env a) (Let env b)
reduce ops env (App a b) = case reduce ops env a of
  Lam x (Let env' a) -> reduce ops ((x, Let env b) : env') a
  Ctr _ 0 a -> reduce ops [] (App a (Let env b))
  Ctr k n a -> Ctr k (n - 1) (App a (Let env b))
  a -> App a (Let env b)
reduce _ env (Ctr k n a) = Ctr k n (Let env a)
reduce ops env (Op op args) = do
  let args' = reduce ops env <$> args
  case lookup op ops of
    Just f -> case f args' of
      Just a -> reduce ops env a
      Nothing -> Op op args'
    Nothing -> Op op args'

eval :: Ops -> Env -> Term -> Term
eval ops env term = case reduce ops env term of
  Typ -> Typ
  IntT -> IntT
  NumT -> NumT
  Int i -> Int i
  Num n -> Num n
  Var x -> Var x
  Let _ _ -> error "unreachable"
  Lam x a -> Lam x (eval ops [(x, Var x)] a)
  For x a -> For x (eval ops [(x, Var x)] a)
  Fun a b -> Fun (eval ops [] a) (eval ops [] b)
  App a b -> App (eval ops [] a) (eval ops [] b)
  Ctr k n a -> Ctr k n (eval ops [(k, Var k)] a)
  Op op args -> Op op (eval ops [] <$> args)

apply :: Ops -> Context -> Term -> Term
apply ops ctx = do
  let toEnv :: (String, Symbol) -> (String, Term)
      toEnv (x, Val a) = (x, a)
      toEnv (x, Ann a _) = (x, a)
  eval ops (toEnv <$> ctx)

unify :: Ops -> Context -> Term -> Term -> Either TypeError Context
unify ops ctx a b = case (apply ops ctx a, apply ops ctx b) of
  (Typ, Typ) -> Right ctx
  (IntT, IntT) -> Right ctx
  (Int i, Int i') | i == i' -> Right ctx
  (NumT, NumT) -> Right ctx
  (Num n, Num n') | n == n' -> Right ctx
  (Var x, Var x') | x == x' -> Right ctx
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> Right (set x (Val b) ctx)
  (a, Var y) -> unify ops ctx (Var y) a
  (For x a, b) -> do
    ctx <- unify ops ((x, Val (Var x)) : ctx) a b
    Right (pop x ctx)
  (a, For x b) -> do
    ctx <- unify ops ((x, Val (Var x)) : ctx) a b
    Right (pop x ctx)
  (Fun a1 b1, Fun a2 b2) -> do
    ctx <- unify ops ctx a1 a2
    unify ops ctx b1 b2
  (App a1 b1, App a2 b2) -> do
    ctx <- unify ops ctx a1 a2
    unify ops ctx b1 b2
  (Ctr k _ a, b) -> do
    ctx <- unify ops ((k, Val (Var k)) : ctx) a b
    Right (pop k ctx)
  (a, Ctr k _ b) -> do
    ctx <- unify ops ((k, Val (Var k)) : ctx) a b
    Right (pop k ctx)
  (a, b) -> Left (TypeMismatch a b)

infer :: Ops -> Context -> Term -> Either TypeError (Type, Context)
infer _ ctx Typ = Right (Typ, ctx)
infer _ ctx IntT = Right (Typ, ctx)
infer _ ctx (Int _) = Right (IntT, ctx)
infer _ ctx NumT = Right (Typ, ctx)
infer _ ctx (Num _) = Right (NumT, ctx)
infer ops ctx (Var x) = case lookup x ctx of
  Just (Val (Var x')) | x == x' -> Right (Typ, ctx)
  Just (Val a) -> infer ops ctx a
  Just (Ann (Var x') b) | x == x' -> Right (apply ops ctx b, ctx)
  Just (Ann a b) -> do
    ctx <- checkType ops ctx a b
    Right (apply ops ctx b, ctx)
  Nothing -> Left (UndefinedVar x)
infer ops ctx (Let env a) = infer ops (ctx ++ map (second Val) env) a
infer ops ctx (Lam x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (t2, ctx) <- infer ops ((xT, Val (Var xT)) : (x, Ann (Var x) (Var xT)) : ctx) a
  (t1, ctx) <- infer ops ctx (Var x)
  case (t1, pop x ctx) of
    (Var xT, ctx) -> Right (For xT $ Fun (Var xT) t2, ctx)
    (t1, ctx) -> Right (Fun t1 t2, ctx)
infer ops ctx (For x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (aT, ctx) <- infer ops ((xT, Val (Var xT)) : (x, Ann (Var x) (Var xT)) : ctx) a
  case (aT, pop x ctx) of
    (Var xT, ctx) -> Right (For xT $ Var xT, ctx)
    (aT, ctx) -> Right (aT, ctx)
infer ops ctx (Fun a b) = do
  ctx <- checkType ops ctx a Typ
  ctx <- checkType ops ctx b Typ
  Right (Typ, ctx)
infer ops ctx (App a b) = do
  let xT = newName "t" (map fst ctx)
  ctx <- Right ((xT, Val (Var xT)) : ctx)
  (ta, ctx) <- infer ops ctx a
  (tb, ctx) <- infer ops ctx b
  ctx <- unify ops ctx (Fun tb (Var xT)) ta
  let t = apply ops ctx (Var xT)
  Right (for (freeVars t) t, pop xT ctx)
infer ops ctx (Ctr k _ a) = do
  let xT = newName (k ++ "T") (map fst ctx)
  (ta, ctx) <- infer ops ((xT, Val (Var xT)) : (k, Ann (Var k) (Var xT)) : ctx) a
  Right (ta, pop k ctx)
infer ops ctx (Op op args) = case lookup op ctx of
  Just (Ann _ b) -> do
    (bT, ctx) <- infer ops ((op, Ann (Var op) b) : ctx) (app (Var op) args)
    Right (bT, pop op ctx)
  Just sym -> Left (InvalidOp op sym)
  Nothing -> Left (UndefinedOp op)

checkType :: Ops -> Context -> Term -> Type -> Either TypeError Context
checkType ops ctx a b = do
  (ta, ctx) <- infer ops ctx a
  unify ops ctx ta b

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names
