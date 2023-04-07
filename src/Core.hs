{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (Foldable (foldl'))
import Data.List (intercalate)

{- TODO:

Clean up code
- Show Term with precedence

Function / operator overloading
- Via inferred type classes

Do notation
- Overload (<-) operator

-}

data Term
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Typ !String
  | Ctr !String !Term
  | Var !String
  | Lam !String !Term
  | Fix !String !Term
  | For !String !Term
  | Fun !Type !Type
  | App !Term !Term
  | Case ![(String, Term)]
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
showPrec _ IntT = "%Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "%Num"
showPrec _ (Num n) = show n
showPrec _ (Typ t) = "$" ++ t -- ++ " {" ++ intercalate " | " alts ++ "}"
showPrec _ (Ctr k a) = "#" ++ k ++ " (" ++ show a ++ ")"
showPrec _ (Var x) = x
showPrec p (For x a) = showPrefix p 2 ("@" ++ x ++ ". ") a
showPrec p (Lam x a) = showPrefix p 2 ("\\" ++ x ++ " -> ") a
showPrec p (Fix x a) = showPrefix p 2 ("%fix " ++ x ++ " -> ") a
showPrec p (Case branches) = do
  let showBranch (k, b) = k ++ " -> " ++ show b
  "%case {" ++ intercalate " | " (showBranch <$> branches) ++ "}"
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (App a b) = showInfixL p 3 a " " b
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
  | Union ![String] !Type
  | Alt !(String, [String]) !Type
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
  | Mismatch !Term !Term
  | NotACtr !String !Symbol
  | NotAUnionType !String !Symbol
  | NotAFunction !Term !Type
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

eval :: Ops -> Env -> Term -> Term
eval _ _ Knd = Knd
eval _ _ IntT = IntT
eval _ _ NumT = NumT
eval _ _ (Int i) = Int i
eval _ _ (Num n) = Num n
eval _ _ (Typ t) = Typ t
eval ops env (Ctr k a) = Ctr k (eval ops env a)
eval ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just a -> eval ops ((x, Var x) : env) a
  Nothing -> Var x
eval ops env (For x a) = For x (eval ops ((x, Var x) : env) a)
eval ops env (Lam x a) = Lam x (eval ops ((x, Var x) : env) a)
eval ops env (Fix x a) = Fix x (eval ops ((x, Var x) : env) a)
eval ops env (Fun a b) = Fun (eval ops env a) (eval ops env b)
eval ops env (App a b) = case (eval ops env a, eval ops env b) of
  (Lam x a, b) -> eval ops ((x, b) : env) a
  (Fix x a, b) -> eval ops ((x, Fix x a) : env) (App a b)
  (Case branches, Ctr k b) -> case lookup k branches of
    Just a -> eval ops env (App b a)
    Nothing -> error ("case not covered: " ++ k)
  (a, b) -> App a b
eval ops env (Case branches) = Case (second (eval ops env) <$> branches)
eval ops env (Op op args) = do
  let args' = eval ops env <$> args
  case lookup op ops of
    Just f -> case f args' of
      Just a -> eval ops env a
      Nothing -> Op op args'
    Nothing -> Op op args'

untyped :: (String, Symbol) -> (String, Term)
untyped (x, Val a) = (x, a)
untyped (x, Ann a _) = (x, a)
untyped (x, Union alts _) = (x, Typ x)
untyped (x, Alt (_, args) _) = (x, lam args $ Ctr x (Lam x $ app (Var x) (Var <$> args)))

solve :: Ops -> Context -> Term -> Term
solve ops ctx = eval ops (untyped <$> ctx)

occurs :: String -> Term -> Bool
occurs _ Knd = False
occurs _ IntT = False
occurs _ (Int _) = False
occurs _ NumT = False
occurs _ (Num _) = False
occurs _ (Typ _) = False
occurs x (Ctr _ a) = occurs x a
occurs x (Var y) = x == y
occurs x (For x' _) | x == x' = False
occurs x (For _ a) = occurs x a
occurs x (Lam x' _) | x == x' = False
occurs x (Lam _ a) = occurs x a
occurs x (Fix x' _) | x == x' = False
occurs x (Fix _ a) = occurs x a
occurs x (Case branches) = any (occurs x . snd) branches
occurs x (Fun a b) = occurs x a || occurs x b
occurs x (App a b) = occurs x a || occurs x b
occurs x (Op _ args) = any (occurs x) args

apply :: Ops -> (String, Term) -> Symbol -> Symbol
apply ops sub (Val a) = Val (eval ops [sub] a)
apply ops sub (Ann a b) = Ann (eval ops [sub] a) (eval ops [sub] b)
apply ops sub (Union alts b) = Union alts (eval ops [sub] b)
apply ops sub (Alt alt b) = Alt alt (eval ops [sub] b)

unify :: Ops -> Context -> Term -> Term -> Either TypeError (Term, Context)
unify ops ctx a b = case (solve ops ctx a, solve ops ctx b) of
  (Knd, Knd) -> Right (Knd, ctx)
  (IntT, IntT) -> Right (IntT, ctx)
  (Int i, Int i') | i == i' -> Right (Int i, ctx)
  (NumT, NumT) -> Right (NumT, ctx)
  (Num n, Num n') | n == n' -> Right (Num n, ctx)
  (Typ t, Typ t') | t == t' -> Right (Typ t, ctx)
  (Ctr k a, Ctr k' b) | k == k' -> do
    (a, ctx) <- unify ops ctx a b
    Right (Ctr k a, ctx)
  (Var x, Var x') | x == x' -> Right (Var x, ctx)
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> Right (b, set x (Val b) (second (apply ops (x, b)) <$> ctx))
  (a, Var y) -> unify ops ctx (Var y) a
  (For x a, b) -> do
    (a, ctx) <- unify ops ((x, Val (Var x)) : ctx) a b
    case (a, pop x ctx) of
      (a, ctx) | x `occurs` a -> Right (For x a, ctx)
      (a, ctx) -> Right (a, ctx)
  (a, For x b) -> do
    (a, ctx) <- unify ops ((x, Val (Var x)) : ctx) a b
    case (a, pop x ctx) of
      (a, ctx) | x `occurs` a -> Right (For x a, ctx)
      (a, ctx) -> Right (a, ctx)
  (Fun a1 b1, Fun a2 b2) -> do
    (a, ctx) <- unify ops ctx a1 a2
    (b, ctx) <- unify ops ctx b1 b2
    Right (Fun (solve ops ctx a) b, ctx)
  (App a1 b1, App a2 b2) -> do
    (a, ctx) <- unify ops ctx a1 a2
    (b, ctx) <- unify ops ctx b1 b2
    Right (App (solve ops ctx a) b, ctx)
  (a, b) -> Left (Mismatch a b)

inferType :: Ops -> Context -> Term -> Either TypeError (Type, Context)
inferType _ ctx Knd = Right (Knd, ctx)
inferType _ ctx IntT = Right (Knd, ctx)
inferType _ ctx (Int _) = Right (IntT, ctx)
inferType _ ctx NumT = Right (Knd, ctx)
inferType _ ctx (Num _) = Right (NumT, ctx)
inferType _ _ (Typ t) = Left (MissingType t)
inferType _ _ (Ctr k _) = Left (MissingType k)
inferType ops ctx (Var x) = case lookup x ctx of
  Just (Val (Var x')) | x == x' -> do
    let xT = newName (x ++ "T") (map fst ctx)
    Right (Var xT, (xT, Val (Var xT)) : set x (Ann (Var x) (Var xT)) ctx)
  Just (Val a) -> inferType ops ctx a
  Just (Ann (Var x') b) | x == x' -> Right (solve ops ctx b, ctx)
  Just (Ann a b) -> do
    ctx <- checkType ops ctx a b
    Right (solve ops ctx b, ctx)
  Just (Union alts b) -> do
    -- TODO: check alts
    Right (solve ops ctx b, ctx)
  Just (Alt (t, args) b) -> case lookup t ctx of
    Just (Union alts _) | x `elem` alts -> do
      -- TODO: type check against b
      Right (solve ops ctx b, ctx)
    Just (Union alts _) -> Left (CtrNotInType x t alts)
    Just sym -> Left (NotAUnionType t sym)
    Nothing -> Left (UndefinedType t)
  Nothing -> Left (UndefinedVar x)
inferType ops ctx (For x a) = do
  (aT, ctx) <- inferType ops ((x, Val (Var x)) : ctx) a
  case (aT, pop x ctx) of
    (Var xT, ctx) -> Right (For xT $ Var xT, ctx)
    (aT, ctx) -> Right (aT, ctx)
inferType ops ctx (Lam x a) = do
  (t2, ctx) <- inferType ops ((x, Val (Var x)) : ctx) a
  (t1, ctx) <- inferType ops ctx (Var x)
  case (t1, pop x ctx) of
    (Var xT, ctx) -> Right (For xT $ Fun (Var xT) t2, ctx)
    (t1, ctx) -> Right (Fun t1 t2, ctx)
inferType ops ctx (Fix x a) | x `occurs` a = do
  (t, ctx) <- inferType ops ((x, Val (Var x)) : ctx) a
  Right (t, pop x ctx)
inferType ops ctx (Fix _ a) = inferType ops ctx a
inferType ops ctx (Fun a b) = do
  ctx <- checkType ops ctx a Knd
  ctx <- checkType ops ctx b Knd
  Right (Knd, ctx)
inferType ops ctx (App a b) = do
  (ta, ctx) <- inferType ops ctx a
  case instantiate ctx ta of
    (xs, Var y, ctx) -> do
      let y' = newName y (map fst ctx)
      Right (For y' $ Var y', foldr pop ctx xs)
    (xs, Fun t1 t2, ctx) -> do
      (tb, ctx) <- inferType ops ctx b
      (_, ctx) <- unify ops ctx tb t1
      Right (for xs $ solve ops ctx t2, foldr pop ctx xs)
    (_, ta, _) -> Left (NotAFunction a ta)
inferType _ _ (Case []) = Left EmptyCase
inferType ops ctx (Case [(k, b)]) = case lookup k ctx of
  Just (Alt (t, args) t1) -> do
    -- TODO: clean up
    (xs, a, b, ctx) <- expand ctx k args b
    (t1, ctx) <- inferType ops ctx a
    (t2, ctx) <- inferType ops ctx b
    let (ys, t1', _) = instantiate ctx t1
    Right (for ys $ solve ops ctx (Fun t1' t2), foldr pop ctx xs)
  Just sym -> Left (NotACtr k sym)
  Nothing -> Left (UndefinedCtr k)
inferType ops ctx (Case (branch : branches)) = do
  (a, ctx) <- inferType ops ctx (Case [branch])
  (b, ctx) <- inferType ops ctx (Case branches)
  unify ops ctx a b
inferType ops ctx (Op op args) = case lookup op ctx of
  Just (Ann _ b) -> do
    (bT, ctx) <- inferType ops ((op, Ann (Var op) b) : ctx) (app (Var op) args)
    Right (bT, pop op ctx)
  Just sym -> Left (InvalidOp op sym)
  Nothing -> Left (UndefinedOp op)

expand :: Context -> String -> [String] -> Term -> Either TypeError ([String], Term, Term, Context)
expand ctx k [] b = Right ([], Var k, b, ctx)
expand ctx k (_ : xs) (Lam y b) = do
  (ys, a, b, ctx) <- expand ctx k xs b
  Right (y : ys, App a (Var y), b, (y, Val (Var y)) : ctx)
expand _ k _ _ = Left (CaseTooFewArguments k)

instantiate :: Context -> Type -> ([String], Type, Context)
instantiate ctx (For x a) = case instantiate ctx a of
  (xs, a, ctx) -> (x : xs, a, (x, Val (Var x)) : ctx)
instantiate ctx a = ([], a, ctx)

checkType :: Ops -> Context -> Term -> Type -> Either TypeError Context
checkType ops ctx a b = do
  (ta, ctx) <- inferType ops ctx a
  (_, ctx) <- unify ops ctx ta b
  Right ctx

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names
