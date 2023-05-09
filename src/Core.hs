{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (Foldable (foldl'))
import Data.List (delete, intercalate, union)

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
  | Var !String
  | Lam !String !Term
  | For !String !Term
  | Fun !Term !Term
  | App !Term !Term
  | Ann !Term !Type
  | Let !Env !Term
  | Fix !String !Term
  | Ctr !String ![(String, Term)] ![String]
  | Op !String ![Term]
  deriving (Eq)

showParen' :: Bool -> String -> String
showParen' True a = "(" ++ a ++ ")"
showParen' False a = a

showPrefix :: Int -> Int -> String -> Term -> String
showPrefix p q op a = showParen' (p > q) (op ++ showPrec q a)

showInfixL :: Int -> Int -> Term -> String -> Term -> String
showInfixL p q a op b = showParen' (p > q) (showPrec q a ++ op ++ showPrec (q + 1) b)

showInfixR :: Int -> Int -> Term -> String -> Term -> String
showInfixR p q a op b = showParen' (p > q) (showPrec (q + 1) a ++ op ++ showPrec q b)

showPrec :: Int -> Term -> String
showPrec _ Knd = "@Type"
showPrec _ IntT = "@Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "@Num"
showPrec _ (Num n) = show n
showPrec _ (Var x) = x
showPrec p (Lam x a) = showPrefix p 2 ("\\" ++ x ++ " -> ") a
showPrec p (For x a) = showPrefix p 2 ("@for " ++ x ++ ". ") a
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (App a b) = showInfixL p 3 a " " b
showPrec p (Ann a b) = showInfixL p 1 a " : " b
showPrec p (Let [] a) = showPrec p a
showPrec p (Let env a) = do
  let showDef (x, b) = x ++ " = " ++ show b
  let defs = "@let {" ++ intercalate "; " (showDef <$> env) ++ "} "
  showPrefix p 2 defs a
showPrec _ (Fix x a) = "@fix " ++ x ++ " {" ++ show a ++ "}"
showPrec _ (Ctr ctr args ctrs) =
  "#" ++ ctr ++ " [" ++ intercalate ", " (show <$> args) ++ "] {" ++ intercalate " | " ctrs ++ "}"
showPrec _ (Op op args) = "@op " ++ op ++ " (" ++ intercalate ", " (show <$> args) ++ ")"

instance Show Term where
  show :: Term -> String
  show a = showPrec 0 a

type Type = Term

type Operator = (Term -> Term) -> [Term] -> Maybe Term

type Ops = [(String, Operator)]

type Env = [(String, Term)]

data TypeError
  = InfiniteType !String !Term
  | MissingType !String !Term
  | TooManyArgs !Term ![Term]
  | NotAFunction !Type
  | NotAUnionAlt !String !Term
  | NotAUnionType !Term
  | TypeMismatch !Term !Term
  | UndefinedOp !String
  | UndefinedCtr !String
  | UndefinedType !String
  | UndefinedUnionAlt !String
  | UndefinedUnionType !String
  | UndefinedVar !String
  deriving (Eq, Show)

lam :: [String] -> Term -> Term
lam xs a = foldr Lam a xs

for :: [String] -> Term -> Term
for xs a = foldr (\x a -> if x `occurs` a then For x a else a) a xs

forFrom :: Term -> ([String], Term)
forFrom (For x a) = let (xs, b) = forFrom a in (x : xs, b)
forFrom a = ([], a)

fun :: [Type] -> Type -> Type
fun bs ret = foldr Fun ret bs

app :: Term -> [Term] -> Term
app = foldl' App

let' :: Env -> Term -> Term
let' [] a = a
let' env a = Let env a

pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

set :: Eq k => k -> v -> [(k, v)] -> [(k, v)]
set _ _ [] = []
set x y ((x', _) : kvs) | x == x' = (x, y) : kvs
set x y (kv : kvs) = kv : set x y kvs

freeVars :: Term -> [String]
freeVars Knd = []
freeVars IntT = []
freeVars (Int _) = []
freeVars NumT = []
freeVars (Num _) = []
freeVars (Var x) = [x]
freeVars (Lam x a) = delete x (freeVars a)
freeVars (For x a) = delete x (freeVars a)
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a b) = freeVars a `union` freeVars b
freeVars (Let env a) =
  filter (`notElem` map fst env) (foldr (union . freeVars . snd) (freeVars a) env)
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Ctr _ args _) = foldr (union . freeVars . snd) [] args
freeVars (Op _ args) = foldr (union . freeVars) [] args

occurs :: String -> Term -> Bool
occurs x a = x `elem` freeVars a

reduce :: Ops -> Env -> Term -> Term
reduce _ _ Knd = Knd
reduce _ _ IntT = IntT
reduce _ _ NumT = NumT
reduce _ _ (Int i) = Int i
reduce _ _ (Num n) = Num n
reduce ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Let env a) -> reduce ops env a
  Just a -> reduce ops env a
  Nothing -> Var x
reduce _ env (Lam x a) = Lam x (Let env a)
reduce _ env (For x a) = For x (Let env a)
reduce _ env (Fun a b) = Fun (Let env a) (Let env b)
reduce ops env (App a b) = case reduce ops env a of
  Lam x (Let env' a) -> reduce ops ((x, Let env b) : env') a
  Fix _ a -> reduce ops [] (App a (Let env b))
  Ctr ctr args ctrs -> reduce ops env (App (lam ctrs (app (Var ctr) (snd <$> args))) b)
  a -> App a (Let env b)
reduce ops env (Ann a _) = reduce ops env a
reduce ops env (Let env' a) = reduce ops (env ++ env') a
reduce _ env (Fix x a) = Fix x (Let env a)
reduce _ env (Ctr ctr args ctrs) = Ctr ctr (second (Let env) <$> args) ctrs
reduce ops env (Op op args) = case lookup op ops of
  Just f -> case f (eval ops env) args of
    Just a -> reduce ops env a
    Nothing -> Op op (Let env <$> args)
  Nothing -> Op op (Let env <$> args)

eval :: Ops -> Env -> Term -> Term
eval ops env term = case reduce ops env term of
  Knd -> Knd
  IntT -> IntT
  NumT -> NumT
  Int i -> Int i
  Num n -> Num n
  Var x -> Var x
  Lam x a -> Lam x (eval ops [(x, Var x)] a)
  For x a -> For x (eval ops [(x, Var x)] a)
  Fun a b -> Fun (eval ops [] a) (eval ops [] b)
  App a b -> App (eval ops [] a) (eval ops [] b)
  Ann _ _ -> error "unreachable"
  Let _ _ -> error "unreachable"
  Fix x a -> case eval ops [(x, Var x)] a of
    a | x `occurs` a -> Fix x a
    a -> a
  Ctr ctr args ctrs -> Ctr ctr (second (eval ops []) <$> args) ctrs
  Op op args -> Op op (eval ops [] <$> args)

unify :: Ops -> Env -> Term -> Term -> Either TypeError (Term, Env)
unify ops env a b = case (eval ops env a, eval ops env b) of
  (Knd, Knd) -> Right (Knd, env)
  (IntT, IntT) -> Right (IntT, env)
  (Int i, Int i') | i == i' -> Right (Int i, env)
  (NumT, NumT) -> Right (NumT, env)
  (Num n, Num n') | n == n' -> Right (Num n, env)
  (Var x, Var x') | x == x' -> Right (Var x, env)
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> Right (b, set x b env)
  (a, Var y) -> unify ops env (Var y) a
  (For x a, b) -> do
    (a, env) <- unify ops ((x, Var x) : env) a b
    Right (for [x] a, pop x env)
  (a, For x b) -> do
    (a, env) <- unify ops ((x, Var x) : env) a b
    Right (for [x] a, pop x env)
  (Fun a1 b1, Fun a2 b2) -> do
    (a, env) <- unify ops env a1 a2
    (b, env) <- unify ops env b1 b2
    Right (Fun (eval ops env a) b, env)
  (App a1 b1, App a2 b2) -> do
    (a, env) <- unify ops env a1 a2
    (b, env) <- unify ops env b1 b2
    Right (App (eval ops env a) b, env)
  (Ctr ctr args ctrs, Ctr ctr' args' ctrs') | ctr == ctr' && map fst args == map fst args' && ctrs == ctrs' -> do
    (argValues, env) <- unifyMany ops env (snd <$> args) (snd <$> args')
    Right (Ctr ctr (zip (fst <$> args) argValues) ctrs, env)
  (Ctr ctr args ctrs, b) -> do
    a <- expandType ops env ctrs ctr args
    unify ops env a b
  (a, Ctr ctr args ctrs) -> do
    b <- expandType ops env ctrs ctr args
    unify ops env a b
  (Op op args, Op op' args') | op == op' && length args == length args' -> do
    (args, env) <- unifyMany ops env args args'
    Right (Op op args, env)
  (a, b) -> Left (TypeMismatch a b)

unifyMany :: Ops -> Env -> [Term] -> [Term] -> Either TypeError ([Term], Env)
unifyMany _ env [] _ = Right ([], env)
unifyMany _ env _ [] = Right ([], env)
unifyMany ops env (a1 : bs1) (a2 : bs2) = do
  (a, env) <- unify ops env a1 a2
  (bs, env) <- unifyMany ops env bs1 bs2
  Right (a : bs, env)

expandType :: Ops -> Env -> [String] -> String -> [(String, Term)] -> Either TypeError Term
expandType ops env ctrs typ args = do
  let env' = (typ, Var typ) : args ++ env
  let branch :: Type -> Term
      branch (For x a) | x `elem` (fst <$> args) = branch a
      branch (For x a) = for [x] (branch a)
      branch (Fun a b) = Fun (eval ops env' a) (branch b)
      branch _ = Var typ
  ctrTypes <- mapM (findTyped env) ctrs
  let xs = typ : (fst <$> args)
  Right (for xs (fun (branch . snd <$> ctrTypes) (Var typ)))

findTyped :: Env -> String -> Either TypeError (Term, Type)
findTyped env x = case lookup x env of
  Just (Ann a b) -> Right (a, b)
  Just a -> Left (MissingType x a)
  Nothing -> Left (UndefinedVar x)

infer :: Ops -> Env -> Term -> Either TypeError (Type, Env)
infer _ env Knd = Right (Knd, env)
infer _ env IntT = Right (Knd, env)
infer _ env (Int _) = Right (IntT, env)
infer _ env NumT = Right (Knd, env)
infer _ env (Num _) = Right (NumT, env)
infer ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Right (Knd, env)
  Just (Ann (Var x') b) | x == x' -> Right (eval ops env b, env)
  Just (Ann a b) -> do
    (_, env) <- checkType ops env a b
    Right (eval ops env b, env)
  Just a -> infer ops env a
  Nothing -> Left (UndefinedVar x)
infer ops env (Lam x a) = do
  let xT = newName (x ++ "T") (map fst env)
  (t2, env) <- infer ops ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env) a
  (t1, env) <- infer ops env (Var x)
  Right (for [xT] $ Fun t1 t2, pop x env)
infer ops env (For x a) = do
  let xT = newName (x ++ "T") (map fst env)
  (aT, env) <- infer ops ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env) a
  Right (for [xT] aT, pop x env)
infer ops env (Fun a b) = do
  (_, env) <- checkType ops env a Knd
  (_, env) <- checkType ops env b Knd
  Right (Knd, env)
infer ops env (App a b) = do
  let xT = newName "t" (map fst env)
  env <- Right ((xT, Var xT) : env)
  (ta, env) <- infer ops env a
  (tb, env) <- infer ops env b
  (funT, env) <- unify ops env (Fun tb (Var xT)) ta
  case (forFrom funT, pop xT env) of
    ((xs, Fun _ t), env) -> Right (for xs t, env)
    ((xs, t), _) -> Left (NotAFunction (for xs t))
infer ops env (Ann a b) = checkType ops env a b
infer ops env (Let env' a) = infer ops (env ++ env') a
infer ops env (Fix x a) = do
  let xT = newName (x ++ "T") (map fst env)
  (ta, env) <- infer ops ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env) a
  Right (ta, pop x env)
infer ops env (Ctr ctr args ctrs) = do
  (_, b) <- findTyped env ctr
  (retType, env) <- infer ops ((ctr, Ann (Var ctr) b) : env) (app (Var ctr) (snd <$> args))
  Right (retType, pop ctr env)
infer ops env (Op op args) = do
  (_, b) <- findTyped env op
  (bT, env) <- infer ops ((op, Ann (Var op) b) : env) (app (Var op) args)
  Right (bT, pop op env)

inferMany :: Ops -> Env -> [Term] -> Either TypeError ([Type], Env)
inferMany _ env [] = Right ([], env)
inferMany ops env (a : bs) = do
  (t, env) <- infer ops env a
  (ts, env) <- inferMany ops env bs
  Right (t : ts, env)

checkType :: Ops -> Env -> Term -> Type -> Either TypeError (Type, Env)
checkType ops env a b = do
  (ta, env) <- infer ops env a
  unify ops env ta b

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names
