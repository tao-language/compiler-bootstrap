module Core3 where

import Data.List (foldl')

data Expr
  = Err
  | Typ
  | NilT
  | Nil
  | IntT
  | Int !Int
  | NumT
  | Num !Double
  | Ctr !String
  | Var !String
  | For !String !Expr
  | Fun !Expr !Expr
  | Lam !Expr !Expr
  | Ann !Expr !Expr
  | App !Expr !Expr
  | And !Expr !Expr
  | Or !Expr !Expr
  | Eq !Expr !Expr
  | Op2 !BinaryOp !Expr !Expr
  deriving (Eq, Show)

data BinaryOp
  = Add
  | Sub
  | Mul
  | Lt
  deriving (Eq, Show)

type Env = [(String, Expr)]

data TypeError
  = ErrorType
  | NotAType !Expr !Expr
  | TypeMismatch !Expr !Expr
  | UndefinedVar !String
  | UnifyError !Expr !Expr
  | UntypedCtr !String
  deriving (Eq, Show)

lam :: [Expr] -> Expr -> Expr
lam ps body = foldr Lam body ps

app :: Expr -> [Expr] -> Expr
app = foldl' App

for :: [String] -> Expr -> Expr
for xs expr = foldr For expr xs

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

lt :: Expr -> Expr -> Expr
lt = Op2 Lt

get :: String -> Env -> Maybe Expr
get _ [] = Nothing
get x ((x', expr) : _) | x == x' = Just expr
get x (_ : env) = get x env

set :: (String, Expr) -> Env -> Env
set _ [] = []
set (x, expr) ((x', _) : env) | x == x' = (x, expr) : env
set (x, expr) (def : env) = def : set (x, expr) env

pop :: String -> Env -> Env
pop _ [] = []
pop x ((x', _) : env) | x == x' = env
pop x (_ : env) = pop x env

unify :: Env -> Expr -> Expr -> Maybe Env
unify env Err Err = Just env
unify env Typ Typ = Just env
unify env NilT NilT = Just env
unify env Nil Nil = Just env
unify env IntT IntT = Just env
unify env (Int i) (Int i') | i == i' = Just env
unify env NumT NumT = Just env
unify env (Num n) (Num n') | n == n' = Just env
unify env (Ctr k) (Ctr k') | k == k' = Just env
unify env (Var x) b = Just (set (x, b) env)
unify env a (Var x) = Just (set (x, a) env)
unify env (For x a) b = unify ((x, Var x) : env) a b
unify env a (For x b) = unify ((x, Var x) : env) a b
unify env (Fun a1 b1) (Fun a2 b2) = do
  env <- unify env a1 a2
  unify env (reduce env b1) (reduce env b2)
unify env (Ann a1 b1) (Ann a2 b2) = do
  env <- unify env a1 a2
  unify env (reduce env b1) (reduce env b2)
unify env (App a1 b1) (App a2 b2) = do
  env <- unify env a1 a2
  unify env (reduce env b1) (reduce env b2)
unify env (And a1 b1) (App a2 b2) = do
  env <- unify env a1 a2
  unify env (reduce env b1) (reduce env b2)
unify env (Or a1 a2) b = case unify env a1 b of
  Just env -> Just env
  Nothing -> unify env a2 b
unify env a (Or b1 b2) = case unify env a b1 of
  Just env -> Just env
  Nothing -> unify env a b2
unify _ _ _ = Nothing

reduce :: Env -> Expr -> Expr
reduce env (Var x) = case get x env of
  Just (Var x') | x == x' -> Var x
  Just a -> reduce env a
  Nothing -> Err
reduce env (For x a) = For x (reduce ((x, Var x) : env) a)
reduce env (Fun a b) = Fun (reduce env a) (reduce env b)
reduce env (App a b) = case (reduce env a, reduce env b) of
  (Err, _) -> Err
  (For x a, b) -> reduce ((x, Var x) : env) (App a b)
  (Lam a c, b) -> case unify env (reduce env a) b of
    Just env -> reduce env c
    Nothing -> Err
  (Or a1 a2, b) -> case reduce env (App a1 b) of
    Err -> reduce env (App a2 b)
    c -> c
  (a, b) -> App a b
reduce env (Ann a b) = Ann (reduce env a) (reduce env b)
reduce env (And a b) = And (reduce env a) (reduce env b)
reduce env (Eq a b) = case unify env (reduce env a) (reduce env b) of
  Just env -> reduce env a
  Nothing -> Err
reduce env (Op2 op a b) = case (op, reduce env a, reduce env b) of
  (Add, Int a, Int b) -> Int (a + b)
  (Add, Num a, Num b) -> Num (a + b)
  (Sub, Int a, Int b) -> Int (a - b)
  (Sub, Num a, Num b) -> Num (a - b)
  (Mul, Int a, Int b) -> Int (a * b)
  (Mul, Num a, Num b) -> Num (a * b)
  (Lt, Int a, Int b) -> if a < b then Int a else Err
  (Lt, Num a, Num b) -> if a < b then Num a else Err
  (op, a, b) -> Op2 op a b
reduce _ a = a

newName :: [String] -> String -> String
newName existing x | x `elem` existing = newName existing (x ++ "'")
newName _ x = x

occurs :: String -> Expr -> Bool
occurs x (Var y) = x == y
occurs x (For y a) | x /= y = occurs x a
occurs x (Fun a b) = occurs x a || occurs x b
occurs x (Lam a b) = occurs x a || occurs x b
occurs x (Ann a b) = occurs x a || occurs x b
occurs x (App a b) = occurs x a || occurs x b
occurs x (And a b) = occurs x a || occurs x b
occurs x (Or a b) = occurs x a || occurs x b
occurs x (Eq a b) = occurs x a || occurs x b
occurs x (Op2 _ a b) = occurs x a || occurs x b
occurs _ _ = False

unifyTypes :: Env -> Expr -> Expr -> Either TypeError Env
unifyTypes env t1 t2 = case unify env t1 t2 of
  Just env -> Right env
  Nothing -> Left (TypeMismatch t1 t2)

infer :: Env -> Expr -> Either TypeError (Expr, Env)
infer _ Err = Left ErrorType
infer env Typ = Right (Typ, env)
infer env NilT = Right (Typ, env)
infer env Nil = Right (NilT, env)
infer env IntT = Right (Typ, env)
infer env (Int _) = Right (IntT, env)
infer env NumT = Right (Typ, env)
infer env (Num _) = Right (NumT, env)
infer _ (Ctr k) = Left (UntypedCtr k)
infer env (Var x) = case get x env of
  Just (Var x') | x == x' -> infer env (For x (Var x))
  Just (Ann (Var x') type') | x == x' -> Right (reduce env type', env)
  Just expr -> do
    (t, env) <- infer ((x, Var x) : env) expr
    Right (t, pop x env)
  Nothing -> Left (UndefinedVar x)
infer env (For x a) = do
  let xT = newName (map fst env) (x ++ "T")
  (t, env) <- infer ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env) a
  if xT `occurs` t
    then Right (For xT t, pop x env)
    else Right (t, pop x env)
infer env (Fun a b) = do
  env <- checkType env a
  env <- checkType env b
  Right (Typ, env)
infer env (Lam a b) = do
  (aT, env) <- infer env a
  (bT, env) <- infer env b
  Right (Fun (reduce env aT) bT, env)
infer env (Ann (Ctr _) t) = do
  env <- checkType env t
  Right (reduce env t, env)
infer env (Ann a t) = do
  env <- checkType env t
  (aT, env) <- infer env a
  env <- unifyTypes env aT t
  Right (reduce env t, env)
infer env (App a b) = do
  let x = newName (map fst env) "_ret"
  (funT, env) <- infer ((x, Var x) : env) a
  (argT, env) <- infer env b
  env <- unifyTypes env funT (Fun argT (Var x))
  case reduce env (Var x) of
    Var x' | x == x' -> Right (For x (Var x), pop x env)
    t -> Right (t, pop x env)
infer env (And a b) = do
  (aT, env) <- infer env a
  (bT, env) <- infer env b
  Right (And aT bT, env)
infer env (Or a b) = do
  (aT, env) <- infer env a
  (bT, env) <- infer env b
  env <- unifyTypes env aT bT
  Right (reduce env aT, env)
infer env (Eq a b) = case unify env a b of
  Just env -> infer env a
  Nothing -> Left (UnifyError a b)
infer env (Op2 _ a b) = do
  (aT, env) <- infer env a
  (bT, env) <- infer env b
  env <- unifyTypes env aT bT
  Right (reduce env aT, env)

checkType :: Env -> Expr -> Either TypeError Env
checkType env a = do
  let check :: Env -> Expr -> Either TypeError Env
      check env Typ = Right env
      check env (For x (Var x')) | x == x' = Right env
      check env (For x a) = do
        env <- check ((x, Var x) : env) a
        Right (pop x env)
      check _ type' = Left (NotAType a type')

  (type', env) <- infer env a
  check env type'
