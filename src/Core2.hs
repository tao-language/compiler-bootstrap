module Core2 where

import Data.List (delete, foldl', union)

data Expr
  = Err
  | Int !Int
  | Num !Double
  | Var !String
  | Ann !Expr !Expr
  | Lam !Env !String !Expr
  | App !Expr !Expr
  | Fix !String !Expr
  | TypT
  | IntT
  | NumT
  | ForT !String !Expr
  | FunT !Expr !Expr
  | Op !BuiltIn
  deriving (Eq, Show)

data BuiltIn
  = Add
  | Eq
  deriving (Eq, Show)

type Env = [(String, Expr)]

data TypeError
  = InfiniteType !String !Expr
  | NotAType !Expr
  | TypeMismatch !Expr !Expr
  | UndefinedVar !String
  deriving (Eq, Show)

lam :: [String] -> Expr -> Expr
lam xs a = foldr (Lam []) a xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

forT :: [String] -> Expr -> Expr
forT xs a = foldr ForT a xs

funT :: [Expr] -> Expr -> Expr
funT ts t = foldr FunT t ts

add :: Expr -> Expr -> Expr
add a b = app (Op Add) [a, b]

eq :: Expr -> Expr -> Expr
eq a b = app (Op Eq) [a, b]

let' :: Env -> (String, Expr) -> Expr -> Expr
let' env (x, value) expr = App (Lam env x expr) value

binopT :: String -> String -> Expr -> Expr
binopT x x' returnT | x == x' = ForT x (funT [Var x, Var x] returnT)
binopT x y returnT = forT [x, y] (funT [Var x, Var y] returnT)

boolT :: Expr
boolT = binopT "Bool" "Bool" (Var "Bool")

true :: Expr
true = lam ["True", "False"] (Var "True")

false :: Expr
false = lam ["True", "False"] (Var "False")

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

annotate :: (String, String) -> Env -> Env
annotate _ [] = []
annotate (x, xT) ((x', _) : env) | x == x' = (xT, Var xT) : (x, Ann (Var x) (Var xT)) : env
annotate (x, xT) (def : env) = def : annotate (x, xT) env

freeVars :: Expr -> [String]
freeVars (Var x) = [x]
freeVars (Ann expr type') = freeVars expr `union` freeVars type'
freeVars (Lam _ x body) = delete x (freeVars body)
freeVars (App fun arg) = freeVars fun `union` freeVars arg
freeVars (ForT x a) = delete x (freeVars a)
freeVars (FunT a b) = freeVars a `union` freeVars b
freeVars _ = []

occurs :: String -> Expr -> Bool
occurs x (Var y) = x == y
occurs x (Ann expr type') = occurs x expr || occurs x type'
occurs x (Lam _ y body) | x /= y = occurs x body
occurs x (App fun arg) = occurs x fun || occurs x arg
occurs x (ForT y a) | x /= y = occurs x a
occurs x (FunT a b) = occurs x a || occurs x b
occurs _ _ = False

newName :: [String] -> String -> String
newName existing x | x `elem` existing = newName existing (x ++ "'")
newName _ x = x

substitute :: (String, Expr) -> Expr -> Expr
substitute (x, sub) (Var x') | x == x' = sub
substitute (x, sub) (Ann expr type') = Ann (substitute (x, sub) expr) (substitute (x, sub) type')
substitute (x, sub) (Lam env y body) | x /= y = Lam env y (substitute (x, sub) body)
substitute (x, sub) (App fun arg) = App (substitute (x, sub) fun) (substitute (x, sub) arg)
substitute (x, sub) (ForT y a) | x /= y = ForT y (substitute (x, sub) a)
substitute (x, sub) (FunT a b) = FunT (substitute (x, sub) a) (substitute (x, sub) b)
substitute _ expr = expr

instantiate :: Env -> Expr -> (Expr, Env)
instantiate env (ForT x a) = do
  let y = newName (map fst env) x
  (substitute (x, Var y) a, (y, Var y) : env)
instantiate env a = (a, env)

unify :: Env -> Expr -> Expr -> Either TypeError (Expr, Env)
unify env a b = case (eval env a, eval env b) of
  (Var x, Var x') | x == x' -> Right (Var x, env)
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> Right (b, set (x, b) env)
  (a, Var x) | x `occurs` a -> Left (InfiniteType x a)
  (a, Var x) -> Right (a, set (x, a) env)
  (ForT x a, b) -> do
    (t, env) <- unify ((x, Var x) : env) a b
    if x `occurs` t then Right (ForT x t, pop x env) else Right (t, pop x env)
  (a, ForT x b) -> do
    (t, env) <- unify ((x, Var x) : env) a b
    if x `occurs` t then Right (ForT x t, pop x env) else Right (t, pop x env)
  (FunT a1 b1, FunT a2 b2) -> do
    (a, env) <- unify env a1 a2
    (b, env) <- unify env b1 b2
    Right (FunT a b, env)
  (a, a') | a == a' -> Right (a, env)
  (a, b) -> Left (TypeMismatch a b)

infer :: Env -> Expr -> Either TypeError (Expr, Env)
infer env Err = Right (Err, env)
infer env (Int _) = Right (IntT, env)
infer env (Num _) = Right (NumT, env)
infer env (Var x) = case get x env of
  Just (Var x') | x == x' -> do
    let xT = newName (map fst env) (x ++ "T")
    Right (Var xT, annotate (x, xT) env)
  Just (Ann (Var x') type') | x == x' -> Right (eval env type', env)
  Just expr -> infer env expr
  Nothing -> Left (UndefinedVar x)
infer env (Ann expr type') = do
  _ <- checkType env type'
  (exprT, env) <- infer env expr
  unify env exprT type'
infer env (Lam env' x body) = do
  (t2, env) <- infer ((x, Var x) : env ++ env') body
  (t1, env) <- infer env (Var x)
  case t1 of
    -- TODO: get rid of env'
    Var xT -> Right (ForT xT (FunT t1 t2), pop x env)
    t1 -> Right (FunT t1 t2, pop x env)
infer env (App fun arg) = do
  (funT, env) <- infer env fun
  (argT, env) <- infer env arg
  let x = newName (map fst env) "a"
  (resultT, env) <- unify ((x, Var x) : env) funT (FunT argT (Var x))
  case instantiate env resultT of
    (FunT _ (Var x'), env) | x == x' -> Right (ForT x (Var x), pop x env)
    (FunT _ t2, env) -> Right (t2, pop x env)
    _impossible -> Left (TypeMismatch funT (FunT argT (Var x)))
infer env (Fix x fun) = do
  (funT, env) <- infer ((x, Var x) : env) fun
  case funT of
    Var xT -> Right (ForT xT (Var xT), pop x env)
    funT -> Right (funT, pop x env)
infer env TypT = Right (TypT, env)
infer env IntT = Right (TypT, env)
infer env NumT = Right (TypT, env)
infer env (ForT x a) = do
  _ <- checkType ((x, Var x) : env) a
  Right (TypT, env)
infer env (FunT a b) = do
  env <- checkType env a
  env <- checkType env b
  Right (TypT, env)
infer env (Op Add) = let a = Var "a" in Right (ForT "a" (funT [a, a] a), env)
infer env (Op Eq) = let a = Var "a" in Right (ForT "a" (funT [a, a] boolT), env)

checkType :: Env -> Expr -> Either TypeError Env
checkType env type' = do
  (kind, env) <- infer env type'
  case kind of
    Var _ -> Right env
    TypT -> Right env
    _else -> Left (NotAType type')

reduce :: Env -> Expr -> Expr
reduce env (Var x) = case get x env of
  Just (Var x') | x == x' -> Var x
  Just expr -> reduce env expr
  Nothing -> Var x
reduce env (Ann expr _) = reduce env expr
reduce env (Lam env' x body) = Lam (env ++ env') x body
reduce env (App fun arg) = case (reduce env fun, reduce env arg) of
  (Lam env x body, arg) -> reduce ((x, arg) : env) body
  (Fix x fun, arg) -> reduce ((x, Fix x fun) : env) (App fun arg)
  (fun, arg) -> App fun arg
reduce env (ForT x a) = ForT x (reduce ((x, Var x) : env) a)
reduce env (FunT a b) = FunT (reduce env a) (reduce env b)
reduce _ expr = expr

eval :: Env -> Expr -> Expr
eval env expr = case reduce env expr of
  Lam env x body -> Lam [] x (eval ((x, Var x) : env) body)
  App (App (Op op) a) b -> case (op, eval env a, eval env b) of
    (Add, Int a, Int b) -> Int (a + b)
    (Add, Num a, Num b) -> Num (a + b)
    (Eq, Int a, Int b) -> if a == b then true else false
    (Eq, Num a, Num b) -> if a == b then true else false
    (op, a, b) -> app (Op op) [a, b]
  App fun arg -> App (eval env fun) (eval env arg)
  Fix x fun -> Fix x (eval ((x, Var x) : env) fun)
  ForT x a -> ForT x (eval ((x, Var x) : env) a)
  FunT a b -> FunT (eval env a) (eval env b)
  expr -> expr
