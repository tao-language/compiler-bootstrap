{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (Foldable (foldl'))
import Data.List (intercalate)

{- TODO:

Clean up code
- Push and pop variables from scope (fresh variables)
- Show Expr with precedence
- The "_app" variable created on inferType for App

Exhaustive pattern checks (warnings, not errors)
- Use `Or` to express unions
- Find all available cases
  - Usually all the constructors on a union type
  - Can be filtered if a type says a constructor is not possible (e.g. `head`)
- Filter by all the `Case`s covered

Function / operator overloading
- Via inferred type classes

Do notation
- Overload (<-) operator

-}

data Expr
  = Typ
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Ctr !String
  | Var !String
  | Let !Env !Expr
  | For !String !Expr
  | Lam !String !Expr
  | Case ![(String, Expr)]
  | Fun !Type !Type
  | App !Expr !Expr
  | Op !String ![Expr]
  deriving (Eq)

showParen' :: Bool -> String -> String
showParen' True a = "(" ++ a ++ ")"
showParen' False a = a

showPrefix :: Int -> Int -> String -> Expr -> String
showPrefix p q op a = showParen' (p > q) (op ++ showPrec (q + 1) a)

showInfixL :: Int -> Int -> Expr -> String -> Expr -> String
showInfixL p q a op b = showParen' (p > q) (showPrec q a ++ op ++ showPrec (q + 1) b)

showInfixR :: Int -> Int -> Expr -> String -> Expr -> String
showInfixR p q a op b = showParen' (p > q) (showPrec (q + 1) a ++ op ++ showPrec q b)

showPrec :: Int -> Expr -> String
showPrec _ Typ = "%Type"
showPrec _ IntT = "%Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "%Num"
showPrec _ (Num n) = show n
showPrec _ (Ctr k) = "#" ++ k
showPrec _ (Var x) = x
showPrec _ (Let env b) = do
  let showDef (x, a) = x ++ " = " ++ show a
  let x = "[" ++ intercalate "; " (showDef <$> env) ++ "]"
  show (App (Var x) b)
showPrec p (For x a) = showPrefix p 2 ("@" ++ x ++ ". ") a
showPrec p (Lam x a) = showPrefix p 2 ("\\" ++ x ++ " -> ") a
showPrec _ (Case branches) = do
  let showBranch (k, a) = k ++ " -> " ++ show a
  "{" ++ intercalate " | " (showBranch <$> branches) ++ "}"
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (App a b) = showInfixL p 3 a " " b
showPrec _ (Op op args) = "%" ++ op ++ " (" ++ intercalate ", " (show <$> args) ++ ")"

instance Show Expr where
  show :: Expr -> String
  show a = showPrec 0 a

type Type = Expr

type Ops = [(String, [Expr] -> Maybe Expr)]

type Env = [(String, Expr)]

data Symbol
  = Val !Expr
  | Ann !Expr !Type
  deriving (Eq, Show)

type Context = [(String, Symbol)]

data TypeError
  = EmptyCase
  | InfiniteType !String !Expr
  | InvalidCtr !String !Symbol
  | InvalidOp !String !Symbol
  | Mismatch !Expr !Expr
  | NotAFunction !Expr !Type
  | RuntimeError
  | UndefinedCtr !String
  | UndefinedOp !String
  | UndefinedVar !String
  deriving (Eq, Show)

fun :: [Type] -> Type -> Type
fun bs ret = foldr Fun ret bs

lam :: [String] -> Expr -> Expr
lam xs a = foldr Lam a xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

set :: Eq k => k -> v -> [(k, v)] -> [(k, v)]
set _ _ [] = []
set x y ((x', _) : kvs) | x == x' = (x, y) : kvs
set x y (kv : kvs) = kv : set x y kvs

eval :: Ops -> Env -> Expr -> Expr
eval _ _ Typ = Typ
eval _ _ IntT = IntT
eval _ _ NumT = NumT
eval _ _ (Int i) = Int i
eval _ _ (Num n) = Num n
eval _ _ (Ctr k) = Ctr k
eval ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just a -> eval ops ((x, Var x) : env) a
  Nothing -> Var x
eval ops env (Let env' a) = eval ops (env ++ env') a
eval ops env (For x a) = For x (eval ops ((x, Var x) : env) a)
eval ops env (Lam x a) = Lam x (eval ops ((x, Var x) : env) a)
eval ops env (Fun a b) = Fun (eval ops env a) (eval ops env b)
eval ops env (App a b) = case (eval ops env a, eval ops env b) of
  (Lam x a, b) -> eval ops ((x, b) : env) a
  (Case branches, b) -> case spine b of
    Ctr k : args -> case lookup k branches of
      Just b -> eval ops env (app b args)
      Nothing -> App (Case branches) b
    _else -> App (Case branches) b
  (a, b) -> App a b
eval ops env (Case branches) = Case (second (eval ops env) <$> branches)
eval ops env (Op op args) = do
  let args' = eval ops env <$> args
  case lookup op ops of
    Just f -> case f args' of
      Just a -> a
      Nothing -> Op op args'
    Nothing -> Op op args'

spine :: Expr -> [Expr]
spine (App a b) = spine a ++ [b]
spine a = [a]

ctxEnv :: Context -> Env
ctxEnv [] = []
ctxEnv ((x, Val a) : ctx) = (x, a) : ctxEnv ctx
ctxEnv ((x, Ann a _) : ctx) = (x, a) : ctxEnv ctx

solve :: Ops -> Context -> Expr -> Expr
solve ops ctx = eval ops (ctxEnv ctx)

occurs :: String -> Expr -> Bool
occurs _ Typ = False
occurs _ IntT = False
occurs _ (Int _) = False
occurs _ NumT = False
occurs _ (Num _) = False
occurs _ (Ctr _) = False
occurs x (Var y) = x == y
occurs x (Let env _) | x `elem` map fst env = False
occurs x (Let _ a) = occurs x a
occurs x (For x' _) | x == x' = False
occurs x (For _ a) = occurs x a
occurs x (Lam x' _) | x == x' = False
occurs x (Lam _ a) = occurs x a
occurs x (Case branches) = any (occurs x . snd) branches
occurs x (Fun a b) = occurs x a || occurs x b
occurs x (App a b) = occurs x a || occurs x b
occurs x (Op _ args) = any (occurs x) args

apply :: Ops -> (String, Expr) -> Symbol -> Symbol
apply ops sub (Val a) = Val (eval ops [sub] a)
apply ops sub (Ann a t) = Ann (eval ops [sub] a) (eval ops [sub] t)

unify :: Ops -> Context -> Expr -> Expr -> Either TypeError Context
unify ops ctx a b = case (solve ops ctx a, solve ops ctx b) of
  (Typ, Typ) -> Right ctx
  (IntT, IntT) -> Right ctx
  (Int i, Int i') | i == i' -> Right ctx
  (NumT, NumT) -> Right ctx
  (Num n, Num n') | n == n' -> Right ctx
  (Ctr k, Ctr k') | k == k' -> Right ctx
  (Var x, Var x') | x == x' -> Right ctx
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> Right (set x (Val b) (second (apply ops (x, b)) <$> ctx))
  (a, Var y) -> unify ops ctx (Var y) a
  (For x a, b) -> do
    let xT = newName (x ++ "T") (map fst ctx)
    ctx <- unify ops ((xT, Ann (Var xT) Typ) : (x, Ann (Var x) (Var xT)) : ctx) a b
    Right (pop x ctx)
  (a, For x b) -> do
    let xT = newName (x ++ "T") (map fst ctx)
    ctx <- unify ops ((xT, Ann (Var xT) Typ) : (x, Ann (Var x) (Var xT)) : ctx) a b
    Right (pop x ctx)
  -- TODO: Lam
  -- TODO: Case
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

inferType :: Ops -> Context -> Expr -> Either TypeError (Type, Context)
inferType _ ctx Typ = Right (Typ, ctx)
inferType _ ctx IntT = Right (Typ, ctx)
inferType _ ctx (Int _) = Right (IntT, ctx)
inferType _ ctx NumT = Right (Typ, ctx)
inferType _ ctx (Num _) = Right (NumT, ctx)
inferType ops ctx (Ctr k) = case lookup k ctx of
  Just (Ann (Ctr k') t) | k == k' -> Right (solve ops ctx t, ctx)
  Just sym -> Left (InvalidCtr k sym)
  Nothing -> Left (UndefinedCtr k)
inferType ops ctx (Var x) = case lookup x ctx of
  Just (Val (Var x')) | x == x' -> do
    let xT = newName (x ++ "T") (map fst ctx)
    Right (Var xT, (xT, Val (Var xT)) : (x, Ann (Var x) (Var xT)) : ctx)
  Just (Val a) -> do
    (t, ctx) <- inferType ops ((x, Val (Var x)) : ctx) a
    Right (t, pop x ctx)
  Just (Ann (Var x') t) | x == x' -> Right (solve ops ctx t, ctx)
  Just (Ann a t) -> do
    ctx <- checkType ops ctx a t
    Right (solve ops ctx t, ctx)
  Nothing -> Left (UndefinedVar x)
inferType ops ctx (Let env a) = inferType ops (ctx ++ map (second Val) env) a
inferType ops ctx (For x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (t, ctx) <- inferType ops ((xT, Ann (Var xT) Typ) : (x, Ann (Var x) (Var xT)) : ctx) a
  case (t, pop x ctx) of
    (Var xT', ctx) | xT == xT' -> Right (For xT $ Var xT, ctx)
    (t, ctx) -> Right (t, ctx)
inferType ops ctx (Lam x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (t2, ctx) <- inferType ops ((xT, Ann (Var xT) Typ) : (x, Ann (Var x) (Var xT)) : ctx) a
  case (solve ops ctx (Var xT), pop x ctx) of
    (t1, ctx) | xT `occurs` t1 -> Right (For xT $ Fun t1 t2, ctx)
    (t1, ctx) -> Right (Fun t1 t2, ctx)
inferType _ _ (Case []) = Left EmptyCase
inferType ops ctx (Case [(k, b)]) = do
  (ctrT, ctx) <- inferType ops ctx (Ctr k)
  (bT, ctx) <- inferType ops ctx b
  inferBranch ops ctx ctrT bT
inferType ops ctx (Case (branch : branches)) = do
  (t1, ctx) <- inferType ops ctx (Case [branch])
  (t2, ctx) <- inferType ops ctx (Case branches)
  ctx <- unify ops ctx t1 t2
  Right (solve ops ctx t1, ctx)
inferType ops ctx (Fun a b) = do
  ctx <- checkType ops ctx a Typ
  ctx <- checkType ops ctx b Typ
  Right (Typ, ctx)
inferType ops ctx (App a b) = do
  let xT = newName "_app" (map fst ctx)
  (ta, ctx) <- inferType ops ((xT, Val (Var xT)) : ctx) a
  (tb, ctx) <- inferType ops ctx b
  ctx <- unify ops ctx (Fun tb (Var xT)) ta
  Right (solve ops ctx (Var xT), pop xT ctx)
inferType ops ctx (Op op args) = case lookup op ctx of
  Just (Ann _ t) -> do
    (t, ctx) <- inferType ops ((op, Ann (Var op) t) : ctx) (app (Var op) args)
    Right (t, pop op ctx)
  Just sym -> Left (InvalidOp op sym)
  Nothing -> Left (UndefinedOp op)

inferBranch :: Ops -> Context -> Type -> Type -> Either TypeError (Type, Context)
inferBranch ops ctx (For x a) b = do
  let xT = newName (x ++ "T") (map fst ctx)
  (t, ctx) <- inferBranch ops ((xT, Ann (Var xT) Typ) : (x, Ann (Var x) (Var xT)) : ctx) a b
  case (t, pop x ctx) of
    (t, ctx) | x `occurs` t -> Right (For x t, ctx)
    (t, ctx) -> Right (t, ctx)
inferBranch ops ctx a (For x b) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (t, ctx) <- inferBranch ops ((xT, Ann (Var xT) Typ) : (x, Ann (Var x) (Var xT)) : ctx) a b
  Right (t, pop x ctx)
inferBranch ops ctx (Fun alt1 alt2) (Fun br1 br2) = do
  ctx <- unify ops ctx br1 alt1
  inferBranch ops ctx alt2 br2
inferBranch ops ctx altT branchT = Right (solve ops ctx (Fun altT branchT), ctx)

checkType :: Ops -> Context -> Expr -> Type -> Either TypeError Context
checkType ops ctx a t = do
  (ta, ctx) <- inferType ops ctx a
  unify ops ctx ta t

newName :: String -> [String] -> String
newName x xs = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` xs) names
