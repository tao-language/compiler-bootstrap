module Core where

import Control.Monad (when)
import Data.Bifunctor (Bifunctor (second))
import Data.Char (isDigit)
import Data.List (delete, dropWhileEnd, foldl', intercalate, union)
import Debug.Trace (trace)

-- More on pattern matching in Haskell:
--    https://www.politesi.polimi.it/bitstream/10589/140161/1/Tesi.pdf
-- f (x := 5) = x --> f (x as 5) = x --> f x = 5 ---> always returns 5
-- f (x + 1) = x --> ??

-- More on type inference:
--    https://crypto.stanford.edu/~blynn/lambda/pts.html
--    https://youtu.be/ytPAlhnAKro

{- TODO:
* TypeError

* Function / operator overloading
* Do notation
  - Overload (<-) operator
-}

data Literal
  = IntT
  | Int !Int
  | Ctr !String
  deriving (Eq)

data Expr
  = Knd
  | Typ
  | Lit !Literal
  | Var !String
  | Fun !Type !Type
  | For !String !Type !Expr
  | Lam !String !Type !Expr
  | Case !Literal !Expr
  | Or !Expr !Expr
  | App !Expr !Expr
  | Fix !Expr
  | Op !String ![Expr]
  | Err
  deriving (Eq)

type Type = Expr

type Context = [(String, Type)]

type Env = [(String, Expr)]

type Ops = [(String, [Expr] -> Maybe Expr)]

data TypeError
  = InfiniteExpr !String !Expr
  | NotAFunction !Expr !Type
  | RuntimeError
  | UndefinedCtr !String
  | UndefinedOp !String
  | UndefinedVar !String
  | UnifyError !Expr !Expr
  | TODO !String -- REMOVE!
  deriving (Eq, Show)

instance Show Literal where
  show IntT = "Int"
  show (Int i) = show i
  show (Ctr k) = "#" ++ k

instance Show Expr where
  show Knd = "@Kind"
  show Typ = "@Type"
  show (Lit k) = show k
  show (Var x) = x
  show (Fun t u) = showArrow t u
    where
      showArrow t u = showL t ++ " -> " ++ showR u
        where
          showL Lam {} = "(" ++ show t ++ ")"
          showL Fun {} = "(" ++ show t ++ ")"
          showL For {} = "(" ++ show t ++ ")"
          showL _ = show t
          showR Lam {} = "(" ++ show u ++ ")"
          showR (Fun _ _) = show u
          showR For {} = "(" ++ show u ++ ")"
          showR _ = show u
  show (For x a b) = "@" ++ x ++ " : " ++ show a ++ ". " ++ show b
  show (Lam x t u) = "\\" ++ x ++ " : " ++ show t ++ " -> " ++ show u
  show (Case k a) = "\\" ++ show k ++ " -> " ++ show a
  show (Or a b) = "(" ++ show a ++ ") | (" ++ show b ++ ")" -- TODO: parentheses
  show (App x y) = showL x ++ showR y
    where
      showL Fun {} = "(" ++ show x ++ ")"
      showL Lam {} = "(" ++ show x ++ ")"
      showL _ = show x
      showR (Var s) = ' ' : s
      showR (Lit k) = ' ' : show k
      showR _ = "(" ++ show y ++ ")"
  show (Fix a) = show (App (Var "@fix") a)
  show (Op s a) = "{" ++ s ++ "[" ++ intercalate ", " (show <$> a) ++ "]}"
  show Err = "@error"

intT :: Expr
intT = Lit IntT

int :: Int -> Expr
int = Lit . Int

ctr :: String -> Expr
ctr = Lit . Ctr

fun :: [Expr] -> Expr -> Expr
fun bs ret = foldr Fun ret bs

lam :: [(String, Type)] -> Expr -> Expr
lam args body = foldr (uncurry Lam) body args

pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

set :: Eq k => k -> v -> [(k, v)] -> [(k, v)]
set x y [] = [(x, y)]
set x y ((x', _) : kvs) | x == x' = (x, y) : kvs
set x y (kv : kvs) = kv : set x y kvs

newName :: String -> [String] -> String
newName x xs = do
  let names = map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` xs) names

freeVars :: Expr -> [String]
freeVars Knd = []
freeVars Typ = []
freeVars (Lit _) = []
freeVars (Var x) = [x]
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (For x t a) = freeVars t `union` delete x (freeVars a)
freeVars (Lam x t a) = freeVars t `union` delete x (freeVars a)
freeVars (Case _ a) = freeVars a
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Fix a) = freeVars a
freeVars (Op _ []) = []
freeVars (Op op (a : args)) = freeVars a `union` freeVars (Op op args)
freeVars Err = []

occurs :: String -> Expr -> Bool
occurs _ Knd = False
occurs _ Typ = False
occurs _ (Lit _) = False
occurs x (Var y) = x == y
occurs x (Fun a b) = occurs x a || occurs x b
occurs x (For x' t _) | x == x' = occurs x t
occurs x (For _ t a) = occurs x t || occurs x a
occurs x (Lam x' t _) | x == x' = occurs x t
occurs x (Lam _ t a) = occurs x t || occurs x a
occurs x (Case _ a) = occurs x a
occurs x (Or a b) = occurs x a || occurs x b
occurs x (App a b) = occurs x a || occurs x b
occurs x (Fix a) = occurs x a
occurs x (Op _ args) = any (occurs x) args
occurs _ Err = False

rename :: String -> String -> Expr -> Expr
rename _ _ Knd = Knd
rename _ _ Typ = Typ
rename _ _ (Lit k) = Lit k
rename x y (Var x') | x == x' = Var y
rename _ _ (Var x) = Var x
rename x _ (For x' t a) | x == x' = For x t a
rename x y (For z t a) = For z (rename x y t) (rename x y a)
rename x y (Fun a b) = Fun (rename x y a) (rename x y b)
rename x _ (Lam x' t a) | x == x' = Lam x t a
rename x y (Lam z t a) = Lam z (rename x y t) (rename x y a)
rename x y (Case k a) = Case k (rename x y a)
rename x y (Or a b) = Or (rename x y a) (rename x y b)
rename x y (App a b) = App (rename x y a) (rename x y b)
rename x y (Fix a) = Fix (rename x y a)
rename x y (Op op args) = Op op (rename x y <$> args)
rename _ _ Err = Err

beta :: (String, Expr) -> Expr -> Expr
beta _ Knd = Knd
beta _ Typ = Typ
beta _ (Lit k) = Lit k
beta (x, a) (Var x') | x == x' = a
beta _ (Var x) = Var x
beta sub (Fun a b) = Fun (beta sub a) (beta sub b)
beta (x, _) (For x' t b) | x == x' = For x t b
beta (x, a) (For y t b) | y `occurs` a = do
  let z = newName y (freeVars a)
  For z (beta (x, a) t) (beta (x, a) (rename y z b))
beta sub (For y t b) = For y (beta sub t) (beta sub b)
beta (x, _) (Lam x' t b) | x == x' = Lam x t b
beta (x, a) (Lam y t b) | y `occurs` a = do
  let z = newName y (freeVars a)
  Lam z (beta (x, a) t) (beta (x, a) (rename y z b))
beta sub (Lam y t b) = Lam y (beta sub t) (beta sub b)
beta sub (Case k a) = Case k (beta sub a)
beta sub (Or a b) = Or (beta sub a) (beta sub b)
beta sub (App a b) = App (beta sub a) (beta sub b)
beta sub (Fix b) = Fix (beta sub b)
beta sub (Op op args) = Op op (beta sub <$> args)
beta _ Err = Err

reduce :: Ops -> Env -> Expr -> Expr
reduce _ _ Knd = Knd
reduce _ _ Typ = Typ
reduce _ _ (Lit k) = Lit k
reduce ops env (Var x) = case lookup x env of
  Just a | a /= Var x -> reduce ops env a
  _else -> Var x
reduce _ _ (Fun a b) = Fun a b
reduce _ _ (For x a b) = For x a b
reduce _ _ (Lam x a b) = Lam x a b
reduce _ _ (Case k a) = Case k a
reduce _ _ (Or a b) = Or a b
reduce ops env (App a b) = case reduce ops env a of
  Lam x _ a -> reduce ops env (beta (x, b) a)
  Case k a -> case reduce ops env b of
    Lit k' | k == k' -> reduce ops env a
    App b1 b2 -> reduce ops env (App (reduce ops env (App (Case k a) b1)) b2)
    _patternMismatch -> Err
  Or a1 a2 -> case reduce ops env (App a1 b) of
    Err -> reduce ops env (App a2 b)
    c -> c
  Op op args -> reduce ops env (Op op (args ++ [b]))
  Err -> Err
  a -> App a b
reduce ops env (Fix a) = reduce ops env (App a (Fix a))
reduce ops env (Op op args) = do
  let args' = reduce ops env <$> args
  case lookup op ops of
    Just f -> case f args' of
      Just a -> a
      Nothing -> Op op args'
    Nothing -> Op op args'
reduce _ _ Err = Err

eval :: Ops -> Env -> Expr -> Expr
eval ops env term = case reduce ops env term of
  Knd -> Knd
  Typ -> Typ
  Lit k -> Lit k
  Var x -> Var x
  Fun a b -> Fun (eval ops env a) (eval ops env b)
  For x t a -> For x (eval ops env t) (eval ops ((x, Var x) : env) a)
  Lam x t a -> Lam x (eval ops env t) (eval ops ((x, Var x) : env) a)
  Case k a -> Case k (eval ops env a)
  Or a b -> Or (eval ops env a) (eval ops env b)
  App a b -> App (eval ops env a) (eval ops env b)
  Fix a -> Fix (eval ops env a)
  Op op args -> Op op (eval ops env <$> args)
  Err -> Err

unify :: Ops -> Env -> Expr -> Expr -> Either TypeError Env
unify ops env a b = case (eval ops env a, eval ops env b) of
  (Knd, Knd) -> Right env
  (Typ, Typ) -> Right env
  (Lit k, Lit k') | k == k' -> Right env
  (Var x, Var x') | x == x' -> Right env
  (Var x, b) | x `occurs` b -> Left (InfiniteExpr x b)
  (Var x, b) -> Right (set x b env)
  (a, Var y) | y `occurs` a -> Left (InfiniteExpr y a)
  (a, Var y) -> Right (set y a env)
  (a, b) -> Left (UnifyError a b)

inferLit :: Context -> Literal -> Either TypeError Expr
inferLit _ IntT = Right Typ
inferLit _ (Int _) = Right (Lit IntT)
inferLit ctx (Ctr k) = case lookup k ctx of
  Just t -> Right t
  Nothing -> Left (UndefinedCtr k)

infer :: Ops -> Env -> Context -> Expr -> Either TypeError (Expr, Env, Context)
infer _ env ctx Knd = Right (Knd, env, ctx)
infer _ env ctx Typ = Right (Knd, env, ctx)
infer ops env ctx (Lit k) = do
  t <- inferLit ctx k
  Right (eval ops env t, env, ctx)
infer ops env ctx (Var x) = case lookup x ctx of
  Just t -> Right (eval ops env t, env, ctx)
  Nothing -> Left (UndefinedVar x)
infer ops env ctx (Fun a b) = do
  _ <- infer ops env ctx a
  infer ops env ctx b
infer ops env ctx (For x t a) = do
  (t, env, ctx) <- infer ops ((x, Var x) : env) ((x, eval ops env t) : ctx) a
  Right (t, pop x env, pop x ctx)
infer ops env ctx (Lam x t a) = do
  let t1 = eval ops env t
  (t2, env, ctx) <- infer ops ((x, Var x) : env) ((x, t1) : ctx) a
  Right (Fun t1 t2, pop x env, pop x ctx)
infer ops env ctx (Case k b) = do
  t1 <- inferLit ctx k
  (t2, env, ctx) <- infer ops env ctx b
  Right (Fun t1 t2, env, ctx)
infer ops env ctx (Or a b) = Left $ TODO "infer Or"
infer ops env ctx (App a b) = do
  (ta, env, ctx) <- infer ops env ctx a
  case instantiate ops env ctx ta of
    (Fun t1 t2, env, ctx) -> do
      (k1, env, ctx) <- infer ops env ctx t1
      case k1 of
        k1 | k1 == Knd || k1 == Typ -> do
          (tb, env, ctx) <- infer ops env ctx b
          env <- unify ops env t1 tb
          Right (eval ops env t2, env, ctx)
        _typeLiteral -> do
          env <- unify ops env t1 b
          Right (eval ops env t2, env, ctx)
    (ta, _, _) -> Left (NotAFunction a ta)
infer ops env ctx (Fix a) = Left $ TODO "infer Fix"
infer _ env ctx (Op op args) = case lookup op ctx of
  Just t -> Right (t, env, ctx) -- TODO: make sure `args` types match
  Nothing -> Left (UndefinedOp op)
infer _ _ _ Err = Left RuntimeError

instantiate :: Ops -> Env -> Context -> Type -> (Type, Env, Context)
instantiate ops env ctx (For x t a) =
  instantiate ops ((x, Var x) : env) ((x, eval ops env t) : ctx) a
instantiate ops env ctx a = (eval ops env a, env, ctx)
