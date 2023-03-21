{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (Foldable (foldl'))
import Data.List (intercalate)

-- Lambda calculus:
--  https://github.com/mroman42/mikrokosmos
--  https://github.com/mroman42/mikrokosmos/blob/master/source/Lambda.hs      -- Core language
--  https://github.com/mroman42/mikrokosmos/blob/master/source/Stlc/Types.hs  -- Type inference

-- More on pattern matching in Haskell:
--    https://www.politesi.polimi.it/bitstream/10589/140161/1/Tesi.pdf
-- f (x := 5) = x --> f (x as 5) = x --> f x = 5 ---> always returns 5
-- f (x + 1) = x --> ??

-- More on type inference:
--    https://crypto.stanford.edu/~blynn/lambda/pts.html
--    https://youtu.be/ytPAlhnAKro

-- Dependent types:
--  http://strictlypositive.org/Easy.pdf

-- Bidirectional type checking:
--  https://www.youtube.com/live/utyBNDj7s2w?feature=share

{- TODO:
* Function / operator overloading
* Do notation
  - Overload (<-) operator
-}

data Literal
  = IntT
  | Int !Int
  | NumT
  | Num !Double
  | Ctr !String
  deriving (Eq)

instance Show Literal where
  show :: Literal -> String
  show IntT = "@Int"
  show (Int i) = show i
  show NumT = "@Num"
  show (Num n) = show n
  show (Ctr k) = "#" ++ k

data Expr
  = Typ
  | Lit !Literal
  | Var !String
  | Let !Env !Expr
  | Lam !String !Expr
  | Fun !Type !Type
  | App !Expr !Expr
  | Case !Expr ![(String, Expr)]
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
showPrec _ Typ = "@Type"
showPrec _ (Lit k) = show k
showPrec _ (Var x) = x
showPrec _ (Let env b) = do
  let showDef (x, a) = x ++ " = " ++ show a
  let x = "[" ++ intercalate "; " (map showDef env) ++ "]"
  show (App (Var x) b)
showPrec p (Lam x a) = showPrefix p 1 ("\\" ++ x ++ " -> ") a
showPrec p (Fun a b) = showInfixR p 1 a " -> " b
showPrec p (App a b) = showInfixL p 2 a " " b
showPrec _ (Case a cases) = do
  let showCase (k, b) = k ++ " -> " ++ show b
  "@case " ++ show a ++ " {" ++ intercalate " | " (map showCase cases) ++ "}"
showPrec _ (Op op args) = "%" ++ op ++ " (" ++ intercalate ", " (map show args) ++ ")"

instance Show Expr where
  show :: Expr -> String
  show a = showPrec 0 a

type Type = Expr

type Ops = [(String, [Expr] -> Maybe Expr)]

type Env = [(String, Expr)]

data Scheme = For ![String] !Type
  deriving (Eq, Show)

data Symbol
  = Val !Expr
  | Ann !Expr !Scheme
  deriving (Eq, Show)

type Context = [(String, Symbol)]

data TypeError
  = InfiniteType !String !Expr
  | InvalidCtr !String !Symbol
  | InvalidOp !String !Symbol
  | NotAFunction !Expr !Type
  | Mismatch !Expr !Expr
  | UndefinedCtr !String
  | UndefinedOp !String
  | UndefinedVar !String
  | EmptyCase
  deriving (Eq, Show)

intT :: Expr
intT = Lit IntT

int :: Int -> Expr
int = Lit . Int

numT :: Expr
numT = Lit NumT

num :: Double -> Expr
num = Lit . Num

ctr :: String -> Expr
ctr = Lit . Ctr

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
set x y [] = [(x, y)]
set x y ((x', _) : kvs) | x == x' = (x, y) : kvs
set x y (kv : kvs) = kv : set x y kvs

eval :: Ops -> Env -> Expr -> Expr
eval _ _ Typ = Typ
eval _ _ (Lit k) = Lit k
eval ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just a -> eval ops env a
  Nothing -> Var x
eval ops env (Let env' a) = eval ops (env ++ env') a
eval ops env (Lam x a) = Lam x (eval ops ((x, Var x) : env) a)
eval ops env (Fun a b) = Fun (eval ops env a) (eval ops env b)
eval ops env (App a b) = case (eval ops env a, eval ops env b) of
  (Lam x a, b) -> eval ops ((x, b) : env) a
  (a, b) -> App a b
eval ops env (Case a cases) =
  Case (eval ops env a) (second (eval ops env) <$> cases)
eval ops env (Op op args) = do
  let args' = eval ops env <$> args
  case lookup op ops of
    Just f -> case f args' of
      Just a -> a
      Nothing -> Op op args'
    Nothing -> Op op args'

ctxEnv :: Context -> Env
ctxEnv [] = []
ctxEnv ((x, Val a) : ctx) = (x, a) : ctxEnv ctx
ctxEnv ((x, Ann a _) : ctx) = (x, a) : ctxEnv ctx

solve :: Ops -> Context -> Expr -> Expr
solve ops ctx = eval ops (ctxEnv ctx)

occurs :: String -> Expr -> Bool
occurs _ Typ = False
occurs _ (Lit _) = False
occurs x (Var y) = x == y
occurs x (Let env _) | x `elem` map fst env = False
occurs x (Let _ a) = occurs x a
occurs x (Lam x' _) | x == x' = False
occurs x (Lam _ a) = occurs x a
occurs x (Fun a b) = occurs x a || occurs x b
occurs x (App a b) = occurs x a || occurs x b
occurs x (Case a cases) = occurs x a || any (occurs x . snd) cases
occurs x (Op _ args) = any (occurs x) args

apply :: Ops -> (String, Expr) -> Symbol -> Symbol
apply ops sub (Val b) = Val (eval ops [sub] b)
apply ops sub (Ann b (For xs t)) = do
  let b' = eval ops [sub] b
  let t' = eval ops (sub : map (\x -> (x, Var x)) xs) t
  Ann b' (For xs t')

unify :: Ops -> Context -> Expr -> Expr -> Either TypeError Context
unify ops ctx a b = case (solve ops ctx a, solve ops ctx b) of
  (Typ, Typ) -> Right ctx
  (Lit k, Lit k') | k == k' -> Right ctx
  (Var x, Var x') | x == x' -> Right ctx
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) ->
    Right (set x (Val b) (map (second $ apply ops (x, b)) ctx))
  (a, Var y) -> unify ops ctx (Var y) a
  -- TODO: Lam
  (Fun a1 a2, Fun b1 b2) -> do
    ctx <- unify ops ctx a1 b1
    unify ops ctx a2 b2
  (App a1 a2, App b1 b2) -> do
    ctx <- unify ops ctx a1 b1
    unify ops ctx a2 b2
  -- TODO: Op
  (a, b) -> Left (Mismatch a b)

instantiate :: Ops -> Context -> Scheme -> Either TypeError (Type, Context)
instantiate ops ctx (For [] a) =
  Right (solve ops ctx a, ctx)
instantiate ops ctx (For (x : xs) a) = do
  let y = newName x (map fst ctx)
  let a' = eval ops [(x, Var y)] a
  instantiate ops ((y, Val (Var y)) : ctx) (For xs a')

inferType :: Ops -> Context -> Expr -> Either TypeError (Type, Context)
inferType _ ctx Typ = Right (Typ, ctx)
inferType _ ctx (Lit IntT) = Right (Typ, ctx)
inferType _ ctx (Lit (Int _)) = Right (Lit IntT, ctx)
inferType _ ctx (Lit NumT) = Right (Typ, ctx)
inferType _ ctx (Lit (Num _)) = Right (Lit NumT, ctx)
inferType ops ctx (Lit (Ctr k)) = case lookup k ctx of
  Just (Ann (Lit (Ctr k')) scheme) | k == k' -> instantiate ops ctx scheme
  Just sym -> Left (InvalidCtr k sym)
  Nothing -> Left (UndefinedCtr k)
inferType ops ctx (Var x) = case lookup x ctx of
  Just (Val (Var x')) | x == x' -> do
    let xT = newName (x ++ "T") (map fst ctx)
    Right (Var xT, (x, Ann (Var x) (For [xT] (Var xT))) : ctx)
  Just (Val a) -> inferType ops ctx a
  Just (Ann (Var x') scheme) | x == x' -> instantiate ops ctx scheme
  Just (Ann a scheme) -> do
    (t, ctx) <- instantiate ops ctx scheme
    ctx <- checkType ops ctx a t
    Right (solve ops ctx t, ctx)
  Nothing -> Left (UndefinedVar x)
inferType ops ctx (Let env a) = inferType ops (ctx ++ map (second Val) env) a
inferType ops ctx (Lam x a) = do
  let xT = x ++ "T"
  (t2, ctx) <- inferType ops ((x, Ann (Var x) (For [xT] (Var xT))) : ctx) a
  Right (Fun (solve ops ctx (Var xT)) t2, ctx)
inferType ops ctx (Fun a b) = do
  ctx <- checkType ops ctx a Typ
  ctx <- checkType ops ctx b Typ
  Right (Typ, ctx)
inferType ops ctx (App a b) = do
  (ta, ctx) <- inferType ops ctx a
  case ta of
    Fun t1 t2 -> do
      ctx <- checkType ops ctx b t1
      Right (solve ops ctx t2, ctx)
    ta -> Left (NotAFunction a ta)
inferType _ _ (Case _ []) = Left EmptyCase
inferType ops ctx (Case a [(alt, branch)]) = do
  (b, ctx) <- inferType ops ctx (ctr alt)
  (c, ctx) <- inferType ops ctx branch
  case (b, c) of
    (Fun b1 b2, Fun c1 c2) -> do
      ctx <- unify ops ctx b1 c1
      let x = newName alt (map fst ctx)
      (t, ctx) <- inferType ops ((x, Ann (Var x) (For [] b1)) : (alt, Ann (ctr alt) (For [] b2)) : ctx) (App branch (Var x))
      Right (solve ops ctx b, ctx)
    (a, b) -> Right (Fun a b, ctx)
inferType ops ctx (Case a (case' : cases)) = do
  (t, ctx) <- inferType ops ctx (Case a [case'])
  (t', ctx) <- inferType ops ctx (Case a cases)
  ctx <- unify ops ctx t t'
  Right (solve ops ctx t, ctx)
inferType ops ctx (Op op args) = case lookup op ctx of
  Just (Ann (Var op') scheme) | op == op' -> do
    (t, ctx) <- inferType ops ((op, Ann (Var op) scheme) : ctx) (app (Var op) args)
    Right (t, pop op ctx)
  Just sym -> Left (InvalidOp op sym)
  Nothing -> Left (UndefinedOp op)

checkType :: Ops -> Context -> Expr -> Type -> Either TypeError Context
checkType _ ctx (Op _ []) _ = Right ctx
checkType ops ctx (Op op (a : bs)) (Fun t1 t2) = do
  ctx <- checkType ops ctx a t1
  checkType ops ctx (Op op bs) t2
checkType _ _ a@Op {} t = Left (NotAFunction a t)
checkType ops ctx a t = do
  (ta, ctx) <- inferType ops ctx a
  unify ops ctx ta t

newName :: String -> [String] -> String
newName x xs = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` xs) names
