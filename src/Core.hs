{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable (Foldable (foldl'))
import Data.List (delete, intercalate, union)

{- TODO:

Clean up code
- unify just return env
- unify don't evaluate at the start
- check just return env
- Consistency on variable names:
  * Expr: a, b, c
  * Type: t, t1, t2, ta, tb, tc
  * Var: x, y, z
- Show Term with precedence
- Remove unused errors

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
  | Ctr !String ![Term]
  | Typ !String ![(String, Term)] ![String]
  | Case !String ![(String, Term)] !Term
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
showPrec p (Lam x a) = do
  let (xs, a') = asLam (Lam x a)
  showPrefix p 2 ("\\" ++ unwords xs ++ " -> ") a'
showPrec p (For x a) = do
  let (xs, a') = asFor (For x a)
  showPrefix p 2 ("@for " ++ unwords xs ++ ". ") a'
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (App a b) = showInfixL p 3 a " " b
showPrec p (Ann a b) = showInfixL p 1 a " : " b
showPrec p (Let [] a) = showPrec p a
showPrec p (Let env a) = do
  let showDef (x, b) = x ++ " = " ++ show b
  let defs = "@let {" ++ intercalate "; " (showDef <$> env) ++ "} "
  showPrefix p 2 defs a
showPrec _ (Fix x a) = "@fix " ++ x ++ " {" ++ show a ++ "}"
showPrec p (Ctr name args) = "#" ++ showPrec p (app (Var name) args)
showPrec p (Typ name args ctrs) = do
  -- let x = name ++ "[" ++ unwords (map fst args) ++ "]{" ++ intercalate "|" ctrs ++ "}"
  let x = name
  "%" ++ showPrec p (app (Var x) (map snd args))
showPrec _ (Case x brs c) = do
  let showBr (k, b) = k ++ " => " ++ show b
  "@Case " ++ x ++ " {" ++ intercalate " | " (map showBr (brs ++ [("_", c)])) ++ "}"
showPrec p (Op op args) = showPrec p (app (Var ("@op[" ++ op ++ "]")) args)

instance Show Term where
  show :: Term -> String
  show a = showPrec 0 a

type Type = Term

type Operator = [Term] -> Maybe Term

type Ops = [(String, Operator)]

type Env = [(String, Term)]

data TypeError
  = InfiniteType !String !Term
  | CtrNotInType !String ![(String, Type)]
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

asLam :: Term -> ([String], Term)
asLam (Lam x a) = first (x :) (asLam a)
asLam a = ([], a)

for :: [String] -> Term -> Term
for xs a = foldr (\x a -> if x `occurs` a then For x a else a) a xs

asFor :: Term -> ([String], Term)
asFor (For x a) = first (x :) (asFor a)
asFor a = ([], a)

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
freeVars (Ctr _ args) = foldr (union . freeVars) [] args
freeVars (Typ _ args _) = foldr (union . freeVars . snd) [] args
freeVars (Case _ brs c) = foldr (union . freeVars . snd) (freeVars c) brs
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
  Case x brs c -> case reduce ops env b of
    Ctr k args -> case lookup k brs of
      Just b -> reduce ops [] (app b args)
      Nothing -> reduce ops [] c
    b -> App (Case x brs c) b
  a -> App a (Let env b)
reduce ops env (Ann a _) = reduce ops env a
reduce ops env (Let env' a) = reduce ops (env ++ env') a
reduce _ env (Fix x a) = Fix x (Let env a)
reduce _ env (Ctr name args) = Ctr name (Let env <$> args)
reduce _ env (Typ name args ctrs) = Typ name (second (Let env) <$> args) ctrs
reduce _ env (Case x brs c) = Case x (second (Let env) <$> brs) (Let env c)
reduce ops env (Op op args) = do
  case (lookup op ops, eval ops env <$> args) of
    (Just f, args) -> case f args of
      Just a -> reduce ops env a
      Nothing -> Op op args
    (Nothing, args) -> Op op args

eval :: Ops -> Env -> Term -> Term
eval ops env term = case reduce ops env term of
  Knd -> Knd
  IntT -> IntT
  NumT -> NumT
  Int i -> Int i
  Num n -> Num n
  Var x -> Var x
  Lam x a -> Lam x (eval ops [(x, Var x)] a)
  For x a -> for [x] (eval ops [(x, Var x)] a)
  Fun a b -> Fun (eval ops [] a) (eval ops [] b)
  App a b -> App (eval ops [] a) (eval ops [] b)
  Ann _ _ -> error "unreachable"
  Let _ _ -> error "unreachable"
  Fix x a -> case eval ops [(x, Var x)] a of
    a | x `occurs` a -> Fix x a
    a -> a
  Ctr name args -> Ctr name (eval ops [] <$> args)
  Typ name args ctrs -> Typ name (second (eval ops []) <$> args) ctrs
  Case x brs c -> Case x (second (eval ops []) <$> brs) (eval ops [] c)
  Op op args -> Op op (eval ops [] <$> args)

-- TODO: move pattern matching into definition level.
unify :: Ops -> Env -> Term -> Term -> Either TypeError (Term, Env)
unify ops env a b = case (a, b) of
  (Knd, Knd) -> Right (Knd, env)
  (IntT, IntT) -> Right (IntT, env)
  (Int i, Int i') | i == i' -> Right (Int i, env)
  (NumT, NumT) -> Right (NumT, env)
  (Num n, Num n') | n == n' -> Right (Num n, env)
  (Var x, Var x') | x == x' -> Right (Var x, env)
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> do
    let b' = eval ops env b
    Right (b', set x b' env)
  (a, Var y) -> unify ops env (Var y) a
  (a, For x b) -> do
    let y = newName x (map fst env)
    (a, env) <- unify ops ((y, Var y) : env) a (eval ops [(x, Var y)] b)
    Right (for [y] a, pop y env)
  (For x a, b) -> do
    let y = newName x (map fst env)
    (a, env) <- unify ops ((y, Var y) : env) (eval ops [(x, Var y)] a) b
    Right (for [y] a, pop y env)
  (Fun a1 b1, Fun a2 b2) -> do
    (a, env) <- unify ops env a1 a2
    (b, env) <- unify ops env (eval ops env b1) (eval ops env b2)
    Right (Fun (eval ops env a) b, env)
  (App a1 b1, App a2 b2) -> do
    (a, env) <- unify ops env a1 a2
    (b, env) <- unify ops env (eval ops env b1) (eval ops env b2)
    Right (App (eval ops env a) b, env)
  (Typ name args ctrs, Typ name' args' ctrs') | name == name' && map fst args == map fst args' && ctrs == ctrs' -> do
    (argsT, env) <- unifyMany ops env (map snd args) (map snd args')
    Right (Typ name (zip (map fst args) argsT) ctrs, env)
  (Op op args, Op op' args') | op == op' && length args == length args' -> do
    (args, env) <- unifyMany ops env args args'
    Right (Op op args, env)
  (a, b) -> Left (TypeMismatch a b)

unifyMany :: Ops -> Env -> [Term] -> [Term] -> Either TypeError ([Term], Env)
unifyMany _ env [] _ = Right ([], env)
unifyMany _ env _ [] = Right ([], env)
unifyMany ops env (a1 : bs1) (a2 : bs2) = do
  (a, env) <- unify ops env a1 a2
  (bs, env) <- unifyMany ops env (eval ops env <$> bs1) (eval ops env <$> bs2)
  Right (eval ops env a : bs, env)

expandType :: Ops -> Env -> String -> [(String, Term)] -> [(String, Type)] -> Type
expandType ops env name args alts = do
  let x = newName ("$" ++ name) (foldr (union . freeVars . snd) [] alts)
  let branch :: Type -> Type
      branch (Fun a b) = Fun (eval ops (args ++ env) a) (branch b)
      branch _ = Var x
  for (x : map fst args) (fun (branch . snd <$> alts) (Var x))

findTyped :: Ops -> Env -> String -> Either TypeError (Term, Type)
findTyped ops env x = case lookup x env of
  Just (Ann a t) -> Right (a, eval ops env t)
  Just a -> Left (MissingType x a)
  Nothing -> Left (UndefinedVar x)

instantiate :: Ops -> Env -> Type -> ([String], Type, Env)
instantiate ops env (For x t) = do
  let y = newName x (map fst env)
  let (xs, t', env') = instantiate ops ((y, Var y) : env) (eval ops [(x, Var y)] t)
  (y : xs, t', env')
instantiate ops env t = ([], eval ops env t, env)

infer :: Ops -> Env -> Term -> Either TypeError (Type, Env)
infer _ env Knd = Right (Knd, env)
infer _ env IntT = Right (Knd, env)
infer _ env (Int _) = Right (IntT, env)
infer _ env NumT = Right (Knd, env)
infer _ env (Num _) = Right (NumT, env)
infer ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Right (Knd, env)
  Just (Ann (Var x') t) | x == x' -> Right (eval ops env t, env)
  Just a -> infer ops env a
  Nothing -> Left (UndefinedVar x)
infer ops env (Lam x a) = do
  let xT = newName (x ++ "T") (map fst env)
  env <- Right ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env)
  (t2, env) <- infer ops env a
  (t1, env) <- infer ops env (Var x)
  Right (for [xT] $ Fun t1 t2, pop x env)
infer ops env (For x a) = do
  let xT = newName (x ++ "T") (map fst env)
  env <- Right ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env)
  (aT, env) <- infer ops env a
  Right (for [xT] aT, pop x env)
infer ops env (Fun a b) = do
  (_, env) <- infer ops env (Ann a Knd)
  (_, env) <- infer ops env (Ann b Knd)
  Right (Knd, env)
infer ops env (App a b) = do
  (ta, env) <- infer ops env a
  (tb, env) <- infer ops env b
  let x = newName "t" (map fst env)
  env <- Right ((x, Var x) : env)
  (t, env) <- unify ops env (Fun tb (Var x)) ta
  case asFor t of
    (xs, Fun _ t) -> Right (for xs t, pop x env)
    _else -> error "unreachable"
infer ops env (Ann a t) = do
  (ta, env) <- infer ops env a
  unify ops env ta (eval ops env t)
infer ops env (Let env' a) = infer ops (env ++ env') a
infer ops env (Fix x a) = do
  let xT = newName (x ++ "T") (map fst env)
  env <- Right ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env)
  (ta, env) <- infer ops env a
  Right (ta, pop x env)
infer ops env (Ctr k args) = do
  (_, t) <- findTyped ops env k
  inferApply ops env (k, t) args
infer ops env (Typ name args alts) = do
  (_, t) <- findTyped ops env name
  inferApply ops env (name, t) (map snd args)
infer ops env (Case x brs c) = do
  (tname, targs, ctrs) <- case lookup x env of
    Just a -> case asTypeDef a of
      Just tdef -> Right tdef
      Nothing -> Left (NotAUnionType a)
    Nothing -> Left (UndefinedType x)
  let xs = map fst targs
  alts <- mapM (altBranchType ops env xs) ctrs
  env <- Right (map (\x -> (x, Var x)) (xs ++ ctrs ++ [tname]) ++ env)
  (tb, env) <- inferBranches ops env alts brs c
  let ta = eval ops env (Typ tname targs ctrs)
  Right (for xs (Fun ta tb), pop tname env)
infer ops env (Op op args) = do
  (_, t) <- findTyped ops env op
  inferApply ops env (op, t) args

altBranchType :: Ops -> Env -> [String] -> String -> Either TypeError (String, Type)
altBranchType ops env xs k = do
  (_, ctrT) <- findTyped ops env k
  Right (k, asBranchType xs ctrT (Var k))

inferBranches :: Ops -> Env -> [(String, Type)] -> [(String, Term)] -> Term -> Either TypeError (Type, Env)
inferBranches ops env _ [] c = infer ops env c
inferBranches ops env alts (br : brs) c = do
  (t1, env) <- inferBranch ops env alts br
  (t2, env) <- inferBranches ops env alts brs c
  unify ops env t1 t2

inferBranch :: Ops -> Env -> [(String, Type)] -> (String, Term) -> Either TypeError (Type, Env)
inferBranch ops env alts (k, a) = case lookup k alts of
  Just t -> do
    (_, env) <- infer ops env (Ann a t)
    Right (eval ops env (Var k), env)
  Nothing -> Left (CtrNotInType k alts)

asBranchType :: [String] -> Type -> Type -> Type
asBranchType xs (For x a) c | x `elem` xs = asBranchType xs a c
asBranchType xs (For x a) c = For x (asBranchType xs a c)
asBranchType xs (Fun a b) c = Fun a (asBranchType xs b c)
asBranchType _ _ c = c

asTypeDef :: Term -> Maybe (String, [(String, Term)], [String])
asTypeDef (Ann a _) = asTypeDef a
asTypeDef (Lam _ a) = asTypeDef a
asTypeDef (Typ name args ctrs) = Just (name, args, ctrs)
asTypeDef _ = Nothing

inferApply :: Ops -> Env -> (String, Type) -> [Term] -> Either TypeError (Type, Env)
inferApply ops env (x, t) args = do
  env <- Right ((x, Ann (Var x) t) : env)
  (t, env) <- infer ops env (app (Var x) args)
  Right (t, pop x env)

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names
