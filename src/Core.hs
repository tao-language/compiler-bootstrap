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
  | Fun !Type !Type
  | App !Term !Term
  | Let !Env !Term
  | Fix !String !Term
  | Typ !String ![Term]
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
showPrec _ Knd = "%Type"
showPrec _ IntT = "%Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "%Num"
showPrec _ (Num n) = show n
showPrec _ (Var x) = x
showPrec p (Lam x a) = showPrefix p 2 ("\\" ++ x ++ " -> ") a
showPrec p (For x a) = showPrefix p 2 ("@" ++ x ++ ". ") a
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (App a b) = showInfixL p 3 a " " b
showPrec _ (Let env a) = do
  let showDef (x, b) = x ++ " = " ++ show b
  "@let {" ++ intercalate "; " (showDef <$> env) ++ "} " ++ show a
showPrec _ (Fix x a) = "%fix " ++ x ++ " {" ++ show a ++ "}"
showPrec _ (Typ t args) = "#" ++ t ++ " [" ++ intercalate ", " (show <$> args) ++ "]"
showPrec _ (Op op args) = "%op " ++ op ++ " (" ++ intercalate ", " (show <$> args) ++ ")"

instance Show Term where
  show :: Term -> String
  show a = showPrec 0 a

type Type = Term

type Operator = (Term -> Term) -> [Term] -> Maybe Term

type Ops = [(String, Operator)]

type Env = [(String, Term)]

data Symbol
  = Val !Term
  | Ann !Term !Type
  | Ctr !String !String ![(String, Type)] !Type
  | Union ![(String, Type)] ![String]
  deriving (Eq, Show)

type Context = [(String, Symbol)]

data TypeError
  = InfiniteType !String !Term
  | InvalidOp !String !Symbol
  | NotACtr !String !Symbol
  | NotAFunction !Type
  | NotAUnionType !String !Symbol
  | TypeMismatch !Term !Term
  | UndefinedCtr !String
  | UndefinedOp !String
  | UndefinedType !String
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
freeVars (Let env a) = filter (`notElem` map fst env) (freeVars a)
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Typ _ args) = foldr (union . freeVars) [] args
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
  a -> App a (Let env b)
reduce ops env (Let env' a) = reduce ops (env ++ env') a
reduce _ env (Fix x a) = Fix x (Let env a)
reduce _ env (Typ t args) = Typ t (Let env <$> args)
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
  Let _ _ -> error "unreachable"
  Fix x a -> case eval ops [(x, Var x)] a of
    a | x `occurs` a -> Fix x a
    a -> a
  Typ t args -> Typ t (eval ops [] <$> args)
  Op op args -> Op op (eval ops [] <$> args)

symbolToTerm :: Context -> (String, Symbol) -> (String, Term)
symbolToTerm _ (x, Val a) = (x, a)
symbolToTerm _ (x, Ann a _) = (x, a)
symbolToTerm ctx (_, Ctr t k args _) = do
  let xs = fst <$> args
  let alts = case lookup t ctx of
        Just (Union _ alts) -> alts
        _else -> [k]
  (k, lam (xs ++ alts) (app (Var k) (Var <$> xs)))
symbolToTerm _ (x, Union args _) = do
  let xs = fst <$> args
  (x, lam xs (Typ x (Var <$> xs)))

ctxToEnv :: Context -> Env
ctxToEnv ctx = symbolToTerm ctx <$> ctx

apply :: Ops -> Context -> Term -> Term
apply ops ctx = eval ops (ctxToEnv ctx)

unify :: Ops -> Context -> Term -> Term -> Either TypeError (Term, Context)
unify ops ctx a b = case (apply ops ctx a, apply ops ctx b) of
  (Knd, Knd) -> Right (Knd, ctx)
  (IntT, IntT) -> Right (IntT, ctx)
  (Int i, Int i') | i == i' -> Right (Int i, ctx)
  (NumT, NumT) -> Right (NumT, ctx)
  (Num n, Num n') | n == n' -> Right (Num n, ctx)
  (Var x, Var x') | x == x' -> Right (Var x, ctx)
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> Right (b, set x (Val b) ctx)
  (a, Var y) -> unify ops ctx (Var y) a
  (For x a, b) -> do
    (a, ctx) <- unify ops ((x, Val (Var x)) : ctx) a b
    Right (for [x] a, pop x ctx)
  (a, For x b) -> do
    (a, ctx) <- unify ops ((x, Val (Var x)) : ctx) a b
    Right (for [x] a, pop x ctx)
  (Fun a1 b1, Fun a2 b2) -> do
    (a, ctx) <- unify ops ctx a1 a2
    (b, ctx) <- unify ops ctx b1 b2
    Right (Fun (apply ops ctx a) b, ctx)
  (App a1 b1, App a2 b2) -> do
    (a, ctx) <- unify ops ctx a1 a2
    (b, ctx) <- unify ops ctx b1 b2
    Right (App (apply ops ctx a) b, ctx)
  (Typ t args, Typ t' args') | t == t' && length args == length args' -> do
    (args, ctx) <- unifyMany ops ctx args args'
    Right (Typ t args, ctx)
  (Typ t args, b) -> do
    (a, ctx) <- expandType ops ctx t args
    unify ops ctx a b
  (a, Typ t args) -> do
    (b, ctx) <- expandType ops ctx t args
    unify ops ctx a b
  (a, b) -> Left (TypeMismatch a b)

unifyMany :: Ops -> Context -> [Term] -> [Term] -> Either TypeError ([Term], Context)
unifyMany _ ctx [] _ = Right ([], ctx)
unifyMany _ ctx _ [] = Right ([], ctx)
unifyMany ops ctx (a1 : bs1) (a2 : bs2) = do
  (a, ctx) <- unify ops ctx a1 a2
  (bs, ctx) <- unifyMany ops ctx bs1 bs2
  Right (a : bs, ctx)

expandType :: Ops -> Context -> String -> [Term] -> Either TypeError (Term, Context)
expandType ops ctx t args = do
  (typeArgs, alts) <- findType ctx t
  altDefs <- mapM (findAlt ctx) alts
  let altArgs = (snd <$>) . fst <$> altDefs
  let xs = fst <$> typeArgs
  let altTypes = map (\argsT -> fun argsT (Var t)) altArgs
  let body = lam xs (for [t] (fun altTypes (Var t)))
  Right (for xs $ apply ops ctx (app body args), ctx)

findType :: Context -> String -> Either TypeError ([(String, Type)], [String])
findType ctx t = case lookup t ctx of
  Just (Union args alts) -> Right (args, alts)
  Just a -> Left (NotAUnionType t a)
  Nothing -> Left (UndefinedType t)

findAlt :: Context -> String -> Either TypeError ([(String, Type)], Type)
findAlt ctx k = case lookup k ctx of
  Just (Ctr _ _ args retT) -> Right (args, retT)
  Just a -> Left (NotACtr k a)
  Nothing -> Left (UndefinedCtr k)

infer :: Ops -> Context -> Term -> Either TypeError (Type, Context)
infer _ ctx Knd = Right (Knd, ctx)
infer _ ctx IntT = Right (Knd, ctx)
infer _ ctx (Int _) = Right (IntT, ctx)
infer _ ctx NumT = Right (Knd, ctx)
infer _ ctx (Num _) = Right (NumT, ctx)
infer ops ctx (Var x) = case lookup x ctx of
  Just (Val (Var x')) | x == x' -> Right (Knd, ctx)
  Just (Val a) -> infer ops ctx a
  Just (Ann (Var x') b) | x == x' -> Right (apply ops ctx b, ctx)
  Just (Ann a b) -> do
    ctx <- checkType ops ctx a b
    Right (apply ops ctx b, ctx)
  Just (Ctr t _ args retT) -> do
    -- TODO: check `alts`
    (typeArgs, alts) <- findType ctx t
    let altType = for (fst <$> typeArgs) (fun (snd <$> args) retT)
    Right (apply ops ctx altType, ctx)
  Just (Union args alts) -> do
    -- TODO: check `alts`
    Right (fun (snd <$> args) Knd, ctx)
  Nothing -> Left (UndefinedVar x)
infer ops ctx (Lam x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (t2, ctx) <- infer ops ((xT, Val (Var xT)) : (x, Ann (Var x) (Var xT)) : ctx) a
  (t1, ctx) <- infer ops ctx (Var x)
  Right (for [xT] $ Fun t1 t2, pop x ctx)
infer ops ctx (For x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (aT, ctx) <- infer ops ((xT, Val (Var xT)) : (x, Ann (Var x) (Var xT)) : ctx) a
  Right (for [xT] aT, pop x ctx)
infer ops ctx (Fun a b) = do
  ctx <- checkType ops ctx a Knd
  ctx <- checkType ops ctx b Knd
  Right (Knd, ctx)
infer ops ctx (App a b) = do
  let xT = newName "t" (map fst ctx)
  ctx <- Right ((xT, Val (Var xT)) : ctx)
  (ta, ctx) <- infer ops ctx a
  (tb, ctx) <- infer ops ctx b
  (funT, ctx) <- unify ops ctx (Fun tb (Var xT)) ta
  case (forFrom funT, pop xT ctx) of
    ((xs, Fun _ t), ctx) -> Right (for xs t, ctx)
    ((xs, t), _) -> Left (NotAFunction (for xs t))
infer ops ctx (Let env a) = infer ops (ctx ++ map (second Val) env) a
infer ops ctx (Fix x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  (ta, ctx) <- infer ops ((xT, Val (Var xT)) : (x, Ann (Var x) (Var xT)) : ctx) a
  Right (ta, pop x ctx)
infer ops ctx (Typ t args) = do
  -- TODO: check `t`
  (_, ctx) <- inferMany ops ctx args
  Right (Knd, ctx)
infer ops ctx (Op op args) = case lookup op ctx of
  Just (Ann _ b) -> do
    (bT, ctx) <- infer ops ((op, Ann (Var op) b) : ctx) (app (Var op) args)
    Right (bT, pop op ctx)
  Just sym -> Left (InvalidOp op sym)
  Nothing -> Left (UndefinedOp op)

inferMany :: Ops -> Context -> [Term] -> Either TypeError ([Type], Context)
inferMany _ ctx [] = Right ([], ctx)
inferMany ops ctx (a : bs) = do
  (t, ctx) <- infer ops ctx a
  (ts, ctx) <- inferMany ops ctx bs
  Right (t : ts, ctx)

checkType :: Ops -> Context -> Term -> Type -> Either TypeError Context
checkType ops ctx a b = do
  (ta, ctx) <- infer ops ctx a
  (_, ctx) <- unify ops ctx ta b
  Right ctx

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names
