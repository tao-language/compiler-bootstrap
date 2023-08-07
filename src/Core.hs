{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (first, second))
import Data.Char (isLetter)
import Data.Foldable (Foldable (foldl'))
import Data.List (delete, intercalate, union)

{- TODO:
- Add Records
- Clean up code
  * infer Case
- Consistency on variable names:
  * Expr: a, b, c
  * Type: t, t1, t2, ta, tb, tc
  * Var: x, y, z
- Remove unused errors
-}

data Expr
  = Err
  | Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Var !String
  | Union ![(String, Type)]
  | Typ !String ![Expr]
  | Ctr !String !String ![Expr]
  | Lam !Pattern !Expr
  | Fun !Expr !Type
  | App !Expr !Expr
  | Ann !Expr !TypeScheme
  | Or !Expr !Expr
  | Let !Env !Expr
  | Fix !String !Expr
  | Op2 !BinaryOp !Expr !Expr
  | Call !String ![Expr]
  deriving (Eq)

type Type = Expr

type Pattern = Expr

data BinaryOp
  = Add
  | Sub
  | Mul
  deriving (Eq, Show)

instance Show Expr where
  show :: Expr -> String
  show a = showPrec 0 a

showParen' :: Bool -> String -> String
showParen' True a = "(" ++ a ++ ")"
showParen' False a = a

showPrefix :: Int -> Int -> String -> Expr -> String
showPrefix p q op a = showParen' (p > q) (op ++ showPrec q a)

showInfixL :: Int -> Int -> Expr -> String -> Expr -> String
showInfixL p q a op b = showParen' (p > q) (showPrec q a ++ op ++ showPrec (q + 1) b)

showInfixR :: Int -> Int -> Expr -> String -> Expr -> String
showInfixR p q a op b = showParen' (p > q) (showPrec (q + 1) a ++ op ++ showPrec q b)

showPrec :: Int -> Expr -> String
showPrec _ Err = "@error"
showPrec _ Knd = "@Kind"
showPrec _ IntT = "@Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "@Num"
showPrec _ (Num n) = show n
-- TODO: do actual check that it's a valid identifier
showPrec _ (Var "") = "_"
showPrec _ (Var x@('_' : _)) = x
showPrec _ (Var x@(ch : _)) | isLetter ch = x
showPrec _ (Var x) = "${" ++ x ++ "}"
showPrec p (Ctr tx k args) = "#" ++ showPrec p (app (Var (tx ++ "." ++ k)) args)
showPrec p (Typ name args) = "%" ++ showPrec p (app (Var name) args)
showPrec p (Union alts) = do
  let showAlt (k, t) = "#" ++ k ++ " : " ++ show t
  "{" ++ intercalate " | " (map showAlt alts) ++ "}"
showPrec p (Lam q a) = do
  let (ps, a') = asLam (Lam q a)
  showPrefix p 2 ("\\" ++ unwords (map show ps) ++ ". ") a'
showPrec p (Let [] a) = showPrec p a
showPrec p (Let env a) = do
  let showDef (x, b) = x ++ " = " ++ show b
  let defs = "@let {" ++ intercalate "; " (showDef <$> env) ++ "} "
  showPrefix p 2 defs a
showPrec _ (Fix x a) = "@fix " ++ x ++ " (" ++ show a ++ ")"
showPrec p (Or a b) = showInfixR p 1 a " | " b
showPrec p (Ann a (For [] b)) = showInfixL p 2 a " : " b
showPrec p (Ann a (For xs b)) = showInfixL p 2 a (" : $" ++ unwords xs ++ ". ") b
showPrec p (Fun a b) = showInfixR p 3 a " -> " b
showPrec p (Op2 Add a b) = showInfixL p 4 a " + " b
showPrec p (Op2 Sub a b) = showInfixL p 4 a " - " b
showPrec p (Op2 Mul a b) = showInfixL p 5 a " * " b
showPrec p (App a b) = showInfixL p 6 a " " b
showPrec p (Call f args) = showPrec p (app (Var ("@call " ++ f)) args)

data TypeScheme
  = For ![String] !Type
  deriving (Eq)

instance Show TypeScheme where
  show (For [] a) = show a
  show (For xs a) = "@forall " ++ unwords xs ++ ". " ++ show a

type Substitution = [(String, Type)]

type Operator = [Expr] -> Maybe Expr

type Ops = [(String, Operator)]

type Env = [(String, Expr)]

data TypeError
  = CtrNotInType !String ![(String, Type)]
  | EmptyCase
  | InfiniteType !String !Expr
  | MissingType !String !Expr
  | NotAFunction !Type
  | NumArgsMismatch !String !Int ![Expr]
  | TooFewArgs !String !Type ![Expr]
  | NotAUnionAlt !String !Expr
  | NotAUnionType !String !Expr
  | NotAnOp !String !Expr
  | RuntimeError
  | TooManyArgs !Expr ![Expr]
  | TypeMismatch !Expr !Expr
  | UndefinedCtr !String
  | UndefinedOp !String
  | UndefinedType !String
  | UndefinedUnionAlt !String
  | UndefinedUnionType !String
  | UndefinedVar !String
  deriving (Eq, Show)

lam :: [Expr] -> Expr -> Expr
lam ps a = foldr Lam a ps

asLam :: Expr -> ([Expr], Expr)
asLam (Lam p a) = first (p :) (asLam a)
asLam a = ([], a)

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = second (++ [b]) (asApp a)
asApp a = (a, [])

fun :: [Type] -> Type -> Type
fun bs ret = foldr Fun ret bs

asFun :: Expr -> ([Expr], Expr)
asFun (Fun a b) = first (a :) (asFun b)
asFun a = ([], a)

app :: Expr -> [Expr] -> Expr
app = foldl' App

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

let' :: Env -> Expr -> Expr
let' [] a = a
let' env a = Let env a

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

set :: Eq k => k -> v -> [(k, v)] -> [(k, v)]
set _ _ [] = []
set x y ((x', _) : kvs) | x == x' = (x, y) : kvs
set x y (kv : kvs) = kv : set x y kvs

pushAll :: [(String, Expr)] -> Env -> Env
pushAll vars env = foldr (:) env vars

popAll :: [String] -> Env -> Env
popAll xs env = foldl' (flip pop) env xs

pushVars :: [String] -> Env -> Env
pushVars xs = pushAll (map (\x -> (x, Var x)) xs)

freeVars :: Expr -> [String]
freeVars Err = []
freeVars Knd = []
freeVars IntT = []
freeVars NumT = []
freeVars (Int _) = []
freeVars (Num _) = []
freeVars (Var x) = [x]
freeVars (Ctr _ _ args) = foldr (union . freeVars) [] args
freeVars (Typ _ args) = foldr (union . freeVars) [] args
freeVars (Union alts) = foldr (union . freeVars . snd) [] alts
freeVars (Lam p a) = filter (`notElem` freeVars p) (freeVars a)
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a (For xs b)) = freeVars a `union` filter (`notElem` xs) (freeVars b)
freeVars (Let env a) =
  filter (`notElem` map fst env) (foldr (union . freeVars . snd) (freeVars a) env)
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars (Call _ args) = foldr (union . freeVars) [] args

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

isOpen :: Expr -> Bool
isOpen Var {} = True
isOpen App {} = True
isOpen Or {} = True
isOpen Op2 {} = True
isOpen _ = False

isClosed :: Expr -> Bool
isClosed a = not (isOpen a)

reduce :: Env -> Expr -> Expr
reduce _ Err = Err
reduce _ Knd = Knd
reduce _ IntT = IntT
reduce _ NumT = NumT
reduce _ (Int i) = Int i
reduce _ (Num n) = Num n
reduce env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Let env a) -> reduce env a
  Just a -> reduce [] a
  Nothing -> Var x
reduce env (Union alts) = Union (second (reduce env) <$> alts)
reduce env (Typ tx args) = Typ tx (reduce env <$> args)
reduce env (Ctr tx k args) = Ctr tx k (reduce env <$> args)
reduce env (Lam p a) = Lam p (reduce (pushVars (freeVars p) env) a)
reduce env (Fun (Ann p (For xs a)) b) = Fun (Ann p (For xs (reduce env a))) (reduce env b)
reduce env (Fun a b) = Fun (reduce env a) (reduce env b)
reduce env (App a b) = case (reduce env a, reduce env b) of
  (Err, _) -> Err
  (Lam (Var x) a, b) -> reduce [(x, Let env b)] a
  (Lam (Int i) a, Int i') | i == i' -> reduce [] a
  (Lam (Int _) _, Int _) -> Err
  (Lam (Ctr tx k ps) a, Ctr tx' k' args) | tx == tx' && k == k' -> do
    reduce [] (app (lam ps a) args)
  (Lam Ctr {} _, Ctr {}) -> Err
  (Lam p a, b) -> App (Lam p a) b
  (Ann a _, b) -> reduce [] (App a b)
  (Or a1 a2, b) -> case reduce [] (App a1 b) of
    Err -> reduce [] (App a2 b)
    a | isOpen a -> Or a (App a2 b)
    c -> c
  (Fix x a, b) | isOpen b -> App (Fix x a) b
  (Fix x a, b) -> reduce [(x, Fix x a)] (App a b)
  (a, b) -> App a b
reduce env (Fix x a) = Fix x (reduce ((x, Var x) : env) a)
-- reduce env (Ann a (For xs b)) = Ann (reduce env a) (For xs (reduce (pushVars xs env) b))
reduce env (Ann a _) = reduce env a
reduce env (Or a b) = Or (reduce env a) (reduce env b)
reduce env (Let env' a) = reduce (env ++ env') a
reduce env (Op2 op a b) = case (op, reduce env a, reduce env b) of
  (Add, Int a, Int b) -> Int (a + b)
  (Sub, Int a, Int b) -> Int (a - b)
  (Mul, Int a, Int b) -> Int (a * b)
  (op, a, b) -> Op2 op a b
reduce env (Call f args) = Call f (reduce env <$> args)

eval :: Env -> Expr -> Expr
eval env term = case reduce env term of
  Err -> Err
  Knd -> Knd
  IntT -> IntT
  NumT -> NumT
  Int i -> Int i
  Num n -> Num n
  Var x -> Var x
  Union alts -> Union (second (eval []) <$> alts)
  Typ tx args -> Typ tx (eval [] <$> args)
  Ctr tx k args -> Ctr tx k (eval [] <$> args)
  Lam p a -> Lam p (eval (pushVars (freeVars p) []) a)
  Fun (Ann p (For xs a)) b -> Fun (Ann p (For xs (reduce env a))) (reduce env b)
  Fun a b -> Fun (eval [] a) (eval [] b)
  App a b -> App a (eval [] b)
  Ann a _ -> a
  Or a b -> Or (eval [] a) (eval [] b)
  Let _ _ -> error "unreachable"
  Fix x a | x `occurs` a -> Fix x a
  Fix _ a -> a
  Op2 op a b -> Op2 op (eval [] a) (eval [] b)
  Call f args -> Call f (eval [] <$> args)

subtype :: Type -> Type -> Either TypeError (Type, [(String, Expr)])
subtype Knd Knd = Right (Knd, [])
subtype IntT IntT = Right (IntT, [])
subtype NumT NumT = Right (NumT, [])
-- subtype (Int _) IntT = Right (IntT, [])
subtype (Int i) (Int i') | i == i' = Right (Int i, [])
subtype (Num _) NumT = Right (NumT, [])
subtype (Num n) (Num n') | n == n' = Right (Num n, [])
subtype (Var x) (Var x') | x == x' = Right (Var x, [])
subtype a (Var x) | x `occurs` a = Left (InfiniteType x a)
subtype a (Var x) = Right (a, [(x, a)])
subtype (Var x) b = subtype b (Var x)
subtype (Ctr tx k args) (Ctr tx' k' args') | tx == tx' && k == k' && length args == length args' = do
  (argsT, s) <- subtypeAll args args'
  Right (Ctr tx k argsT, s)
subtype (Typ tx args) (Typ tx' args') | tx == tx' && length args == length args' = do
  (args, s) <- subtypeAll args args'
  Right (Typ tx args, s)
subtype (Union alts) (Union alts') | map fst alts == map fst alts' = do
  (altTypes, s) <- subtypeAll (map snd alts) (map snd alts')
  Right (Union (zip (map fst alts) altTypes), s)
subtype (Fun a1 b1) (Fun a2 b2) = do
  (a, s1) <- subtype a1 a2
  (b, s2) <- subtype (apply s1 b2) (apply s1 b1)
  Right (Fun (apply s2 a) b, s2 `compose` s1)
subtype (App a1 b1) (App a2 b2) = do
  (a, s1) <- subtype a1 a2
  (b, s2) <- subtype (apply s1 b1) (apply s1 b2)
  Right (App (apply s2 a) b, s2 `compose` s1)
subtype (Ann _ (For _ a)) b = subtype a b
subtype a (Ann _ (For _ b)) = subtype a b
subtype a (Or b1 b2) = case subtype a b1 of
  Right (a, s1) -> case subtype a (apply s1 b2) of
    Right (b, s2) -> case unify (apply s2 a) b of
      Right (c, s3) -> Right (c, s3 `compose` s2 `compose` s1)
      Left _ -> Right (Or (apply s2 a) b, s2 `compose` s1)
    Left _ -> Right (a, s1)
  Left _ -> subtype a b2
subtype (Or a1 a2) b = do
  (a1, s1) <- subtype a1 b
  (a2, s2) <- subtype (apply s1 a2) (apply s1 b)
  case unify (apply s2 a1) a2 of
    Right (a, s3) -> Right (a, s3 `compose` s2 `compose` s1)
    Left _ -> Right (Or (apply s2 a1) a2, s2 `compose` s1)
subtype (Call f args) (Call f' args') | f == f' && length args == length args' = do
  (args, s) <- subtypeAll args args'
  Right (Call f args, s)
subtype a b = Left (TypeMismatch a b)

subtypeAll :: [Expr] -> [Expr] -> Either TypeError ([Expr], Env)
subtypeAll [] _ = Right ([], [])
subtypeAll _ [] = Right ([], [])
subtypeAll (a1 : bs1) (a2 : bs2) = do
  (a, s1) <- subtype a1 a2
  (bs, s2) <- subtypeAll (apply s1 <$> bs1) (apply s1 <$> bs2)
  Right (apply s2 a : bs, s2 `compose` s1)

apply :: Substitution -> Expr -> Expr
apply s (Ann a (For xs b)) = Ann (apply s a) (For xs (apply (pushVars xs s) b))
apply s a = eval s a

applyEnv :: Substitution -> Env -> Env
applyEnv _ [] = []
applyEnv s ((x, Ann a (For xs b)) : env) = do
  let typ = For xs (apply (foldr pop s xs) b)
  (x, Ann a typ) : applyEnv s env
applyEnv s (def : env) = def : applyEnv s env

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = map (second (apply s1)) s2 `union` s1

unify :: Type -> Type -> Either TypeError (Type, Substitution)
unify a b = case subtype b a of
  Right (c, s) -> Right (c, s)
  Left _ -> subtype a b

-- findUnionType :: Env -> String -> Either TypeError ([(String, Expr)], [(String, Type)])
-- findUnionType env tx = case lookup tx env of
--   -- Just a -> case asLam a of
--   --   (ps, Ann a (For xs b))
--   --   (ps, a) -> error "untyped"
--   Just (Ann a _) -> findUnionType ((tx, a) : env) tx
--   Just a -> case snd (asLam a) of
--     Typ _ args alts -> Right (args, alts)
--     a -> Left (NotAUnionType tx a)
--   Nothing -> Left (UndefinedType tx)

instantiate :: [String] -> TypeScheme -> (Type, Env)
instantiate _ (For [] t) = (t, [])
instantiate existing (For (x : xs) t) = do
  let (t', env) = instantiate existing (For xs t)
  let y = newName x (map fst env)
  (eval [(x, Var y)] t', (y, Var y) : env)

-- https://youtu.be/ytPAlhnAKro
infer :: Env -> Expr -> Either TypeError (Type, Substitution)
infer _ Err = Left RuntimeError
infer _ Knd = Right (Knd, [])
infer _ IntT = Right (Knd, [])
infer _ (Int _) = Right (IntT, [])
infer _ NumT = Right (Knd, [])
infer _ (Num _) = Right (NumT, [])
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Right (Knd, [])
  Just (Ann (Var x') typ) | x == x' -> Right (instantiate (map fst env) typ)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Union alts) = do
  -- (_, s) <- inferAll env (map snd alts)
  -- Right (Knd, s)
  Right (Knd, [])
infer env (Typ tx args) = do
  (kind, s) <- infer env (Var tx)
  case length (fst (asFun kind)) of
    numArgs | numArgs == length args -> do
      inferApply (applyEnv s env) (tx, For [] kind) args
    numArgs -> Left (NumArgsMismatch tx numArgs args)
infer env (Ctr tx k args) = do
  error "TODO: infer Ctr"
infer env (Lam p a) = do
  let xs = freeVars p
  let ts = newNames (map (++ "T") xs) (map fst env)
  let env' = zipWith (\x xT -> (x, Ann (Var x) (For [] (Var xT)))) xs ts ++ env
  ((t1, t2), s1) <- infer2 env' p a
  (t, s2) <- check (applyEnv s1 env') (Lam p a) (Fun t1 t2)
  Right (t, s2 `compose` s1)
infer env (Fun a b) = do
  (_, s) <- infer2 env a b
  Right (Knd, s)
infer env (App a b) = do
  let returnType :: Type -> Type -> Either TypeError (Type, Substitution)
      returnType (Fun (Ann p (For xs t1)) t2) tb = do
        (_, s) <- subtype t1 tb
        Right (eval (pushVars xs env) (App (Lam p (apply s t2)) b), s)
      returnType (Fun t1 t2) tb = do
        (_, s) <- subtype t1 tb
        Right (apply s t2, s)
      returnType (Or t1 t2) tb = do
        (t1, s1) <- returnType t1 tb
        (t2, s2) <- returnType (apply s1 t2) (apply s1 tb)
        (t, s3) <- unify (apply s2 t1) t2
        Right (t, s3 `compose` s2 `compose` s1)
      returnType t _ = Left (NotAFunction t)
  ((ta, tb), s1) <- infer2 env a b
  (t, s2) <- returnType ta tb
  Right (eval env t, s2 `compose` s1)
infer env (Ann a typ) = do
  (t, defs) <- Right (instantiate (map fst env) typ)
  check (defs ++ env) a t
infer env (Let defs a) = infer (env ++ defs) a
infer env (Fix x a) = do
  let x1 = newName (x ++ "T1") (map fst env)
  let x2 = newName (x ++ "T2") (x1 : map fst env)
  let env' = (x, Ann (Var x) (For [x1, x2] (Fun (Var x1) (Var x2)))) : env
  infer env' a
infer env (Or a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case subtype (eval env tb) (eval env ta) of
    Right (t, s2) -> Right (t, s2 `compose` s1)
    Left _ -> case subtype ta tb of
      Right (t, s2) -> Right (t, s2 `compose` s1)
      Left _ -> Right (Or ta tb, s1)
infer env (Call f args) = case lookup f env of
  Just (Ann a typ) -> inferApply env (f, typ) args
  Just a -> Left (MissingType f a)
  Nothing -> Left (UndefinedVar f)
infer env (Op2 op a b) = do
  ((ta, tb), s1) <- infer2 env a b
  (t, s2) <- unify ta tb
  Right (t, s2 `compose` s1)

check :: Env -> Expr -> Type -> Either TypeError (Type, Substitution)
check env (Typ tx args) t = do
  Right (eval env t, [])
check env (Lam p a) t = case t of
  Fun t1 t2 -> do
    (t1, s1) <- check env p t1
    (t2, s2) <- check env a t2
    Right (Fun (Ann p (For [] t1)) t2, s2 `compose` s1)
  t -> error ("check Lam: not a Fun: " ++ show t)
check env a t = do
  (ta, s1) <- infer env a
  (t, s2) <- subtype ta (eval env t)
  Right (t, s2 `compose` s1)

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Type, Type), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (applyEnv s1 env) b
  Right ((apply s2 ta, tb), s2 `compose` s1)

inferAll :: Env -> [Expr] -> Either TypeError ([Type], Env)
inferAll _ [] = Right ([], [])
inferAll env (a : bs) = do
  (t, s1) <- infer env a
  (ts, s2) <- inferAll (applyEnv s1 env) bs
  Right (apply s2 t : ts, s2 `compose` s1)

inferApply :: Env -> (String, TypeScheme) -> [Expr] -> Either TypeError (Type, Env)
inferApply env (x, typ) args = do
  let env' = (x, Ann (Var x) typ) : env
  infer env' (app (Var x) args)

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names

newNames :: [String] -> [String] -> [String]
newNames [] _ = []
newNames (x : xs) existing = do
  let y = newName x existing
  y : newNames xs (y : existing)
