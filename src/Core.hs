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
  | Fun !(Pattern, Type) !Type
  | App !Expr !Expr
  | Ann !Expr !Type
  | For !String !Type
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
showPrec p (Ann a b) = showInfixL p 2 a " : " b
showPrec p (For x a) = do
  let (xs, a') = asFor a
  "@for " ++ unwords (x : xs) ++ ". " ++ show a'
showPrec p (Fun (q, a) b) = showInfixR p 3 (Ann q a) " -> " b
showPrec p (Op2 Add a b) = showInfixL p 4 a " + " b
showPrec p (Op2 Sub a b) = showInfixL p 4 a " - " b
showPrec p (Op2 Mul a b) = showInfixL p 5 a " * " b
showPrec p (App a b) = showInfixL p 6 a " " b
showPrec p (Call f args) = showPrec p (app (Var ("@call " ++ f)) args)

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

fun :: [(Pattern, Type)] -> Type -> Type
fun args ret = foldr Fun ret args

asFun :: Type -> ([(Pattern, Type)], Type)
asFun (Fun a b) = first (a :) (asFun b)
asFun a = ([], a)

for :: [String] -> Type -> Type
for xs a = foldr For a xs

asFor :: Expr -> ([String], Type)
asFor (For x a) = first (x :) (asFor a)
asFor a = ([], a)

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
freeVars (Fun (p, a) b) = filter (`notElem` freeVars p) (freeVars a `union` freeVars b)
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a b) = freeVars a `union` freeVars b
freeVars (For x a) = delete x (freeVars a)
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
reduce env (Fun (p, a) b) = Fun (p, reduce env a) (reduce env b)
reduce env (App a b) = case (reduce env a, reduce env b) of
  (Err, _) -> Err
  (Lam (Var x) a, b) -> reduce [(x, Let env b)] a
  (Lam (Int i) a, Int i') | i == i' -> reduce [] a
  (Lam (Int _) _, Int _) -> Err
  (Lam (Ctr tx k ps) a, Ctr tx' k' args) | tx == tx' && k == k' -> do
    reduce [] (app (lam ps a) args)
  (Lam Ctr {} _, Ctr {}) -> Err
  (Lam (Or p q) a, b) -> reduce [] (App (Or (Lam p a) (Lam q a)) b)
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
reduce env (Ann a _) = reduce env a
reduce env (For x a) = For x (reduce ((x, Var x) : env) a)
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
  Fun (p, a) b -> Fun (p, reduce env a) (reduce env b)
  App a b -> App a (eval [] b)
  Ann a _ -> a
  For x a | x `occurs` a -> For x (eval [(x, Var x)] a)
  For _ a -> eval [] a
  Or a b -> Or (eval [] a) (eval [] b)
  Let _ _ -> error "unreachable"
  Fix x a | x `occurs` a -> Fix x (eval [(x, Var x)] a)
  Fix _ a -> eval [] a
  Op2 op a b -> Op2 op (eval [] a) (eval [] b)
  Call f args -> Call f (eval [] <$> args)

subtype :: Type -> Type -> Either TypeError (Type, Substitution)
subtype Knd Knd = Right (Knd, [])
subtype IntT IntT = Right (IntT, [])
subtype NumT NumT = Right (NumT, [])
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
subtype (Union alts) (Union alts') | alts == alts' = do
  (altTypes, s) <- subtypeAll (map snd alts) (map snd alts')
  Right (Union (zip (map fst alts) altTypes), s)
subtype (Fun (p1, a1) b1) (Fun (p2, a2) b2) = do
  ((a, b), s) <- subtype2 (a1, a2) (b2, b1)
  Right (Fun (Or p1 p2, a) b, s)
subtype (App a1 b1) (App a2 b2) = do
  ((a, b), s) <- subtype2 (a1, a2) (b1, b2)
  Right (App a b, s)
subtype (Ann _ a) b = subtype a b
subtype a (Ann _ b) = subtype a b
subtype a (Or b1 b2) = case subtype a b1 of
  Right (a, s1) -> case subtype a (eval s1 b2) of
    Right (b, s2) -> Right (Or (eval s2 a) b, s2 `compose` s1)
    Left _ -> Right (a, s1)
  Left _ -> subtype a b2
subtype (Or a1 a2) b = do
  ((a1, a2), s1) <- subtype2 (a1, b) (a2, b)
  case subtype a1 a2 of
    Right (a, s2) -> Right (a, s2 `compose` s1)
    Left _ -> Right (Or a1 a2, s1)
subtype (Call f args) (Call f' args') | f == f' && length args == length args' = do
  (args, s) <- subtypeAll args args'
  Right (Call f args, s)
-- subtype (Int i) (Int i') | i == i' = Right (Int i, [])
-- subtype (Int i) Op2 {} = Right (Int i, [])
-- subtype (Num n) (Num n') | n == n' = Right (Num n, [])
-- subtype (Num n) Op2 {} = Right (Num n, [])
subtype a b = Left (TypeMismatch a b)

subtype2 :: (Type, Type) -> (Type, Type) -> Either TypeError ((Type, Type), Substitution)
subtype2 (a1, a2) (b1, b2) = do
  (a, s1) <- subtype a1 a2
  (b, s2) <- subtype (eval s1 b1) (eval s1 b2)
  Right ((eval s2 a, b), s2 `compose` s1)

subtypeAll :: [Expr] -> [Expr] -> Either TypeError ([Expr], Env)
subtypeAll [] _ = Right ([], [])
subtypeAll _ [] = Right ([], [])
subtypeAll (a1 : bs1) (a2 : bs2) = do
  (a, s1) <- subtype a1 a2
  (bs, s2) <- subtypeAll (eval s1 <$> bs1) (eval s1 <$> bs2)
  Right (eval s2 a : bs, s2 `compose` s1)

apply :: Substitution -> Env -> Env
apply _ [] = []
apply s ((x, Ann a b) : env) = (x, Ann a (eval s b)) : apply s env
apply s (def : env) = def : apply s env

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = map (second (eval s1)) s2 `union` s1

instantiate :: [String] -> Type -> (Type, Env)
instantiate existing (For x t) = do
  let (t', env) = instantiate existing t
  let y = newName x (map fst env)
  (eval [(x, Var y)] t', (y, Var y) : env)
instantiate _ t = (t, [])

-- https://youtu.be/ytPAlhnAKro
infer :: Env -> Expr -> Either TypeError (Type, Substitution)
infer _ Err = Left RuntimeError
infer _ Knd = Right (Knd, [])
infer _ IntT = Right (Knd, [])
infer _ (Int _) = Right (IntT, [])
infer _ NumT = Right (Knd, [])
infer _ (Num _) = Right (NumT, [])
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let xT = newName (x ++ "T") (map fst env)
    Right (Var xT, [(x, Ann (Var x) (Var xT))])
  Just (Ann (Var x') typ) | x == x' -> Right (instantiate (map fst env) typ)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Union alts) = do
  (_, s) <- inferAll env (map snd alts)
  Right (Knd, s)
infer env (Typ tx args) = do
  (kind, s) <- infer env (Var tx)
  case length (fst (asFun kind)) of
    numArgs | numArgs == length args -> do
      inferApply (apply s env) (tx, kind) args
    numArgs -> Left (NumArgsMismatch tx numArgs args)
infer env (Ctr tx k args) = do
  (tdef, s1) <- infer env (Var tx)
  case snd (asFun tdef) of
    Union alts -> case lookup k alts of
      Just altType -> do
        -- let altType' = eval (apply s1 env) altType
        (t, s2) <- inferApply (apply s1 env) (k, altType) args
        Right (t, s2 `compose` s1)
      Nothing -> Left (UndefinedUnionAlt k)
    t -> Left (NotAUnionType tx t)
infer env (Lam p a) = do
  let xs = freeVars p
  let ts = newNames (map (++ "T") xs) (map fst env)
  let env' = zipWith (\x xT -> (x, Ann (Var x) (Var xT))) xs ts ++ env
  ((t1, t2), s) <- infer2 env' p a
  Right (Fun (p, t1) t2, s)
infer env (Fun (p, a) b) = do
  (_, s) <- infer2 env a b
  Right (Knd, s)
infer env (App a b) = do
  ((ta, tb), s1) <- infer2 env a b
  (t, s2) <- inferApplyReturn (apply s1 env) ta (b, tb)
  Right (eval env t, s2 `compose` s1)
infer env (Ann a typ) = do
  (t, defs) <- Right (instantiate (map fst env) typ)
  check (defs ++ env) a t
infer env (For x a) = infer ((x, Var x) : env) a
infer env (Let defs a) = infer (env ++ defs) a
infer env (Fix x a) = infer ((x, Var x) : env) a
infer env (Or a b) = do
  ((ta, tb), s1) <- infer2 env a b
  (t, s2) <- subtype ta tb
  -- (ta, s1) <- infer env a
  -- (t, s2) <- check (apply s1 env) b ta
  Right (t, s2 `compose` s1)
infer env (Call f args) = case lookup f env of
  Just (Ann a typ) -> inferApply env (f, typ) args
  Just a -> Left (MissingType f a)
  Nothing -> Left (UndefinedVar f)
infer env (Op2 op a b) = do
  ((ta, tb), s1) <- infer2 env a b
  (t, s2) <- subtype ta tb
  Right (t, s2 `compose` s1)

check :: Env -> Expr -> Type -> Either TypeError (Type, Substitution)
check env (Typ tx args) t = do
  Right (eval env t, [])
-- check env (Lam p a) t = case t of
--   Fun (q, t1) t2 -> do
--     let xs = freeVars p
--     let env' = pushVars xs env
--     ((t1, t2), s) <- check2 env' (p, t1) (a, t2)
--     Right (Fun (Or q p, t1) t2, s)
--   t -> error ("check Lam: not a Fun: " ++ show t)
check env a t = do
  (ta, s1) <- infer env a
  (t, s2) <- subtype ta (eval env t)
  Right (t, s2 `compose` s1)

check2 :: Env -> (Expr, Type) -> (Expr, Type) -> Either TypeError ((Type, Type), Substitution)
check2 env (a, ta) (b, tb) = do
  (ta, s1) <- check env a ta
  (tb, s2) <- check (apply s1 env) b (eval s1 tb)
  Right ((eval s2 ta, tb), s2 `compose` s1)

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Type, Type), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (apply s1 env) b
  Right ((eval s2 ta, tb), s2 `compose` s1)

inferAll :: Env -> [Expr] -> Either TypeError ([Type], Env)
inferAll _ [] = Right ([], [])
inferAll env (a : bs) = do
  (t, s1) <- infer env a
  (ts, s2) <- inferAll (apply s1 env) bs
  Right (eval s2 t : ts, s2 `compose` s1)

inferApply :: Env -> (String, Type) -> [Expr] -> Either TypeError (Type, Env)
inferApply env (x, t) args = do
  let env' = (x, Ann (Var x) t) : env
  infer env' (app (Var x) args)

inferApplyReturn :: Env -> Type -> (Expr, Type) -> Either TypeError (Type, Substitution)
inferApplyReturn env (Var x) (_, tb) = do
  let y = newName x (map fst env)
  Right (Var y, [(y, Var y), (x, Fun (Var "", tb) (Var y))])
inferApplyReturn env (Fun (p, t1) t2) (b, tb) = do
  (_, s) <- subtype t1 tb
  Right (eval env (App (Lam p (eval s t2)) b), s)
inferApplyReturn env (Or t1 t2) (b, tb) = do
  (t1, s1) <- inferApplyReturn env t1 (b, tb)
  (t2, s2) <- inferApplyReturn (apply s1 env) (eval s1 t2) (b, eval s1 tb)
  (t, s3) <- subtype (eval s2 t1) t2
  Right (t, s3 `compose` s2 `compose` s1)
inferApplyReturn _ t _ = Left (NotAFunction t)

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names

newNames :: [String] -> [String] -> [String]
newNames [] _ = []
newNames (x : xs) existing = do
  let y = newName x existing
  y : newNames xs (y : existing)
