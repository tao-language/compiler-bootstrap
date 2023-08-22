module Core where

import Data.List (delete, union)

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
-- https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- https://www.youtube.com/live/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf
data Expr
  = Err
  | Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Ctr !String
  | Typ !String
  | Var !String
  | Fun !Expr !Expr
  | Lam !String !Expr
  | App !Expr !Expr
  | Iff !Expr !Expr
  | Ann !Expr !Type
  | Or !Expr !Expr
  | Fix !String !Expr
  | Op2 !BinaryOp !Expr !Expr
  | Op1 !UnaryOp !Expr
  deriving (Eq)

instance Show Expr where
  show Err = "@err"
  show Knd = "@Type"
  show IntT = "@Int"
  show NumT = "@Num"
  show (Int i) = show i
  show (Num n) = show n
  show (Ctr k) = "#" ++ k
  show (Typ t) = "%" ++ t
  show (Var x) = x
  show (Fun a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (Lam p b) = "(\\" ++ show p ++ ". " ++ show b ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (Iff a b) = "(@if " ++ show a ++ "; " ++ show b ++ ")"
  show (Ann a ty) = "(" ++ show a ++ " : " ++ show ty ++ ")"
  show (Or a b) = "(" ++ show a ++ " | " ++ show b ++ ")"
  show (Fix x a) = "(@fix " ++ x ++ " " ++ show a ++ ")"
  show (Op2 op a b) = "(" ++ show op ++ " " ++ show a ++ " " ++ show b ++ ")"
  show (Op1 op a) = "(" ++ show op ++ " " ++ show a ++ ")"

data Type
  = For ![String] !Expr
  deriving (Eq)

instance Show Type where
  show (For [] t) = show t
  show (For xs t) = "@for " ++ unwords xs ++ ". " ++ show t

data BinaryOp
  = Add
  | Sub
  | Mul
  | Eq
  | Lt
  deriving (Eq)

instance Show BinaryOp where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Eq = "=="
  show Lt = "<"

data UnaryOp
  = IsInt
  | IsNum
  | IsFun
  | IsApp
  | Int2Num
  deriving (Eq)

instance Show UnaryOp where
  show IsInt = "@isInt"
  show IsNum = "@isNum"
  show IsFun = "@isFun"
  show IsApp = "@isApp"
  show Int2Num = "@int2Num"

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

data TypeError
  = UndefinedVar !String
  | UndefinedCtr !String
  | UndefinedTyp !String
  | InconsistentCtr !String !String
  | InconsistentTyp !String !String
  | InfiniteType !String !Expr
  | MissingType !String
  | NotAFunction !Expr !Expr
  | TypeMismatch !Expr !Expr
  deriving (Eq, Show)

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

lam :: [String] -> Expr -> Expr
lam xs b = foldr Lam b xs

lamAny :: Expr -> Expr
lamAny b = Lam (newName (freeVars b) "_") b

lamIf :: Expr -> Expr -> Expr
lamIf a b = do
  let x = newName (freeVars b) "x"
  lamIfAs (x, a) b

lamIfAs :: (String, Expr) -> Expr -> Expr
lamIfAs (x, a) b = Lam x (Iff a b)

lamEq :: Expr -> Expr -> Expr
lamEq a b = lamEqAs (newName (freeVars b) "x", a) b

lamEqAs :: (String, Expr) -> Expr -> Expr
lamEqAs (x, a) b = Lam x (Iff (eq (Var x) a) b)

lamInt :: String -> Expr -> Expr
lamInt x b = Lam x (Iff (isInt (Var x)) b)

lamNum :: String -> Expr -> Expr
lamNum x b = Lam x (Iff (isNum (Var x)) b)

lamFunAs :: String -> Expr -> Expr
lamFunAs x b = Lam x (Iff (isFun (Var x)) b)

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

eq :: Expr -> Expr -> Expr
eq = Op2 Eq

lt :: Expr -> Expr -> Expr
lt = Op2 Lt

int2Num :: Expr -> Expr
int2Num = Op1 Int2Num

isInt :: Expr -> Expr
isInt = Op1 IsInt

isNum :: Expr -> Expr
isNum = Op1 IsNum

isFun :: Expr -> Expr
isFun = Op1 IsFun

isApp :: Expr -> Expr
isApp = Op1 IsApp

let' :: [(String, Expr)] -> Expr -> Expr
let' [] b = b
let' ((x, a) : defs) b = App (Lam x (let' defs b)) a

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

app :: Expr -> [Expr] -> Expr
app = foldl App

-- Helper functions
pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

pushAll :: [(String, Expr)] -> Env -> Env
pushAll vars env = foldr (:) env vars

popAll :: [String] -> Env -> Env
popAll xs env = foldl (flip pop) env xs

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
freeVars (Ctr _) = []
freeVars (Typ _) = []
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (Lam x a) = delete x (freeVars a)
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Iff a b) = freeVars a `union` freeVars b
freeVars (Ann a _) = freeVars a
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars (Op1 _ a) = freeVars a

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

newName :: [String] -> String -> String
newName existing x = do
  head
    [ name
      | i <- [(0 :: Int) ..],
        let name = if i == 0 then x else x ++ show i,
        name `notElem` existing
    ]

isClosed :: Expr -> Bool
isClosed = null . freeVars

isOpen :: Expr -> Bool
isOpen = not . isClosed

-- Evaluation
eval :: Env -> Expr -> Expr
eval _ Err = Err
eval _ Knd = Knd
eval _ IntT = IntT
eval _ NumT = NumT
eval _ (Int i) = Int i
eval _ (Num n) = Num n
eval _ (Ctr k) = Ctr k
eval _ (Typ t) = Typ t
eval env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Ann (Var x') _) | x == x' -> Var x
  Just a -> eval env a
  Nothing -> Var x
eval env (Fun a b) = case (eval env a, eval env b) of
  (Or a1 a2, b) -> Or (Fun a1 b) (Fun a2 b)
  (a, Or b1 b2) -> Or (Fun a b1) (Fun a b2)
  (a, b) -> Fun a b
eval env (Lam x b) = case eval ((x, Var x) : env) b of
  Or b1 b2 -> Or (Lam x b1) (Lam x b2)
  b -> Lam x b
eval env (App a b) = case (eval env a, eval env b) of
  (Err, _) -> Err
  (Lam x a, b) -> eval [(x, b)] a
  (Or a1 a2, b) -> eval [] (Or (App a1 b) (App a2 b))
  (Fix x a, b) | isClosed b -> eval [(x, Fix x a)] (App a b)
  (a, b) -> App a b
eval env (Iff a b) = case eval env a of
  Err -> Err
  a | isClosed a -> eval env b
  a -> Iff a (eval env b)
eval env (Ann a _) = eval env a
eval env (Or a b) = case (eval env a, eval env b) of
  (a, Err) -> a
  (Err, b) -> b
  (Or a1 a2, b) -> Or a1 (Or a2 b)
  (a, b) -> Or a b
eval env (Fix x a) = Fix x (eval ((x, Var x) : env) a)
eval env (Op2 op a b) = case (eval env a, eval env b) of
  (Or a1 a2, b) -> eval [] (Or (Op2 op a1 b) (Op2 op a2 b))
  (a, Or b1 b2) -> eval [] (Or (Op2 op a b1) (Op2 op a b2))
  (a, b) | isClosed a && isClosed b -> case (op, a, b) of
    (Add, Int a, Int b) -> Int (a + b)
    (Add, Num a, Num b) -> Num (a + b)
    (Sub, Int a, Int b) -> Int (a - b)
    (Sub, Num a, Num b) -> Num (a - b)
    (Mul, Int a, Int b) -> Int (a * b)
    (Mul, Num a, Num b) -> Num (a * b)
    (Eq, Err, Err) -> Knd
    (Eq, IntT, IntT) -> IntT
    (Eq, NumT, NumT) -> NumT
    (Eq, Int a, Int b) | a == b -> Int a
    (Eq, Num a, Num b) | a == b -> Num a
    (Eq, Ctr a, Ctr b) | a == b -> Ctr a
    (Eq, Typ a, Typ b) | a == b -> Typ a
    (Eq, Var a, Var b) | a == b -> Var a
    (Eq, Fun a1 a2, Fun b1 b2) -> eval [] (Iff (eq a1 b1) (eq a2 b2))
    (Eq, App a1 a2, App b1 b2) -> eval [] (Iff (eq a1 b1) (eq a2 b2))
    (Lt, Int a, Int b) | a < b -> Int a
    (Lt, Num a, Num b) | a < b -> Num a
    (Lt, Ctr a, Ctr b) | a < b -> Ctr a
    (Lt, Typ a, Typ b) | a < b -> Typ a
    (Lt, Fun a1 a2, Fun b1 b2) -> eval [] (Iff (lt a1 b1) (lt a2 b2))
    (Lt, App a1 a2, Fun b1 b2) -> eval [] (Iff (lt a1 b1) (lt a2 b2))
    _else -> Err
  (a, b) -> Op2 op a b
eval env (Op1 op a) = case eval env a of
  Or a1 a2 -> eval [] (Or (Op1 op a1) (Op1 op a2))
  a | isClosed a -> case (op, a) of
    (IsInt, Int a) -> Int a
    (IsNum, Num a) -> Num a
    (Int2Num, Int a) -> Num (fromIntegral a)
    _else -> Err
  a -> Op1 op a

-- Type inference
apply :: Substitution -> Env -> Env
apply _ [] = []
apply s ((x, Ann a (For xs t)) : env) = do
  let t' = eval (pushVars xs s) t
  (x, Ann (eval s a) (For xs t')) : apply s env
apply s ((x, a) : env) = (x, eval s a) : apply s env

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = apply s1 s2 `union` s1

instantiate :: [String] -> Type -> (Expr, Substitution)
instantiate _ (For [] a) = (a, [])
instantiate existing (For (x : xs) a) = do
  let y = newName existing x
  let (b, s) = instantiate (y : existing) (For xs a)
  (eval [(x, Var y)] b, [(y, Var y)] `union` s)

unify :: Expr -> Expr -> Either TypeError (Expr, Substitution)
unify Err Err = Right (Err, [])
unify Knd Knd = Right (Knd, [])
unify IntT IntT = Right (IntT, [])
unify (Typ t) (Typ t') | t == t' = Right (Typ t, [])
unify (Var x) (Var x') | x == x' = Right (Var x, [])
unify (Var x) b | x `occurs` b = Left (InfiniteType x b)
unify (Var x) b = Right (b, [(x, b)])
unify a (Var x) = unify (Var x) a
unify (Fun a1 b1) (Fun a2 b2) = do
  ((a, b), s) <- unify2 (a1, a2) (b1, b2)
  Right (Fun a b, s)
unify (App a1 b1) (App a2 b2) = do
  ((a, b), s) <- unify2 (a1, a2) (b1, b2)
  Right (App a b, s)
unify a (Or b1 b2) = case unify a b1 of
  Right (a, s1) -> case unify a (eval s1 b2) of
    Right (a, s2) -> Right (a, s2 `compose` s1)
    Left _ -> Right (a, s1)
  Left _ -> unify a b2
-- Or !Expr !Expr
unify a b = Left (TypeMismatch a b)

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either TypeError ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  (a, s1) <- unify a1 a2
  (b, s2) <- unify (eval s1 b1) (eval s1 b2)
  Right ((a, b), s2 `compose` s1)

infer :: Env -> Expr -> Either TypeError (Expr, Substitution)
infer _ Err = Right (Err, [])
infer _ Knd = Right (Knd, [])
infer _ IntT = Right (Knd, [])
infer _ NumT = Right (Knd, [])
infer _ (Int _) = Right (IntT, [])
infer _ (Num _) = Right (NumT, [])
infer env (Ctr k) = case lookup k env of
  Just (Ann (Ctr k') ty) | k == k' -> do
    let (t, s) = instantiate (map fst env) ty
    Right (eval (s ++ apply s env) t, s)
  Just (Ann (Ctr k') _) -> Left (InconsistentCtr k k')
  Just _ -> Left (MissingType k)
  Nothing -> Left (UndefinedCtr k)
infer env (Typ t) = case lookup t env of
  Just (Ann (Typ t') ty) | t == t' -> do
    let (t, s) = instantiate (map fst env) ty
    Right (eval (s ++ apply s env) t, s)
  Just (Ann (Typ t') _) -> Left (InconsistentTyp t t')
  Just _ -> Left (MissingType t)
  Nothing -> Left (UndefinedTyp t)
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let xT = newName (map fst env) (x ++ "T")
    Right (Var xT, [(xT, Var xT), (x, Ann (Var x) (For [] (Var xT)))])
  Just (Ann (Var x') ty) | x == x' -> do
    let (t, s) = instantiate (map fst env) ty
    Right (eval (s ++ apply s env) t, s)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Fun a b) = do
  (_, s) <- infer2 env a b
  Right (Knd, s)
infer env (Lam x b) = do
  ((t1, t2), s) <- infer2 ((x, Var x) : env) (Var x) b
  Right (Fun t1 t2, s)
infer env (App a b) = do
  ((ta, tb), s1) <- infer2 env a b
  let x = newName (map fst (s1 ++ env)) "t"
  (_, s2) <- unify (Fun tb (Var x)) ta
  let s = s2 `compose` s1
  case eval s (Var x) of
    Var x' | x == x' -> Right (Var x, [(x, Var x)] `compose` s)
    t -> Right (t, s)
infer env (Iff a b) = do
  ((_, t), s) <- infer2 env a b
  Right (t, s)
infer env (Ann a ty) = do
  (ta, s1) <- infer env a
  let (t, s2) = instantiate (map fst (s1 ++ apply s1 env)) ty
  (t, s3) <- unify (eval s2 ta) t
  Right (t, s3 `compose` s2 `compose` s1)
infer env (Or a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case unify ta tb of
    Right (t, s2) -> Right (t, s2 `compose` s1)
    Left _ -> Right (Or ta tb, s1)
infer env (Fix x a) = infer ((x, Var x) : env) a
infer env (Op2 Add a b) = do
  ((ta, tb), s1) <- infer2 env (Ann a (For [] (Or IntT NumT))) b
  (t, s2) <- unify ta tb
  Right (t, s2 `compose` s1)
infer env (Op2 Sub a b) = do
  ((ta, tb), s1) <- infer2 env (Ann a (For [] (Or IntT NumT))) b
  (t, s2) <- unify ta tb
  Right (t, s2 `compose` s1)
infer env (Op2 Mul a b) = do
  ((ta, tb), s1) <- infer2 env (Ann a (For [] (Or IntT NumT))) b
  (t, s2) <- unify ta tb
  Right (t, s2 `compose` s1)
infer env (Op2 Eq a b) = do
  ((ta, tb), s1) <- infer2 env a b
  (t, s2) <- unify ta tb
  Right (t, s2 `compose` s1)
infer env (Op2 Lt a b) = do
  ((ta, tb), s1) <- infer2 env a b
  (t, s2) <- unify ta tb
  Right (t, s2 `compose` s1)
infer env (Op1 IsInt a) = infer env (Ann a (For [] IntT))
infer env (Op1 IsNum a) = infer env (Ann a (For [] NumT))
infer env (Op1 IsFun a) = error "TODO: infer IsFun"
infer env (Op1 IsApp a) = error "TODO: infer IsApp"
infer env (Op1 Int2Num a) = do
  (_, s) <- infer env (Ann a (For [] IntT))
  Right (NumT, s)

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (s1 ++ apply s1 env) b
  Right ((eval s2 ta, tb), s2 `compose` s1)