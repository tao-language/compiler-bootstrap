module Core where

import Data.List (delete, union)

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
-- https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- https://www.youtube.com/live/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf
data Expr
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Ctr !String
  | Typ !String
  | Var !String
  | Fun !Expr !Expr
  | Lam !Pattern !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Or !Expr !Expr
  | Fix !String !Expr
  | Op2 !BinaryOp !Expr !Expr
  | Err
  deriving (Eq)

instance Show Expr where
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
  show (Ann a ty) = "(" ++ show a ++ " : " ++ show ty ++ ")"
  show (Or a b) = "(" ++ show a ++ " | " ++ show b ++ ")"
  show (Fix x a) = "(@fix " ++ x ++ " " ++ show a ++ ")"
  show (Op2 op a b) = "(" ++ show op ++ " " ++ show a ++ " " ++ show b ++ ")"
  show Err = "@err"

data Pattern
  = KndP
  | IntTP
  | IntP !Int
  | CtrP !String
  | TypP !String
  | VarP !String
  | FunP !Pattern !Pattern
  | AppP !Pattern !Pattern
  | ErrP
  deriving (Eq)

instance Show Pattern where
  show p = show (patternValue p)

data Type
  = For ![String] !Expr
  deriving (Eq)

instance Show Type where
  show (For [] t) = show t
  show (For xs t) = "@for " ++ unwords xs ++ ". " ++ show t

data BinaryOp
  = AddI
  | SubI
  | MulI
  deriving (Eq)

instance Show BinaryOp where
  show AddI = "@addI"
  show SubI = "@subI"
  show MulI = "@mulI"

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

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

addI :: Expr -> Expr -> Expr
addI = Op2 AddI

subI :: Expr -> Expr -> Expr
subI = Op2 SubI

mulI :: Expr -> Expr -> Expr
mulI = Op2 MulI

let' :: [(Pattern, Expr)] -> Expr -> Expr
let' [] b = b
let' ((p, a) : defs) b = App (Lam p (let' defs b)) a

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

patternValue :: Pattern -> Expr
patternValue KndP = Knd
patternValue IntTP = IntT
patternValue (IntP i) = Int i
patternValue (CtrP k) = Ctr k
patternValue (TypP t) = Typ t
patternValue (VarP x) = Var x
patternValue (FunP p q) = Fun (patternValue p) (patternValue q)
patternValue (AppP p q) = App (patternValue p) (patternValue q)
patternValue ErrP = Err

freeVars :: Expr -> [String]
freeVars Knd = []
freeVars IntT = []
freeVars NumT = []
freeVars (Int _) = []
freeVars (Num _) = []
freeVars (Var x) = [x]
freeVars (Ctr _) = []
freeVars (Typ _) = []
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (Lam p a) = filter (`notElem` freeVars (patternValue p)) (freeVars a)
freeVars (Ann a _) = freeVars a
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars Err = []

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
eval env (Lam p b) = do
  let xs = freeVars (patternValue p)
  case eval (pushVars xs env) b of
    Or b1 b2 -> Or (Lam p b1) (Lam p b2)
    b -> Lam p b
eval env (App a b) = case (eval env a, eval env b) of
  (Lam KndP a, Knd) -> a
  (Lam IntTP a, IntT) -> a
  (Lam (IntP i) a, Int i') | i == i' -> a
  (Lam (VarP x) a, b) -> eval [(x, b)] a
  (Lam (CtrP k) a, Ctr k') | k == k' -> a
  (Lam (TypP t) a, Typ t') | t == t' -> a
  (Lam (AppP p q) a, App b1 b2) -> eval [] (let' [(p, b1), (q, b2)] a)
  (Lam (FunP p q) a, Fun b1 b2) -> eval [] (let' [(p, b1), (q, b2)] a)
  (Lam ErrP a, Err) -> a
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err -> eval [] (App a2 b)
    c -> c
  (a@Ctr {}, b) -> App a b
  (a@Typ {}, b) -> App a b
  (a@Var {}, b) -> App a b
  (a@App {}, b) -> App a b
  (a, b) | isOpen b -> App a b
  (Fix x a, b) -> eval [(x, Fix x a)] (App a b)
  _patternMismatch -> Err
eval env (Ann a _) = eval env a
eval env (Or a b) = case (eval env a, eval env b) of
  (a, Err) -> a
  (Err, b) -> b
  (Or a1 a2, b) -> Or a1 (Or a2 b)
  (a, b) -> Or a b
eval env (Fix x a) = Fix x (eval ((x, Var x) : env) a)
eval env (Op2 op a b) = case (op, eval env a, eval env b) of
  (op, Or a1 a2, b) -> eval [] (Or (Op2 op a1 b) (Op2 op a2 b))
  (op, a, Or b1 b2) -> eval [] (Or (Op2 op a b1) (Op2 op a b2))
  (AddI, Int a, Int b) -> Int (a + b)
  (SubI, Int a, Int b) -> Int (a - b)
  (MulI, Int a, Int b) -> Int (a * b)
  (op, a, b) -> Op2 op a b
eval _ Err = Err

-- Type inference
apply :: Substitution -> Env -> Env
apply _ [] = []
apply s ((x, Ann a (For xs t)) : env) = do
  let t' = eval (pushVars xs s) t
  (x, Ann (eval s a) (For xs t')) : apply s env
apply s ((x, a) : env) = (x, eval s a) : apply s env

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = apply s1 s2 `union` s1

intOps :: [BinaryOp]
intOps = [AddI, SubI, MulI]

instantiate :: [String] -> Type -> (Expr, Substitution)
instantiate _ (For [] a) = (a, [])
instantiate existing (For (x : xs) a) = do
  let y = newName existing x
  let (b, s) = instantiate (y : existing) (For xs a)
  (eval [(x, Var y)] b, [(y, Var y)] `union` s)

unify :: Expr -> Expr -> Either TypeError (Expr, Substitution)
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
-- Or !Expr !Expr
unify Err Err = Right (Err, [])
unify a b = Left (TypeMismatch a b)

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either TypeError ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  (a, s1) <- unify a1 a2
  (b, s2) <- unify (eval s1 b1) (eval s1 b2)
  Right ((a, b), s2 `compose` s1)

infer :: Env -> Expr -> Either TypeError (Expr, Substitution)
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
infer env (Lam p b) = do
  let a = patternValue p
  ((t1, t2), s) <- infer2 (pushVars (freeVars a) env) a b
  Right (Fun t1 t2, s)
infer env (App a b) = do
  ((ta, tb), s1) <- infer2 env a b
  let x = newName (map fst (s1 ++ env)) "t"
  (_, s2) <- unify (Fun tb (Var x)) ta
  let s = s2 `compose` s1
  case eval s (Var x) of
    Var x' | x == x' -> Right (Var x, [(x, Var x)] `compose` s)
    t -> Right (t, s)
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
infer env (Op2 AddI a b) = do
  (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
  Right (IntT, s)
infer env (Op2 SubI a b) = do
  (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
  Right (IntT, s)
infer env (Op2 MulI a b) = do
  (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
  Right (IntT, s)
infer _ Err = Right (Err, [])

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (s1 ++ apply s1 env) b
  Right ((eval s2 ta, tb), s2 `compose` s1)