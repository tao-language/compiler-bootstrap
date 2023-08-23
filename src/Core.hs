module Core where

import Data.List (delete, union)

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
-- https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- https://www.youtube.com/live/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf
data Expr
  = Knd
  | Tup
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
  | And !Expr !Expr
  | Fix !String !Expr
  | Op2 !BinaryOp !Expr !Expr
  | Op1 !UnaryOp !Expr
  | Err !Expr
  deriving (Eq)

data Pattern
  = PVar !String
  | PFun !String !String
  | PApp !String !String
  deriving (Eq)

data Type
  = For ![String] !Expr
  deriving (Eq)

data BinaryOp
  = Add
  | Sub
  | Mul
  | Pow
  | Eq
  | Lt
  deriving (Eq)

data UnaryOp
  = IsInt
  | IsNum
  | Int2Num
  deriving (Eq)

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

instance Show Expr where
  showsPrec p expr = case expr of
    Knd -> atom 11 "@Type"
    Tup -> atom 11 "@Tuple"
    IntT -> atom 11 "@Int"
    NumT -> atom 11 "@Num"
    Int i -> atom 11 (show i)
    Num n -> atom 11 (show n)
    Ctr k -> atom 11 ("#" ++ k)
    Typ t -> atom 11 ("%" ++ t)
    Var x -> atom 11 x
    Op2 Pow a b -> infixR 10 a "^" b
    App a b -> infixL 8 a " " b
    Op1 IsInt a -> prefix 8 "@isInt " a
    Op1 IsNum a -> prefix 8 "@isNum " a
    Op1 Int2Num a -> prefix 8 "@int2Num " a
    Err a -> prefix 8 "@error " a
    Op2 Mul a b -> infixL 7 a " * " b
    Op2 Add a b -> infixL 6 a " + " b
    Op2 Sub a b -> infixL 6 a " - " b
    Fun a b -> infixR 5 a " -> " b
    Op2 Lt a b -> infixR 4 a " < " b
    Op2 Eq a b -> infixL 3 a " == " b
    Ann a (For xs b) -> infixR 2 a (" : " ++ for xs) b
    Lam p b -> do
      let (ps, b') = asLam b
      let args = app (patternExpr p) (map patternExpr ps)
      prefix 2 ("\\" ++ show args ++ ". ") b'
    Fix x a -> prefix 2 ("@fix " ++ x ++ ". ") a
    Or a b -> infixR 1 a " | " b
    And a b -> infixL 1 a "; " b
    where
      atom n k = showParen (p > n) $ showString k
      prefix n k a = showParen (p > n) $ showString k . showsPrec (n + 1) a
      infixL n a op b = showParen (p > n) $ showsPrec n a . showString op . showsPrec (n + 1) b
      infixR n a op b = showParen (p > n) $ showsPrec (n + 1) a . showString op . showsPrec n b
      for [] = ""
      for xs = "@for " ++ unwords xs ++ ". "

instance Show Pattern where
  show = show . patternExpr

instance Show Type where
  show (For [] t) = show t
  show (For xs t) = "@for " ++ unwords xs ++ ". " ++ show t

instance Show BinaryOp where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Pow = "^"
  show Eq = "=="
  show Lt = "<"

instance Show UnaryOp where
  show IsInt = "@isInt"
  show IsNum = "@isNum"
  show Int2Num = "@int2Num"

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

asLam :: Expr -> ([Pattern], Expr)
asLam (Lam p a) = let (ps, b) = asLam a in (p : ps, b)
asLam a = ([], a)

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

pow :: Expr -> Expr -> Expr
pow = Op2 Pow

eq :: Expr -> Expr -> Expr
eq = Op2 Eq

lt :: Expr -> Expr -> Expr
lt = Op2 Lt

isInt :: Expr -> Expr
isInt = Op1 IsInt

isNum :: Expr -> Expr
isNum = Op1 IsNum

int2Num :: Expr -> Expr
int2Num = Op1 Int2Num

let' :: [(Pattern, Expr)] -> Expr -> Expr
let' [] b = b
let' ((p, a) : defs) b = App (Lam p (let' defs b)) a

or' :: [Expr] -> Expr
or' [] = Err Tup
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
freeVars (Err a) = freeVars a
freeVars Knd = []
freeVars Tup = []
freeVars IntT = []
freeVars NumT = []
freeVars (Int _) = []
freeVars (Num _) = []
freeVars (Var x) = [x]
freeVars (Ctr _) = []
freeVars (Typ _) = []
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (Lam p a) = do
  let xs = freeVars (patternExpr p)
  filter (`notElem` xs) (freeVars a)
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a _) = freeVars a
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (And a b) = freeVars a `union` freeVars b
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars (Op1 _ a) = freeVars a

patternExpr :: Pattern -> Expr
patternExpr (PVar x) = Var x
patternExpr (PFun x y) = Fun (Var x) (Var y)
patternExpr (PApp x y) = App (Var x) (Var y)

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
eval _ (Err a) = Err a
eval _ Knd = Knd
eval _ IntT = IntT
eval _ NumT = NumT
eval _ Tup = Tup
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
eval env (Lam p b) = case eval (pushVars (freeVars (patternExpr p)) env) b of
  Or b1 b2 -> Or (Lam p b1) (Lam p b2)
  b -> Lam p b
eval env (App a b) = case (eval env a, eval env b) of
  (Err a, _) -> Err a
  (a@Ctr {}, b) -> App a b
  (a@Typ {}, b) -> App a b
  (a@Var {}, b) -> App a b
  (a@App {}, b) -> App a b
  (a, b) | isOpen b -> App a b
  (Lam (PVar x) a, b) -> eval [(x, b)] a
  (Lam (PFun x y) a, Fun b1 b2) -> eval [] (let' [(PVar x, b1), (PVar y, b2)] a)
  (Lam (PApp x y) a, App b1 b2) -> eval [] (let' [(PVar x, b1), (PVar y, b2)] a)
  (Or a1 a2, b) -> eval [] (Or (App a1 b) (App a2 b))
  (Fix x a, b) -> eval [(x, Fix x a)] (App a b)
  (a, b) -> Err (App a b)
eval env (Ann a _) = eval env a
eval env (Or a b) = case (eval env a, eval env b) of
  (Err _, b) -> b
  (a, Err _) -> a
  (Or a1 a2, b) -> Or a1 (Or a2 b)
  (a, b) -> Or a b
eval env (And a b) = case eval env a of
  Err a -> Err a
  a | isClosed a -> eval env b
  a -> And a (eval env b)
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
    (Pow, Int a, Int b) -> Int (a ^ b)
    (Pow, Num a, Num b) -> Num (a ** b)
    (Eq, Err _, Err _) -> Tup
    (Eq, Knd, Knd) -> Knd
    (Eq, Tup, Tup) -> Tup
    (Eq, IntT, IntT) -> IntT
    (Eq, NumT, NumT) -> NumT
    (Eq, Int a, Int b) | a == b -> Int a
    (Eq, Num a, Num b) | a == b -> Num a
    (Eq, Ctr a, Ctr b) | a == b -> Ctr a
    (Eq, Typ a, Typ b) | a == b -> Typ a
    (Eq, Var a, Var b) | a == b -> Var a
    (Eq, Fun a1 a2, Fun b1 b2) -> And (eq a1 b1) (eq a2 b2)
    (Eq, App a1 a2, App b1 b2) -> And (eq a1 b1) (eq a2 b2)
    (Lt, Int a, Int b) | a < b -> Int a
    (Lt, Num a, Num b) | a < b -> Num a
    (Lt, Ctr a, Ctr b) | a < b -> Ctr a
    (Lt, Typ a, Typ b) | a < b -> Typ a
    (op, a, b) -> Err (Op2 op a b)
  (a, b) -> Op2 op a b
eval env (Op1 op a) = case eval env a of
  Or a1 a2 -> eval [] (Or (Op1 op a1) (Op1 op a2))
  a | isClosed a -> case (op, a) of
    (IsInt, Int a) -> Int a
    (IsNum, Num a) -> Num a
    (Int2Num, Int a) -> Num (fromIntegral a)
    (op, a) -> Err (Op1 op a)
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
unify (Err a) (Err b) = do
  (a, s) <- unify a b
  Right (Err a, s)
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
infer _ (Err a) = Right (Err a, [])
infer _ Knd = Right (Knd, [])
infer _ Tup = error "TODO: infer Tup"
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
  let a = patternExpr p
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
infer env (And a b) = do
  ((_, tb), s) <- infer2 env a b
  Right (tb, s)
infer env (Fix x a) = infer ((x, Var x) : env) a
infer env (Op2 op a b) = case op of
  Add -> do
    ((ta, tb), s1) <- infer2 env (Ann a (For [] (Or IntT NumT))) b
    (t, s2) <- unify ta tb
    Right (t, s2 `compose` s1)
  Sub -> do
    ((ta, tb), s1) <- infer2 env (Ann a (For [] (Or IntT NumT))) b
    (t, s2) <- unify ta tb
    Right (t, s2 `compose` s1)
  Mul -> do
    ((ta, tb), s1) <- infer2 env (Ann a (For [] (Or IntT NumT))) b
    (t, s2) <- unify ta tb
    Right (t, s2 `compose` s1)
  Pow -> do
    ((ta, tb), s1) <- infer2 env (Ann a (For [] (Or IntT NumT))) b
    (t, s2) <- unify ta tb
    Right (t, s2 `compose` s1)
  Eq -> do
    ((ta, tb), s1) <- infer2 env a b
    (t, s2) <- unify ta tb
    Right (t, s2 `compose` s1)
  Lt -> do
    ((ta, tb), s1) <- infer2 env a b
    (t, s2) <- unify ta tb
    Right (t, s2 `compose` s1)
infer env (Op1 op a) = case op of
  IsInt -> infer env (Ann a (For [] IntT))
  IsNum -> infer env (Ann a (For [] NumT))
  Int2Num -> do
    (_, s) <- infer env (Ann a (For [] IntT))
    Right (NumT, s)

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (s1 ++ apply s1 env) b
  Right ((eval s2 ta, tb), s2 `compose` s1)