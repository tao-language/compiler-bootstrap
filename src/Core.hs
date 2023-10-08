module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Char (isAlphaNum, isLower, isUpper, toLower)
import Data.List (delete, intercalate, union)
import Debug.Trace

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
  | Tag !String
  | Var !String
  | Ann !Expr !Type
  | Lam !String !Expr
  | Fix !String !Expr
  | Fun !Expr !Expr
  | Or !Expr !Expr
  | If !Expr !Expr
  | App !Expr !Expr
  | Fst !Expr
  | Snd !Expr
  | Rec ![(String, Expr)]
  | Typ !String ![Expr] ![(String, Type)]
  | Op1 !UnaryOp !Expr
  | Op2 !BinaryOp !Expr !Expr
  | Err ![Error]
  deriving (Eq)

data Type
  = For ![String] !Expr
  deriving (Eq)

data BinaryOp
  = AddI
  | AddN
  | Sub
  | Mul
  | Pow
  | Eq
  | Lt
  deriving (Eq)

data UnaryOp
  = Int2Num
  deriving (Eq)

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

data Error
  = UndefinedVar !String
  | InfiniteType !String !Expr
  | NotAFunction !Expr !Expr
  | TypeMismatch !Expr !Expr
  | Op1Error !UnaryOp !Expr
  | Op2Error !BinaryOp !Expr !Expr
  deriving (Eq, Show)

instance Show Expr where
  showsPrec p expr = case expr of
    Or a b -> infixR 1 a " | " b
    If a b -> infixR 1 a " ? " b
    Ann a (For xs b) -> infixR 2 a (" : " ++ for xs) b
    Lam x b -> do
      let (xs, b') = asLam (Lam x b)
      prefix 2 ("\\" ++ unwords xs ++ ". ") b'
    Fix x a -> prefix 2 ("@fix " ++ x ++ ". ") a
    Op2 Eq a b -> infixL 3 a (op2 Eq) b
    Op2 Lt a b -> infixR 4 a (op2 Lt) b
    Fun a b -> infixR 5 a " -> " b
    Op2 AddI a b -> infixL 6 a (op2 AddI) b
    Op2 AddN a b -> infixL 6 a (op2 AddN) b
    Op2 Sub a b -> infixL 6 a (op2 Sub) b
    Op2 Mul a b -> infixL 7 a (op2 Mul) b
    Fst a -> prefix 8 "@fst " a
    Snd a -> prefix 8 "@snd " a
    Err stack -> prefix 8 "@error " stack
    Op1 Int2Num a -> prefix 8 (op1 Int2Num) a
    Op2 Pow a b -> infixR 10 a (show Pow) b
    App a b -> infixL 8 a " " b
    Knd -> atom 11 "@Type"
    IntT -> atom 11 "@Int"
    NumT -> atom 11 "@Num"
    Int i -> atom 11 (show i)
    Num n -> atom 11 (show n)
    Tag k | isTagName k -> atom 11 k
    Tag k -> atom 11 ("(@tag '" ++ k ++ "')")
    Var x | isVarName x -> atom 11 x
    Var x -> atom 11 ("(@var '" ++ x ++ "')")
    Rec kvs -> do
      let showField (x, a) = x ++ ": " ++ show a
      atom 11 ("{" ++ intercalate ", " (map showField kvs) ++ "}")
    Typ k args alts -> do
      let showAlt (k, ty) = show (Ann (Tag k) ty)
      atom 11 ("(@type " ++ show (app (Tag k) args) ++ " = {" ++ intercalate " | " (map showAlt alts) ++ "})")
    where
      atom n k = showParen (p > n) $ showString k
      prefix n k a = showParen (p > n) $ showString k . showsPrec (n + 1) a
      infixL n a op b = showParen (p > n) $ showsPrec n a . showString op . showsPrec (n + 1) b
      infixR n a op b = showParen (p > n) $ showsPrec (n + 1) a . showString op . showsPrec n b
      for [] = ""
      for xs = "@for " ++ unwords xs ++ ". "
      isVarName ('$' : xs) = all isAlphaNum xs
      isVarName (x : xs) = isLower x && all isAlphaNum xs
      isVarName [] = False
      isTagName (x : xs) = isUpper x && all isAlphaNum xs
      isTagName [] = False
      op2 op = " " ++ show op ++ " "
      op1 op = show op ++ " "

instance Show Type where
  show (For [] t) = show t
  show (For xs t) = "@for " ++ unwords xs ++ ". " ++ show t

instance Show BinaryOp where
  show AddI = "+"
  show AddN = "+"
  show Sub = "-"
  show Mul = "*"
  show Pow = "^"
  show Eq = "=="
  show Lt = "<"

instance Show UnaryOp where
  show Int2Num = "@int2num"

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

asFun :: Expr -> ([Expr], Expr)
asFun (Fun a1 a2) = let (bs, b) = asFun a2 in (a1 : bs, b)
asFun a = ([], a)

lam :: [String] -> Expr -> Expr
lam xs b = foldr Lam b xs

asLam :: Expr -> ([String], Expr)
asLam (Lam x a) = let (xs, b) = asLam a in (x : xs, b)
asLam a = ([], a)

addI :: Expr -> Expr -> Expr
addI = Op2 AddI

addN :: Expr -> Expr -> Expr
addN = Op2 AddN

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

gt :: Expr -> Expr -> Expr
gt a b = Op2 Lt b a

int2num :: Expr -> Expr
int2num = Op1 Int2Num

ann :: Expr -> Expr -> Expr
ann a t = Ann a (For [] t)

let' :: [(String, Expr)] -> Expr -> Expr
let' [] b = b
let' ((x, a) : defs) b = App (Lam x (let' defs b)) a

or' :: [Expr] -> Expr
or' [] = Err []
or' [a] = a
or' (a : bs) = Or a (or' bs)

app :: Expr -> [Expr] -> Expr
app = foldl App

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = let (a', bs) = asApp a in (a', bs ++ [b])
asApp a = (a, [])

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
freeVars Knd = []
freeVars IntT = []
freeVars NumT = []
freeVars (Int _) = []
freeVars (Num _) = []
freeVars (Tag _) = []
freeVars (Var x) = [x]
freeVars (Ann a _) = freeVars a
freeVars (Lam x a) = delete x (freeVars a)
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (If a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Fst a) = freeVars a
freeVars (Snd a) = freeVars a
freeVars (Rec []) = []
freeVars (Rec ((_, a) : kvs)) = freeVars a `union` freeVars (Rec kvs)
freeVars (Typ _ [] _) = []
freeVars (Typ k (a : bs) _) = freeVars a `union` freeVars (Typ k bs [])
freeVars (Op1 _ a) = freeVars a
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars (Err _) = []

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

newName :: [String] -> String -> String
newName existing x = head (newNames existing x)

newNames :: [String] -> String -> [String]
newNames existing x =
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
eval env (Tag k) = case lookup k env of
  Just (Tag k') | k == k' -> Tag k
  Just (Ann (Tag k) ty) -> Ann (Tag k) ty
  Just a -> eval env a
  Nothing -> Tag k
eval env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Tag k) -> Tag k
  Just (Ann (Var x') _) | x == x' -> Var x
  Just a -> eval env a
  Nothing -> Var x
eval env (Lam x b) = Lam x (eval ((x, Var x) : env) b)
eval env (Fix x a) = Fix x (eval ((x, Var x) : env) a)
eval env (Fun a b) = Fun (eval env a) (eval env b)
eval env (App a b) = case (eval env a, eval env b) of
  (Err stack, _) -> Err stack
  (_, Err stack) -> Err stack
  (Lam x a, b) -> eval [(x, b)] a
  (Ann a (For xs (Fun t1 t2)), b) -> case infer env (ann b t1) of
    Right (_, s) -> annotated (eval s (App a b)) (For (filter (`notElem` map fst s) xs) (eval s t2))
    Left err -> Err [err]
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err _ -> eval [] (App a2 b)
    Lam x a -> Or (Lam x a) (App a2 b)
    Ann a ty -> Or (Ann a ty) (App a2 b)
    a | isOpen a -> Or a (App a2 b)
    a -> a
  (Fix x a, b) | isClosed b -> eval [(x, Fix x a)] (App a b)
  (a, b) -> App a b
eval env (Ann a (For xs t)) = case infer env (Ann a (For xs t)) of
  Right (_, s) -> annotated (eval (s ++ env) a) (For (filter (`notElem` map fst s) xs) (eval (s ++ env) t))
  Left err -> Err [err]
eval env (Or a b) = case (eval env a, eval env b) of
  (Err stack1, Err stack2) -> Err (stack1 ++ stack2)
  (Err _, b) -> b
  (a, Err _) -> a
  (Or a1 a2, b) -> Or a1 (Or a2 b)
  (a, b) -> Or a b
eval env (If a b) = case eval env a of
  Err stack -> Err stack
  a | isClosed a -> eval env b
  a -> If a (eval env b)
eval env (Fst a) = case eval env a of
  App a b | isClosed b -> a
  a -> Fst a
eval env (Snd a) = case eval env a of
  App a b | isClosed b -> b
  a -> Fst a
eval env (Rec kvs) = Rec (map (second (eval env)) kvs)
eval env (Typ k args alts) = do
  let evalAlt (For xs t) = For xs (eval ((k, Tag k) : pushVars xs env) t)
  Typ k (map (eval env) args) (second evalAlt <$> alts)
eval env (Op1 op a) = case (op, eval env a) of
  (op, a) | isOpen a -> Op1 op a
  (op, a) -> evalOp1 op a
eval env (Op2 op a b) = case (op, eval env a, eval env b) of
  (op, a, b) | isOpen a || isOpen b -> Op2 op a b
  (op, a, b) -> evalOp2 op a b
eval _ (Err stack) = Err stack

evalOp1 :: UnaryOp -> Expr -> Expr
evalOp1 Int2Num (Int b) = Num (fromIntegral b)
evalOp1 op a = Err [Op1Error op a]

evalOp2 :: BinaryOp -> Expr -> Expr -> Expr
evalOp2 AddI (Int a) (Int b) = Int (a + b)
evalOp2 AddN (Num a) (Num b) = Num (a + b)
evalOp2 Sub (Int a) (Int b) = Int (a - b)
evalOp2 Sub (Num a) (Num b) = Num (a - b)
evalOp2 Mul (Int a) (Int b) = Int (a * b)
evalOp2 Mul (Num a) (Num b) = Num (a * b)
evalOp2 Pow (Int a) (Int b) = Int (a ^ b)
evalOp2 Pow (Num a) (Num b) = Num (a ** b)
evalOp2 Eq Knd Knd = Knd
evalOp2 Eq IntT IntT = IntT
evalOp2 Eq NumT NumT = NumT
evalOp2 Eq (Int a) (Int b) | a == b = Int a
evalOp2 Eq (Num a) (Num b) | a == b = Num a
evalOp2 Eq (Var a) (Var b) | a == b = Var a
evalOp2 Eq (App a1 a2) (App b1 b2) = If (eq a1 b1) (eq a2 b2)
evalOp2 Lt (Int a) (Int b) | a < b = Int a
evalOp2 Lt (Num a) (Num b) | a < b = Num a
evalOp2 op a b = Err [Op2Error op a b]

annotated :: Expr -> Type -> Expr
annotated (Tag k) (For _ (Tag k')) | k == k' = Tag k
annotated a@Tag {} ty = Ann a ty
annotated a@Var {} ty = Ann a ty
annotated a@Lam {} ty = Ann a ty
annotated a@App {} ty = Ann a ty
annotated a _ = a

unify :: Expr -> Expr -> Either Error (Expr, Substitution)
unify Knd Knd = Right (Knd, [])
unify IntT IntT = Right (IntT, [])
unify NumT NumT = Right (NumT, [])
unify (Int i) (Int i') | i == i' = Right (Int i, [])
unify (Num n) (Num n') | n == n' = Right (Num n, [])
unify (Tag k) (Tag k') | k == k' = Right (Tag k, [])
unify (Var x) (Var x') | x == x' = Right (Var x, [])
unify (Var x) b | x `occurs` b = Left (InfiniteType x b)
unify (Var x) b = Right (b, [(x, b)])
unify a (Var x) = unify (Var x) a
-- Ann !Expr !Type
-- Lam !String !Expr
-- Fix !String !Expr
unify (Fun a1 b1) (Fun a2 b2) = do
  ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
  Right (Fun ta tb, s)
unify a (Or b1 b2) = case unify a b1 of
  Right (a, s1) -> case unify a b2 of
    Right (a, s2) -> Right (a, s2 `compose` s1)
    Left _ -> Right (a, s1)
  Left _ -> unify a b2
unify (Or a1 a2) b = case unify a1 b of
  Right (b, s1) -> case unify a2 b of
    Right (b, s2) -> Right (b, s2 `compose` s1)
    Left _ -> Right (b, s1)
  Left _ -> unify a2 b
-- If !Expr !Expr
unify (App a1 b1) (App a2 b2) = do
  ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
  Right (App ta tb, s)
-- Fst !Expr
-- Snd !Expr
-- Op1 !UnaryOp !Expr
-- Op2 !BinaryOp !Expr !Expr
-- Rec ![(String, Expr)]
-- Ann !Expr !Type
unify a (Typ k args _) = unify a (app (Tag k) args)
unify (Typ k args _) b = unify (app (Tag k) args) b
-- unify (Tag _) b = Right (b, [])
-- unify a (Tag _) = Right (a, [])
unify a b = Left (TypeMismatch a b)

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either Error ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  (ta, s1) <- unify a1 a2
  (tb, s2) <- unify (eval s1 b1) (eval s1 b2)
  Right ((eval s2 ta, tb), s2 `compose` s1)

unifyAll :: [Expr] -> [Expr] -> Either Error ([Expr], Substitution)
unifyAll [] _ = Right ([], [])
unifyAll _ [] = Right ([], [])
unifyAll (a1 : bs1) (a2 : bs2) = do
  (bs, s1) <- unifyAll bs1 bs2
  (a, s2) <- unify (eval s1 a1) (eval s1 a2)
  Right (a : map (eval s2) bs, s2 `compose` s1)

unifyRec :: [(String, Expr)] -> [(String, Expr)] -> Either Error ([(String, Expr)], Substitution)
unifyRec [] _ = Right ([], [])
unifyRec ((x, a) : kvs) kvs' = case lookup x kvs' of
  Just b -> do
    (kvs, s1) <- unifyRec kvs kvs'
    (t, s2) <- unify (eval s1 a) (eval s1 b)
    Right ((x, t) : kvs, s2 `compose` s1)
  Nothing -> unifyRec kvs kvs'

print' :: (Show a, Show b, Show c, Applicative f) => a -> b -> c -> f ()
print' msg x y = traceM (show msg ++ "\t  " ++ show x ++ "  ~~>  " ++ show y)

infer :: Env -> Expr -> Either Error (Expr, Substitution)
infer _ Knd = Right (Knd, [])
infer _ IntT = Right (Knd, [])
infer _ NumT = Right (Knd, [])
infer _ (Int _) = Right (IntT, [])
infer _ (Num _) = Right (NumT, [])
infer env (Tag k) = case lookup k env of
  Just (Tag k') | k == k' -> Right (Tag k, [])
  Just (Ann (Tag k') ty) | k == k' -> Right (instantiate (map fst env) ty)
  Just a -> infer env a
  Nothing -> Right (Tag k, [])
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let y = newName (map fst env) (x ++ "T")
    Right (Var y, [(y, Var y), (x, Ann (Var x) (For [] (Var y)))])
  Just (Ann (Var x') ty) | x == x' -> Right (instantiate (map fst env) ty)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Ann a ty) = do
  let (t, vars) = instantiate (map fst env) ty
  let (t', alts) = case eval env t of
        Typ k args alts -> (Typ k args alts, map (\(k, ty) -> (k, Ann (Tag k) ty)) alts)
        t' -> (t', [])
  (ta, s1) <- infer (vars ++ alts ++ env) a
  (t', s2) <- unify ta t'
  Right (t', s2 `compose` s1)
infer env (Lam x b) = do
  ((t1, t2), s) <- infer2 ((x, Var x) : env) (Var x) b
  Right (Fun t1 t2, s)
infer env (Fix x a) = infer ((x, Var x) : env) a
infer env (Fun a b) = do
  ((ta, tb), s) <- infer2 env a b
  Right (Fun ta tb, s)
infer env (Or a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case unify ta tb of
    Right (t, s2) -> Right (t, s2 `compose` s1)
    Left _ -> Right (Or ta tb, s1)
infer env (If a b) = do
  ((_, tb), s) <- infer2 env a b
  Right (tb, s)
infer env (App a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case ta of
    Var x -> do
      let y = newName (map fst (s1 ++ env)) "t"
      (_, s2) <- unify (Fun tb (Var y)) (Var x)
      Right (Var y, [(y, Var y)] `compose` s2 `compose` s1)
    Tag _ -> Right (App ta tb, s1)
    Fun t1 t2 -> do
      (_, s2) <- unify tb t1
      Right (eval s2 t2, s2 `compose` s1)
    App _ _ -> Right (App ta tb, s1)
    ta -> Left (NotAFunction a ta)
infer env (Fst a) = error "TODO: infer Fst"
infer env (Snd a) = error "TODO: infer Snd"
infer env (Rec kvs) = do
  (kvsT, s) <- inferRec env kvs
  Right (Rec kvsT, s)
infer env (Typ _ args alts) = do
  (_, s1) <- inferAll env args
  (_, s2) <- inferAll (apply s1 env) (map (\(k, For xs t) -> Ann (Tag k) (For xs (eval (pushVars xs s1) t))) alts)
  Right (Knd, s2 `compose` s1)
infer env (Op1 op a) = inferOp1 env op a
infer env (Op2 op a b) = inferOp2 env op a b
infer _ (Err stack) = Right (Err stack, [])

infer2 :: Env -> Expr -> Expr -> Either Error ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (s1 ++ apply s1 env) b
  Right ((eval s2 ta, tb), s2 `compose` s1)

inferAll :: Env -> [Expr] -> Either Error ([Expr], Substitution)
inferAll _ [] = Right ([], [])
inferAll env (a : bs) = do
  (ta, s1) <- infer env a
  (tbs, s2) <- inferAll (apply s1 env) bs
  Right (eval s2 ta : tbs, s2 `compose` s1)

inferRec :: Env -> [(String, Expr)] -> Either Error ([(String, Expr)], Substitution)
inferRec _ [] = Right ([], [])
inferRec env ((x, a) : kvs) = do
  (kvsT, s1) <- inferRec env kvs
  (ta, s2) <- infer (apply s1 env) a
  Right ((x, ta) : kvsT, s2 `compose` s1)

inferOp1 :: Env -> UnaryOp -> Expr -> Either Error (Expr, Substitution)
inferOp1 env Int2Num a = do
  (_, s) <- infer env (ann a IntT)
  Right (NumT, s)

inferOp2 :: Env -> BinaryOp -> Expr -> Expr -> Either Error (Expr, Substitution)
inferOp2 env AddI a b = do
  (_, s) <- infer2 env (ann a IntT) (ann b IntT)
  Right (IntT, s)
inferOp2 env AddN a b = do
  (_, s) <- infer2 env (ann a NumT) (ann b NumT)
  Right (NumT, s)
inferOp2 env Sub a b = do
  (_, s) <- infer2 env (ann a IntT) (ann b IntT)
  Right (IntT, s)
inferOp2 env Mul a b = do
  (_, s) <- infer2 env (ann a IntT) (ann b IntT)
  Right (IntT, s)
inferOp2 env Pow a b = do
  (_, s) <- infer2 env (ann a IntT) (ann b IntT)
  Right (IntT, s)
inferOp2 env Eq a b = do
  (ta, s1) <- infer env a
  (t, s2) <- infer (apply s1 env) (ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Lt a b = do
  (ta, s1) <- infer env a
  (t, s2) <- infer (apply s1 env) (ann b ta)
  Right (t, s2 `compose` s1)

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
  let (b, s) = instantiate (y : x : existing) (For xs a)
  (eval [(x, Var y)] b, [(y, Var y)] `union` s)

-- unify :: Expr -> Expr -> Either Error (Expr, Substitution)
-- unify Knd Knd = Right (Knd, [])
-- unify IntT IntT = Right (IntT, [])
-- unify NumT NumT = Right (NumT, [])
-- unify (Int i) (Int i') | i == i' = Right (Int i, [])
-- unify (Tag k) (Tag k') | k == k' = Right (Tag k, [])
-- unify (Tag k) (Ann (Tag k') (For [] b)) | k == k' = Right (b, [])
-- unify (Fun a1 b1) (Fun a2 b2) = do
--   ((a, b), s) <- unify2 (a1, a2) (b1, b2)
--   Right (Fun a b, s)
-- unify (Ann (Tag k) (For [] a)) (Tag k') | k == k' = Right (a, [])
-- unify (App a1 a2) (Ann (Tag k) (For [] (Fun b1 b2))) = do
--   (_, s1) <- unify a2 b1
--   (c, s2) <- unify (eval s1 a1) (Ann (Tag k) (For [] (eval s1 b2)))
--   Right (c, s2 `compose` s1)
-- unify a@(Ann (Tag _) _) b@(App _ _) = unify b a
-- unify a (Ann (Tag k) ty@(For (_ : _) _)) = do
--   let (b, vars) = instantiate (freeVars a) ty
--   (c, s) <- unify a (Ann (Tag k) (For [] b))
--   Right (c, s `compose` vars)
-- unify (Ann (Tag k) ty@(For (_ : _) _)) b = unify b (Ann (Tag k) ty)
-- unify (Rec kvs) (Rec kvs') = do
--   (kvs, s) <- unifyRec kvs kvs'
--   Right (Rec kvs, s)
-- unify (Var x) (Var x') | x == x' = Right (Var x, [])
-- unify (Var x) b | x `occurs` b = Left (InfiniteType x b)
-- unify (Var x) b = Right (b, [(x, b)])
-- unify a (Var x) = unify (Var x) a
-- unify (App a1 b1) (App a2 b2) = do
--   ((a, b), s) <- unify2 (a1, a2) (b1, b2)
--   Right (App a b, s)
-- unify a (Or b1 b2) = case unify a b1 of
--   Right (a, s1) -> case unify a (eval s1 b2) of
--     Right (a, s2) -> Right (a, s2 `compose` s1)
--     Left _ -> Right (a, s1)
--   Left _ -> case unify a b2 of
--     Left (TypeMismatch a b2) -> Left (TypeMismatch a (Or b1 b2))
--     result -> result
-- unify (Or a1 a2) b = unify b (Or a1 a2)
-- unify (Op1 op a) (Op1 op' b) | op == op' = do
--   (a, s) <- unify a b
--   Right (Op1 op a, s)
-- unify (Op2 op a1 b1) (Op2 op' a2 b2) | op == op' = do
--   ((a, b), s) <- unify2 (a1, a2) (b1, b2)
--   Right (Op2 op a b, s)
-- unify a b = Left (TypeMismatch a b)

-- unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either Error ((Expr, Expr), Substitution)
-- unify2 (a1, a2) (b1, b2) = do
--   (a, s1) <- unify a1 a2
--   (b, s2) <- unify (eval s1 b1) (eval s1 b2)
--   Right ((a, b), s2 `compose` s1)

-- unifyRec :: [(String, Expr)] -> [(String, Expr)] -> Either Error ([(String, Expr)], Substitution)
-- unifyRec [] _ = Right ([], [])
-- unifyRec ((x, a) : kvs) kvs' = case lookup x kvs' of
--   Just b -> do
--     (kvs, s1) <- unifyRec kvs kvs'
--     (c, s2) <- unify (eval s1 a) (eval s1 b)
--     Right ((x, c) : kvs, s2 `compose` s1)
--   Nothing -> unifyRec kvs kvs'

-- infer :: Env -> Expr -> Either Error (Expr, Substitution)
-- infer _ Err = Right (Err, [])
-- infer _ Knd = Right (Knd, [])
-- infer _ IntT = Right (Knd, [])
-- infer _ NumT = Right (Knd, [])
-- infer _ (Int _) = Right (IntT, [])
-- infer _ (Num _) = Right (NumT, [])
-- infer env (Tag k) = case lookup k env of
--   Just (Tag k') | k == k' -> Right (Tag k, [])
--   Just (Ann (Tag k') ty) | k == k' -> Right (instantiate (map fst env) ty)
--   Just a -> infer env a
--   Nothing -> Right (Tag k, [])
-- infer env (Rec kvs) = do
--   (kvsT, s) <- inferRec env kvs
--   Right (Rec kvsT, s)
-- infer env (Var x) = case lookup x env of
--   Just (Var x') | x == x' -> do
--     let xT = newName (map fst env) (x ++ "T")
--     Right (Var xT, [(xT, Var xT), (x, Ann (Var x) (For [] (Var xT)))])
--   Just (Ann (Var x') ty) | x == x' -> do
--     let (t, vars) = instantiate (map fst env) ty
--     Right (eval (apply vars env) t, vars)
--   Just a -> infer env a
--   Nothing -> Left (UndefinedVar x)
-- infer env (Lam x b) = do
--   ((t1, t2), s) <- infer2 ((x, Var x) : env) (Var x) b
--   Right (fun [t1] t2, s)
-- infer env (Fun a b) = do
--   ((ta, tb), s) <- infer2 env a b
--   Right (Fun ta tb, s)
-- infer env (App a b) = do
--   ((ta, tb), s1) <- infer2 env a b
--   case ta of
--     Var x -> do
--       let y = newName (map fst (s1 ++ env)) "t"
--       (_, s2) <- unify (fun [tb] (Var y)) (Var x)
--       Right (Var y, [(y, Var y)] `compose` s2 `compose` s1)
--     Tag _ -> Right (App ta tb, s1)
--     Fun t1 t2 -> do
--       (_, s2) <- unify tb t1
--       Right (eval s2 t2, s2 `compose` s1)
--     App _ _ -> Right (App ta tb, s1)
--     ta -> Left (NotAFunction a ta)
-- infer env (Ann a ty) = do
--   let (t, vars) = instantiate (map fst env) ty
--   let alts = listAlts (eval (apply vars env) t)
--   (ta, s1) <- infer (apply vars (alts ++ env)) a
--   (t, s2) <- unify ta (eval s1 t)
--   Right (t, s2 `compose` s1)
-- infer env (Or a b) = do
--   ((ta, tb), s1) <- infer2 env a b
--   case unify ta tb of
--     Right (t, s2) -> Right (t, s2 `compose` s1)
--     Left _ -> Right (Or ta tb, s1)
-- infer env (If a b) = do
--   ((_, tb), s) <- infer2 env a b
--   Right (tb, s)
-- infer env (Fst a) = error "TODO: infer Fst"
-- infer env (Snd a) = error "TODO: infer Snd"
-- infer env (Fix x a) = infer ((x, Var x) : env) a
-- infer env (Op1 op a) = case op of
--   Int2Num -> do
--     (_, s) <- infer env (Ann a (For [] IntT))
--     Right (NumT, s)
-- infer env (Op2 op a b) = case op of
--   Add -> do
--     (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
--     Right (IntT, s)
--   Sub -> do
--     (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
--     Right (IntT, s)
--   Mul -> do
--     (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
--     Right (IntT, s)
--   Pow -> do
--     (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
--     Right (IntT, s)
--   Eq -> do
--     (ta, s1) <- infer env a
--     (t, s2) <- infer (apply s1 env) (Ann b (For [] ta))
--     Right (t, s2 `compose` s1)
--   Lt -> do
--     (ta, s1) <- infer env a
--     (t, s2) <- infer (apply s1 env) (Ann b (For [] ta))
--     Right (t, s2 `compose` s1)

-- listAlts :: Expr -> Env
-- listAlts (Ann (Tag k) ty) = [(k, Ann (Tag k) ty)]
-- listAlts (Or a b) = listAlts a ++ listAlts b
-- listAlts _ = []

-- Optimize
optimize :: Expr -> Expr
optimize a = a
