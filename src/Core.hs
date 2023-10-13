{-# LANGUAGE InstanceSigs #-}

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

{- TODO:
- Add `TypeOf Expr` as infer, `TypeOf (Var x)` == `TypeOf (Var x)`
- Add `Let Expr Expr Expr` as unify, Let (Var x) a b == let x = a in b
  To support pattern matching
  Maybe instead change Lam' to Lam' Expr Expr
  Maybe just add back Pattern to avoid "invalid" patterns
- Remove If
-}

data Expr
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Tag !String
  | Var !String
  | Ann !Expr !Type
  | Lam !Pattern !Expr
  | Fix !String !Expr
  | Fun !Expr !Expr
  | Or !Expr !Expr
  | App !Expr !Expr
  | Rec ![(String, Expr)]
  | Typ !String ![Expr] ![(String, Type)]
  | Op1 !UnaryOp !Expr
  | Op2 !BinaryOp !Expr !Expr
  | Err ![Error]
  deriving (Eq)

data Pattern
  = PKnd
  | PIntT
  | PNumT
  | PInt !Int
  | PTag !String
  | PVar !String
  | PAnn !Pattern !Type
  | PFun !Pattern !Pattern
  | PApp !Pattern !Pattern
  | PRec ![(String, Pattern)]
  | PErr
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
  = InfiniteType !String !Expr
  | NotAFunction !Expr !Expr
  | Op1Error !UnaryOp !Expr
  | Op2Error !BinaryOp !Expr !Expr
  | PatternMatchError !Pattern !Expr
  | TypeMismatch !Expr !Expr
  | UndefinedVar !String
  deriving (Eq, Show)

instance Show Expr where
  showsPrec :: Int -> Expr -> ShowS
  showsPrec p expr = case expr of
    Or a b -> infixR 1 a " | " b
    Ann a (For xs b) -> infixR 2 a (" : " ++ for xs) b
    Lam p b -> do
      let (ps, b') = asLam (Lam p b)
      prefix 2 ("\\" ++ unwords (map show ps) ++ ". ") b'
    Fix x a -> prefix 2 ("@fix " ++ x ++ ". ") a
    Op2 Eq a b -> infixL 3 a (op2 Eq) b
    Op2 Lt a b -> infixR 4 a (op2 Lt) b
    Fun a b -> infixR 5 a " -> " b
    Op2 AddI a b -> infixL 6 a (op2 AddI) b
    Op2 AddN a b -> infixL 6 a (op2 AddN) b
    Op2 Sub a b -> infixL 6 a (op2 Sub) b
    Op2 Mul a b -> infixL 7 a (op2 Mul) b
    Err err -> prefix 8 "@error " err
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

instance Show Pattern where
  show :: Pattern -> String
  show p = show (patternExpr p)

instance Show Type where
  show :: Type -> String
  show (For [] t) = show t
  show (For xs t) = "@for " ++ unwords xs ++ ". " ++ show t

instance Show BinaryOp where
  show :: BinaryOp -> String
  show AddI = "+"
  show AddN = "+"
  show Sub = "-"
  show Mul = "*"
  show Pow = "^"
  show Eq = "=="
  show Lt = "<"

instance Show UnaryOp where
  show :: UnaryOp -> String
  show Int2Num = "@int2num"

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

asFun :: Expr -> ([Expr], Expr)
asFun (Fun a1 a2) = let (bs, b) = asFun a2 in (a1 : bs, b)
asFun a = ([], a)

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

asLam :: Expr -> ([Pattern], Expr)
asLam (Lam p a) = let (ps, b) = asLam a in (p : ps, b)
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

let' :: [(Pattern, Expr)] -> Expr -> Expr
let' [] b = b
let' ((p, a) : defs) b = App (Lam p (let' defs b)) a

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
pop :: (Eq k) => k -> [(k, v)] -> [(k, v)]
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
freeVars (Lam p a) = filter (`notElem` freeVarsP p) (freeVars a)
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Rec []) = []
freeVars (Rec ((_, a) : kvs)) = freeVars a `union` freeVars (Rec kvs)
freeVars (Typ _ [] _) = []
freeVars (Typ k (a : bs) _) = freeVars a `union` freeVars (Typ k bs [])
freeVars (Op1 _ a) = freeVars a
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars (Err _) = []

freeVarsP :: Pattern -> [String]
freeVarsP = freeVars . patternExpr

patternExpr :: Pattern -> Expr
patternExpr PKnd = Knd
patternExpr PIntT = IntT
patternExpr PNumT = NumT
patternExpr (PInt i) = Int i
patternExpr (PTag k) = Tag k
patternExpr (PVar x) = Var x
patternExpr (PAnn p ty) = Ann (patternExpr p) ty
patternExpr (PFun p q) = Fun (patternExpr p) (patternExpr q)
patternExpr (PApp p q) = App (patternExpr p) (patternExpr q)
patternExpr (PRec kvs) = Rec (map (second patternExpr) kvs)
patternExpr PErr = Err []

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
eval env (Lam p b) = Lam p (eval (pushVars (freeVarsP p) env) b)
eval env (Fix x a) = Fix x (eval ((x, Var x) : env) a)
eval env (Fun a b) = Fun (eval env a) (eval env b)
eval env (App a b) = case (eval env a, eval env b) of
  (Lam p a, b) -> case (p, b) of
    (PKnd, Knd) -> a
    (PIntT, IntT) -> a
    (PNumT, NumT) -> a
    (PInt i, Int i') | i == i' -> a
    (PTag k, Tag k') | k == k' -> a
    (PVar x, b) -> eval [(x, b)] a
    (PAnn p ty, b) -> error "TODO: eval App Lam PAnn"
    (PFun p q, Fun b1 b2) -> app (lam [p, q] a) [b1, b2]
    (PApp p q, App b1 b2) -> app (lam [p, q] a) [b1, b2]
    (PRec [], Rec _) -> a
    (PErr, Err _) -> a
    (p, b) -> Err [PatternMatchError p b]
  (Err err, _) -> Err err
  (_, Err err) -> Err err
  (Ann a (For xs (Fun t1 t2)), b) -> case infer env (Ann b (For xs t1)) of
    Right (_, s) -> annotated (eval s (App a b)) (For (filter (`notElem` map fst s) xs) (eval s t2))
    Left err -> Err err
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err _ -> eval [] (App a2 b)
    Lam p a -> Or (Lam p a) (App a2 b)
    Ann a (For xs (Fun t1 t2)) -> Or (Ann a (For xs (Fun t1 t2))) (App a2 b)
    a | isOpen a -> Or a (App a2 b)
    a -> a
  (Fix x a, b) | isClosed b -> eval [(x, Fix x a)] (App a b)
  (a, b) -> App a b
eval env (Ann a (For xs t)) = case infer env (Ann a (For xs t)) of
  Right (t, s) -> annotated (eval (s ++ env) a) (For (filter (`notElem` map fst s) xs) t)
  Left err -> Err err
eval env (Or a b) = case (eval env a, eval env b) of
  (Err err1, Err err2) -> Err (err1 ++ err2)
  (Err _, b) -> b
  (a, Err _) -> a
  (Or a1 a2, b) -> Or a1 (Or a2 b)
  (a, b) -> Or a b
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
eval _ (Err err) = Err err

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
-- evalOp2 Eq (App a1 a2) (App b1 b2) = If (eq a1 b1) (eq a2 b2)
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

unify :: Expr -> Expr -> Either [Error] (Expr, Substitution)
unify Knd Knd = Right (Knd, [])
unify IntT IntT = Right (IntT, [])
unify NumT NumT = Right (NumT, [])
unify (Int i) (Int i') | i == i' = Right (Int i, [])
unify (Num n) (Num n') | n == n' = Right (Num n, [])
unify (Tag k) (Tag k') | k == k' = Right (Tag k, [])
unify (Var x) (Var x') | x == x' = Right (Var x, [])
unify (Var x) b | x `occurs` b = Left [InfiniteType x b]
unify (Var x) b = Right (b, [(x, b)])
unify a (Var x) = unify (Var x) a
-- Ann !Expr !Type
unify (Fun a1 b1) (Fun a2 b2) = do
  ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
  Right (Fun ta tb, s)
unify a (Or b1 b2) = case unify a b1 of
  Right (a, s1) -> case unify a b2 of
    Right (a, s2) -> Right (a, s2 `compose` s1)
    Left _ -> Right (a, s1)
  Left err1 -> case unify a b2 of
    Right (a, s) -> Right (a, s)
    Left err2 -> Left (err1 ++ err2)
unify (Or a1 a2) b = case unify a1 b of
  Right (b, s1) -> case unify a2 b of
    Right (b, s2) -> Right (b, s2 `compose` s1)
    Left _ -> Right (b, s1)
  Left err1 -> case unify a2 b of
    Right (a, s) -> Right (a, s)
    Left err2 -> Left (err1 ++ err2)
unify (App a1 b1) (App a2 b2) = do
  ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
  Right (App ta tb, s)
unify (Op1 op a) (Op1 op' b) | op == op' = do
  (a, s) <- unify a b
  Right (Op1 op a, s)
unify (Op2 op a1 b1) (Op2 op' a2 b2) | op == op' = do
  ((a, b), s) <- unify2 (a1, a2) (b1, b2)
  Right (Op2 op a b, s)
unify (Rec kvs) (Rec kvs') = do
  (kvs, s) <- unifyRec kvs kvs'
  Right (Rec kvs, s)
unify a (Typ k args alts) = case unify a (app (Tag k) args) of
  Right (_, s) -> Right (Typ k args alts, s)
  Left err -> Left (TypeMismatch a (Typ k args alts) : err)
unify (Typ k args alts) b = case unify (app (Tag k) args) b of
  Right (_, s) -> Right (Typ k args alts, s)
  Left err -> Left (TypeMismatch (Typ k args alts) b : err)
unify a b = Left [TypeMismatch a b]

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either [Error] ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  (ta, s1) <- unify a1 a2
  (tb, s2) <- unify (eval s1 b1) (eval s1 b2)
  Right ((eval s2 ta, tb), s2 `compose` s1)

unifyAll :: [Expr] -> [Expr] -> Either [Error] ([Expr], Substitution)
unifyAll [] _ = Right ([], [])
unifyAll _ [] = Right ([], [])
unifyAll (a1 : bs1) (a2 : bs2) = do
  (bs, s1) <- unifyAll bs1 bs2
  (a, s2) <- unify (eval s1 a1) (eval s1 a2)
  Right (a : map (eval s2) bs, s2 `compose` s1)

unifyRec :: [(String, Expr)] -> [(String, Expr)] -> Either [Error] ([(String, Expr)], Substitution)
unifyRec [] _ = Right ([], [])
unifyRec ((x, a) : kvs) kvs' = case lookup x kvs' of
  Just b -> do
    (kvs, s1) <- unifyRec kvs kvs'
    (t, s2) <- unify (eval s1 a) (eval s1 b)
    Right ((x, t) : kvs, s2 `compose` s1)
  Nothing -> unifyRec kvs kvs'

print' :: (Show a, Show b, Show c, Applicative f) => a -> b -> c -> f ()
print' msg x y = traceM (show msg ++ "\t  " ++ show x ++ "  ~~>  " ++ show y)

infer :: Env -> Expr -> Either [Error] (Expr, Substitution)
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
  Nothing -> Left [UndefinedVar x]
infer env (Ann a ty) = do
  -- TODO: SIMPLIFY
  -- let (t, vars) = instantiate (map fst env) ty
  -- (ta, s1) <- infer (env `compose` vars) a
  -- (t', s2) <- unify ta (eval (env `compose` s1) t)
  -- Right (t', s2 `compose` s1 `compose` vars)
  let (t, vars) = instantiate (map fst env) ty
  case (a, eval env t) of
    (Lam p b, Fun t1 t2) -> do
      let a = patternExpr p
      ((t1, t2), s) <- infer2 (pushVars (freeVars a) (vars ++ env)) (ann a t1) (ann b t2)
      Right (Fun t1 t2, s)
    (a, Typ k args alts) -> do
      let ctrs = map (\(k, ty) -> (k, Ann (Tag k) ty)) alts
      (ta, s1) <- infer (vars ++ ctrs ++ env) a
      (t, s2) <- unify ta (Typ k args alts)
      Right (t, s2 `compose` s1)
    (a, t) -> do
      (ta, s1) <- infer (vars ++ env) a
      (t, s2) <- unify ta t
      Right (t, s2 `compose` s1)
infer env (Lam p b) = do
  let a = patternExpr p
  ((t1, t2), s) <- infer2 (pushVars (freeVars a) env) a b
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
infer env (App a b) = do
  -- TODO: SIMPLIFY
  -- ((ta, tb), s1) <- infer2 env a b
  -- let x = newName (map fst (s1 ++ env)) "t"
  -- (_, s2) <- unify (Fun tb (Var x)) ta
  -- Right (eval (env `compose` s2) (Var x), s2 `compose` s1 `compose` [(x, Var x)])
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
    ta -> Left [NotAFunction a ta]
infer env (Rec kvs) = do
  (kvsT, s) <- inferRec env kvs
  Right (Rec kvsT, s)
infer env (Typ _ args alts) = do
  (_, s1) <- inferAll env args
  (_, s2) <- inferAll (env `compose` s1) (map (\(k, For xs t) -> Ann (Tag k) (For xs (eval (pushVars xs s1) t))) alts)
  Right (Knd, s2 `compose` s1)
infer env (Op1 op a) = inferOp1 env op a
infer env (Op2 op a b) = inferOp2 env op a b
infer _ (Err err) = Right (Err err, [])

infer2 :: Env -> Expr -> Expr -> Either [Error] ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (env `compose` s1) b
  Right ((eval s2 ta, tb), s2 `compose` s1)

inferAll :: Env -> [Expr] -> Either [Error] ([Expr], Substitution)
inferAll _ [] = Right ([], [])
inferAll env (a : bs) = do
  (ta, s1) <- infer env a
  (tbs, s2) <- inferAll (env `compose` s1) bs
  Right (eval s2 ta : tbs, s2 `compose` s1)

inferRec :: Env -> [(String, Expr)] -> Either [Error] ([(String, Expr)], Substitution)
inferRec _ [] = Right ([], [])
inferRec env ((x, a) : kvs) = do
  (kvsT, s1) <- inferRec env kvs
  (ta, s2) <- infer (env `compose` s1) a
  Right ((x, ta) : kvsT, s2 `compose` s1)

inferOp1 :: Env -> UnaryOp -> Expr -> Either [Error] (Expr, Substitution)
inferOp1 env Int2Num a = do
  (_, s) <- infer env (ann a IntT)
  Right (NumT, s)

inferOp2 :: Env -> BinaryOp -> Expr -> Expr -> Either [Error] (Expr, Substitution)
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
  (t, s2) <- infer (env `compose` s1) (ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Lt a b = do
  (ta, s1) <- infer env a
  (t, s2) <- infer (env `compose` s1) (ann b ta)
  Right (t, s2 `compose` s1)

-- Type inference
compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = apply s1 s2 `union` s1
  where
    apply :: Substitution -> Env -> Env
    apply _ [] = []
    apply s ((x, Ann a (For xs t)) : env) = do
      let t' = eval (pushVars xs s) t
      (x, Ann (eval s a) (For xs t')) : apply s env
    apply s ((x, a) : env) = (x, eval s a) : apply s env

instantiate :: [String] -> Type -> (Expr, Substitution)
instantiate _ (For [] a) = (a, [])
instantiate existing (For (x : xs) a) = do
  let y = newName existing x
  let (b, s) = instantiate (y : x : existing) (For xs a)
  (eval [(x, Var y)] b, [(y, Var y)] `union` s)

instantiate2 :: [String] -> Type -> Type -> ((Expr, Expr), Substitution)
instantiate2 existing (For xs t1) (For ys t2) = do
  let (t2', vars1) = instantiate (freeVars t1 ++ existing) (For ys t2)
  let (t1', vars2) = instantiate (freeVars t2 ++ map fst vars1 ++ existing) (For xs t1)
  ((t1', t2'), vars1 ++ vars2)
