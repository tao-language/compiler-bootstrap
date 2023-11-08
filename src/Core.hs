{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (first, second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.List (delete, intercalate, union)

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
  | Int Int
  | Num Double
  | Tag String
  | Var String
  | Ann Expr Type
  | Lam Pattern Expr
  | Fix String Expr
  | Fun Expr Expr
  | Or Expr Expr
  | App Expr Expr
  | Rec [(String, Expr)]
  | Typ String [String]
  | Op1 UnaryOp Expr
  | Op2 BinaryOp Expr Expr
  | Meta [Metadata] Expr
  | Err Error
  deriving (Eq)

data Pattern
  = PKnd
  | PIntT
  | PNumT
  | PInt Int
  | PTag String
  | PVar String
  | PFun Pattern Pattern
  | PApp Pattern Pattern
  | PRec [(String, Pattern)]
  | PMeta [Metadata] Pattern
  deriving (Eq)

data Type
  = For [String] Expr
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
  = Int2Num
  deriving (Eq)

data Module = Module
  { name :: String,
    -- docs :: Maybe DocString,
    env :: Env,
    run :: [Expr]
  }
  deriving (Eq, Show)

data DocString = DocString
  { public :: Bool,
    description :: String,
    meta :: [Metadata]
  }
  deriving (Eq, Show)

newDocString :: DocString
newDocString =
  DocString
    { public = True,
      description = "",
      meta = []
    }

data Error
  = SyntaxError String (Int, Int) String
  | NotImplementedError
  | -- Runtime errors
    PatternMatchError Pattern Expr
  | Op1Error UnaryOp Expr
  | Op2Error BinaryOp Expr Expr
  | -- Type errors
    OccursError String Expr
  | TypeMismatch Expr Expr
  | UndefinedVar String
  deriving
    ( Eq,
      Show
    )

data Comment
  = Comment (Int, Int) String
  deriving (Eq, Show)

data Metadata
  = Location String (Int, Int)
  | Comments [Comment]
  | TrailingComment Comment
  deriving (Eq, Show)

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

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
    Op2 Add a b -> infixL 6 a (op2 Add) b
    Op2 Sub a b -> infixL 6 a (op2 Sub) b
    Op2 Mul a b -> infixL 7 a (op2 Mul) b
    Op1 Int2Num a -> prefix 8 (op1 Int2Num) a
    Op2 Pow a b -> infixR 10 a (show Pow) b
    App a b -> infixL 8 a " " b
    Err err -> prefix 0 "@error " err
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
    Typ k alts -> atom 11 (show (Tag k) ++ "[" ++ intercalate "|" alts ++ "]")
    Meta _ a -> showsPrec p a
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
  show Add = "+"
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
or' [] = error "`or'` must have at least one expression"
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
freeVars (Typ _ _) = []
freeVars (Op1 _ a) = freeVars a
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars (Meta _ a) = freeVars a
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
patternExpr (PFun p q) = Fun (patternExpr p) (patternExpr q)
patternExpr (PApp p q) = App (patternExpr p) (patternExpr q)
patternExpr (PRec kvs) = Rec (map (second patternExpr) kvs)
patternExpr (PMeta m p) = Meta m (patternExpr p)

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
    (PFun p q, Fun b1 b2) -> app (lam [p, q] a) [b1, b2]
    (PApp p q, App b1 b2) -> app (lam [p, q] a) [b1, b2]
    (PRec [], Rec _) -> a
    (p, b) -> Err (PatternMatchError p b)
  (Err e, _) -> Err e
  -- (Ann a (For xs (Fun t1 t2)), b) -> case infer env (Ann b (For xs t1)) of
  --   Right (_, s) -> annotated (eval s (App a b)) (For (filter (`notElem` map fst s) xs) (eval s t2))
  --   Left err -> Err
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err _ -> eval [] (App a2 b)
    Lam p a -> Or (Lam p a) (App a2 b)
    Ann a (For xs (Fun t1 t2)) -> Or (Ann a (For xs (Fun t1 t2))) (App a2 b)
    a | isOpen a -> Or a (App a2 b)
    a -> a
  (Fix x a, b) | isClosed b -> eval [(x, Fix x a)] (App a b)
  (a, b) -> App a b
-- eval env (Ann a (For xs t)) = case infer env (Ann a (For xs t)) of
--   Right (t, s) -> annotated (eval (s ++ env) a) (For (filter (`notElem` map fst s) xs) t)
--   Left err -> Err
eval env (Ann a _) = eval env a
eval env (Or a b) = case (eval env a, eval env b) of
  (Err _, b) -> b
  (a, Err _) -> a
  (Or a1 a2, b) -> Or a1 (Or a2 b)
  (a, b) -> Or a b
eval env (Rec kvs) = Rec (map (second (eval env)) kvs)
eval env (Typ k alts) = Typ k alts
eval env (Op1 op a) = case (op, eval env a) of
  (op, a) | isOpen a -> Op1 op a
  (op, a) -> evalOp1 op a
eval env (Op2 op a b) = case (op, eval env a, eval env b) of
  (op, a, b) | isOpen a || isOpen b -> Op2 op a b
  (op, a, b) -> evalOp2 op a b
eval env (Meta meta a) = Meta meta (eval env a)
eval _ (Err e) = Err e

evalOp1 :: UnaryOp -> Expr -> Expr
evalOp1 Int2Num (Int b) = Num (fromIntegral b)
evalOp1 op a = Err (Op1Error op a)

evalOp2 :: BinaryOp -> Expr -> Expr -> Expr
evalOp2 Add (Int a) (Int b) = Int (a + b)
evalOp2 Add (Num a) (Num b) = Num (a + b)
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
evalOp2 op a b = Err (Op2Error op a b)

annotated :: Expr -> Type -> Expr
annotated (Tag k) (For _ (Tag k')) | k == k' = Tag k
annotated a@Tag {} ty = Ann a ty
annotated a@Var {} ty = Ann a ty
annotated a@Lam {} ty = Ann a ty
annotated a@App {} ty = Ann a ty
annotated a _ = a

unify :: Expr -> Expr -> (Expr, Substitution)
unify Knd Knd = (Knd, [])
unify IntT IntT = (IntT, [])
unify NumT NumT = (NumT, [])
unify (Int i) (Int i') | i == i' = (Int i, [])
unify (Num n) (Num n') | n == n' = (Num n, [])
unify (Tag k) (Tag k') | k == k' = (Tag k, [])
unify (Var x) (Var x') | x == x' = (Var x, [])
unify (Var x) b | x `occurs` b = (Err (OccursError x b), [])
unify (Var x) b = (b, [(x, b)])
unify a (Var x) = unify (Var x) a
unify (Fun a1 a2) b@Tag {} = unify a2 (App b a1)
unify (Fun a1 a2) b@App {} = unify a2 (App b a1)
unify a@Tag {} (Fun b1 b2) = unify (App a b1) b2
unify a@App {} (Fun b1 b2) = unify (App a b1) b2
unify (Fun a1 b1) (Fun a2 b2) = do
  let ((ta, tb), s) = unify2 (a1, a2) (b1, b2)
  (Fun ta tb, s)
unify a (Or b1 b2) = case unify a b1 of
  (Err _, _) -> unify a b2
  (a, s1) -> case unify a b2 of
    (Err _, _) -> (a, s1)
    (a, s2) -> (a, s2 `compose` s1)
unify (Or a1 a2) b = case unify a1 b of
  (Err _, _) -> unify a2 b
  (b, s1) -> case unify a2 b of
    (Err _, _) -> (b, s1)
    (b, s2) -> (b, s2 `compose` s1)
unify (App a1 b1) (App a2 b2) = do
  let ((ta, tb), s) = unify2 (a1, a2) (b1, b2)
  (App ta tb, s)
unify (Op1 op a) (Op1 op' b) | op == op' = do
  let (a', s) = unify a b
  (Op1 op a', s)
unify (Op2 op a1 b1) (Op2 op' a2 b2) | op == op' = do
  let ((a, b), s) = unify2 (a1, a2) (b1, b2)
  (Op2 op a b, s)
unify (Rec kvs) (Rec kvs') = first Rec (unifyRec kvs kvs')
unify (Typ k alts) b = case unify (Tag k) b of
  (Err e, s) -> (Err e, s)
  (_, s) -> (Typ k alts, s)
unify a (Typ k alts) = case unify a (Tag k) of
  (Err e, s) -> (Err e, s)
  (_, s) -> (Typ k alts, s)
unify (Meta _ a) b = unify a b
unify a (Meta _ b) = unify a b
unify a b = (Err (TypeMismatch a b), [])

unify2 :: (Expr, Expr) -> (Expr, Expr) -> ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  let (ta, s1) = unify a1 a2
  let (tb, s2) = unify (eval s1 b1) (eval s1 b2)
  ((eval s2 ta, tb), s2 `compose` s1)

unifyAll :: [Expr] -> [Expr] -> ([Expr], Substitution)
unifyAll [] _ = ([], [])
unifyAll _ [] = ([], [])
unifyAll (a1 : bs1) (a2 : bs2) = do
  let (bs, s1) = unifyAll bs1 bs2
  let (a, s2) = unify (eval s1 a1) (eval s1 a2)
  (a : map (eval s2) bs, s2 `compose` s1)

unifyRec :: [(String, Expr)] -> [(String, Expr)] -> ([(String, Expr)], Substitution)
unifyRec [] _ = ([], [])
unifyRec ((x, a) : kvs) kvs' = case lookup x kvs' of
  Just b -> do
    let (kvs, s1) = unifyRec kvs kvs'
    let (t, s2) = unify (eval s1 a) (eval s1 b)
    ((x, t) : kvs, s2 `compose` s1)
  Nothing -> unifyRec kvs kvs'

infer :: Env -> Expr -> (Expr, Substitution)
infer _ Knd = (Knd, [])
infer _ IntT = (Knd, [])
infer _ NumT = (Knd, [])
infer _ (Int _) = (IntT, [])
infer _ (Num _) = (NumT, [])
infer env (Tag k) = case lookup k env of
  Just (Tag k') | k == k' -> (Tag k, [])
  Just (Ann (Tag k') ty) | k == k' -> instantiate env ty
  Just (Ann (Typ k' _) ty) | k == k' -> instantiate env ty
  Just a -> infer env a
  Nothing -> (Tag k, [])
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let y = newName (map fst env) (x ++ "T")
    (Var y, [(y, Var y), (x, Ann (Var x) (For [] (Var y)))])
  Just (Ann (Var x') ty) | x == x' -> instantiate env ty
  Just a -> infer env a
  Nothing -> (Err (UndefinedVar x), [])
infer env (Ann a ty) = do
  let (t, vars) = instantiate env ty
  let (ta, s1) = infer (vars ++ env) a
  let (t', s2) = unify ta (eval (env `compose` s1) t)
  (eval env t', s2 `compose` s1 `compose` vars)
infer env (Lam p b) = do
  let a = patternExpr p
  let ((t1, t2), s) = infer2 (pushVars (freeVars a) env) a b
  (Fun t1 t2, s)
infer env (Fix x a) = infer ((x, Var x) : env) a
infer env (Fun a b) = do
  let ((ta, tb), s) = infer2 env a b
  (Fun ta tb, s)
infer env (Or a b) = do
  let ((ta, tb), s1) = infer2 env a b
  case unify ta tb of
    (Err _, _) -> (Or ta tb, s1)
    (t, s2) -> (eval env t, s2 `compose` s1)
infer env (App a b) = do
  let ((ta, tb), s1) = infer2 env a b
  let x = newName (map fst (s1 ++ env)) "t"
  case unify (Fun tb (Var x)) ta of
    (Err e, s2) -> (Err e, s2 `compose` s1)
    (_, s2) -> (eval (env `compose` s2) (Var x), s2 `compose` s1 `compose` [(x, Var x)])
infer env (Rec kvs) = do
  let (kvsT, s) = inferRec env kvs
  (Rec kvsT, s)
infer env (Typ k alts) = (Typ k alts, [])
infer env (Op1 op a) = inferOp1 env op a
infer env (Op2 op a b) = inferOp2 env op a b
infer env (Meta _ a) = infer env a
infer _ (Err e) = (Err e, [])

infer2 :: Env -> Expr -> Expr -> ((Expr, Expr), Substitution)
infer2 env a b = do
  let (ta, s1) = infer env a
  let (tb, s2) = infer (env `compose` s1) b
  ((eval s2 ta, tb), s2 `compose` s1)

inferAll :: Env -> [Expr] -> ([Expr], Substitution)
inferAll _ [] = ([], [])
inferAll env (a : bs) = do
  let (ta, s1) = infer env a
  let (tbs, s2) = inferAll (env `compose` s1) bs
  (eval s2 ta : tbs, s2 `compose` s1)

inferRec :: Env -> [(String, Expr)] -> ([(String, Expr)], Substitution)
inferRec _ [] = ([], [])
inferRec env ((x, a) : kvs) = do
  let (kvsT, s1) = inferRec env kvs
  let (ta, s2) = infer (env `compose` s1) a
  ((x, ta) : kvsT, s2 `compose` s1)

inferOp1 :: Env -> UnaryOp -> Expr -> (Expr, Substitution)
inferOp1 env Int2Num a = do
  let (_, s) = infer env (ann a IntT)
  (NumT, s)

inferOp2 :: Env -> BinaryOp -> Expr -> Expr -> (Expr, Substitution)
inferOp2 env Add a b = do
  let (ta, s1) = infer env (ann a IntT)
  let (t, s2) = infer (s1 `compose` env) (ann b ta)
  (t, s2 `compose` s1)
inferOp2 env Sub a b = do
  let (ta, s1) = infer env (ann a IntT)
  let (t, s2) = infer (s1 `compose` env) (ann b ta)
  (t, s2 `compose` s1)
inferOp2 env Mul a b = do
  let (ta, s1) = infer env (ann a IntT)
  let (t, s2) = infer (s1 `compose` env) (ann b ta)
  (t, s2 `compose` s1)
inferOp2 env Pow a b = do
  let (ta, s1) = infer env (ann a IntT)
  let (t, s2) = infer (s1 `compose` env) (ann b ta)
  (t, s2 `compose` s1)
inferOp2 env Eq a b = do
  let (ta, s1) = infer env a
  let (t, s2) = infer (env `compose` s1) (ann b ta)
  (t, s2 `compose` s1)
inferOp2 env Lt a b = do
  let (ta, s1) = infer env a
  let (t, s2) = infer (env `compose` s1) (ann b ta)
  (t, s2 `compose` s1)

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

instantiate :: Env -> Type -> (Expr, Substitution)
instantiate env (For [] a) = (eval env a, [])
instantiate env (For (x : xs) a) = do
  let y = newName (map fst env) x
  let (b, s) = instantiate env (For xs $ eval [(x, Var y)] a)
  (b, [(y, Var y)] `union` s)
