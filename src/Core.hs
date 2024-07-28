module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.Function ((&))
import Data.List (delete, intercalate, union)

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
-- https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- https://www.youtube.com/live/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf

-- TODO: replace operators with Target or Builtin terms
data Expr
  = Knd
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Var String
  | Tag String
  | For String Expr
  | Fix String Expr
  | Fun Expr Expr
  | Lam Pattern Expr
  | App Expr Expr
  | Or Expr Expr
  | Ann Expr Expr
  | Op1 UnaryOp Expr
  | Op2 BinaryOp Expr Expr
  | Meta Metadata Expr
  | Err
  deriving (Eq)

data Pattern
  = PKnd
  | PAny
  | PIntT
  | PNumT
  | PInt Int
  | PNum Double
  | PVar String
  | PTag String
  | PApp Pattern Pattern
  | PFun Pattern Pattern
  | PEq Expr
  | PMeta Metadata Pattern
  | PErr
  deriving (Eq)

data BinaryOp
  = Add
  | Sub
  | Mul
  | Pow
  | Eq
  | Lt
  | Gt
  deriving (Eq)

data UnaryOp
  = Int2Num
  deriving (Eq)

data Metadata
  = Location String (Int, Int)
  | Comment String
  deriving (Eq, Show)

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

-- https://package.elm-lang.org/packages/elm-in-elm/compiler/latest/Elm.Compiler.Error
-- https://github.com/elm-in-elm/compiler/blob/master/src/Elm/Compiler/Error.elm
-- https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/error.rs
data Error
  = TypeError TypeError
  | PatternError PatternError
  deriving (Eq, Show)

data TypeError
  = OccursError String Expr
  | TypeMismatch Expr Expr
  | TypeCheck Expr Expr
  | NotAFunction Expr Expr
  | UndefinedVar String
  | UndefinedField String [(String, Expr)]
  deriving (Eq, Show)

data PatternError
  = MissingCases [Expr]
  | UnreachableCase Expr
  deriving (Eq, Show)

instance Show Expr where
  showsPrec :: Int -> Expr -> ShowS
  showsPrec p expr = case expr of
    -- App (Lam [Case [p] b]) a -> prefix 1 (show p ++ " = " ++ show a ++ "; ") b
    Or a b -> infixR 1 a " | " b
    Ann a b -> infixR 2 a " : " b
    Op2 Eq a b -> infixL 3 a (op2 Eq) b
    Op2 Lt a b -> infixR 4 a (op2 Lt) b
    Op2 Gt a b -> infixR 4 a (op2 Gt) b
    For x a -> do
      let (xs, a') = asFor (For x a)
      prefix 2 ("@" ++ unwords xs ++ ". ") a'
    Fix x a -> prefix 2 ("$fix " ++ x ++ ". ") a
    Fun p b -> infixR 5 p " -> " b
    Op2 Add a b -> infixL 6 a (op2 Add) b
    Op2 Sub a b -> infixL 6 a (op2 Sub) b
    Op2 Mul a b -> infixL 7 a (op2 Mul) b
    Op1 Int2Num a -> prefix 8 (op1 Int2Num) a
    Op2 Pow a b -> infixR 10 a (show Pow) b
    App a b -> infixL 8 a " " b
    Err -> atom 12 "$error"
    Knd -> atom 12 "$Kind"
    IntT -> atom 12 "$Int"
    NumT -> atom 12 "$Num"
    Int i -> atom 12 (show i)
    Num n -> atom 12 (show n)
    Var x | isVarName x -> atom 12 x
    Var x -> atom 12 ("($var '" ++ x ++ "')")
    Tag k -> atom 12 k
    Meta _ a -> showsPrec p a
    Lam p b -> infixR 8 (toExpr p) " => " b
    where
      atom n k = showParen (p > n) $ showString k
      prefix n k a = showParen (p > n) $ showString k . showsPrec (n + 1) a
      infixL n a op b = showParen (p > n) $ showsPrec n a . showString op . showsPrec (n + 1) b
      infixR n a op b = showParen (p > n) $ showsPrec (n + 1) a . showString op . showsPrec n b
      isVarName ('$' : xs) = all isNameChar xs
      isVarName ('_' : xs) = all isNameChar xs
      isVarName (x : xs) = isLower x && all isNameChar xs
      isVarName [] = False
      isTagName (x : xs) = isUpper x && all isNameChar xs
      isTagName [] = False
      isNameChar '-' = True
      isNameChar '_' = True
      isNameChar c = isAlphaNum c
      op2 op = " " ++ show op ++ " "
      op1 op = show op ++ " "

instance Show Pattern where
  show :: Pattern -> String
  show = show . toExpr

instance Show BinaryOp where
  show :: BinaryOp -> String
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Pow = "^"
  show Eq = "=="
  show Lt = "<"
  show Gt = ">"

instance Show UnaryOp where
  show :: UnaryOp -> String
  show Int2Num = "@int2num"

-- Syntax sugar
intT :: Int -> Expr
intT i = Int i `Or` IntT

numT :: Double -> Expr
numT n = Num n `Or` NumT

tag :: String -> [Expr] -> Expr
tag k = call (Tag k)

ptag :: String -> [Pattern] -> Pattern
ptag k = pCall (PTag k)

fix :: [String] -> Expr -> Expr
fix xs a = foldr Fix a xs

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

asFor :: Expr -> ([String], Expr)
asFor (For x a) = let (xs, b) = asFor a in (x : xs, b)
asFor a = ([], a)

fun :: [Expr] -> Expr -> Expr
fun args ret = foldr Fun ret args

asFun :: Expr -> ([Expr], Expr)
asFun (Fun arg ret) = let (args, ret') = asFun ret in (arg : args, ret')
asFun a = ([], a)

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
gt = Op2 Gt

int2num :: Expr -> Expr
int2num = Op1 Int2Num

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

let' :: (Pattern, Expr) -> Expr -> Expr
let' (PVar x, Var x') b | x == x' = b
let' (p, a) b = do
  let xs = filter (`occurs` a) (freeVars p)
  App (lam [p] b) (fix xs a)

lets :: [(Pattern, Expr)] -> Expr -> Expr
lets defs b = foldr let' b defs

app :: [Expr] -> Expr
app [] = Err
app (a : bs) = call a bs

pApp :: [Pattern] -> Pattern
pApp [] = PErr
pApp (p : qs) = pCall p qs

call :: Expr -> [Expr] -> Expr
call = foldl App

pCall :: Pattern -> [Pattern] -> Pattern
pCall = foldl PApp

callOf :: Expr -> (Expr, [Expr])
callOf (App a b) = let (a', bs) = callOf a in (a', bs ++ [b])
callOf a = (a, [])

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

list :: Expr -> Expr -> [Expr] -> Expr
list _ nil [] = nil
list cons nil (a : bs) = call cons [a, list cons nil bs]

meta :: [Metadata] -> Expr -> Expr
meta ms a = foldr Meta a ms

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

class FreeVars a where
  freeVars :: a -> [String]

instance FreeVars Expr where
  freeVars :: Expr -> [String]
  freeVars Knd = []
  freeVars IntT = []
  freeVars NumT = []
  freeVars (Int _) = []
  freeVars (Num _) = []
  freeVars (Var x) = [x]
  freeVars (Tag _) = []
  freeVars (For x a) = delete x (freeVars a)
  freeVars (Fix x a) = delete x (freeVars a)
  freeVars (Fun a b) = freeVars a `union` freeVars b
  freeVars (Lam p b) = freeVars p `union` freeVars b
  freeVars (App a b) = freeVars a `union` freeVars b
  freeVars (Or a b) = freeVars a `union` freeVars b
  freeVars (Ann a _) = freeVars a
  freeVars (Op1 _ a) = freeVars a
  freeVars (Op2 _ a b) = freeVars a `union` freeVars b
  freeVars (Meta _ a) = freeVars a
  freeVars Err = []

instance FreeVars Pattern where
  freeVars :: Pattern -> [String]
  freeVars = freeVars . toExpr

toExpr :: Pattern -> Expr
toExpr PKnd = Knd
toExpr PAny = For "_" (Var "_")
toExpr PIntT = IntT
toExpr PNumT = NumT
toExpr (PInt i) = Int i
toExpr (PNum n) = Num n
toExpr (PVar x) = Var x
toExpr (PTag k) = Tag k
toExpr (PApp p q) = App (toExpr p) (toExpr q)
toExpr (PFun p q) = Fun (toExpr p) (toExpr q)
toExpr (PEq a) = a
toExpr (PMeta m p) = Meta m (toExpr p)
toExpr PErr = Err

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

newName :: [String] -> String -> String
newName existing x = head (newNamesStream existing x)

newNames :: [String] -> [String] -> [String]
newNames _ [] = []
newNames existing (x : xs) = do
  let y = newName existing x
  let ys = newNames (y : existing) xs
  y : ys

newNamesStream :: [String] -> String -> [String]
newNamesStream existing x =
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
eval env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Tag k) -> Tag k
  Just (Ann (Var x') _) | x == x' -> Var x
  Just a -> eval env a
  Nothing -> Var x
eval env (Tag k) = case lookup k env of
  Just (Tag k') | k == k' -> Tag k
  Just a -> eval ((k, Tag k) : env) a
  Nothing -> Tag k
eval env (For x a) = For x (eval ((x, Var x) : env) a)
eval env (Fix x a) = Fix x (eval ((x, Var x) : env) a)
eval env (Fun a b) = Fun (eval env a) (eval env b)
eval env (Lam p b) = Lam p (eval (pushVars (freeVars p) env) b)
eval env (App a b) = case (eval env a, eval env b) of
  (For x a, b) -> eval [(x, Var x)] (App a b)
  (Fix x a, b) | isClosed b -> eval [(x, Fix x a)] (App a b)
  (Err, _) -> Err
  (Lam p c, b) -> case match p b of
    Just bindings -> eval bindings c
    Nothing -> Err
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err -> eval [] (App a2 b)
    a | isOpen a -> Or a (App a2 b)
    a -> a
  (a, b) -> App a b
eval env (Or a b) = Or (eval env a) (eval env b)
eval env (Ann (Tag k) ty) = Ann (Tag k) (eval env ty)
eval env (Ann a _) = eval env a
eval env (Op1 op a) = case (op, eval env a) of
  (op, a) | isOpen a -> Op1 op a
  (op, a) -> evalOp1 op a
eval env (Op2 op a b) = case (op, eval env a, eval env b) of
  (op, a, b) | isOpen a || isOpen b -> Op2 op a b
  (op, a, b) -> evalOp2 op a b
eval env (Meta _ a) = eval env a
eval _ Err = Err

evalOp1 :: UnaryOp -> Expr -> Expr
evalOp1 Int2Num (Int b) = Num (fromIntegral b)
evalOp1 _ _ = Err

evalOp2 :: BinaryOp -> Expr -> Expr -> Expr
evalOp2 Add (Int a) (Int b) = Int (a + b)
evalOp2 Add (Num a) (Num b) = Num (a + b)
evalOp2 Sub (Int a) (Int b) = Int (a - b)
evalOp2 Sub (Num a) (Num b) = Num (a - b)
evalOp2 Mul (Int a) (Int b) = Int (a * b)
evalOp2 Mul (Num a) (Num b) = Num (a * b)
evalOp2 Pow (Int a) (Int b) = Int (a ^ b)
evalOp2 Pow (Num a) (Num b) = Num (a ** b)
evalOp2 Eq (Tag k) (Tag k') | k == k' = Tag k
evalOp2 Eq IntT IntT = IntT
evalOp2 Eq NumT NumT = NumT
evalOp2 Eq (Int a) (Int b) | a == b = Int a
evalOp2 Eq (Num a) (Num b) | a == b = Num a
evalOp2 Eq (Var a) (Var b) | a == b = Var a
evalOp2 Lt (Int a) (Int b) | a < b = Int a
evalOp2 Lt (Num a) (Num b) | a < b = Num a
evalOp2 _ _ _ = Err

match :: Pattern -> Expr -> Maybe [(String, Expr)]
match PAny _ = Just []
match PIntT IntT = Just []
match PNumT NumT = Just []
match (PInt i) (Int i') | i == i' = Just []
match (PNum n) (Num n') | n == n' = Just []
match (PVar x) b = Just [(x, b)]
match (PApp p q) (App a b) = match2 (p, a) (q, b)
match (PTag k) (Tag k') | k == k' = Just []
match (PFun p q) (Fun a b) = match2 (p, a) (q, b)
match (PMeta _ p) b = match p b
match PErr Err = Just []
match _ _ = Nothing

match2 :: (Pattern, Expr) -> (Pattern, Expr) -> Maybe [(String, Expr)]
match2 (p, a) (q, b) = do
  env1 <- match p a
  env2 <- match q b
  Just (env1 ++ env2)

matchAll :: [Pattern] -> [Expr] -> Maybe [(String, Expr)]
matchAll [] [] = Just []
matchAll (p : ps) (a : bs) = do
  env1 <- match p a
  env2 <- matchAll ps bs
  Just (env1 ++ env2)
matchAll _ _ = Nothing

-- matchArgs :: [(String, Pattern)] -> [(String, Expr)] -> Maybe [(String, Expr)]
-- matchArgs [] _ = Just []
-- matchArgs (("", p) : ps) ((_, a) : args) = do
--   env1 <- match p a
--   env2 <- matchArgs ps args
--   Just (env1 ++ env2)
-- matchArgs ((x, p) : ps) args = case lookup x args of
--   Just a ->
--     matchArgs (("", p) : ps) ((x, a) : filter (\(x', _) -> x /= x') args)
--   Nothing -> Nothing

substitute :: Substitution -> Expr -> Expr
substitute _ Knd = Knd
substitute _ IntT = IntT
substitute _ NumT = NumT
substitute _ (Int i) = Int i
substitute _ (Num n) = Num n
substitute [] (Var x) = Var x
substitute ((x, a) : _) (Var x') | x == x' = a
substitute (_ : s) (Var x) = substitute s (Var x)
substitute _ (Tag k) = Tag k
substitute s (For x a) = For x (substitute (filter ((/= x) . fst) s) a)
substitute s (Fix x a) = Fix x (substitute (filter ((/= x) . fst) s) a)
substitute s (Fun a b) = Fun (substitute s a) (substitute s b)
substitute s (Lam p b) = Lam p (substitute (filter ((`elem` freeVars p) . fst) s) b)
substitute s (App a b) = App (substitute s a) (substitute s b)
substitute s (Or a b) = Or (substitute s a) (substitute s b)
substitute s (Ann (Tag k) ty) = Ann (Tag k) (substitute s ty)
substitute s (Ann a _) = substitute s a
substitute s (Op1 op a) = Op1 op (substitute s a)
substitute s (Op2 op a b) = Op2 op (substitute s a) (substitute s b)
substitute s (Meta m a) = Meta m (substitute s a)
substitute _ Err = Err

unify :: Expr -> Expr -> Either TypeError (Expr, Substitution)
unify IntT IntT = Right (IntT, [])
unify (Int _) IntT = Right (IntT, [])
unify IntT (Int _) = Right (IntT, [])
unify NumT NumT = Right (NumT, [])
unify (Num _) NumT = Right (NumT, [])
unify NumT (Num _) = Right (NumT, [])
unify (Int i) (Int i') | i == i' = Right (Int i, [])
unify (Num n) (Num n') | n == n' = Right (Num n, [])
unify (Var x) (Var x') | x == x' = Right (Var x, [])
unify (Tag k) (Tag k') | k == k' = Right (Tag k, [])
unify (Tag k) (Ann (Tag k') ty) | k == k' = Right (ty, [])
unify (Ann (Tag k) ty) (Tag k') | k == k' = Right (ty, [])
unify (Ann (Tag k) ty) (Ann (Tag k') ty') | k == k' = unify ty ty'
unify (Var x) b | x `occurs` b = Left (OccursError x b)
unify (Var x) b = Right (b, [(x, b)])
unify a (Var x) = unify (Var x) a
unify (Fun a1 b1) (Fun a2 b2) = do
  ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
  Right (Fun ta tb, s)
unify (Or a1 a2) b = case unify a1 b of
  Left _ -> case unify a2 b of
    Left _ -> Left (TypeMismatch (Or a1 a2) b)
    Right (a, s) -> Right (a, s)
  Right (a, s1) -> case unify a2 b of
    Left _ -> Right (a, s1)
    Right (b, s2) -> case unify (substitute s2 a) b of
      Left _ -> Right (a, s1)
      Right (c, s3) -> Right (c, s3 `compose` s2 `compose` s1)
unify a (Or b1 b2) = case unify a b1 of
  Left _ -> case unify a b2 of
    Left _ -> Left (TypeMismatch a (Or b1 b2))
    Right (a, s) -> Right (a, s)
  Right (a, s1) -> case unify a b2 of
    Left _ -> Right (a, s1)
    Right (b, s2) -> case unify (substitute s2 a) b of
      Left _ -> Right (b, s1)
      Right (c, s3) -> Right (c, s3 `compose` s2 `compose` s1)
unify (App a1 b1) (App a2 b2) = do
  ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
  Right (App ta tb, s)
unify (Op1 op a) (Op1 op' b) | op == op' = do
  (a', s) <- unify a b
  Right (Op1 op a', s)
unify (Op2 op a1 b1) (Op2 op' a2 b2) | op == op' = do
  ((a, b), s) <- unify2 (a1, a2) (b1, b2)
  Right (Op2 op a b, s)
unify (Meta _ a) b = unify a b
unify a (Meta _ b) = unify a b
unify a b = Left (TypeMismatch a b)

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either TypeError ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  (ta, s1) <- unify a1 a2
  (tb, s2) <- unify (substitute s1 b1) (substitute s1 b2)
  Right ((substitute s2 ta, tb), s2 `compose` s1)

unifyAll :: [Expr] -> [Expr] -> Either TypeError ([Expr], Substitution)
unifyAll (a : bs) (a' : bs') = do
  (ta, s1) <- unify a a'
  (tbs, s2) <- unifyAll bs bs'
  Right (ta : tbs, s2 `compose` s1)
unifyAll _ _ = Right ([], [])

unifyArgs :: [(String, Expr)] -> [(String, Expr)] -> Either TypeError ([(String, Expr)], Substitution)
unifyArgs (("", a) : args1) ((x, b) : args2) = do
  (ta, s1) <- unify a b
  (ts, s2) <- unifyArgs args1 args2
  Right ((x, ta) : ts, s2 `compose` s1)
unifyArgs ((x, a) : args1) (("", b) : args2) = do
  (ta, s1) <- unify a b
  (ts, s2) <- unifyArgs args1 args2
  Right ((x, ta) : ts, s2 `compose` s1)
unifyArgs ((x, a) : args1) args2 = case lookup x args2 of
  Just b ->
    unifyArgs (("", a) : args1) ((x, b) : filter (\(y, _) -> x /= y) args2)
  Nothing -> Left (UndefinedField x args2)
unifyArgs [] ((y, _) : _) = Left (UndefinedField y [])
unifyArgs [] [] = Right ([], [])

check :: Env -> Expr -> Expr -> Either TypeError (Expr, Substitution)
check env a (Var x) = do
  (t, s) <- infer env a
  Right (t, [(x, t)] `compose` s)
check env a (For x t) = do
  let (t', vars) = instantiate env (For x t)
  check (vars ++ env) a t'
check env a (Or t1 t2) = case check env a t1 of
  Left _ -> case check env a t2 of
    Left _ -> Left (TypeCheck a (Or t1 t2))
    Right (t, s) -> Right (t, s)
  Right (t1, s1) -> case check (s1 `compose` env) a t2 of
    Left _ -> Right (t1, s1)
    Right (t2, s2) -> Right (substitute s2 t1 `Or` t2, s2 `compose` s1)
check _ Knd Knd = Right (Knd, [])
check _ IntT Knd = Right (Knd, [])
check _ IntT IntT = Right (IntT, [])
check _ NumT Knd = Right (Knd, [])
check _ NumT NumT = Right (NumT, [])
check _ (Int _) IntT = Right (IntT, [])
check _ (Int i) (Int i') | i == i' = Right (Int i, [])
check _ (Num _) NumT = Right (NumT, [])
check _ (Num n) (Num n') | n == n' = Right (Num n, [])
check env (Var x) t = case lookup x env of
  Just (Var x') | x == x' -> Right (t, [(x, Ann (Var x) t)])
  Just (Ann (Var x') ty) | x == x' -> do
    let (ty', vars) = instantiate env ty
    (t', s) <- unify t ty'
    Right (t', s `compose` vars)
  Just a -> check env a t
  Nothing -> Left (UndefinedVar x)
check env (Tag k) t = case lookup k env of
  Just a -> check env a t
  Nothing -> Right (t, [])
check env (Or a b) t = do
  ((ta, tb), s1) <- check2 env (a, t) (b, t)
  case unify ta tb of
    Left _ -> Right (Or ta tb, s1)
    Right (t, s2) -> Right (t, s2 `compose` s1)
check env (Ann a ty) t = do
  (ta, s1) <- check env a ty
  (t', s2) <- unify ta (substitute s1 t)
  Right (t', s2 `compose` s1)
check env (For x a) t = check ((x, Var x) : env) a t
check env (Fix x a) t = check ((x, Var x) : env) a t
check env (Fun a b) (Fun ta tb) = do
  ((ta', tb'), s) <- check2 env (a, ta) (b, tb)
  Right (Fun ta' tb', s)
check env (Lam p b) (Fun tp tb) = do
  let env' = pushVars (freeVars p) env
  ((tp', tb'), s) <- check2 env' (toExpr p, tp) (b, tb)
  Right (Fun tp' tb', s)
check env (App a b) t = do
  (tb, s1) <- infer env b
  (_, s2) <- check (s1 `compose` env) a (Fun tb t)
  Right (substitute (s2 `compose` s1) t, s2 `compose` s1)
check env (Op1 op a) t = Right (t, [])
check env (Op2 op a b) t = Right (t, [])
check env (Meta _ a) t = check env a t
check _ Err Err = Right (Err, [])
check _ a t = Left (TypeCheck a t)

check2 :: Env -> (Expr, Expr) -> (Expr, Expr) -> Either TypeError ((Expr, Expr), Substitution)
check2 env (a, ta) (b, tb) = do
  (t1, s1) <- check env a ta
  (t2, s2) <- check (s1 `compose` env) b tb
  Right ((substitute s2 t1, t2), s2 `compose` s1)

infer :: Env -> Expr -> Either TypeError (Expr, Substitution)
infer _ Knd = Right (Knd, [])
infer _ IntT = Right (IntT `Or` Knd, [])
infer _ NumT = Right (NumT `Or` Knd, [])
infer _ (Int i) = Right (Int i `Or` IntT, [])
infer _ (Num n) = Right (Num n `Or` NumT, [])
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let y = newName (map fst env) (x ++ "T")
    Right (Var y, [(y, Var y), (x, Ann (Var x) (Var y))])
  Just (Ann (Var x') ty) | x == x' -> Right (instantiate env ty)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Tag k) = case lookup k env of
  Just (Tag k') | k == k' -> Right (Tag k, [])
  Just a -> infer env a
  Nothing -> Right (Tag k, [])
infer env (Or a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case unify ta tb of
    Left _ -> Right (Or ta tb, s1)
    Right (t, s2) -> Right (t, s2 `compose` s1)
infer env (Ann (Tag k) ty) = do
  let (t, vars) = instantiate env ty
  (t', s) <- unify (Ann (Tag k) t) (eval env t)
  Right (t', s `compose` vars)
infer env (Ann a ty) = check env a ty
infer env (For x a) = infer ((x, Var x) : env) a
infer env (Fix x a) = infer ((x, Var x) : env) a
infer env (Fun a b) = do
  ((ta, tb), s) <- infer2 env a b
  Right (Fun ta tb, s)
infer env (Lam p b) = do
  ((tp, tb), s) <- infer2 (pushVars (freeVars p) env) (toExpr p) b
  Right (Fun tp tb, s)
infer env (App a b) = do
  (ta, s1) <- infer env a
  case ta of
    Var x -> do
      let y = newName (map fst (s1 `compose` env)) x
      (tb, s2) <- infer (s1 `compose` env) b
      (t, s3) <- infer (s2 `compose` s1 `compose` env) (App (Ann a (For "y" $ Fun tb (Var y))) b)
      Right (t, (y, t) : s3 `compose` s2 `compose` s1)
    Fun t1 t2 -> do
      (_, s2) <- check (s1 `compose` env) b t1
      Right (substitute s2 t2, s2 `compose` s1)
    ta -> Left (NotAFunction a ta)
infer env (Op1 op a) = inferOp1 env op a
infer env (Op2 op a b) = inferOp2 env op a b
infer env (Meta _ a) = infer env a
infer _ Err = Right (Err, [])

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (s1 `compose` env) b
  Right ((substitute s2 ta, tb), s2 `compose` s1)

inferArgs :: Env -> [(String, Expr)] -> Either TypeError ([(String, Expr)], Substitution)
inferArgs _ [] = Right ([], [])
inferArgs env ((x, a) : args) = do
  (ta, s1) <- infer env a
  (ts, s2) <- inferArgs (s1 `compose` env) args
  Right ((x, substitute s2 ta) : ts, s2 `compose` s1)

inferAll :: Env -> [Expr] -> Either TypeError ([Expr], Substitution)
inferAll _ [] = Right ([], [])
inferAll env (a : bs) = do
  (t, s1) <- infer env a
  (ts, s2) <- inferAll (s1 `compose` env) bs
  Right (substitute s2 t : ts, s2 `compose` s1)

inferOp1 :: Env -> UnaryOp -> Expr -> Either TypeError (Expr, Substitution)
inferOp1 env Int2Num a = do
  (_, s) <- infer env (Ann a IntT)
  Right (NumT, s)

inferOp2 :: Env -> BinaryOp -> Expr -> Expr -> Either TypeError (Expr, Substitution)
inferOp2 env Add a b = do
  (_, s) <- check2 env (a, IntT) (b, IntT)
  Right (IntT, s)
inferOp2 env Sub a b = do
  (_, s) <- check2 env (a, IntT) (b, IntT)
  Right (IntT, s)
inferOp2 env Mul a b = do
  (_, s) <- check2 env (a, IntT) (b, IntT)
  Right (IntT, s)
inferOp2 env Pow a b = do
  (_, s) <- check2 env (a, IntT) (b, IntT)
  Right (IntT, s)
inferOp2 env Eq a b = do
  (ta, s1) <- infer env a
  (t, s2) <- infer (s1 `compose` env) (Ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Lt a b = do
  (ta, s1) <- infer env a
  (t, s2) <- infer (s1 `compose` env) (Ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Gt a b = do
  (ta, s1) <- infer env a
  (t, s2) <- infer (s1 `compose` env) (Ann b ta)
  Right (t, s2 `compose` s1)

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = apply s1 s2 `union` s1
  where
    apply :: Substitution -> Env -> Env
    apply _ [] = []
    apply s ((x, Ann a t) : env) = do
      (x, Ann (substitute s a) (substitute s t)) : apply s env
    apply s ((x, a) : env) = (x, substitute s a) : apply s env

instantiate :: Env -> Expr -> (Expr, Substitution)
instantiate env (For x a) = do
  let y = newName (map fst env) x
  let (b, s) = instantiate env (substitute [(x, Var y)] a)
  (b, [(y, Var y)] `union` s)
instantiate _ a = (a, [])

checkTypes :: Env -> [TypeError]
checkTypes env = do
  let checkDef (_, a) = case infer env a of
        Right _ -> []
        Left err -> [err]
  concatMap checkDef env

rename :: (Expr -> [String] -> String -> String) -> [String] -> Env -> Env -> Env
rename _ _ _ [] = []
rename f names env ((x, a) : env') = do
  let t = case infer env a of
        Right (t, _) -> t
        Left _ -> Err
  let y = f t (names ++ map fst env') x
  (y, eval [(x, Var y)] a) : rename f (y : names) env env'
