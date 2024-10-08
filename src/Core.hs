module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.Function ((&))
import Data.List (delete, intercalate, union)
import Stdlib (replace, replaceString)

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
  | App Expr Expr
  | And Expr Expr
  | Or Expr Expr
  | Ann Expr Expr
  | Call String [Expr]
  | Meta Metadata Expr
  | Err
  deriving (Eq)

data Metadata
  = Location String (Int, Int)
  | Comment String
  | Unwrap
  deriving (Eq)

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

data Package = Package
  { name :: String,
    modules :: [(String, Module)]
  }

data Module = Module
  { public :: Env,
    private :: Env,
    types :: Env,
    tests :: [UnitTest]
  }

data UnitTest = UnitTest
  { name :: String,
    expr :: Expr,
    expect :: Expr
  }

data TestError = TestError
  { test :: UnitTest,
    got :: Expr
  }

instance Show Expr where
  showsPrec :: Int -> Expr -> ShowS
  showsPrec p expr = case expr of
    -- App (Lam [Case [p] b]) a -> prefix 1 (show p ++ " = " ++ show a ++ "; ") b
    Or a b -> infixR 1 a " | " b
    And a b -> infixL 1 a ", " b
    Ann a b -> infixR 2 a " : " b
    Call "==" [a, b] -> infixL 3 a " == " b
    Call "<" [a, b] -> infixR 4 a " < " b
    Call ">" [a, b] -> infixR 4 a " > " b
    For x a -> do
      let (xs, a') = asFor (For x a)
      prefix 2 ("@" ++ unwords xs ++ ". ") a'
    Fix x a -> prefix 2 ("!fix " ++ show (Var x) ++ ". ") a
    Fun p b -> infixR 5 p " -> " b
    Call "+" [a, b] -> infixL 6 a " + " b
    Call "-" [a, b] -> infixL 6 a " - " b
    Call "*" [a, b] -> infixL 7 a " * " b
    Call "/" [a, b] -> infixL 7 a " / " b
    Call "^" [a, b] -> infixL 10 a "^" b
    Call ('$' : op) [a] -> prefix 8 ('$' : op ++ " ") a
    Call op [a] -> prefix 8 op a
    App a b -> infixL 8 a " " b
    Err -> atom 12 "!error"
    Knd -> atom 12 "!Kind"
    IntT -> atom 12 "!Int"
    NumT -> atom 12 "!Num"
    Int i -> atom 12 (show i)
    Num n -> atom 12 (show n)
    Var x | isVarName x -> atom 12 x
    Var x -> atom 12 ("`" ++ replaceString "`" "\\`" x ++ "`")
    Tag "" -> atom 12 "()"
    Tag k -> atom 12 k
    Call op [] -> atom 12 ("(" ++ op ++ ")")
    Call op args -> showsPrec p (app (Call op []) args)
    Meta m a -> prefix p ("#(" ++ show m ++ ")") a
    where
      atom n k = showParen (p > n) $ showString k
      prefix n k a = showParen (p > n) $ showString k . showsPrec (n + 1) a
      infixL n a op b = showParen (p > n) $ showsPrec n a . showString op . showsPrec (n + 1) b
      infixR n a op b = showParen (p > n) $ showsPrec (n + 1) a . showString op . showsPrec n b
      isVarName ('!' : xs) = all isNameChar xs
      isVarName ('@' : xs) = True
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

instance Show Metadata where
  show :: Metadata -> String
  show (Location src (row, col)) = src ++ ':' : show row ++ ':' : show col

-- Syntax sugar
intT :: Int -> Expr
intT i = Int i `Or` IntT

numT :: Double -> Expr
numT n = Num n `Or` NumT

tag :: String -> [Expr] -> Expr
tag k args = and' (Tag k : args)

-- ptag :: String -> [Pattern] -> Pattern
-- ptag k = pApp (PTag k)

fix :: [String] -> Expr -> Expr
fix [] a = a
fix (x : xs) a
  | x `occurs` a = Fix x (fix xs a)
  | otherwise = fix xs a

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

asFor :: Expr -> ([String], Expr)
asFor (For x a) = let (xs, b) = asFor a in (x : xs, b)
asFor a = ([], a)

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

lam :: [Expr] -> Expr -> Expr
lam ps b = for (freeVars ps) (fun ps b)

asFun :: Expr -> ([Expr], Expr)
asFun (Fun arg ret) = let (args, ret') = asFun ret in (arg : args, ret')
asFun a = ([], a)

add :: Expr -> Expr -> Expr
add a b = Call "+" [a, b]

and' :: [Expr] -> Expr
and' [] = Err
and' [a] = a
and' (a : bs) = And a (and' bs)

andOf :: Expr -> [Expr]
andOf (And a b) = a : andOf b
andOf a = [a]

sub :: Expr -> Expr -> Expr
sub a b = Call "-" [a, b]

mul :: Expr -> Expr -> Expr
mul a b = Call "*" [a, b]

pow :: Expr -> Expr -> Expr
pow a b = Call "^" [a, b]

eq :: Expr -> Expr -> Expr
eq a b = Call "==" [a, b]

lt :: Expr -> Expr -> Expr
lt a b = Call "<" [a, b]

gt :: Expr -> Expr -> Expr
gt a b = Call ">" [a, b]

int2num :: Expr -> Expr
int2num a = Call "$i2n" [a]

let' :: (Expr, Expr) -> Expr -> Expr
let' (Var x, Var x') b | x == x' = b
let' (p, a) b = do
  let xs = filter (`occurs` a) (freeVars p)
  App (lam [p] b) (fix xs a)

lets :: [(Expr, Expr)] -> Expr -> Expr
lets defs b = foldr let' b defs

app :: Expr -> [Expr] -> Expr
app = foldl App

-- appOf :: Expr -> (Expr, [Expr])
-- appOf (App a b) = let (a', bs) = appOf a in (a', bs ++ [b])
-- appOf a = (a, [])

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

list :: Expr -> Expr -> [Expr] -> Expr
list _ nil [] = nil
list cons nil (a : bs) = app cons [a, list cons nil bs]

match' :: [Expr] -> [([Expr], Expr)] -> Expr
match' args cases = app (matchFun cases) args

matchFun :: [([Expr], Expr)] -> Expr
matchFun [] = Err
matchFun [(ps, b)] = fun ps b
matchFun ((ps, b) : cases) = fun ps b `Or` matchFun cases

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
  freeVars (App a b) = freeVars a `union` freeVars b
  freeVars (And a b) = freeVars a `union` freeVars b
  freeVars (Or a b) = freeVars a `union` freeVars b
  freeVars (Ann a _) = freeVars a
  freeVars (Call _ args) = foldr (union . freeVars) [] args
  freeVars (Meta _ a) = freeVars a
  freeVars Err = []

instance FreeVars [Expr] where
  freeVars :: [Expr] -> [String]
  freeVars [] = []
  freeVars (a : bs) = freeVars a `union` freeVars bs

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
  Just (Ann (Var x') _) | x == x' -> Var x
  Just a -> eval env a
  Nothing -> Var x
eval env (Tag k) = Tag k
eval env (For x a) = For x (eval ((x, Var x) : env) a)
eval env (Fix x a) = Fix x (eval ((x, Var x) : env) a)
eval env (Fun a b) = Fun (eval env a) (eval env b)
eval env (App a b) = case (eval env a, eval env b) of
  (For x a, b) -> eval [(x, Var x)] (App a b)
  (Fix x a, b) | isClosed b -> eval [(x, Fix x a)] (App a b)
  (Tag k, b) -> And (Tag k) b
  (And a b, c) -> And a (And b c)
  (Err, _) -> Err
  (Fun a c, b) -> case match a b of
    Just bindings -> eval bindings c
    Nothing -> Err
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err -> eval [] (App a2 b)
    a | isOpen a -> Or a (App a2 b)
    a -> a
  (a, b) -> App a b
eval env (And a b) = And (eval env a) (eval env b)
eval env (Or a b) = Or (eval env a) (eval env b)
eval env (Ann (Tag k) ty) = Ann (Tag k) (eval env ty)
eval env (Ann a _) = eval env a
eval env (Call op args) = case (op, map (eval env) args) of
  ("+", [Int a, Int b]) -> Int (a + b)
  ("-", [Int a, Int b]) -> Int (a - b)
  ("*", [Int a, Int b]) -> Int (a * b)
  ("^", [Int a, Int b]) -> Int (a ^ b)
  (op, args) -> Call op args
eval env (Meta _ a) = eval env a
eval _ Err = Err

match :: Expr -> Expr -> Maybe [(String, Expr)]
match IntT IntT = Just []
match NumT NumT = Just []
match (Int i) (Int i') | i == i' = Just []
match (Num n) (Num n') | n == n' = Just []
match (Var x) b = Just [(x, b)]
match (And p q) (And a b) = match2 (p, a) (q, b)
match (Tag k) (Tag k') | k == k' = Just []
match (Fun p q) (Fun a b) = match2 (p, a) (q, b)
match (Meta _ p) b = match p b
match Err Err = Just []
match _ _ = Nothing

match2 :: (Expr, Expr) -> (Expr, Expr) -> Maybe [(String, Expr)]
match2 (p, a) (q, b) = do
  env1 <- match p a
  env2 <- match q b
  Just (env1 ++ env2)

matchAll :: [Expr] -> [Expr] -> Maybe [(String, Expr)]
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
substitute s (Tag k) = Tag k
substitute s (For x a) = For x (substitute (filter ((/= x) . fst) s) a)
substitute s (Fix x a) = Fix x (substitute (filter ((/= x) . fst) s) a)
substitute s (Fun a b) = Fun (substitute s a) (substitute s b)
substitute s (App a b) = App (substitute s a) (substitute s b)
substitute s (And a b) = And (substitute s a) (substitute s b)
substitute s (Or a b) = Or (substitute s a) (substitute s b)
substitute s (Ann (Tag k) ty) = Ann (Tag k) (substitute s ty)
substitute s (Ann a _) = substitute s a
substitute s (Call op args) = Call op (map (substitute s) args)
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
unify (Ann (Tag _) ty) ty' = unify ty ty'
unify ty (Ann (Tag _) ty') = unify ty ty'
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
unify (Call op args) (Call op' args') | op == op' = do
  (args, s) <- unifyAll args args'
  Right (Call op args, s)
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
  (tbs, s2) <- unifyAll (map (substitute s1) bs) (map (substitute s1) bs')
  Right (ta : tbs, s2 `compose` s1)
unifyAll _ _ = Right ([], [])

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
check env (App a b) t = do
  (tb, s1) <- infer env b
  (_, s2) <- check (s1 `compose` env) a (Fun tb t)
  Right (substitute (s2 `compose` s1) t, s2 `compose` s1)
check env (Call op args) t = case lookup op env of
  Just a -> check env (app a args) t
  Nothing -> Right (t, []) -- TODO: check args
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
infer env (And a b) = do
  ((ta, tb), s) <- infer2 env a b
  Right (And ta tb, s)
infer env (Ann (Tag k) ty) = do
  let (t, vars) = instantiate env ty
  (t', s) <- unify (Ann (Tag k) t) (eval env t)
  Right (t', s `compose` vars)
infer env (Ann a ty) = check env a ty
infer env (For x a) = infer ((x, Var x) : env) a
infer env (Fix x a) = do
  (t, s) <- infer ((x, Var x) : env) a
  Right (Fix x t, s)
infer env (Fun a b) = do
  ((ta, tb), s) <- infer2 env a b
  Right (Fun ta tb, s)
infer env (App a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case ta of
    Var x -> do
      let y = newName (map fst (s1 `compose` env)) x
      (t, s2) <- infer (s1 `compose` env) (App (Ann a (For y $ Fun tb (Var y))) b)
      Right (t, (y, t) : s2 `compose` s1)
    Tag k -> Right (Tag k, s1)
    Fun t1 t2 -> do
      (_, s2) <- unify tb t1
      Right (substitute s2 t2, s2 `compose` s1)
    ta -> Left (NotAFunction a ta)
infer env (Call op args) = case lookup op env of
  Just a -> infer env (app a args)
  Nothing -> do
    let y = newName (map fst env) (op ++ "T")
    Right (Var y, [(y, Var y), (op, Ann (Call op []) (Var y))])
infer env (Meta m a) = do
  (t, s) <- infer env a
  Right (Meta m t, s)
infer _ Err = Right (Err, [])

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (s1 `compose` env) b
  Right ((substitute s2 ta, tb), s2 `compose` s1)

inferAll :: Env -> [Expr] -> Either TypeError ([Expr], Substitution)
inferAll _ [] = Right ([], [])
inferAll env (a : bs) = do
  (t, s1) <- infer env a
  (ts, s2) <- inferAll (s1 `compose` env) bs
  Right (substitute s2 t : ts, s2 `compose` s1)

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

class DropMeta a where
  dropMeta :: a -> a

instance DropMeta Expr where
  dropMeta :: Expr -> Expr
  dropMeta Knd = Knd
  dropMeta IntT = IntT
  dropMeta NumT = NumT
  dropMeta (Int i) = Int i
  dropMeta (Num n) = Num n
  dropMeta (Var x) = Var x
  dropMeta (Tag k) = Tag k
  dropMeta (For x a) = For x (dropMeta a)
  dropMeta (Fix x a) = Fix x (dropMeta a)
  dropMeta (Fun a b) = Fun (dropMeta a) (dropMeta b)
  dropMeta (App a b) = App (dropMeta a) (dropMeta b)
  dropMeta (And a b) = And (dropMeta a) (dropMeta b)
  dropMeta (Or a b) = Or (dropMeta a) (dropMeta b)
  dropMeta (Ann a t) = Ann (dropMeta a) (dropMeta t)
  dropMeta (Call op args) = Call op (map dropMeta args)
  dropMeta (Meta _ a) = dropMeta a
  dropMeta Err = Err

instance DropMeta (String, Expr) where
  dropMeta :: (String, Expr) -> (String, Expr)
  dropMeta (x, a) = (x, dropMeta a)

-- test :: Env -> Expr -> Expr -> Either Expr ()
-- test env expr expected = do
--   let actual = eval env expr
--   let test' = match' [actual] [([expected], Tag "")]
--   case eval env test' of
--     Err -> Left actual
--     _ -> Right ()

class Test a where
  test :: Env -> a -> [TestError]

instance Test Module where
  test :: Env -> Module -> [TestError]
  test env mod = do
    let env' = mod.public ++ mod.private ++ env
    concatMap (test env') mod.tests

instance Test UnitTest where
  test :: Env -> UnitTest -> [TestError]
  test env t = do
    let got = eval env t.expr
    let test' = match' [got] [([t.expect], Tag "")]
    case eval env test' of
      Err -> [TestError {test = t, got = got}]
      _ -> []
