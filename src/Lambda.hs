module Lambda where

-- TODO: import Prelude() -- don't import prelude
-- TODO: {-# LANGUAGE NoImplicitPrelude #-}

import Data.List (union)
import Text.Read (readMaybe)

-- Lambda calculus: https://www.cse.iitk.ac.in/users/ppk/teaching/cs653/notes/lectures/Lambda-calculus.lhs.pdf
-- Closure calculus: https://youtu.be/ogXlQf8lDD4
-- Type inference from scratch: https://youtu.be/ytPAlhnAKro
-- Bidirectional type checking: https://youtu.be/utyBNDj7s2w

-- The Little Typer: https://thelittletyper.com
-- Epigram: http://www.e-pig.org/ http://www.e-pig.org/downloads/view.pdf
-- Implementing dependent types: https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf
-- Complete and Easy: https://arxiv.org/pdf/1306.6032.pdf https://arxiv.org/abs/1306.6032

-- TODO: Lambda: reduce recursive functions to normal form
-- TODO: Core: support types and ADTs like Bool, Maybe, List, Vec, Tuples and Records
-- TODO: Core: do-notation, monadas, effects, I/O
-- TODO: Tao: support types (tagged unions, type alias)
-- TODO: Tao: modules and stdlib (files, parser, compiler)
-- TODO: self compiling compiler
data Expr
  = IntT
  | Typ !Int
  | Int !Int
  | Var !String
  | Lam !Env !String !Expr
  | App !Expr !Expr
  | Fun !Expr !Expr
  | Ann !Expr !Type
  | Call !String
  | Fix !String !Expr
  deriving (Eq, Show)

data Type
  = T ![String] !Expr
  deriving (Eq, Show)

type Env = [(String, Expr)]

-- instance Show Expr where
--   show IntT = "#Int"
--   show (Typ u) = "#Type{" ++ show u ++ "}"
--   show (Int i) = show i
--   show (Var x) = x
--   show (Lam env x a) = do
--     let vars :: Expr -> [String] -> ([String], Expr)
--         vars (Lam env x a) xs = let (xs', a') = vars a xs in (x : xs', a')
--         vars a xs = (xs, a)
--     let (xs, a') = vars a []
--     "\\" ++ unwords (x : xs) ++ ". " ++ show a'
--   show (App (Lam env x a) (App Fix (Lam env' x' b))) | x == x' = "#letrec " ++ x ++ " = " ++ show b ++ "; " ++ show a
--   show (App (Lam env x a) b) = "#let " ++ x ++ " = " ++ show b ++ "; " ++ show a
--   show (App a b@App {}) = show a ++ " (" ++ show b ++ ")"
--   show (App a b@Lam {}) = show a ++ " (" ++ show b ++ ")"
--   show (App a b) = show a ++ " " ++ show b
--   show (Call f) = "&" ++ f
--   show Fix = "#fix"
--   show (Ann a t) = show a ++ " : " ++ show t
--   show (Fun a b) = show a ++ " => " ++ show b

-- Syntax sugar
lam :: [String] -> Expr -> Expr
lam xs a = foldr (Lam []) a xs

app :: Expr -> [Expr] -> Expr
app = foldl App

fun :: [Expr] -> Expr -> Expr
fun xs a = foldr Fun a xs

add :: Expr -> Expr -> Expr
add a b = app (Call "+") [a, b]

sub :: Expr -> Expr -> Expr
sub a b = app (Call "-") [a, b]

mul :: Expr -> Expr -> Expr
mul a b = app (Call "*") [a, b]

eq :: Expr -> Expr -> Expr
eq a b = app (Call "==") [a, b]

let' :: Env -> Expr -> Expr
let' env a = reduce a (map (\(x, b) -> (x, eval (Fix x b) env)) env)

-- Evaluation --
reduce :: Expr -> Env -> Expr
reduce (Var x) env = case lookup x env of
  Just a -> reduce a []
  Nothing -> Var x
reduce (Lam env x a) env' = Lam (env ++ env') x a
reduce (App a b) env = case (reduce a env, reduce b env) of
  (Lam env x a, b) -> reduce a ((x, b) : env)
  -- (Ann a (T xs (Fun _ t)), b) -> Ann (App a b) (T xs t)
  (App (Call f) a, b) -> case (f, reduce a env, b) of
    ("+", Int a, Int b) -> Int (a + b)
    ("-", Int a, Int b) -> Int (a - b)
    ("*", Int a, Int b) -> Int (a * b)
    ("==", Int a, Int b) | a == b -> lam ["T", "F"] (Var "T")
    ("==", Int _, Int _) -> lam ["T", "F"] (Var "F")
    (_, a, b) -> app (Call f) [a, b]
  (Fix x a, b) -> reduce (App a b) ((x, Fix x a) : env)
  (a, b) -> App a b
reduce (Fun a b) env = Fun (reduce a env) (reduce b env)
reduce (Ann a typ) env = case reduce a env of
  Var x -> Ann (Var x) typ
  a -> a
reduce a _ = a

eval :: Expr -> Env -> Expr
eval a env = case reduce a env of
  Lam env x a -> Lam [] x (eval a ((x, Var x) : env))
  App a b -> App (eval a []) (eval b [])
  Fix x a -> case eval a ((x, Var x) : env) of
    a | x `occurs` a -> Fix x a
    a -> a
  a -> a

-- Type checking --
occurs :: String -> Expr -> Bool
occurs x (Var y) = x == y
occurs x (Lam env y a) | x /= y && x `notElem` map fst env = occurs x a
occurs x (App a b) = occurs x a || occurs x b
occurs x (Fun a b) = occurs x a || occurs x b
-- occurs x (Ann a (T xs b)) | x `notElem` xs = occurs x a || occurs x b
occurs _ _ = False

substitute :: String -> Expr -> Expr -> Expr
substitute x a (Var x') | x == x' = a
substitute x a (Lam env y b) | x /= y && x `notElem` map fst env = Lam env y (substitute x a b)
substitute x a (App b1 b2) = App (substitute x a b1) (substitute x a b2)
substitute x a (Fun b1 b2) = Fun (substitute x a b1) (substitute x a b2)
-- TODO: Ann
substitute _ _ b = b

instantiate :: Type -> Env -> (Expr, Env)
instantiate (T [] a) env = (a, env)
instantiate (T (x : xs) a) env = do
  let x' = newName (map fst env) x
  let a' = substitute x (Var x') a
  instantiate (T xs a') ((x', Var x') : env)

unify :: Expr -> Expr -> Env -> Maybe Env
unify a b env = case (reduce a env, reduce b env) of
  (IntT, IntT) -> Just env
  (Typ u, Typ u') | u == u' -> Just env
  (Int i, Int i') | i == i' -> Just env
  (Var x, Var x') | x == x' -> Just env
  (Var x, b) | x `occurs` b -> Nothing
  (Var x, b) -> Just ((x, b) : env)
  (a, Var x) | x `occurs` a -> Nothing
  (a, Var x) -> Just ((x, a) : env)
  -- TODO: Lam (alpha equivalence?)
  (App a1 a2, App b1 b2) -> unify2 (a1, b1) (a2, b2) env
  -- TODO: Ann
  (Fun a1 a2, Fun b1 b2) -> unify2 (a1, b1) (a2, b2) env
  -- (Fix, Fix) -> Just env
  _typeMismatch -> Nothing

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Env -> Maybe Env
unify2 (a1, b1) (a2, b2) env = do
  env <- unify a1 b1 env
  unify a2 b2 env

infer :: Expr -> Env -> Maybe (Expr, Env)
infer IntT env = Just (Typ 0, env)
infer (Typ u) env = Just (Typ (u + 1), env)
infer (Int _) env = Just (IntT, env)
infer (Var x) env = case lookup x env of
  Just (Ann (Var x') typ) | x == x' -> Just (instantiate typ env)
  Just (Var x') | x == x' -> Just (Var x, env)
  Just a -> infer a env
  Nothing -> Nothing
infer (Lam _ x a) env = do
  let tx = newName (map fst env) x
  (t2, env) <- infer a ((x, Var tx) : (tx, Var tx) : env)
  (t1, env) <- infer (Var tx) env
  Just (Fun t1 (reduce t2 env), env)
infer (App a b) env = do
  (ta, env) <- infer a env
  (tb, env) <- infer b env
  case ta of
    Fun t1 t2 -> do
      env <- unify t1 tb env
      Just (reduce t2 env, env)
    _notAFunction -> Nothing
infer (Fun a b) env = do
  _ <- infer a env
  _ <- infer b env
  Just (Typ 0, env)
infer (Ann a typ) env = do
  let (t, env') = instantiate typ env
  (ta, env) <- infer a env'
  env <- unify t ta env
  Just (reduce t env, env)
infer (Call f) env = Just (instantiate (T [f] (Var f)) env)
infer (Fix _ a) env = infer a env

-- Helper functions --
freeVariables :: Expr -> [String]
freeVariables (Var x) = [x]
freeVariables (Lam env x a) = filter (\y -> y /= x && y `notElem` map fst env) (freeVariables a)
freeVariables (App a b) = freeVariables a `union` freeVariables b
freeVariables (Fun a b) = freeVariables a `union` freeVariables b
-- TODO: Ann
freeVariables _ = []

newName :: [String] -> String -> String
newName existing x = case findNameIdx existing x of
  Just i -> x ++ show (i + 1)
  Nothing -> x

readNameIdx :: String -> String -> Maybe Int
readNameIdx "" x = readMaybe x
readNameIdx (ch : prefix) (ch' : x) | ch == ch' = readNameIdx prefix x
readNameIdx _ _ = Nothing

findNameIdx :: [String] -> String -> Maybe Int
findNameIdx [] _ = Nothing
findNameIdx (x : xs) prefix = case findNameIdx xs prefix of
  Just i -> case readNameIdx prefix x of
    Just j -> Just (max i j)
    Nothing -> Just i
  Nothing -> if prefix == x then Just 0 else readNameIdx prefix x

delete :: Eq a => a -> [a] -> [a]
delete _ [] = []
delete x (x' : xs) | x == x' = delete x xs
delete x (y : xs) = y : delete x xs
