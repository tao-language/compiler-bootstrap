{-# LANGUAGE InstanceSigs #-}

module Core where

-- TODO: import Prelude() -- don't import prelude
-- TODO: {-# LANGUAGE NoImplicitPrelude #-}

import Data.List (foldl', union)
import Text.Read (readMaybe)

-- Lambda calculus: https://www.cse.iitk.ac.in/users/ppk/teaching/cs653/notes/lectures/Lambda-calculus.lhs.pdf
-- Closure calculus: https://youtu.be/ogXlQf8lDD4
-- Type inference from scratch: https://youtu.be/ytPAlhnAKro
-- Bidirectional type checking: https://youtu.be/utyBNDj7s2w

-- The Little Typer: https://thelittletyper.com
-- Epigram: http://www.e-pig.org/ http://www.e-pig.org/downloads/view.pdf
-- Implementing dependent types: https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf
-- Complete and Easy: https://arxiv.org/pdf/1306.6032.pdf https://arxiv.org/abs/1306.6032

-- TODO: TaoLang: parse type annotations
-- TODO: TaoLang: do-notation, monadas, effects, I/O
-- TODO: TaoLang: tuples and records
-- TODO: TaoLang: support types (tagged unions, type alias)
-- TODO: Tao: modules and stdlib (files, parser, compiler)
-- TODO: Tao: show and pretty formatting
-- TODO: self compiling compiler
-- TODO: Core: add source code locations
-- TODO: Core: pretty print error messages
data Expr
  = IntT
  | Typ !Int
  | Int !Int
  | Var !String
  | Lam !Env !String !Expr
  | App !Expr !Expr
  | Fun !Expr !Expr
  | Ann !Expr !Expr
  | For !String !Expr
  | Fix !String !Expr
  | Call !String !Expr
  | Add
  | Sub
  | Mul
  | Eq
  deriving (Eq)

data Pattern
  = PAny
  | PVar !String
  | PCtr !String ![Pattern]
  deriving (Eq, Show)

type Env = [(String, Expr)]

data TypeError
  = UndefinedVar !String
  | NotAFunction !Expr !Expr
  | NotAType !Expr !Expr
  | InfiniteType !String !Expr
  | TypeMismatch !Expr !Expr
  deriving (Eq, Show)

-- TODO: clean up
instance Show Expr where
  show IntT = "@Int"
  show (Typ u) = "@Type[" ++ show u ++ "]"
  show (Int i) = show i
  show (Var x) = x
  show (Lam _ x a) = do
    -- TODO: show env
    let vars :: Expr -> [String] -> ([String], Expr)
        vars (Lam _ x a) xs = let (xs', a') = vars a xs in (x : xs', a')
        vars a xs = (xs, a)
    let (xs, a') = vars a []
    "\\" ++ unwords (x : xs) ++ ". " ++ show a'
  -- show (App (Lam env x a) (App Fix (Lam env' x' b))) | x == x' = "#letrec " ++ x ++ " = " ++ show b ++ "; " ++ show a
  show (App (Lam [] x a) b) = "@let " ++ x ++ " = " ++ show b ++ "; " ++ show a
  show (App a b@App {}) = show a ++ " (" ++ show b ++ ")"
  show (App a b@Lam {}) = show a ++ " (" ++ show b ++ ")"
  show (App a b) = show a ++ " " ++ show b
  show (Fun a b) = show a ++ " => " ++ show b
  show (Ann a t) = "(" ++ show a ++ " : " ++ show t ++ ")"
  show (For x a) = do
    let vars :: Expr -> [String] -> ([String], Expr)
        vars (For x a) xs = let (xs', a') = vars a xs in (x : xs', a')
        vars a xs = (xs, a)
    let (xs, a') = vars a []
    "@for " ++ unwords (x : xs) ++ ". " ++ show a'
  show (Fix x a) = "@fix " ++ show x ++ " (" ++ show a ++ ")"
  show (Call f t) = "@(" ++ f ++ " : " ++ show t ++ ")"
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Eq = "=="

-- Syntax sugar --
lam :: [String] -> Expr -> Expr
lam xs a = foldr (Lam []) a xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

fun :: [Expr] -> Expr -> Expr
fun xs a = foldr Fun a xs

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

let' :: (String, Expr) -> Expr -> Expr
let' (x, a) b = App (Lam [] x b) a

add :: Expr -> Expr -> Expr
add a b = app Add [a, b]

sub :: Expr -> Expr -> Expr
sub a b = app Sub [a, b]

mul :: Expr -> Expr -> Expr
mul a b = app Mul [a, b]

eq :: Expr -> Expr -> Expr
eq a b = app Eq [a, b]

-- Evaluation --
reduce :: Env -> Expr -> Expr
reduce env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just a -> reduce env a
  Nothing -> Var x
reduce env (Lam env' x a) = Lam (env' ++ env) x a
reduce env (App a b) = case (reduce env a, reduce env b) of
  (Lam env x a, b) -> reduce ((x, b) : env) a
  (App op a, b) -> case (op, reduce env a, b) of
    (Add, Int a, Int b) -> Int (a + b)
    (Sub, Int a, Int b) -> Int (a - b)
    (Mul, Int a, Int b) -> Int (a * b)
    (Eq, Int a, Int b) | a == b -> Lam [] "T" (Lam [] "F" (Var "T"))
    (Eq, Int _, Int _) -> Lam [] "T" (Lam [] "F" (Var "F"))
    (_, a, b) -> App (App op a) b
  (Fix x a, b) -> reduce ((x, Fix x a) : env) (App a b)
  (a, b) -> App a b
reduce env (Fun a b) = Fun (reduce env a) (reduce env b)
reduce env (Ann a _) = reduce env a
reduce _ a = a

eval :: Env -> Expr -> Expr
eval env a = case reduce env a of
  Lam env x a -> Lam [] x (eval ((x, Var x) : env) a)
  App a b -> App (eval [] a) (eval [] b)
  Fix x a -> case eval ((x, Var x) : env) a of
    Var x' | x == x' -> Var x
    a | x `occurs` a -> Fix x a
    a -> a
  a -> a

-- Type checking --
occurs :: String -> Expr -> Bool
occurs x (Var y) = x == y
occurs x (Lam env y a) | x /= y && x `notElem` map fst env = occurs x a
occurs x (App a b) = occurs x a || occurs x b
occurs x (Fun a b) = occurs x a || occurs x b
occurs x (Ann a _) = occurs x a
occurs x (For y a) | x /= y = occurs x a
occurs _ _ = False

substitute :: String -> Expr -> Expr -> Expr
substitute x a (Var x') | x == x' = a
substitute x a (Lam env y b) | x /= y && x `notElem` map fst env = Lam env y (substitute x a b)
substitute x a (App b1 b2) = App (substitute x a b1) (substitute x a b2)
substitute x a (Fun b1 b2) = Fun (substitute x a b1) (substitute x a b2)
-- TODO: Ann
-- TODO: For
substitute _ _ b = b

instantiate :: Env -> Expr -> (Expr, Env)
instantiate env (For x t) = do
  let y = newName (map fst env) x
  instantiate ((y, Var y) : env) (substitute x (Var y) t)
instantiate env t = (t, env)

unify :: Env -> Expr -> Expr -> Either TypeError Env
unify env a b = case (reduce env a, reduce env b) of
  (Var x, Var x') | x == x' -> Right env
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> Right ((x, b) : env)
  (a, Var x) | x `occurs` a -> Left (InfiniteType x a)
  (a, Var x) -> Right ((x, a) : env)
  -- TODO: Lam (alpha equivalence?)
  (App a1 a2, App b1 b2) -> unify2 env (a1, b1) (a2, b2)
  (Fun a1 a2, Fun b1 b2) -> unify2 env (a1, b1) (a2, b2)
  -- TODO: Ann
  -- TODO: For
  -- (Fix, Fix) -> Right env
  (a, a') | a == a' -> Right env
  (a, b) -> Left (TypeMismatch a b)

unify2 :: Env -> (Expr, Expr) -> (Expr, Expr) -> Either TypeError Env
unify2 env (a1, b1) (a2, b2) = do
  env <- unify env a1 b1
  unify env a2 b2

infer :: Env -> Expr -> Either TypeError (Expr, Env)
infer env IntT = Right (Typ 0, env)
infer env (Typ u) = Right (Typ (u + 1), env)
infer env (Int _) = Right (IntT, env)
infer env (Var x) = case lookup x env of
  Just (Ann (Var x') t) | x == x' -> Right (t, env)
  Just (Var x') | x == x' -> Right (Var x, env)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Lam env' x a) = do
  let tx = newName (x : map fst env) x
  (t2, env) <- infer ((tx, Var tx) : (x, Ann (Var x) (Var tx)) : env' ++ env) a
  Right (Fun (reduce env (Var tx)) (reduce env t2), env)
infer env (App a b) = do
  (ta, env) <- infer env a
  (tb, env) <- infer env b
  case instantiate env ta of
    (Fun t1 t2, env) -> do
      env <- unify env t1 tb
      Right (reduce env t2, env)
    _notAFunction -> Left (NotAFunction a ta)
infer env (Fun a b) = do
  _ <- infer env a
  _ <- infer env b
  Right (Typ 0, env)
infer env (Ann a t) = do
  (k, env) <- infer env t
  case k of
    Typ _ -> do
      (ta, env) <- infer env a
      env <- unify env t ta
      Right (reduce env t, env)
    k -> Left (NotAType t k)
infer env (For x a) = do
  _ <- infer ((x, Var x) : env) a
  Right (Typ 0, env)
infer env (Fix x a) = infer ((x, Ann (Var x) (for ["a", "b"] (Fun (Var "a") (Var "b")))) : env) a
infer env (Call _ t) = Right (t, env)
infer env Add = Right (For "a" (fun [Var "a", Var "a"] (Var "a")), env)
infer env Sub = Right (For "a" (fun [Var "a", Var "a"] (Var "a")), env)
infer env Mul = Right (For "a" (fun [Var "a", Var "a"] (Var "a")), env)
infer env Eq = Right (For "a" (fun [Var "a", Var "a"] (For "b" (fun [Var "b", Var "b"] (Var "b")))), env)

-- Helper functions --
freeVariables :: Expr -> [String]
freeVariables (Var x) = [x]
freeVariables (Lam env x a) = filter (\y -> y /= x && y `notElem` map fst env) (freeVariables a)
freeVariables (App a b) = freeVariables a `union` freeVariables b
freeVariables (Fun a b) = freeVariables a `union` freeVariables b
-- TODO: Ann
-- TODO: Fun
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
