module Core where

import Data.List (foldl', intercalate)

data Term
  = Err
  | TypT
  | BoolT
  | IntT
  | Int !Int
  | TupT ![Term]
  | RecT ![(String, Term)]
  | SumT ![(String, Term)] ![Alt]
  | NamT !String ![Term]
  | Var !String
  | ForT !String !Term
  | FunT !Term !Term
  | Lam !Env !String !Term
  | App !Term !Term
  | Fix !String !Term
  | Op !Operator
  deriving (Eq)

data Operator
  = Add
  | Sub
  | Mul
  | Eq
  | Call !String !Term
  deriving (Eq)

type Env = [(String, Term)]

type Alt = (String, ([String], Term))

-- TODO: clean up
instance Show Term where
  show Err = "@error"
  show TypT = "@Type"
  show BoolT = "@Bool"
  show IntT = "@Int"
  show (Int i) = show i
  show (TupT items) =
    "@Tuple (" ++ intercalate ", " (map show items) ++ ")"
  show (RecT fields) = do
    let showField (x, a) = x ++ " : " ++ show a
    "@Record (" ++ intercalate ", " (map showField fields) ++ ")"
  show (SumT vars alts) = do
    let showVar (x, t) = "(" ++ x ++ " : " ++ show t ++ ")"
    let showAlt (c, ([], t)) = c ++ " : " ++ show t
        showAlt (c, (args, t)) = c ++ " " ++ unwords args ++ " : " ++ show t
    "@Union (" ++ intercalate ", " (map showVar vars) ++ ") {" ++ intercalate " | " (map showAlt alts) ++ "}"
  show (NamT name args) =
    "@Named " ++ name ++ " (" ++ intercalate ", " (map show args) ++ ")"
  show (Var x) = x
  show (ForT x a) = do
    let vars :: Term -> [String] -> ([String], Term)
        vars (ForT x a) xs = let (xs', a') = vars a xs in (x : xs', a')
        vars a xs = (xs, a)
    let (xs, a') = vars a []
    "@for " ++ unwords (x : xs) ++ ". " ++ show a'
  show (FunT a b) = show a ++ " -> " ++ show b
  show (Lam _ x a) = do
    -- TODO: show env
    let vars :: Term -> [String] -> ([String], Term)
        vars (Lam _ x a) xs = let (xs', a') = vars a xs in (x : xs', a')
        vars a xs = (xs, a)
    let (xs, a') = vars a []
    "\\" ++ unwords (x : xs) ++ " -> " ++ show a'
  show (App a b) = do
    let a' = case a of
          Lam {} -> "(" ++ show a ++ ")"
          a -> show a
    let b' = case b of
          App {} -> "(" ++ show b ++ ")"
          Lam {} -> "(" ++ show b ++ ")"
          b -> show b
    a' ++ " " ++ b'
  show (Fix x a) = "@fix " ++ show x ++ " (" ++ show a ++ ")"
  show (Op op) = show op

instance Show Operator where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Eq = "=="
  show (Call f t) = "@(" ++ f ++ " : " ++ show t ++ ")"

-- Syntax sugar --
forT :: [String] -> Term -> Term
forT xs a = foldr ForT a xs

funT :: [Term] -> Term -> Term
funT xs a = foldr FunT a xs

lam :: [String] -> Term -> Term
lam xs a = foldr (Lam []) a xs

app :: Term -> [Term] -> Term
app = foldl' App

let' :: (String, Term) -> Term -> Term
let' (x, a) b = App (Lam [] x b) a

add :: Term -> Term -> Term
add a b = app (Op Add) [a, b]

sub :: Term -> Term -> Term
sub a b = app (Op Sub) [a, b]

mul :: Term -> Term -> Term
mul a b = app (Op Mul) [a, b]

eq :: Term -> Term -> Term
eq a b = app (Op Eq) [a, b]

-- Evaluation
occurs :: String -> Term -> Bool
occurs x (Var y) = x == y
occurs x (Lam env y a) | x /= y && x `notElem` map fst env = occurs x a
occurs x (App a b) = occurs x a || occurs x b
occurs x (ForT y a) | x /= y = occurs x a
occurs x (FunT a b) = x `occurs` a || x `occurs` b
occurs _ _ = False

reduce :: Env -> Term -> Term
reduce env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just a -> reduce env a
  Nothing -> Var x
reduce env (Lam env' x a) = Lam (env' ++ env) x a
reduce env (App a b) = case (reduce env a, reduce env b) of
  (Lam env x a, b) -> reduce ((x, b) : env) a
  (App (Op op) a, b) -> case (op, reduce env a, b) of
    (Add, Int a, Int b) -> Int (a + b)
    (Sub, Int a, Int b) -> Int (a - b)
    (Mul, Int a, Int b) -> Int (a * b)
    (Eq, Int a, Int b) | a == b -> Lam [] "T" (Lam [] "F" (Var "T"))
    (Eq, Int _, Int _) -> Lam [] "T" (Lam [] "F" (Var "F"))
    (_, a, b) -> App (App (Op op) a) b
  (Fix x a, b) -> reduce ((x, Fix x a) : env) (App a b)
  (a, b) -> App a b
reduce env (FunT a b) = FunT (reduce env a) (reduce env b)
reduce _ a = a

eval :: Env -> Term -> Term
eval env a = case reduce env a of
  Lam env x a -> Lam [] x (eval ((x, Var x) : env) a)
  App a b -> App (eval [] a) (eval [] b)
  Fix x a -> case eval ((x, Var x) : env) a of
    Var x' | x == x' -> Var x
    a | x `occurs` a -> Fix x a
    a -> a
  a -> a
