module Lambda where

import Data.Bifunctor (Bifunctor (second))
import Data.List (union)
import Text.Read (readMaybe)

-- Bidirectional type checking: https://youtu.be/utyBNDj7s2w
-- https://www.cse.iitk.ac.in/users/ppk/teaching/cs653/notes/lectures/Lambda-calculus.lhs.pdf

data Term
  = Typ
  | IntT
  | Int Int
  | Var String
  | Lam String Term
  | App Term Term
  | Call String
  | Fix
  | Ann Term Term
  | For String Term
  | Fun Term Term
  deriving (Eq)

type Env = [(String, Term)]

instance Show Term where
  show Typ = "#Type"
  show IntT = "#Int"
  show (Int i) = show i
  show (Var x) = x
  show (Lam x a) = do
    let vars :: Term -> [String] -> ([String], Term)
        vars (Lam x a) xs = let (xs', a') = vars a xs in (x : xs', a')
        vars a xs = (xs, a)
    let (xs, a') = vars a []
    "\\" ++ unwords (x : xs) ++ ". " ++ show a'
  show (App (Lam x a) (App Fix (Lam x' b))) | x == x' = "#letrec " ++ x ++ " = " ++ show b ++ "; " ++ show a
  show (App (Lam x a) b) = "#let " ++ x ++ " = " ++ show b ++ "; " ++ show a
  show (App a b@(App _ _)) = show a ++ " (" ++ show b ++ ")"
  show (App a b@(Lam _ _)) = show a ++ " (" ++ show b ++ ")"
  show (App a b) = show a ++ " " ++ show b
  show (Call f) = "&" ++ f
  show Fix = "#fix"
  show (Ann a t) = show a ++ " : " ++ show t
  show (For x a) = do
    let vars :: Term -> [String] -> ([String], Term)
        vars (For x a) xs = let (xs', a') = vars a xs in (x : xs', a')
        vars a xs = (xs, a)
    let (xs, a') = vars a []
    "@" ++ unwords (x : xs) ++ ". " ++ show a'
  show (Fun a b) = show a ++ " => " ++ show b

-- Syntax sugar
lam :: [String] -> Term -> Term
lam xs a = foldr Lam a xs

app :: Term -> [Term] -> Term
app = foldl App

for :: [String] -> Term -> Term
for xs a = foldr For a xs

fun :: [Term] -> Term -> Term
fun xs a = foldr Fun a xs

add :: Term -> Term -> Term
add a b = app (Call "+") [a, b]

sub :: Term -> Term -> Term
sub a b = app (Call "-") [a, b]

mul :: Term -> Term -> Term
mul a b = app (Call "*") [a, b]

eq :: Term -> Term -> Term
eq a b = app (Call "==") [a, b]

letVar :: (String, Term) -> Term -> Term
letVar (x, a) b = app (lam [x] b) [a]

letRec :: (String, Term) -> Term -> Term
letRec (x, a) = letVar (x, app Fix [lam [x] a])

let' :: [(String, Term)] -> Term -> Term
let' defs a = do
  let resolve :: [String] -> [(String, Term)]
      resolve [] = []
      resolve (x : xs) = case lookup x defs of
        Just b -> do
          let subdefs = filter (\(y, _) -> x /= y) defs
          (x, App Fix (Lam x (let' subdefs b))) : resolve xs
        Nothing -> resolve xs
  foldr letVar a (resolve (freeVariables a))

-- Type system
substitute :: String -> Term -> Term -> Term
substitute x a (Var x') | x == x' = a
substitute x a (Lam y b) | x /= y = Lam y (substitute x a b)
substitute x a (App b1 b2) = App (substitute x a b1) (substitute x a b2)
substitute x a (Ann b1 b2) = Ann (substitute x a b1) (substitute x a b2)
substitute x a (Fun b1 b2) = Fun (substitute x a b1) (substitute x a b2)
substitute _ _ b = b

occurs :: String -> Term -> Bool
occurs x (Var y) = x == y
occurs x (Lam y a) | x /= y = occurs x a
occurs x (App a b) = occurs x a || occurs x b
occurs x (Ann a b) = occurs x a || occurs x b
occurs x (Fun a b) = occurs x a || occurs x b
occurs _ _ = False

bind :: String -> Term -> Maybe (Term -> Term)
bind x (Var x') | x == x' = Just id
bind x a | x `occurs` a = Nothing
bind x a = Just (substitute x a)

unify :: Term -> Term -> Maybe (Term -> Term)
unify (Var x) b = bind x b
unify a (Var x) = bind x a
unify (App a1 a2) (App b1 b2) = unify2 (a1, b1) (a2, b2)
unify (Ann a1 a2) (Ann b1 b2) = unify2 (a1, b1) (a2, b2)
unify (Fun a1 a2) (Fun b1 b2) = unify2 (a1, b1) (a2, b2)
unify (For x a) b = do
  let x' = newName (freeVariables b) x
  unify (substitute x (Var x') a) b
unify a (For x b) = do
  let x' = newName (freeVariables a) x
  unify a (substitute x (Var x') b)
unify a b | a == b = Just id
unify _ _ = Nothing

unify2 :: (Term, Term) -> (Term, Term) -> Maybe (Term -> Term)
unify2 (a1, b1) (a2, b2) = do
  s1 <- unify a1 b1
  s2 <- unify (s1 a2) (s1 b2)
  Just (s2 . s1)

inferType :: Env -> Term -> Maybe (Term, Term -> Term)
inferType _ Typ = Just (Typ, id)
inferType _ IntT = Just (Typ, id)
inferType _ (Int _) = Just (IntT, id)
inferType env (Var x) = do
  type' <- lookup x env
  Just (type', id)
inferType env (Lam x b) = do
  let x' = newName (map fst env) x
  (tb, s) <- inferType ((x, Var x') : env) b
  case s (Var x') of
    ta | ta == Var x' -> Just (For x' (Fun ta tb), s)
    ta -> Just (Fun ta tb, s)
inferType env (App a b) = do
  let t = Var (newName (map fst env) "%")
  (ta, s1) <- inferType env a
  (tb, s2) <- inferType (map (second s1) env) b
  s3 <- unify (Fun tb t) (s2 ta)
  Just (s3 t, s3 . s2 . s1)
inferType _ (Call _) = Just (for ["a", "b"] (Fun (Var "a") (Var "b")), id)
inferType _ Fix = Just (For "a" (Fun (Var "a") (Var "a")), id)
inferType env (Ann a t) = do
  (ta, s1) <- inferType env a
  s2 <- unify (s1 t) ta
  Just (s2 t, s2 . s1)
inferType _ (For _ _) = Just (Typ, id)
inferType _ (Fun _ _) = Just (Typ, id)

-- Helper functions
freeVariables :: Term -> [String]
freeVariables (Var x) = [x]
freeVariables (App a b) = freeVariables a `union` freeVariables b
freeVariables (Lam x a) = delete x (freeVariables a)
freeVariables _ = []

newName :: [String] -> String -> String
newName existing x = case lastNameIndex x existing of
  Just i -> x ++ show (i + 1)
  Nothing -> x

nameIndex :: String -> String -> Maybe Int
nameIndex "" x = readMaybe x
nameIndex (ch : prefix) (ch' : x) | ch == ch' = nameIndex prefix x
nameIndex _ _ = Nothing

lastNameIndex :: String -> [String] -> Maybe Int
lastNameIndex _ [] = Nothing
lastNameIndex prefix (x : xs) = case lastNameIndex prefix xs of
  Just i -> case nameIndex prefix x of
    Just j -> Just (max i j)
    Nothing -> Just i
  Nothing -> if prefix == x then Just 0 else nameIndex prefix x

-- Standard library functions
delete :: Eq a => a -> [a] -> [a]
delete _ [] = []
delete x (x' : xs) | x == x' = delete x xs
delete x (y : xs) = y : delete x xs

-- TODO: readInt : String -> Maybe Int
