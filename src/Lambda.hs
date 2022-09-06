module Lambda where

import Data.List (union)
import Text.Read (readMaybe)

-- Bidirectional type checking: https://youtu.be/utyBNDj7s2w
-- https://www.cse.iitk.ac.in/users/ppk/teaching/cs653/notes/lectures/Lambda-calculus.lhs.pdf

data Term
  = Var String
  | Int Int
  | App Term Term
  | Lam String Term
  | Call String
  | Fix
  deriving (Eq)

instance Show Term where
  show (Var x) = x
  show (Int i) = show i
  show (App (Lam x a) (App Fix (Lam x' b))) | x == x' = "#letrec " ++ x ++ " = " ++ show b ++ "; " ++ show a
  show (App (Lam x a) b) = "#let " ++ x ++ " = " ++ show b ++ "; " ++ show a
  show (App a b@(App _ _)) = show a ++ " (" ++ show b ++ ")"
  show (App a b@(Lam _ _)) = show a ++ " (" ++ show b ++ ")"
  show (App a b) = show a ++ " " ++ show b
  show (Lam x a) = do
    let vars :: Term -> [String] -> ([String], Term)
        vars (Lam x a) xs = let (xs', a') = vars a xs in (x : xs', a')
        vars a xs = (xs, a)
    let (xs, a') = vars a []
    "\\" ++ unwords (x : xs) ++ ". " ++ show a'
  show (Call op) = "&" ++ op
  show Fix = "#fix"

-- Syntax sugar
app :: Term -> [Term] -> Term
app = foldl App

lam :: [String] -> Term -> Term
lam xs a = foldr Lam a xs

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

-- Helper functions
freeVariables :: Term -> [String]
freeVariables (Var x) = [x]
freeVariables (App a b) = freeVariables a `union` freeVariables b
freeVariables (Lam x a) = delete x (freeVariables a)
freeVariables _ = []

newName :: String -> [String] -> String
newName x existing = case lastNameIndex x existing of
  Just i -> x ++ show (i + 1)
  Nothing -> x ++ "0"

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
