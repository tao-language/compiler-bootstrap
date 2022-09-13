module Lambda where

import Data.List (union)
import Text.Read (readMaybe)

-- Bidirectional type checking: https://youtu.be/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf
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

-- Helper functions
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
