module Core where

import Data.List (union)
import Text.Read (readMaybe)

-- Bidirectional type checking: https://youtu.be/utyBNDj7s2w
-- https://www.cse.iitk.ac.in/users/ppk/teaching/cs653/notes/lectures/Lambda-calculus.lhs.pdf

type Variable = String

type Constructor = String

data Term
  = Err
  | Var Variable
  | Int Int
  | App Term Term
  | Lam Variable Term
  | Call String
  | Fix
  deriving (Eq)

type Type = Term

data Pattern
  = PAny
  | PInt Int
  | PCtr Constructor [Binding]
  deriving (Eq, Show)

type Binding = (Pattern, Variable)

type Case = ([Binding], Expr)

-- TODO: make Context opaque
type Context = [(Constructor, [(Constructor, Int)])]

type Expr = Context -> Term

instance Show Term where
  show Err = "!"
  show (Var x) = x
  show (Int i) = show i
  show (App (Lam x a) (App Fix (Lam x' b))) | x == x' = "@" ++ x ++ " = " ++ show b ++ "; " ++ show a
  show (App a@(Lam _ _) b) = "(" ++ show a ++ ") " ++ show b
  show (App a b@(App _ _)) = show a ++ " (" ++ show b ++ ")"
  show (App a b@(Lam _ _)) = show a ++ " (" ++ show b ++ ")"
  show (App a b) = show a ++ " " ++ show b
  show (Lam x a) = do
    let vars :: Term -> [Variable] -> ([Variable], Term)
        vars (Lam x a) xs = let (xs', a') = vars a xs in (x : xs', a')
        vars a xs = (xs, a)
    let (xs, a') = vars a []
    "\\" ++ unwords (x : xs) ++ ". " ++ show a'
  show (Call op) = "&" ++ op
  show Fix = "#fix"

(|>) :: a -> (a -> b) -> b
(|>) x f = f x

infixl 1 |>

-- Context
empty :: Context
empty = []

defineType :: String -> [Variable] -> [(Constructor, Int)] -> Context -> Context
defineType _ _ alts ctx = map (\(ctr, _) -> (ctr, alts)) alts ++ ctx

-- High level constructs
err :: Expr
err = const Err

var :: Variable -> Expr
var x = const (Var x)

int :: Int -> Expr
int i = const (Int i)

app :: Expr -> [Expr] -> Expr
app a bs ctx = foldl App (a ctx) (map (\b -> b ctx) bs)

lam :: [Variable] -> Expr -> Expr
lam xs a ctx = foldr Lam (a ctx) xs

add :: Expr -> Expr -> Expr
add a b = app (const (Call "+")) [a, b]

sub :: Expr -> Expr -> Expr
sub a b = app (const (Call "-")) [a, b]

mul :: Expr -> Expr -> Expr
mul a b = app (const (Call "*")) [a, b]

eq :: Expr -> Expr -> Expr
eq a b = app (const (Call "==")) [a, b]

if' :: Expr -> Expr -> Expr -> Expr
if' cond then' else' = app cond [then', else']

let' :: [(Variable, Expr)] -> Expr -> Expr
let' defs a ctx = do
  let resolve :: [Variable] -> [(Variable, Term)]
      resolve [] = []
      resolve (x : xs) = case lookup x defs of
        Just b -> do
          let subdefs = filter (\(y, _) -> x /= y) defs
          (x, App Fix (Lam x (let' subdefs b ctx))) : resolve xs
        Nothing -> resolve xs

  freeVariables (a ctx)
    |> resolve
    |> foldr (\(x, b) a -> App (Lam x a) b) (a ctx)

match :: [([Binding], Expr)] -> Expr
match [] = err
match (([], a) : _) = a
match cases = \ctx -> do
  let freeVars = map (\(_, a) -> freeVariables (a ctx)) cases |> foldl union []
  let x = newName freeVars "%"
  case findAlts cases ctx of
    Just alts -> do
      let branches =
            map (matchCtr x) alts
              |> map (`filterMap` cases)
              |> map match
      lam [x] (app (var x) branches) ctx
    Nothing -> case cases of
      ((PInt i, y) : ps, a) : cases -> do
        let cond = eq (var x) (int i)
        let then' = match [(ps, let' [(y, var x)] a)]
        let else' = app (match cases) [var x]
        lam [x] (if' cond then' else') ctx
      _ -> lam [x] (match (filterMap (matchAny x) cases)) ctx

-- Helper functions
freeVariables :: Term -> [String]
freeVariables (Var x) = [x]
freeVariables (App a b) = freeVariables a `union` freeVariables b
freeVariables (Lam x a) = delete x (freeVariables a)
freeVariables _ = []

newName :: [String] -> String -> String
newName used x = case lastNameIndex x used of
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

findAlts :: [([Binding], Expr)] -> Context -> Maybe [(Constructor, Int)]
findAlts [] _ = Nothing
findAlts (((PCtr ctr _, _) : _, _) : _) ctx = lookup ctr ctx
findAlts (_ : cases) ctx = findAlts cases ctx

matchAny :: Variable -> Case -> Maybe Case
matchAny x ((PAny, y) : ps, a) = Just (ps, let' [(y, var x)] a)
matchAny _ _ = Nothing

matchCtr :: Variable -> (Constructor, Int) -> Case -> Maybe Case
matchCtr x (_, n) ((PAny, y) : ps, a) = Just (replicate n (PAny, "") ++ ps, let' [(y, var x)] a)
matchCtr x (ctr, _) ((PCtr ctr' qs, y) : ps, a) | ctr == ctr' = Just (qs ++ ps, let' [(y, var x)] a)
matchCtr _ _ _ = Nothing

-- Standard library functions
filterMap :: (a -> Maybe b) -> [a] -> [b]
filterMap _ [] = []
filterMap f (x : xs) = case f x of
  Just y -> y : filterMap f xs
  Nothing -> filterMap f xs

delete :: Eq a => a -> [a] -> [a]
delete _ [] = []
delete x (x' : xs) | x == x' = delete x xs
delete x (y : xs) = y : delete x xs

-- TODO: union : [a] -> [a] -> [a]
-- TODO: readInt : String -> Maybe Int
