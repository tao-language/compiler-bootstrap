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
  | PAs Pattern Variable
  | PInt Int
  | PCtr Constructor [Pattern]
  deriving (Eq, Show)

type Case = ([Pattern], Expr)

-- TODO: make Context opaque
type Context = [(Constructor, [(Constructor, Int)])]

type Expr = Context -> Term

instance Show Term where
  show Err = "#error"
  show (Var x) = x
  show (Int i) = show i
  show (App (Lam x a) (App Fix (Lam x' b))) | x == x' = "#letrec " ++ x ++ " = " ++ show b ++ "; " ++ show a
  show (App (Lam x a) b) = "#let " ++ x ++ " = " ++ show b ++ "; " ++ show a
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

bind :: Variable -> Pattern
bind = PAs PAny

letVar :: (Variable, Expr) -> Expr -> Expr
letVar (x, a) b = app (lam [x] b) [a]

letRec :: (Variable, Expr) -> Expr -> Expr
letRec (x, a) = letVar (x, app (const Fix) [lam [x] a])

with :: [(Variable, Expr)] -> Expr -> Expr
with defs a ctx = do
  let resolve :: [Variable] -> [(Variable, Term)]
      resolve [] = []
      resolve (x : xs) = case lookup x defs of
        Just b -> do
          let subdefs = filter (\(y, _) -> x /= y) defs
          (x, App Fix (Lam x (with subdefs b ctx))) : resolve xs
        Nothing -> resolve xs

  freeVariables (a ctx)
    |> resolve
    |> foldr (\(x, b) a -> App (Lam x a) b) (a ctx)

inferName :: Variable -> [Case] -> Variable
inferName "" ((PAs _ x : _, _) : cases) = inferName x cases
inferName x ((PAs _ x' : _, _) : cases) | x == x' = inferName x' cases
inferName _ ((PAs _ _ : _, _) : _) = ""
inferName x _ = x

newName :: String -> [String] -> String
newName x existing = case lastNameIndex x existing of
  Just i -> x ++ show (i + 1)
  Nothing -> x ++ "0"

match :: String -> [Case] -> Expr
match _ [] = err
match _ (([], a) : _) = a
match "" cases = \ctx -> do
  let x = case inferName "" cases of
        "" -> newName "%" (concatMap (\(_, a) -> freeVariables (a ctx)) cases)
        x -> x
  match x cases ctx
match x cases = \ctx -> do
  case findAlts cases ctx of
    Just alts -> do
      let branches = map (\alt -> match "" (remaining (matchCtr x alt) cases)) alts
      lam [x] (app (var x) branches) ctx
    Nothing -> case cases of
      (PAs p x' : ps, a) : cases | x == x' -> match x ((p : ps, a) : cases) ctx
      (PAs p y : ps, a) : cases -> match x ((p : ps, letVar (y, var x) a) : cases) ctx
      (PInt i : ps, a) : cases -> do
        let cond = eq (var x) (int i)
        let then' = match "" [(ps, a)]
        let else' = app (match "" cases) [var x]
        lam [x] (if' cond then' else') ctx
      _ -> lam [x] (match "" (remaining (matchAny x) cases)) ctx

bindings :: Pattern -> [String]
bindings (PAs p x) = x : bindings p
bindings (PCtr ctr (p : ps)) = bindings p ++ bindings (PCtr ctr ps)
bindings _ = []

bindVar :: Pattern -> Expr -> String -> (String, Expr)
bindVar PAny a x = (x, a)
bindVar (PAs p x) a x' | x == x' = bindVar p a x
bindVar p a x = (x, app (match "" [([p], var x)]) [a])

unpack :: (Pattern, Expr) -> [(String, Expr)]
unpack (p, a) = map (bindVar p a) (bindings p)

let' :: [(Pattern, Expr)] -> Expr -> Expr
let' defs = with (concatMap unpack defs)

-- Helper functions
freeVariables :: Term -> [String]
freeVariables (Var x) = [x]
freeVariables (App a b) = freeVariables a `union` freeVariables b
freeVariables (Lam x a) = delete x (freeVariables a)
freeVariables _ = []

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

findAlts :: [([Pattern], Expr)] -> Context -> Maybe [(Constructor, Int)]
findAlts [] _ = Nothing
findAlts ((PCtr ctr _ : _, _) : _) ctx = lookup ctr ctx
findAlts (_ : cases) ctx = findAlts cases ctx

matchAny :: Variable -> Case -> Maybe Case
matchAny _ (PAny : ps, a) = Just (ps, a)
matchAny _ _ = Nothing

matchCtr :: Variable -> (Constructor, Int) -> Case -> Maybe Case
matchCtr _ (_, n) (PAny : ps, a) = Just (replicate n PAny ++ ps, a)
matchCtr x (ctr, n) (PAs p y : ps, a) = matchCtr x (ctr, n) (p : ps, with [(y, var x)] a)
matchCtr _ (ctr, _) (PCtr ctr' qs : ps, a) | ctr == ctr' = Just (qs ++ ps, a)
matchCtr _ _ _ = Nothing

remaining :: (Case -> Maybe Case) -> [Case] -> [Case]
remaining f (case' : cases) = case f case' of
  Just case' -> case' : remaining f cases
  Nothing -> remaining f cases
remaining _ _ = []

-- Standard library functions
delete :: Eq a => a -> [a] -> [a]
delete _ [] = []
delete x (x' : xs) | x == x' = delete x xs
delete x (y : xs) = y : delete x xs

-- TODO: readInt : String -> Maybe Int
