module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.Function ((&))
import Data.List (delete, intercalate, union, unionBy)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)
import Error (Error (..), TypeError (..), cannotApply, typeMismatch, unhandledCase)
import Location (Location (..), Position (..), Range (..))
import qualified Parser as P
import Stdlib (replace, replaceString)

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
-- https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- https://www.youtube.com/live/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf
-- https://mroman42.github.io/mikrokosmos/tutorial.html

data Expr
  = Any
  | Unit
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Tag String
  | Var String
  | Ann Expr Type
  | And Expr Expr
  | Or Expr Expr
  | For String Expr
  | Fix String Expr
  | Fun Expr Expr
  | App Expr Expr
  | Call String [Expr]
  | Let [(String, Expr)] Expr
  | Meta Metadata Expr
  | Err (Error Expr)
  deriving (Eq, Show)

type Type = Expr

type Ops = [(String, (Expr -> Expr) -> [Expr] -> Maybe Expr)]

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

data Metadata
  = Loc Location
  | Comments [String]
  | TrailingComment String
  deriving (Eq, Show)

format :: Expr -> String
format expr = case expr of
  Any -> "_"
  Unit -> "()"
  IntT -> "!IntT"
  NumT -> "!NumT"
  Int i -> show i
  Num n -> show n
  Var x -> name x
  Tag ('^' : k) -> '^' : '^' : name k
  Tag ('~' : k) -> '^' : '~' : name k
  Tag k -> '^' : name k
  Ann a b -> "(" ++ format a ++ " : " ++ format b ++ ")"
  And _ _ -> "(" ++ intercalate ", " (map format (andOf expr)) ++ ")"
  Or _ _ -> "(" ++ intercalate " | " (map format (orOf expr)) ++ ")"
  For _ _ -> do
    let (xs, a) = forOf expr
    "(@" ++ unwords (map name xs) ++ ". " ++ format a ++ ")"
  Fix x a -> "(&" ++ name x ++ ". " ++ format a ++ ")"
  Fun _ _ -> do
    let (args, ret) = funOf expr
    "(" ++ intercalate " -> " (map format args) ++ " -> " ++ format ret ++ ")"
  App a b -> do
    let (a', bs) = appOf (App a b)
    "(" ++ format a' ++ " " ++ unwords (map format bs) ++ ")"
  Call f args -> '%' : f ++ "(" ++ intercalate ", " (map format args) ++ ")"
  Let env b -> "@{" ++ intercalate "; " (map (\(x, a) -> name x ++ " = " ++ format a) env) ++ "} " ++ format b
  Meta m a -> case m of
    Comments [] -> show a
    Comments (c : cs) -> "# " ++ c ++ "\n" ++ show (Meta (Comments cs) a)
    TrailingComment c -> show a ++ "  # " ++ c ++ "\n"
    Loc (Location filename range) -> "#(" ++ filename ++ ":" ++ show range.start.row ++ ":" ++ show range.start.col ++ " .." ++ show range.end.row ++ ":" ++ show range.end.col ++ ")" ++ format a
  Err e -> "!" ++ show e
  where
    isAlphaNumOr cs c = isAlphaNum c || c `elem` cs
    name = \case
      x | all (isAlphaNumOr "$-_") x -> x
      '.' : x | not (any (isAlphaNumOr "()") x) -> "(" ++ x ++ ")"
      x -> "`" ++ replaceString "`" "\\`" x ++ "`"

-- instance Show Expr where
--   showsPrec :: Int -> Expr -> ShowS
--   showsPrec p expr = case expr of
--     -- App (Lam [Case [p] b]) a -> prefix 1 (show p ++ " = " ++ show a ++ "; ") b
--     Or a b -> infixR 1 a " | " b
--     And a b -> infixL 1 a ", " b
--     Ann a b -> infixR 2 a " : " b
--     Call "==" [a, b] -> infixL 3 a " == " b
--     Call "<" [a, b] -> infixR 4 a " < " b
--     Call ">" [a, b] -> infixR 4 a " > " b
--     For x a -> do
--       let (xs, a') = asFor (For x a)
--       prefix 2 ("@" ++ unwords xs ++ ". ") a'
--     Fix x a -> prefix 2 ("!fix " ++ show (Var x) ++ ". ") a
--     Fun p b -> infixR 5 p " -> " b
--     Call "+" [a, b] -> infixL 6 a " + " b
--     Call "-" [a, b] -> infixL 6 a " - " b
--     Call "*" [a, b] -> infixL 7 a " * " b
--     Call "/" [a, b] -> infixL 7 a " / " b
--     Call "^" [a, b] -> infixL 10 a "^" b
--     Call ('%' : op) [a] -> prefix 8 ('%' : op ++ " ") a
--     Call op [a] -> prefix 8 op a
--     App a b -> infixL 8 a " " b
--     Err -> atom 12 "!error"
--     IntT -> atom 12 "!Int"
--     NumT -> atom 12 "!Num"
--     Int i -> atom 12 (show i)
--     Num n -> atom 12 (show n)
--     Var x | isVarName x -> atom 12 x
--     Var x -> atom 12 ("`" ++ replaceString "`" "\\`" x ++ "`")
--     Tag "" -> atom 12 "()"
--     Tag k -> atom 12 k
--     Call op [] -> atom 12 ("(" ++ op ++ ")")
--     Call op args -> showsPrec p (app (Call op []) args)
--     where
--       atom n k = showParen (p > n) $ showString k
--       prefix n k a = showParen (p > n) $ showString k . showsPrec (n + 1) a
--       infixL n a op b = showParen (p > n) $ showsPrec n a . showString op . showsPrec (n + 1) b
--       infixR n a op b = showParen (p > n) $ showsPrec (n + 1) a . showString op . showsPrec n b
--       isVarName ('!' : xs) = all isNameChar xs
--       isVarName ('@' : xs) = True
--       isVarName ('_' : xs) = all isNameChar xs
--       isVarName (x : xs) = isLower x && all isNameChar xs
--       isVarName [] = False
--       isTagName (x : xs) = isUpper x && all isNameChar xs
--       isTagName [] = False
--       isNameChar '-' = True
--       isNameChar '_' = True
--       isNameChar c = isAlphaNum c
--       op2 op = " " ++ show op ++ " "
--       op1 op = show op ++ " "

-- Syntax sugar
tag :: String -> [Expr] -> Expr
tag k args = and' (Tag k : args)

and' :: [Expr] -> Expr
and' [] = Unit
and' [a] = a
and' (a : bs) = And a (and' bs)

andOf :: Expr -> [Expr]
andOf (And a b) = a : andOf b
andOf a = [a]

or' :: [Expr] -> Expr
or' [] = Unit
or' [a] = a
or' (a : bs) = Or a (or' bs)

orOf :: Expr -> [Expr]
orOf (Or a b) = a : orOf b
orOf a = [a]

fix :: [String] -> Expr -> Expr
fix [] a = a
fix (x : xs) a
  | x `occurs` a = Fix x (fix xs a)
  | otherwise = fix xs a

for :: [String] -> Expr -> Expr
for [] a = a
for (x : xs) a
  | x `occurs` a = For x (for xs a)
  | otherwise = for xs a

forOf :: Expr -> ([String], Expr)
forOf (For x a) = let (xs, b) = forOf a in (x : xs, b)
forOf a = ([], a)

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

lam :: [Expr] -> Expr -> Expr
lam ps b = for (freeVars (and' ps)) (fun ps b)

funOf :: Expr -> ([Expr], Expr)
funOf (Fun arg ret) = let (args, ret') = funOf ret in (arg : args, ret')
funOf a = ([], a)

app :: Expr -> [Expr] -> Expr
app = foldl App

appOf :: Expr -> (Expr, [Expr])
appOf (App a b) = let (a', bs) = appOf a in (a', bs ++ [b])
appOf a = (a, [])

let' :: [(String, Expr)] -> Expr -> Expr
let' [] b = b
let' defs b = Let defs b

def :: [String] -> (Expr, Expr) -> Expr -> Expr
def xs (a, b) c = App (for xs (Fun a c)) b

list :: Expr -> Expr -> [Expr] -> Expr
list _ nil [] = nil
list cons nil (a : bs) = app cons [a, list cons nil bs]

match' :: [Expr] -> [([Expr], Expr)] -> Expr
match' args cases = app (matchFun cases) args

matchFun :: [([Expr], Expr)] -> Expr
matchFun [] = Unit
matchFun [(ps, b)] = fun ps b
matchFun ((ps, b) : cases) = fun ps b `Or` matchFun cases

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

freeNames :: (Bool, Bool, Bool) -> Expr -> [String]
freeNames (vars, tags, calls) = \case
  Any -> []
  Unit -> []
  IntT -> []
  NumT -> []
  Int _ -> []
  Num _ -> []
  Var x
    | vars -> [x]
    | otherwise -> []
  Tag k
    | tags -> [k]
    | otherwise -> []
  Ann a b -> freeNames' a `union` freeNames' b
  And a b -> freeNames' a `union` freeNames' b
  Or a b -> freeNames' a `union` freeNames' b
  For x a -> delete x (freeNames' a)
  Fix x a -> delete x (freeNames' a)
  Fun a b -> freeNames' a `union` freeNames' b
  App a b -> freeNames' a `union` freeNames' b
  Call f args
    | calls -> foldr (union . freeNames') [f] args
    | otherwise -> foldr (union . freeNames') [] args
  -- TODO: This is much more subtle than it appears for Let.
  --       Free names should be done recursively on definitions used.
  --       More of a graph traversal problem, visiting nodes (definitions).
  --       This could also be used to only keep the relevant definitions and drop irrelevant ones.
  --        e.g. : a -> Bool
  --             (==) = x -> (y -> True | _ -> False) x
  -- Let [] b -> freeNames' b
  -- Let ((x, a) : defs) b -> delete x (freeNames' a `union` freeNames' (Let defs b))
  -- Let defs b -> filter (`notElem` map fst defs) (foldr ((union . freeNames') . snd) (freeNames' b) defs)
  -- Let _ b -> freeNames' b
  Let env b -> freeNames' (reduce [] (Let env b))
  Meta _ a -> freeNames' a
  Err _ -> []
  where
    freeNames' = freeNames (vars, tags, calls)

freeVars :: Expr -> [String]
freeVars = freeNames (True, False, False)

freeTags :: Expr -> [String]
freeTags = freeNames (False, True, False)

occurs :: String -> Expr -> Bool
occurs _ (Var _) = False
occurs x (Or a b) = occurs x a || occurs x b
occurs x (Meta _ a) = occurs x a
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
reduce :: Ops -> Expr -> Expr
reduce ops = \case
  App a b -> reduceApp ops (reduce ops a) (reduce ops b)
  Let env expr -> reduceLet ops env expr
  Meta _ a -> reduce ops a
  expr -> expr

reduceLet :: Ops -> Env -> Expr -> Expr
reduceLet ops env = \case
  Var x -> case lookup x env of
    Just (Var x') | x == x' -> Var x
    Just (Ann (Var x') t) | x == x' -> Ann (Var x) t
    Just a -> reduce ops a
    Nothing -> Var x
  Ann a b -> Ann (Let env a) (Let env b)
  And a b -> And (Let env a) (Let env b)
  Or a b -> Or (Let env a) (Let env b)
  For x a -> For x (Let env a)
  Fix x a -> Fix x (Let env a)
  Fun a b -> Fun (Let env a) (Let env b)
  App a b -> reduceApp ops (reduce ops (Let env a)) (reduce ops (Let env b))
  Call f args -> case (lookup f ops, Let env <$> args) of
    (Just call, args) | Just result <- call (eval ops) args -> result
    (_, args) -> Call f args
  Let env' a -> reduce ops (Let (env ++ env') a)
  Meta _ a -> reduce ops (Let env a)
  expr -> expr

reduceApp :: Ops -> Expr -> Expr -> Expr
reduceApp ops a b = case (a, b) of
  (Any, _) -> Any
  (Err e, _) -> Err e
  (a, b) | isOpen b -> App a b
  (a@Var {}, b) -> App a b
  (a@App {}, b) -> App a b
  (Ann a _, b) -> reduceApp ops (reduce ops a) b
  (Or a1 a2, b) -> case reduceApp ops (reduce ops a1) b of
    Err _ -> reduceApp ops (reduce ops a2) b
    c -> c
  (For x a, b) -> reduceApp ops (reduce ops (Let [(x, Var x)] a)) b
  (Fun a c, b) -> case match False ops a b of
    Just env -> reduce ops (Let env c)
    Nothing -> Err (unhandledCase b)
  (Call f args, b) -> App (Call f args) b
  (Fix x a, b) -> reduceApp ops (reduce ops (Let [(x, Fix x a)] a)) b
  (Meta _ a, b) -> reduceApp ops a b
  _ -> Err (cannotApply a b)

match :: Bool -> Ops -> Expr -> Expr -> Maybe Env
match unify ops (Let env (Tag k)) b = case lookup k env of
  Just def -> do
    let b' = App (Let env def) b
    match unify ops (Tag k) (b' `Or` b)
  Nothing -> match unify ops (Tag k) b
match unify ops (Let env (Meta _ a)) b =
  match unify ops (Let env a) b
match unify ops (Let env (Let env' a)) b =
  match unify ops (Let (env ++ env') a) b
match unify ops a b = case (reduce ops a, reduce ops b) of
  (Any, _) -> Just []
  (_, Any) | unify -> Just []
  (Unit, Unit) -> Just []
  (IntT, IntT) -> Just []
  (NumT, NumT) -> Just []
  (Int i, Int i') | i == i' -> Just []
  (Num n, Num n') | n == n' -> Just []
  (Tag k, Tag k') | k == k' -> Just []
  (Var x, b) -> Just [(x, b)]
  (a, Var x) | unify -> Just [(x, a)]
  (Ann a ta, Ann b tb) -> do
    env1 <- match True ops ta tb
    env2 <- match unify ops a b
    Just (env1 ++ env2)
  (And (Let env (Tag k)) a, b) -> case lookup k env of
    Just def -> do
      let b' = app (Let env def) [a, b]
      match unify ops (And (Tag k) a) (b' `Or` b)
    Nothing -> match unify ops (And (Tag k) a) b
  (And (Let env (Meta _ a1)) a2, b) ->
    match unify ops (Let env (And a1 a2)) b
  (And (Let env (Let env' a1)) a2, b) ->
    match unify ops (Let (env ++ env') (And a1 a2)) b
  (And a1 a2, And b1 b2) -> do
    env1 <- match unify ops a1 b1
    env2 <- match unify ops a2 b2
    Just (env1 ++ env2)
  (Or a1 a2, b) -> case match unify ops a1 b of
    Just env1 -> case match unify ops a2 b of
      Just env2 -> Just (env1 ++ env2)
      Nothing -> Just env1
    Nothing -> match unify ops a2 b
  (a, Or b1 b2) -> case match unify ops a b1 of
    Just env1 -> case match unify ops a b2 of
      Just env2 -> Just (env1 ++ env2)
      Nothing -> Just env1
    Nothing -> match unify ops a b2
  (For x a, b) -> match unify ops (Let [(x, Var x)] a) b
  (a, For x b) -> match unify ops a (Let [(x, Var x)] b)
  -- \| Fix String Expr
  (Fun a1 a2, Fun b1 b2) -> match unify ops (And a1 a2) (And b1 b2)
  (App a1 a2, App b1 b2) -> match unify ops (And a1 a2) (And b1 b2)
  (Call x args, Call x' args') | x == x' -> do
    match unify ops (and' args) (and' args')
  (Err e, Err e') | e == e' -> Just []
  (Ann a _, b) -> match unify ops a b
  (a, Ann b _) -> match unify ops a b
  (Meta _ a, b) -> match unify ops a b
  (_, Meta _ b) -> match unify ops a b
  _ -> Nothing

eval :: Ops -> Expr -> Expr
eval ops expr = case reduce ops expr of
  Ann a _ -> eval ops a
  And a b -> And (eval ops a) (eval ops b)
  Or a b -> Or (eval ops a) (eval ops b)
  For x a -> for [x] (eval ops (Let [(x, Var x)] a))
  Fix x a -> fix [x] (eval ops (Let [(x, Var x)] a))
  Fun a b -> Fun (eval ops a) (eval ops b)
  App a b -> App (eval ops a) (eval ops b)
  Call f args -> Call f (eval ops <$> args)
  Meta m a -> Meta m (eval ops a)
  a -> a

class Substitute a where
  substitute :: Substitution -> a -> a

instance Substitute Expr where
  substitute :: Substitution -> Expr -> Expr
  substitute _ Any = Any
  substitute _ Unit = Unit
  substitute _ IntT = IntT
  substitute _ NumT = NumT
  substitute _ (Int i) = Int i
  substitute _ (Num n) = Num n
  substitute [] (Var x) = Var x
  substitute ((x, a) : _) (Var x') | x == x' = a
  substitute (_ : s) (Var x) = substitute s (Var x)
  substitute _ (Tag k) = Tag k
  substitute s (Ann a b) = Ann (dropTypes (substitute s a)) (dropTypes (substitute s b))
  substitute s (And a b) = And (substitute s a) (substitute s b)
  substitute s (Or a b) = Or (substitute s a) (substitute s b)
  substitute s (For x a) = For x (substitute (filter ((/= x) . fst) s) a)
  substitute s (Fix x a) = Fix x (substitute (filter ((/= x) . fst) s) a)
  substitute s (Fun a b) = Fun (substitute s a) (substitute s b)
  substitute s (App a b) = App (substitute s a) (substitute s b)
  substitute s (Call op args) = Call op (map (substitute s) args)
  substitute s (Let env b) = do
    let sub (x, a) = (x, substitute s a)
    let s' = filter (\(x, _) -> x `notElem` map fst env) s
    Let (map sub env) (substitute s' b)
  substitute s (Meta m a) = Meta m (substitute s a)
  substitute s (Err e) = Err (substitute s e)

instance Substitute (Error Expr) where
  substitute :: Substitution -> Error Expr -> Error Expr
  substitute s = fmap (substitute s)

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = do
  let sub s (x, a) = case lookup x s of
        Just b -> (x, b)
        Nothing -> (x, substitute s a)
  unionBy (\a b -> fst a == fst b) s1 (map (sub s1) s2)

dropTypes :: Expr -> Expr
dropTypes (Ann a@Call {} t) = Ann (dropTypes a) (dropTypes t)
dropTypes (Ann a _) = dropTypes a
dropTypes (And a b) = And (dropTypes a) (dropTypes b)
dropTypes (Or a b) = Or (dropTypes a) (dropTypes b)
dropTypes (For x a) = For x (dropTypes a)
dropTypes (Fix x a) = Fix x (dropTypes a)
dropTypes (Fun (Ann a ta) b) = case andOf ta of
  [Ann ta _] -> Fun (Ann (dropTypes a) (dropTypes ta)) (dropTypes b)
  _ -> Fun (Ann (dropTypes a) (dropTypes ta)) (dropTypes b)
dropTypes (Fun a b) = Fun (dropTypes a) (dropTypes b)
dropTypes (App a (Ann b tb)) = case andOf tb of
  [Ann tb _] -> App (dropTypes a) (Ann (dropTypes b) (dropTypes tb))
  _ -> App (dropTypes a) (Ann (dropTypes b) (dropTypes tb))
dropTypes (App a b) = App (dropTypes a) (dropTypes b)
dropTypes (Call op args) = Call op (map dropTypes args)
dropTypes (Let defs b) = Let (map (second dropTypes) defs) (dropTypes b)
dropTypes (Meta m a) = Meta m (dropTypes a)
dropTypes a = a

dropMeta :: Expr -> Expr
dropMeta (Ann a b) = Ann (dropMeta a) (dropMeta b)
dropMeta (And a b) = And (dropMeta a) (dropMeta b)
dropMeta (Or a b) = Or (dropMeta a) (dropMeta b)
dropMeta (For x a) = For x (dropMeta a)
dropMeta (Fix x a) = Fix x (dropMeta a)
dropMeta (Fun a b) = Fun (dropMeta a) (dropMeta b)
dropMeta (App a b) = App (dropMeta a) (dropMeta b)
dropMeta (Call op args) = Call op (map dropMeta args)
dropMeta (Let defs b) = Let (map (second dropMeta) defs) (dropMeta b)
dropMeta (Meta _ a) = dropMeta a
dropMeta a = a

dropLet :: Expr -> Expr
dropLet (Ann a b) = Ann (dropLet a) (dropLet b)
dropLet (And a b) = And (dropLet a) (dropLet b)
dropLet (Or a b) = Or (dropLet a) (dropLet b)
dropLet (For x a) = For x (dropLet a)
dropLet (Fix x a) = Fix x (dropLet a)
dropLet (Fun a b) = Fun (dropLet a) (dropLet b)
dropLet (App a b) = App (dropLet a) (dropLet b)
dropLet (Call op args) = Call op (map dropLet args)
dropLet (Let _ b) = dropLet b
dropLet (Meta m a) = Meta m (dropLet a)
dropLet a = a

findLocation :: Expr -> Maybe Location
findLocation = \case
  Meta (Loc loc) _ -> Just loc
  Meta _ a -> findLocation a
  _ -> Nothing

unify :: Ops -> Env -> Expr -> Expr -> (Expr, Substitution)
unify ops env a b = case (a, b) of
  (a, Meta m b) -> case unify ops env a b of
    (Err (TypeError (TypeMismatch a b)), s) -> (Err $ typeMismatch a (Meta m b), s)
    result -> result
  (Meta m a, b) -> case unify ops env a b of
    (Err (TypeError (TypeMismatch a b)), s) -> (Err $ typeMismatch (Meta m a) b, s)
    result -> result
  (_, Any) -> (Any, [])
  (Any, _) -> (Any, [])
  (Unit, Unit) -> (Unit, [])
  (IntT, IntT) -> (IntT, [])
  (Int _, IntT) -> (IntT, [])
  (IntT, Int _) -> (IntT, [])
  (NumT, NumT) -> (NumT, [])
  (Num _, NumT) -> (NumT, [])
  (NumT, Num _) -> (NumT, [])
  (Int i, Int i') | i == i' -> (Int i, [])
  (Num n, Num n') | n == n' -> (Num n, [])
  (Var x, Var x') | x == x' -> (Var x, [])
  (Var x, b) | x `occurs` b -> (Err $ TypeError $ OccursError x b, [])
  (Var x, b) -> (b, [(x, b)])
  (a, Var x) -> unify ops env (Var x) a
  (Tag k, Tag k') | k == k' -> (Tag k, [])
  (a, Tag k) | Just def <- lookup k env -> do
    let a' = eval ops (App (Let env def) a)
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s) = unify ops env' a' (Tag k)
    (t, [(k, def)] `compose` s)
  (Tag k, b) | Just def <- lookup k env -> do
    let b' = eval ops (App (Let env def) b)
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s) = unify ops env' (Tag k) b'
    (t, [(k, def)] `compose` s)
  (a, And (Tag k) b) | Just def <- lookup k env -> do
    let a' = eval ops (app (Let env def) [b, a])
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s) = unify ops env' a' (And (Tag k) b)
    (t, [(k, def)] `compose` s)
  (And (Tag k) a, b) | Just def <- lookup k env -> do
    let b' = eval ops (app (Let env def) [a, b])
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s) = unify ops env' (And (Tag k) a) b'
    (t, [(k, def)] `compose` s)
  (And a1 b1, And a2 b2) -> do
    let ((a, b), s) = unify2 ops env (a1, a2) (b1, b2)
    (And a b, s)
  (Ann a ta, Ann b tb) -> do
    let ((a', ta'), s) = unify2 ops env (a, b) (ta, tb)
    (Ann a' ta', s)
  (Ann a _, b) -> unify ops env a b
  (a, Ann b _) -> unify ops env a b
  (Or a1 a2, b) -> case unify ops env a1 b of
    (Err e1, _) -> case unify ops env a2 b of
      (Err e2, _) -> (Or (Err e1) (Err e2), [])
      (c2, s2) -> (c2, s2)
    (c1, s1) -> do
      let env1 = s1 `compose` env
      let (a2', b') = (substitute s1 a2, substitute s1 b)
      case unify ops env1 a2' b' of
        (Err _, _) -> (c1, s1)
        (c2, s2) -> do
          let env2 = s2 `compose` env1
          let c1' = substitute s2 c1
          case unify ops env2 c1' c2 of
            (Err _, _) -> (Or c1' c2, s2 `compose` s1)
            (c, s3) -> (c, s3 `compose` s2 `compose` s1)
  (a, Or b1 b2) -> case unify ops env a b1 of
    (Err e1, _) -> case unify ops env a b2 of
      (Err e2, _) -> (Or (Err e1) (Err e2), [])
      (c2, s2) -> (c2, s2)
    (c1, s1) -> do
      let env1 = s1 `compose` env
      let (a', b2') = (substitute s1 a, substitute s1 b2)
      case unify ops env1 a' b2' of
        (Err _, _) -> (c1, s1)
        (c2, s2) -> do
          let env2 = s2 `compose` env1
          let c1' = substitute s2 c1
          case unify ops env2 c1' c2 of
            (Err _, _) -> (Or c1' c2, s2 `compose` s1)
            (c, s3) -> (c, s3 `compose` s2 `compose` s1)
  (a, For x b) -> do
    let (b', s1) = instantiate (freeVars a) (For x b)
    let (c, s2) = unify ops (s1 `compose` env) a b'
    (c, s2 `compose` s1)
  (For x a, b) -> do
    let (a', s1) = instantiate (freeVars b) (For x a)
    let (c, s2) = unify ops (s1 `compose` env) a' b
    (c, s2 `compose` s1)
  (Fix _ a, b) -> unify ops env a b
  (a, Fix _ b) -> unify ops env a b
  (Fun a1 b1, Fun a2 b2) -> do
    let ((a, b), s) = unify2 ops env (a1, a2) (b1, b2)
    (Fun a b, s)
  (Call op args, Call op' args') | op == op' -> do
    let (args'', s) = unifyAll ops env args args'
    (Call op args'', s)
  (a, b) -> (Err $ TypeError $ TypeMismatch a b, [])

unify2 :: Ops -> Env -> (Expr, Expr) -> (Expr, Expr) -> ((Expr, Expr), Substitution)
unify2 ops env (a1, a2) (b1, b2) = do
  let (ta, s1) = unify ops env a1 a2
  let (tb, s2) = unify ops env (substitute s1 b1) (substitute s1 b2)
  ((substitute s2 ta, tb), s2 `compose` s1)

unifyAll :: Ops -> Env -> [Expr] -> [Expr] -> ([Expr], Substitution)
unifyAll ops env (a : bs) (a' : bs') = do
  let (ta, s1) = unify ops env a a'
  let (tbs, s2) = unifyAll ops env (map (substitute s1) bs) (map (substitute s1) bs')
  (ta : tbs, s2 `compose` s1)
unifyAll _ _ _ _ = ([], [])

infer :: Ops -> Env -> Expr -> ((Expr, Type), Substitution)
infer _ env Any = do
  let y = newName ("_" : map fst env) "_"
  ((Any, Var y), [(y, Var y)])
infer _ _ Unit = ((Unit, Unit), [])
infer _ _ IntT = ((IntT, IntT), [])
infer _ _ NumT = ((NumT, NumT), [])
infer _ _ (Int i) = ((Int i, IntT), [])
infer _ _ (Num n) = ((Num n, NumT), [])
infer _ _ (Tag k) = ((Tag k, Tag k), [])
infer ops env (Var x) = do
  let (ta, s) = case lookup x env of
        Just (Var x') | x == x' -> do
          let y = newName (map fst env) (x ++ "T")
          (Var y, [(y, Var y), (x, Ann (Var x) (Var y))])
        Just (Ann (Var x') ty) | x == x' -> do
          instantiate (map fst env) ty
        Just a -> do
          let ((_, ta), s) = infer ops env a
          (ta, s)
        Nothing -> (Err $ TypeError $ UndefinedVar x, [])
  ((Var x, ta), s)
infer ops env (Ann a t) = do
  let ((a', t'), s) = check ops env a t
  ((Ann a' t', t'), s)
infer ops env (And a b) = do
  let ((a', ta), (b', tb), s) = infer2 ops env a b
  ((And a' b', And ta tb), s)
infer ops env (Or a b) = do
  let ((a', ta), (b', tb), s1) = infer2 ops env a b
  case unify ops (s1 `compose` env) ta tb of
    (Err _, _) -> ((Or a' b', Or ta tb), s1)
    (t, s2) -> ((Or a' b', t), s2 `compose` s1)
infer ops env (For x a) = do
  let y = newName (map fst env) x
  let ((a', ta), s) = infer ops ((y, Var y) : env) (substitute [(x, Var y)] a)
  ((for [x] (substitute [(y, Var x)] a'), ta), s `compose` [(y, Var y)])
infer ops env (Fix x a) = do
  let y = newName (map fst env) x
  let ((a', ta), s) = infer ops ((y, Var y) : env) (substitute [(x, Var y)] a)
  ((fix [x] (substitute [(y, Var x)] a'), ta), s `compose` [(y, Var y)])
infer ops env (Fun a b) = do
  let ((a', ta), (b', tb), s) = infer2 ops env a b
  ((Fun (Ann a' ta) b', Fun ta tb), s)
infer ops env (App a b) = do
  let ((a_, ta), s1) = infer ops env a
  let ((a', b'), (t1, t2), s2) = checkApp ops (s1 `compose` env) (a_, ta) (substitute s1 b)
  ((App a' (Ann b' t1), t2), s2 `compose` s1)
infer ops env (Let defs a) = infer ops (defs ++ env) a
infer ops env (Call op args) = do
  let (args', s) = inferAll ops env args
  ((Call op (map fst args'), Any), s)
infer ops env (Meta m a) = do
  let ((a', ta), s) = infer ops env a
  ((Meta m a', ta), s)
infer _ _ (Err e) = ((Err e, Any), [])

infer2 :: Ops -> Env -> Expr -> Expr -> ((Expr, Type), (Expr, Type), Substitution)
infer2 ops env a b = do
  let ((a', ta), s1) = infer ops env a
  let ((b', tb), s2) = infer ops (s1 `compose` env) (substitute s1 b)
  ((substitute s2 a', substitute s2 ta), (b', tb), s2 `compose` s1)

inferAll :: Ops -> Env -> [Expr] -> ([(Expr, Type)], Substitution)
inferAll _ _ [] = ([], [])
inferAll ops env (a : bs) = do
  let ((a', ta), s1) = infer ops env a
  let (bts, s2) = inferAll ops (s1 `compose` env) (map (substitute s1) bs)
  ((substitute s2 a', substitute s2 ta) : bts, s2 `compose` s1)

check :: Ops -> Env -> Expr -> Type -> ((Expr, Type), Substitution)
check ops env a (For x t) = do
  let y = newName (map fst env) x
  let ((a', t'), s) = check ops ((y, Var y) : env) a (substitute [(x, Var y)] t)
  ((a', for [x] (substitute [(y, Var x)] t')), s `compose` [(y, Var y)])
check ops env (Or a b) t = do
  let ((a', ta'), (b', tb'), s1) = check2 ops env (a, t) (b, t)
  case unify ops (s1 `compose` env) ta' tb' of
    (Err _, _) -> ((Or a' b', Or ta' tb'), s1)
    (t', s2) -> ((Or a' b', t'), s2 `compose` s1)
check ops env (For x a) t = do
  let y = newName (map fst env) x
  let ((a', t'), s) = check ops ((y, Var y) : env) (substitute [(x, Var y)] a) t
  ((for [x] (substitute [(y, Var x)] a'), t'), s `compose` [(y, Var y)])
check ops env (Fun a b) (Fun ta tb) = do
  let ((a', ta'), (b', tb'), s) = check2 ops env (a, ta) (b, tb)
  ((Fun (Ann a' ta') b', Fun ta' tb'), s)
check ops env (App a b) t2 = do
  let ((b', t1), s1) = infer ops env b
  let ((a', _), s2) = check ops (s1 `compose` env) (substitute s1 a) (Fun t1 (substitute s1 t2))
  let s = s2 `compose` s1
  ((App a' (substitute s2 (Ann b' t1)), substitute s t2), s)
check ops env a (Meta m t) = do
  let ((a', t'), s) = check ops env a t
  ((a', Meta m t'), s)
check ops env (Meta m a) t = do
  let ((a', t'), s) = check ops env a t
  ((Meta m a', t'), s)
check ops env a t = do
  let ((a', ta), s1) = infer ops env a
  let (t', s2) = unify ops env ta (substitute s1 t)
  ((substitute s2 a', t'), s2 `compose` s1)

check2 :: Ops -> Env -> (Expr, Type) -> (Expr, Type) -> ((Expr, Type), (Expr, Type), Substitution)
check2 ops env (a, ta) (b, tb) = do
  let ((a', ta'), s1) = check ops env a ta
  let ((b', tb'), s2) = check ops (s1 `compose` env) (substitute s1 b) (substitute s1 tb)
  ((substitute s2 a', substitute s2 ta'), (b', tb'), s2 `compose` s1)

checkApp :: Ops -> Env -> (Expr, Type) -> Expr -> ((Expr, Expr), (Type, Type), Substitution)
checkApp ops env (a, ta) b = case ta of
  Var x -> do
    let x1 = newName ((x ++ "$") : map fst env) (x ++ "$")
    let x2 = newName (x1 : (x ++ "$") : map fst env) (x ++ "$")
    let ((a', _), (b', t1), s) = check2 ops (pushVars [x1, x2] env) (a, Fun (Var x1) (Var x2)) (b, Var x1)
    ((a', b'), (t1, substitute s (Var x2)), s `compose` [(x1, Var x1), (x2, Var x2)])
  For x ta -> do
    let (ta', s1) = instantiate (map fst env) (For x ta)
    let (ab, ts, s2) = checkApp ops (s1 `compose` env) (substitute s1 a, ta') (substitute s1 b)
    (ab, ts, s2 `compose` s1)
  Or ta1 ta2 -> do
    let ((a_, b_), (t1a, t2a), s1) = checkApp ops env (a, ta1) b
    let ((a', b'), (t1b, t2b), s2) = checkApp ops (s1 `compose` env) (a_, substitute s1 ta2) b_
    ((a', b'), (Or t1a t1b, Or t2a t2b), s2 `compose` s1)
  Fun t1 t2 -> do
    let ((a', _), (b', t1'), s) = check2 ops env (a, Fun t1 t2) (b, t1)
    ((a', b'), (t1', substitute s t2), s)
  Meta _ ta -> checkApp ops env (a, ta) b
  _ -> do
    let ((b', tb), s) = infer ops env b
    ((substitute s a, b'), (Err $ TypeError $ NotAFunction (substitute s a) (substitute s ta), tb), s)

instantiate :: [String] -> Expr -> (Expr, Substitution)
instantiate vars (For x a) | x `occurs` a = do
  let y = newName vars x
  let (b, s) = instantiate (y : vars) (substitute [(x, Var y)] a)
  (b, (y, Var y) : s)
instantiate vars (For _ a) = instantiate vars a
instantiate vars (Meta _ a) = instantiate vars a
instantiate _ a = (a, [])

-- -- Core parser
-- type Parser a = P.Parser String a

-- parseEnv :: Parser Env
-- parseEnv = do
--   env <- P.zeroOrMore parseDef
--   _ <- P.endOfFile
--   return env

-- parseDef :: Parser (String, Expr)
-- parseDef = do
--   x <- parseName
--   _ <- P.spaces
--   _ <- P.char '='
--   _ <- P.spaces
--   a <- parseExpr
--   _ <- P.spaces
--   _ <- P.char '\n'
--   _ <- P.whitespaces
--   return (x, a)

-- parseName :: Parser String
-- parseName =
--   (P.oneOrMore . P.oneOf)
--     [ P.alphanumeric,
--       P.char '_',
--       P.char '-'
--     ]

-- parseExpr :: Parser Expr
-- parseExpr =
--   P.oneOf
--     [ Int <$> P.integer,
--       Num <$> P.number,
--       Tag <$> do
--         _ <- P.char ':'
--         parseName,
--       do
--         name <- parseName
--         let expr = case name of
--               "@IntT" -> IntT
--               "@NumT" -> NumT
--               "@Err" -> Err
--               x -> Var x
--         return expr,
--       do
--         _ <- P.char '('
--         tag <- parseName
--         _ <- P.spaces
--         expr <- case tag of
--           "@Ann" -> expr2 Ann parseExpr parseExpr
--           "@And" -> expr2 And parseExpr parseExpr
--           "@Or" -> expr2 Or parseExpr parseExpr
--           "@For" -> expr2 For parseName parseExpr
--           "@Fix" -> expr2 Fix parseName parseExpr
--           "@Fun" -> expr2 Fun parseExpr parseExpr
--           "@App" -> expr2 App parseExpr parseExpr
--           "@Call" -> do
--             f <- parseName
--             args <- P.zeroOrMore $ do
--               _ <- P.spaces
--               parseExpr
--             return (Call f args)
--           _ -> P.fail'
--         _ <- P.spaces
--         _ <- P.char ')'
--         return expr
--     ]
--   where
--     expr2 f p q = do
--       a <- p
--       _ <- P.spaces
--       f a <$> q
