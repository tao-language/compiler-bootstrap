module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.Function ((&))
import Data.List (delete, intercalate, union)
import Data.Maybe (fromMaybe)
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
  | Call String Type [Expr]
  | Let [(String, Expr)] Expr
  | Err
  deriving (Eq, Show)

type Type = Expr

type Ops = [(String, [Expr] -> Maybe Expr)]

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
  Call f t args -> '%' : f ++ "<" ++ format t ++ ">(" ++ intercalate ", " (map format args) ++ ")"
  Let env b -> "@{" ++ intercalate "; " (map (\(x, a) -> name x ++ " = " ++ format a) env) ++ "} " ++ format b
  Err -> "!error"
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
or' [] = Err
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
lam ps b = for (freeVars ps) (fun ps b)

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
matchFun [] = Err
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

class FreeVars a where
  freeVars :: a -> [String]

instance FreeVars Expr where
  freeVars :: Expr -> [String]
  freeVars Any = []
  freeVars Unit = []
  freeVars IntT = []
  freeVars NumT = []
  freeVars (Int _) = []
  freeVars (Num _) = []
  freeVars (Var x) = [x]
  freeVars (Tag _) = []
  freeVars (Ann a b) = freeVars a `union` freeVars b
  freeVars (And a b) = freeVars a `union` freeVars b
  freeVars (Or a b) = freeVars a `union` freeVars b
  freeVars (For x a) = delete x (freeVars a)
  freeVars (Fix x a) = delete x (freeVars a)
  freeVars (Fun a b) = freeVars a `union` freeVars b
  freeVars (App a b) = freeVars a `union` freeVars b
  freeVars (Call _ t args) = foldr (union . freeVars) (freeVars t) args
  freeVars (Let [] b) = freeVars b
  freeVars (Let ((x, a) : defs) b) = delete x (freeVars a `union` freeVars (Let defs b))
  freeVars Err = []

instance FreeVars [Expr] where
  freeVars :: [Expr] -> [String]
  freeVars [] = []
  freeVars (a : bs) = freeVars a `union` freeVars bs

freeTags :: Expr -> [String]
freeTags Any = []
freeTags Unit = []
freeTags IntT = []
freeTags NumT = []
freeTags (Int _) = []
freeTags (Num _) = []
freeTags (Var _) = []
freeTags (Tag k) = [k]
freeTags (Ann a b) = freeTags a `union` freeTags b
freeTags (And a b) = freeTags a `union` freeTags b
freeTags (Or a b) = freeTags a `union` freeTags b
freeTags (For x a) = delete x (freeTags a)
freeTags (Fix x a) = delete x (freeTags a)
freeTags (Fun a b) = freeTags a `union` freeTags b
freeTags (App a b) = freeTags a `union` freeTags b
freeTags (Call _ t args) = foldr (union . freeTags) (freeTags t) args
freeTags (Let [] b) = freeTags b
freeTags (Let ((x, a) : defs) b) = delete x (freeTags a `union` freeTags (Let defs b))
freeTags Err = []

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
reduce :: Ops -> Expr -> Expr
reduce ops = \case
  App a b -> reduceApp ops a b
  Let env expr -> reduceLet ops env expr
  expr -> expr

reduceLet :: Ops -> Env -> Expr -> Expr
reduceLet ops env = \case
  Var x -> case lookup x env of
    Just (Var x') | x == x' -> Var x
    Just (Ann (Var x') _) | x == x' -> Var x
    Just a -> reduce ops a
    Nothing -> Var x
  Ann a b -> Ann (Let env a) (Let env b)
  And a b -> And (Let env a) (Let env b)
  Or a b -> Or (Let env a) (Let env b)
  For x a -> For x (Let env a)
  Fix x a -> Fix x (Let env a)
  Fun a b -> Fun (Let env a) (Let env b)
  App a b -> reduceApp ops (Let env a) (Let env b)
  Call f t args -> case (lookup f ops, Let env t, Let env <$> args) of
    (Just call, t, args) | Just result <- call (eval ops <$> args) -> Ann result t
    (Just call, t, args) -> error $ show (call (eval ops <$> args))
    (_, t, args) -> Call f t args
  Let env' a -> reduce ops (Let (env ++ env') a)
  expr -> expr

reduceApp :: Ops -> Expr -> Expr -> Expr
reduceApp ops a b = case (reduce ops a, reduce ops b) of
  (Any, b) -> App Any b
  (Var x, b) -> App (Var x) b
  (Or a1 a2, b) -> case reduceApp ops a1 b of
    Err -> reduceApp ops a2 b
    c -> c
  (For x a, b) -> reduceApp ops (Let [(x, Var x)] a) b
  (Fix x a, b@Var {}) -> App (Fix x a) b
  (Fix x a, b@App {}) -> App (Fix x a) b
  (Fix x a, b) -> reduceApp ops (Let [(x, Fix x a)] a) b
  (App a1 a2, b) -> App (App a1 a2) b
  (Fun a c, b) -> case match False ops a b of
    Just env -> reduce ops (Let env c)
    Nothing -> Err
  (Call f t args, b) -> App (Call f t args) b
  _ -> Err

match :: Bool -> Ops -> Expr -> Expr -> Maybe Env
match unify ops (Let env (Tag k)) b = case lookup k env of
  Just def -> match unify ops (Tag k) (App def b)
  Nothing -> match unify ops (Tag k) b
match unify ops (Let env (Let env' a)) b =
  match unify ops (Let (env ++ env') a) b
match unify ops a b = case (reduce ops a, reduce ops b, unify) of
  (Any, _, _) -> Just []
  (_, Any, True) -> Just []
  (Unit, Unit, _) -> Just []
  (IntT, IntT, _) -> Just []
  (NumT, NumT, _) -> Just []
  (Int i, Int i', _) | i == i' -> Just []
  (Num n, Num n', _) | n == n' -> Just []
  (Tag k, Tag k', _) | k == k' -> Just []
  (Var x, b, _) -> Just [(x, b)]
  (a, Var x, True) -> Just [(x, a)]
  (Ann a ta, Ann b tb, _) -> do
    env1 <- match True ops ta tb
    env2 <- match unify ops a b
    Just (env1 ++ env2)
  (And (Let env (Tag k)) a, b, _) -> case lookup k env of
    Just def -> match unify ops (And (Tag k) a) (App def b)
    Nothing -> match unify ops (And (Tag k) a) b
  (And (Let env (Let env' a1)) a2, b, _) ->
    match unify ops (Let (env ++ env') (And a1 a2)) b
  (And a1 a2, And b1 b2, _) -> do
    env1 <- match unify ops a1 b1
    env2 <- match unify ops a2 b2
    Just (env1 ++ env2)
  (Or a1 a2, b, _) -> case match unify ops a1 b of
    Just env1 -> case match unify ops a2 b of
      Just env2 -> Just (env1 ++ env2)
      Nothing -> Just env1
    Nothing -> match unify ops a2 b
  (a, Or b1 b2, _) -> case match unify ops a b1 of
    Just env1 -> case match unify ops a b2 of
      Just env2 -> Just (env1 ++ env2)
      Nothing -> Just env1
    Nothing -> match unify ops a b2
  (For x a, b, _) -> do match unify ops (Let [(x, Var x)] a) b
  (a, For x b, _) -> do match unify ops a (Let [(x, Var x)] b)
  -- \| Fix String Expr
  (Fun a1 a2, Fun b1 b2, _) -> match unify ops (And a1 a2) (And b1 b2)
  (App a1 a2, App b1 b2, _) -> match unify ops (And a1 a2) (And b1 b2)
  (Call x t args, Call x' t' args', _) | x == x' -> do
    match unify ops (and' (t : args)) (and' (t' : args'))
  (Err, Err, _) -> Just []
  (Ann a _, b, _) -> match unify ops a b
  (a, Ann b _, _) -> match unify ops a b
  _ -> Nothing

eval :: Ops -> Expr -> Expr
eval ops expr = case reduce ops expr of
  Ann a b -> Ann (eval ops a) (eval ops b)
  And a b -> And (eval ops a) (eval ops b)
  Or a b -> Or (eval ops a) (eval ops b)
  For x a -> for [x] (eval ops (Let [(x, Var x)] a))
  Fix x a -> Fix x (eval ops (Let [(x, Var x)] a))
  Fun a b -> Fun (eval ops a) (eval ops b)
  App a b -> App (eval ops a) (eval ops b)
  Call f t args -> Call f (eval ops t) (eval ops <$> args)
  a -> a

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
substitute s (Call op t args) = Call op (substitute s t) (map (substitute s) args)
substitute s (Let env b) = do
  let sub (x, a) = (x, substitute s a)
  let s' = filter (\(x, _) -> x `notElem` map fst env) s
  Let (map sub env) (substitute s' b)
substitute _ Err = Err

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = do
  let sub s (x, a) = case lookup x s of
        Just b -> (x, b)
        Nothing -> (x, substitute s a)
  let notIn (x, _) s = x `notElem` map fst s
  s1 `union` map (sub s1) s2

dropTypes :: Expr -> Expr
dropTypes (Ann a _) = dropTypes a
dropTypes (And a b) = And (dropTypes a) (dropTypes b)
dropTypes (Or a b) = Or (dropTypes a) (dropTypes b)
dropTypes (For x a) = For x (dropTypes a)
dropTypes (Fix x a) = Fix x (dropTypes a)
dropTypes (Fun (Ann a (Var _)) b) = Fun (dropTypes a) (dropTypes b)
dropTypes (Fun (Ann a1 a2) b) = Fun (Ann (dropTypes a1) (dropTypes a2)) (dropTypes b)
dropTypes (Fun a b) = Fun (dropTypes a) (dropTypes b)
dropTypes (App a (Ann b (Var _))) = App (dropTypes a) (dropTypes b)
dropTypes (App a (Ann b1 b2)) = App (dropTypes a) (Ann (dropTypes b1) (dropTypes b2))
dropTypes (App a b) = App (dropTypes a) (dropTypes b)
dropTypes (Call op t args) = Call op (dropTypes t) (map dropTypes args)
dropTypes (Let defs b) = Let (map (second dropTypes) defs) (dropTypes b)
dropTypes a = a

unify :: Ops -> Env -> Expr -> Expr -> (Expr, Substitution, [TypeError])
unify ops env a b = case (a, b) of
  (Any, b) -> (b, [], [])
  (a, Any) -> (a, [], [])
  (IntT, IntT) -> (IntT, [], [])
  (Int _, IntT) -> (IntT, [], [])
  (IntT, Int _) -> (IntT, [], [])
  (NumT, NumT) -> (NumT, [], [])
  (Num _, NumT) -> (NumT, [], [])
  (NumT, Num _) -> (NumT, [], [])
  (Int i, Int i') | i == i' -> (Int i, [], [])
  (Num n, Num n') | n == n' -> (Num n, [], [])
  (Var x, Var x') | x == x' -> (Var x, [], [])
  (Var x, b) | x `occurs` b -> (b, [], [OccursError x b])
  (Var x, b) -> (b, [(x, b)], [])
  (a, Var x) -> unify ops env (Var x) a
  (Tag k, Tag k') | k == k' -> (Tag k, [], [])
  (a, Tag k) | Just tdef <- lookup k env -> do
    let a' = eval ops (Let env (App (Tag k) a))
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s, e) = unify ops env' a' (Tag k)
    (t, [(k, tdef)] `compose` s, e)
  (Tag k, b) | Just tdef <- lookup k env -> do
    let b' = eval ops (Let env (App (Tag k) b))
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s, e) = unify ops env' (Tag k) b'
    (t, [(k, tdef)] `compose` s, e)
  (a, And (Tag k) b) | Just tdef <- lookup k env -> do
    let a' = eval ops (Let env (App (And (Tag k) b) a))
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s, e) = unify ops env' a' (And (Tag k) b)
    (t, [(k, tdef)] `compose` s, e)
  (And (Tag k) a, b) | Just tdef <- lookup k env -> do
    let b' = eval ops (Let env (App (And (Tag k) a) b))
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s, e) = unify ops env' (And (Tag k) a) b'
    (t, [(k, tdef)] `compose` s, e)
  (Ann a ta, Ann b tb) -> do
    let ((a', ta'), s, e) = unify2 ops env (a, b) (ta, tb)
    (Ann a' ta', s, e)
  (Ann a _, b) -> unify ops env a b
  (a, Ann b _) -> unify ops env a b
  (And a1 b1, And a2 b2) -> do
    let ((a, b), s, e) = unify2 ops env (a1, a2) (b1, b2)
    (And a b, s, e)
  (Or a1 a2, b) -> do
    let ((c1, c2), s1, e1) = unify2 ops env (a1, b) (a2, b)
    let (c, s2, e2) = unify ops env c1 c2
    case (c, s2 `compose` s1, e1 ++ e2) of
      (Err, s, e) -> (substitute s2 (Or c1 c2), s, e)
      (c, s, e) -> (c, s, e)
  (a, Or b1 b2) -> do
    let ((c1, c2), s1, e1) = unify2 ops env (a, b1) (a, b2)
    let (c, s2, e2) = unify ops env c1 c2
    case (c, s2 `compose` s1, e1 ++ e2) of
      (Err, s, e) -> (substitute s2 (Or c1 c2), s, e)
      (c, s, e) -> (c, s, e)
  (a, For x b) -> do
    let (b', s1) = instantiate (freeVars a) (For x b)
    let (c, s2, e) = unify ops (s1 `compose` env) a b'
    (c, s2 `compose` s1, e)
  (For x a, b) -> do
    let (a', s1) = instantiate (freeVars b) (For x a)
    let (c, s2, e) = unify ops (s1 `compose` env) a' b
    (c, s2 `compose` s1, e)
  (Fix _ a, b) -> unify ops env a b
  (a, Fix _ b) -> unify ops env a b
  (Fun a1 b1, Fun a2 b2) -> do
    let ((a, b), s, e) = unify2 ops env (a1, a2) (b1, b2)
    (Fun a b, s, e)
  (Call op a args, Call op' b args') | op == op' -> do
    let (t, s1, e1) = unify ops env a b
    let (args, s2, e2) = unifyAll ops (s1 `compose` env) (substitute s1 <$> args) (substitute s1 <$> args')
    (Call op t args, s2 `compose` s1, e1 ++ e2)
  (a, b) -> (Err, [], [TypeMismatch a b])

unify2 :: Ops -> Env -> (Expr, Expr) -> (Expr, Expr) -> ((Expr, Expr), Substitution, [TypeError])
unify2 ops env (a1, a2) (b1, b2) = do
  let (ta, s1, e1) = unify ops env a1 a2
  let (tb, s2, e2) = unify ops env (substitute s1 b1) (substitute s1 b2)
  ((substitute s2 ta, tb), s2 `compose` s1, e1 ++ e2)

unifyAll :: Ops -> Env -> [Expr] -> [Expr] -> ([Expr], Substitution, [TypeError])
unifyAll ops env (a : bs) (a' : bs') = do
  let (ta, s1, e1) = unify ops env a a'
  let (tbs, s2, e2) = unifyAll ops env (map (substitute s1) bs) (map (substitute s1) bs')
  (ta : tbs, s2 `compose` s1, e1 ++ e2)
unifyAll _ _ _ _ = ([], [], [])

infer :: Ops -> Env -> Expr -> ((Expr, Expr), Substitution, [TypeError])
infer _ env Any = do
  let x = newName ("_" : map fst env) "_"
  ((Any, Var x), [(x, Var x)], [])
infer _ _ Unit = ((Unit, Unit), [], [])
infer _ _ IntT = ((IntT, IntT), [], [])
infer _ _ NumT = ((NumT, NumT), [], [])
infer _ _ (Int i) = ((Int i, IntT), [], [])
infer _ _ (Num n) = ((Num n, NumT), [], [])
infer _ _ (Tag k) = ((Tag k, Tag k), [], [])
infer ops env (Var x) = do
  let (ta, s, e) = case lookup x env of
        Just (Var x') | x == x' -> do
          let y = newName (map fst env) (x ++ "T")
          (Var y, [(y, Var y), (x, Ann (Var x) (Var y))], [])
        Just (Ann (Var x') ty) | x == x' -> do
          let (t, s) = instantiate (map fst env) ty
          (t, s, [])
        Just a -> do
          let ((_, ta), s, e) = infer ops env a
          (ta, s, e)
        Nothing -> (Err, [], [UndefinedVar x])
  ((Var x, ta), s, e)
infer ops env (Ann a t) = check ops env a t
infer ops env (And a b) = do
  let ((a', ta), (b', tb), s, e) = infer2 ops env a b
  ((And a' b', And ta tb), s, e)
infer ops env (Or a b) = do
  let ((a', ta), (b', tb), s, e) = infer2 ops env a b
  ((Or a' b', Or ta tb), s, e)
infer ops env (For x a) = do
  let y = newName (map fst env) x
  let ((a', ta), s, e) = infer ops ((y, Var y) : env) (substitute [(x, Var y)] a)
  ((a', ta), s `compose` [(y, Var y)], e)
infer ops env (Fix x a) = do
  let ((a', ta), s, e) = infer ops ((x, Var x) : env) a
  ((fix [x] a', ta), s, e)
infer ops env (Fun a b) = do
  let ((a', ta), (b', tb), s, e) = infer2 ops env a b
  ((Fun (Ann a' ta) b', Fun ta tb), s, e)
infer ops env (App a b) = do
  let ((a', ta), (b', tb), s1, e1) = infer2 ops env a b
  let unifyApp ops env ta tb = case ta of
        Var x -> do
          let y = newName (map fst env) x
          (Var y, [(y, Var y), (x, Fun tb (Var y))], [])
        Or t1 t2 -> do
          let (t1', s1, e1) = unifyApp ops env t1 tb
          let (t2', s2, e2) = unifyApp ops (s1 `compose` env) (substitute s1 t2) (substitute s1 tb)
          (Or (substitute s2 t1') t2', s2 `compose` s1, e1 ++ e2)
        Fun t1 t2 -> do
          let (_, s, e) = unify ops env t1 tb
          (substitute s t2, s, e)
        _ -> (Err, [], [NotAFunction a ta])
  let (t, s2, e2) = unifyApp ops (s1 `compose` env) ta tb
  ((App (substitute s2 a') (Ann (substitute s2 b') (substitute s2 tb)), t), s2 `compose` s1, e1 ++ e2)
infer ops env (Let defs a) = infer ops (defs ++ env) a
infer ops env (Call op t args) = do
  let ((t', _), s1, e1) = infer ops env t
  let (args', s2, e2) = inferAll ops (s1 `compose` env) (substitute s1 <$> args)
  ((Call op t' (map fst args'), substitute s2 t'), s2 `compose` s1, e1 ++ e2)
infer _ _ Err = ((Err, Any), [], [])

infer2 :: Ops -> Env -> Expr -> Expr -> ((Expr, Expr), (Expr, Expr), Substitution, [TypeError])
infer2 ops env a b = do
  let ((a', ta), s1, e1) = infer ops env a
  let ((b', tb), s2, e2) = infer ops (s1 `compose` env) (substitute s1 b)
  ((substitute s2 a', substitute s2 ta), (b', tb), s2 `compose` s1, e1 ++ e2)

inferAll :: Ops -> Env -> [Expr] -> ([(Expr, Expr)], Substitution, [TypeError])
inferAll _ _ [] = ([], [], [])
inferAll ops env (a : bs) = do
  let ((a', ta), s1, e1) = infer ops env a
  let (bts, s2, e2) = inferAll ops (s1 `compose` env) (map (substitute s1) bs)
  ((substitute s2 a', substitute s2 ta) : bts, s2 `compose` s1, e1 ++ e2)

check :: Ops -> Env -> Expr -> Expr -> ((Expr, Expr), Substitution, [TypeError])
check ops env (And a b) (And ta tb) = do
  let ((a', ta'), (b', tb'), s, e) = check2 ops env (a, ta) (b, tb)
  ((And a' b', And ta' tb'), s, e)
check ops env (Or a b) t = do
  let ((a', ta'), (b', tb'), s, e) = check2 ops env (a, t) (b, t)
  ((Or a' b', ta'), s, e)
check ops env (For x a) t = do
  let y = newName (map fst env) x
  let ((a', t'), s, e) = check ops ((y, Var y) : env) (substitute [(x, Var y)] a) t
  ((a', t'), [(y, Var y)] `compose` s, e)
check ops env (Fun a b) (Fun ta tb) = do
  let ((a', ta'), (b', tb'), s, e) = check2 ops env (a, ta) (b, tb)
  ((Fun (Ann a' ta') b', Fun ta' tb'), s, e)
check ops env (App a b) t2 = do
  let x = newName ("$" : map fst env) "$"
  let env' = (x, Var x) : env
  let ((b', t1), s1, e1) = infer ops env' b
  let ((a', _), s2, e2) = check ops (s1 `compose` env') (substitute s1 a) (Fun t1 (substitute s1 t2))
  let s = s2 `compose` s1
  ((App a' (substitute s2 b'), substitute s t2), s, e1 ++ e2)
check ops env a t = do
  let ((a', ta), s1, e1) = infer ops env a
  let (t', s2, e2) = unify ops env ta (substitute s1 t)
  ((substitute s2 a', t'), s2 `compose` s1, e1 ++ e2)

check2 :: Ops -> Env -> (Expr, Expr) -> (Expr, Expr) -> ((Expr, Expr), (Expr, Expr), Substitution, [TypeError])
check2 ops env (a, ta) (b, tb) = do
  let ((a', ta'), s1, e1) = check ops env a ta
  let ((b', tb'), s2, e2) = check ops (s1 `compose` env) (substitute s1 b) (substitute s1 tb)
  ((substitute s2 a', substitute s2 ta'), (b', tb'), s2 `compose` s1, e1 ++ e2)

instantiate :: [String] -> Expr -> (Expr, Substitution)
instantiate vars (For x a) | x `occurs` a = do
  let y = newName vars x
  let (b, s) = instantiate (y : vars) (substitute [(x, Var y)] a)
  (b, (y, Var y) : s)
instantiate vars (For _ a) = instantiate vars a
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
