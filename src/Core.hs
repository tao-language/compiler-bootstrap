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
  = Knd
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Tag String
  | Var String
  | For String Expr
  | Fix String Expr
  | Fun Expr Expr
  | App Expr Expr
  | And Expr Expr
  | Or Expr Expr
  | Ann Expr Expr
  | Call String [Expr]
  | Let [(String, Expr)] Expr
  | Meta Metadata Expr
  | Err
  deriving (Eq)

data Metadata
  = Location String (Int, Int)
  | Comment String
  | Unwrap
  deriving (Eq)

type Ops = [(String, (Expr -> Expr) -> [Expr] -> Expr)]

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

instance Show Expr where
  show :: Expr -> String
  show expr = case expr of
    Knd -> "!Knd"
    IntT -> "!IntT"
    NumT -> "!NumT"
    Int i -> show i
    Num n -> show n
    Var x | isName x -> x
    Var x -> "`" ++ replaceString "`" "\\`" x ++ "`"
    Tag k | isName k -> ':' : k
    Tag k -> ":`" ++ replaceString "`" "\\`" k ++ "`"
    For _ _ -> do
      let (xs, a) = asFor expr
      "(@" ++ unwords xs ++ ". " ++ show a ++ ")"
    Fix x a -> "(&" ++ x ++ ". " ++ show a ++ ")"
    Fun _ _ -> do
      let (args, ret) = asFun expr
      "(" ++ intercalate ", " (map show args) ++ " -> " ++ show ret ++ ")"
    App a b -> do
      let (xs, a') = asFor a
      case a' of
        Fun a c -> do
          let def = show a ++ " = " ++ show b ++ "; " ++ show c
          if null xs then def else "@" ++ unwords xs ++ ". " ++ def
        _ -> "(" ++ show a ++ " " ++ show b ++ ")"
    And _ _ -> "(" ++ intercalate ", " (map show (andOf expr)) ++ ")"
    Or _ _ -> "(" ++ intercalate " | " (map show (orOf expr)) ++ ")"
    Ann a b -> "(" ++ show a ++ " : " ++ show b ++ ")"
    Call f xs -> '%' : f ++ "(" ++ intercalate ", " (map show xs) ++ ")"
    Let env b -> "{" ++ intercalate "; " (map (\(x, a) -> x ++ " = " ++ show a) env) ++ "} " ++ show b
    Meta m a -> '^' : show m ++ "(" ++ show a ++ ")"
    Err -> "!error"
    where
      isName = all (\c -> isAlphaNum c || c `elem` ['_', '-'])

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
--     Call ('$' : op) [a] -> prefix 8 ('$' : op ++ " ") a
--     Call op [a] -> prefix 8 op a
--     App a b -> infixL 8 a " " b
--     Err -> atom 12 "!error"
--     Knd -> atom 12 "!Kind"
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
--     Meta m a -> prefix p ("#(" ++ show m ++ ")") a
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

instance Show Metadata where
  show :: Metadata -> String
  show (Location src (row, col)) = src ++ ':' : show row ++ ':' : show col

-- Syntax sugar
tag :: String -> [Expr] -> Expr
tag k args = and' (Tag k : args)

-- ptag :: String -> [Pattern] -> Pattern
-- ptag k = pApp (PTag k)

fix :: [String] -> Expr -> Expr
fix [] a = a
fix (x : xs) a
  | x `occurs` a = Fix x (fix xs a)
  | otherwise = fix xs a

for :: [String] -> Expr -> Expr
for [] a = a
for (x : xs) a | x `occurs` a = For x (for xs a)
for (_ : xs) a = for xs a

asFor :: Expr -> ([String], Expr)
asFor (For x a) = let (xs, b) = asFor a in (x : xs, b)
asFor a = ([], a)

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

lam :: [Expr] -> Expr -> Expr
lam ps b = for (freeVars ps) (fun ps b)

asFun :: Expr -> ([Expr], Expr)
asFun (Fun arg ret) = let (args, ret') = asFun ret in (arg : args, ret')
asFun a = ([], a)

add :: Expr -> Expr -> Expr
add a b = Call "+" [a, b]

and' :: [Expr] -> Expr
and' [] = Err
and' [a] = a
and' (a : bs) = And a (and' bs)

andOf :: Expr -> [Expr]
andOf (And a b) = a : andOf b
andOf a = [a]

orOf :: Expr -> [Expr]
orOf (Or a b) = a : orOf b
orOf a = [a]

let' :: (Expr, Expr) -> Expr -> Expr
let' (Var x, Var x') b | x == x' = b
let' (p, a) b = do
  let xs = freeVars p
  App (for xs (Fun p b)) (fix (filter (`occurs` a) xs) a)

lets :: [(Expr, Expr)] -> Expr -> Expr
lets defs b = foldr let' b defs

letVar :: (String, Expr) -> Expr -> Expr
letVar (x, a) = let' (Var x, a)

letVars :: [(String, Expr)] -> Expr -> Expr
letVars vars b = foldr letVar b vars

app :: Expr -> [Expr] -> Expr
app = foldl App

-- appOf :: Expr -> (Expr, [Expr])
-- appOf (App a b) = let (a', bs) = appOf a in (a', bs ++ [b])
-- appOf a = (a, [])

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

list :: Expr -> Expr -> [Expr] -> Expr
list _ nil [] = nil
list cons nil (a : bs) = app cons [a, list cons nil bs]

match' :: [Expr] -> [([Expr], Expr)] -> Expr
match' args cases = app (matchFun cases) args

matchFun :: [([Expr], Expr)] -> Expr
matchFun [] = Err
matchFun [(ps, b)] = fun ps b
matchFun ((ps, b) : cases) = fun ps b `Or` matchFun cases

meta :: [Metadata] -> Expr -> Expr
meta ms a = foldr Meta a ms

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
  freeVars Knd = []
  freeVars IntT = []
  freeVars NumT = []
  freeVars (Int _) = []
  freeVars (Num _) = []
  freeVars (Var x) = [x]
  freeVars (Tag _) = []
  freeVars (For x a) = delete x (freeVars a)
  freeVars (Fix x a) = delete x (freeVars a)
  freeVars (Fun a b) = freeVars a `union` freeVars b
  freeVars (App a b) = freeVars a `union` freeVars b
  freeVars (And a b) = freeVars a `union` freeVars b
  freeVars (Or a b) = freeVars a `union` freeVars b
  freeVars (Ann a _) = freeVars a
  freeVars (Call _ args) = foldr (union . freeVars) [] args
  freeVars (Meta _ a) = freeVars a
  freeVars Err = []

instance FreeVars [Expr] where
  freeVars :: [Expr] -> [String]
  freeVars [] = []
  freeVars (a : bs) = freeVars a `union` freeVars bs

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
  App (Let env (Tag k)) b -> case lookup k env of
    Just a -> reduce ops (App (Let env a) b)
    Nothing -> reduce ops b
  App (Let env (Let env' (Tag k))) b ->
    reduce ops (App (Let (env ++ env') (Tag k)) b)
  App a b -> case (reduce ops a, reduce ops b) of
    (Var x, b) -> App (Var x) b
    (For x a, b) -> reduce ops (App (Let [(x, Var x)] a) b)
    (Fix x a, b@Var {}) -> App (Fix x a) b
    (Fix x a, b@App {}) -> App (Fix x a) b
    (Fix x a, b) -> reduce ops (App (Let [(x, Fix x a)] a) b)
    (App a1 a2, b) -> App (App a1 a2) b
    (And (Let env (Tag k)) a2, b) -> case lookup k env of
      Just a1 -> reduce ops (App (App (Let env a1) a2) b)
      Nothing -> b
    (And (Let env (Let env' a1)) a2, b) ->
      reduce ops (App (And (Let (env ++ env') a1) a2) b)
    (Fun (Let env (Tag k)) c, b) -> do
      let b' = App (Let env (Tag k)) b
      reduce ops (App (Fun (Tag k) c) b')
    (Fun (Let env (Let env' a)) c, b) ->
      reduce ops (App (Fun (Let (env ++ env') a) c) b)
    (Fun a c, b) -> case (reduce ops a, b) of
      (Knd, Knd) -> reduce ops c
      (IntT, IntT) -> reduce ops c
      (NumT, NumT) -> reduce ops c
      (Int i, Int i') | i == i' -> reduce ops c
      (Num n, Num n') | n == n' -> reduce ops c
      (Tag k, Tag k') | k == k' -> reduce ops c
      (Var x, b) -> reduce ops (Let [(x, b)] c)
      (And (Let env (Tag k)) a2, b) -> do
        let b' = App (And (Let env (Tag k)) a2) b
        reduce ops (App (Fun (And (Tag k) a2) c) b')
      (And (Let env (Let env' a1)) a2, b) ->
        reduce ops (App (Fun (And (Let (env ++ env') a1) a2) c) b)
      (And a1 a2, And b1 b2) -> reduce ops (App (Fun a1 (App (Fun a2 c) b2)) b1)
      (Or a1 a2, b) -> reduce ops (App (Or (Fun a1 c) (Fun a2 c)) b)
      (a, Or b1 b2) -> case reduce ops (App (Fun a c) b1) of
        Err -> reduce ops (App (Fun a c) b2)
        c -> c
      (Err, Err) -> reduce ops c
      _ -> Err
    (Or a1 a2, b) -> case reduce ops (App a1 b) of
      Err -> reduce ops (App a2 b)
      c -> c
    _ -> Err
  Let env expr -> case expr of
    Var x -> case lookup x env of
      Just (Var x') | x == x' -> Var x
      Just (Ann (Var x') _) | x == x' -> Var x
      Just a -> reduce ops a
      Nothing -> Var x
    For x a -> For x (Let env a)
    Fix x a -> Fix x (Let env a)
    Fun a b -> Fun (Let env a) (Let env b)
    App a b -> reduce ops (App (Let env a) (Let env b))
    And a b -> And (Let env a) (Let env b)
    Or a b -> Or (Let env a) (Let env b)
    Ann a _ -> reduce ops (Let env a)
    Call f args -> case (lookup f ops, Let env <$> args) of
      (Just call, args) -> call (reduce ops) args
      (Nothing, args) -> Call f args
    Let env' a -> reduce ops (Let (env ++ env') a)
    Meta _ a -> reduce ops (Let env a)
    expr -> expr
  Ann a _ -> reduce ops a
  Meta _ a -> reduce ops a
  expr -> expr

eval :: Ops -> Expr -> Expr
eval ops expr = case reduce ops expr of
  For x a -> For x (eval ops (Let [(x, Var x)] a))
  Fix x a -> Fix x (eval ops (Let [(x, Var x)] a))
  Fun a b -> Fun (eval ops a) (eval ops b)
  App a b -> App (eval ops a) (eval ops b)
  And a b -> And (eval ops a) (eval ops b)
  Or a b -> Or (eval ops a) (eval ops b)
  Call f args -> Call f (eval ops <$> args)
  a -> a

substitute :: Substitution -> Expr -> Expr
substitute _ Knd = Knd
substitute _ IntT = IntT
substitute _ NumT = NumT
substitute _ (Int i) = Int i
substitute _ (Num n) = Num n
substitute [] (Var x) = Var x
substitute ((x, a) : _) (Var x') | x == x' = a
substitute (_ : s) (Var x) = substitute s (Var x)
substitute s (Tag k) = Tag k
substitute s (For x a) = For x (substitute (filter ((/= x) . fst) s) a)
substitute s (Fix x a) = Fix x (substitute (filter ((/= x) . fst) s) a)
substitute s (Fun a b) = Fun (substitute s a) (substitute s b)
substitute s (App a b) = App (substitute s a) (substitute s b)
substitute s (And a b) = And (substitute s a) (substitute s b)
substitute s (Or a b) = Or (substitute s a) (substitute s b)
substitute s (Ann (Tag k) ty) = Ann (Tag k) (substitute s ty)
substitute s (Ann a _) = substitute s a
substitute s (Call op args) = Call op (map (substitute s) args)
substitute s (Meta m a) = Meta m (substitute s a)
substitute _ Err = Err

unify :: Expr -> Expr -> Either TypeError (Expr, Substitution)
unify a b = case (a, b) of
  (IntT, IntT) -> Right (IntT, [])
  (Int _, IntT) -> Right (IntT, [])
  (IntT, Int _) -> Right (IntT, [])
  (NumT, NumT) -> Right (NumT, [])
  (Num _, NumT) -> Right (NumT, [])
  (NumT, Num _) -> Right (NumT, [])
  (Int i, Int i') | i == i' -> Right (Int i, [])
  (Num n, Num n') | n == n' -> Right (Num n, [])
  (Var x, Var x') | x == x' -> Right (Var x, [])
  (Tag k, Tag k') | k == k' -> Right (Tag k, [])
  (Var x, b) | x `occurs` b -> Left (OccursError x b)
  (Var x, b) -> Right (b, [(x, b)])
  (a, Var x) -> unify (Var x) a
  (a, For x b) -> do
    let (b', vars) = instantiate (freeVars a) (For x b)
    (t, s) <- unify a b'
    Right (for (map fst vars) t, s `compose` vars)
  (For x a, b) -> do
    let (a', vars) = instantiate (freeVars b) (For x a)
    (t, s) <- unify a' b
    Right (for (map fst vars) t, s `compose` vars)
  (Fix _ a, b) -> unify a b
  (a, Fix _ b) -> unify a b
  (Fun a1 b1, Fun a2 b2) -> do
    ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
    Right (Fun ta tb, s)
  (And a1 b1, And a2 b2) -> do
    ((a, b), s) <- unify2 (a1, a2) (b1, b2)
    Right (And a b, s)
  (Or a1 a2, b) -> case unify a1 b of
    Left _ -> case unify a2 b of
      Left _ -> Left (TypeMismatch (Or a1 a2) b)
      Right (a, s) -> Right (a, s)
    Right (a, s1) -> case unify a2 b of
      Left _ -> Right (a, s1)
      Right (b, s2) -> case unify (substitute s2 a) b of
        Left _ -> Right (a, s1)
        Right (c, s3) -> Right (c, s3 `compose` s2 `compose` s1)
  (a, Or b1 b2) -> case unify a b1 of
    Left _ -> case unify a b2 of
      Left _ -> Left (TypeMismatch a (Or b1 b2))
      Right (a, s) -> Right (a, s)
    Right (a, s1) -> case unify a b2 of
      Left _ -> Right (a, s1)
      Right (b, s2) -> case unify (substitute s2 a) b of
        Left _ -> Right (b, s1)
        Right (c, s3) -> Right (c, s3 `compose` s2 `compose` s1)
  (Call op args, Call op' args') | op == op' -> do
    (args, s) <- unifyAll args args'
    Right (Call op args, s)
  (Meta _ a, b) -> unify a b
  (a, Meta _ b) -> unify a b
  (a, b) -> Left (TypeMismatch a b)

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either TypeError ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  (ta, s1) <- unify a1 a2
  (tb, s2) <- unify (substitute s1 b1) (substitute s1 b2)
  Right ((substitute s2 ta, tb), s2 `compose` s1)

unifyAll :: [Expr] -> [Expr] -> Either TypeError ([Expr], Substitution)
unifyAll (a : bs) (a' : bs') = do
  (ta, s1) <- unify a a'
  (tbs, s2) <- unifyAll (map (substitute s1) bs) (map (substitute s1) bs')
  Right (ta : tbs, s2 `compose` s1)
unifyAll _ _ = Right ([], [])

infer :: Ops -> Env -> Expr -> Either TypeError (Expr, Substitution)
infer _ _ Knd = Right (Knd, [])
infer _ _ IntT = Right (Knd, [])
infer _ _ NumT = Right (Knd, [])
infer _ _ (Int _) = Right (IntT, [])
infer _ _ (Num _) = Right (NumT, [])
infer ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let y = newName (map fst env) (x ++ "T")
    Right (Var y, [(y, Var y), (x, Ann (Var x) (Var y))])
  Just (Ann (Var x') ty) | x == x' -> Right (instantiate (map fst env) ty)
  Just a -> infer ops env a
  Nothing -> Left (UndefinedVar x)
infer ops env (Tag k) = case lookup k env of
  Just (Tag k') | k == k' -> Right (Tag k, [])
  Just a -> infer ops env a
  Nothing -> Right (Tag k, [])
infer ops env (Or a b) = do
  ((ta, tb), s1) <- infer2 ops env a b
  case unify ta tb of
    Left _ -> Right (Or ta tb, s1)
    Right (t, s2) -> Right (t, s2 `compose` s1)
infer ops env (And a b) = do
  ((ta, tb), s) <- infer2 ops env a b
  Right (And ta tb, s)
infer ops env (Ann a ty) = check ops env a ty
infer ops env (For x a) = infer ops ((x, Var x) : env) a
infer ops env (Fix x a) = do
  (t, s) <- infer ops ((x, Var x) : env) a
  Right (Fix x t, s)
infer ops env (Fun a b) = do
  ((ta, tb), s) <- infer2 ops env a b
  Right (Fun ta tb, s)
infer ops env (App a b) = do
  ((ta, tb), s1) <- infer2 ops env a b
  case instantiate (map fst env) ta of
    (Var x, s2) -> do
      let y = newName (map fst (s1 `compose` env)) x
      (t, s3) <- infer ops (s1 `compose` env) (App (Ann a (For y $ Fun tb (Var y))) b)
      Right (t, (y, t) : s3 `compose` s2 `compose` s1)
    (Fun t1 t2, s2) -> do
      (_, s3) <- unify tb t1
      Right (substitute s3 t2, s3 `compose` s2 `compose` s1)
    (ta, _) -> Left (NotAFunction a ta)
infer ops env (Let env' a) = infer ops (env' ++ env) a
infer ops env (Call op args) = case lookup op env of
  Just a -> infer ops env (app a args)
  Nothing -> do
    let y = newName (map fst env) (op ++ "T")
    Right (Var y, [(y, Var y), (op, Ann (Call op []) (Var y))])
infer ops env (Meta m a) = do
  (t, s) <- infer ops env a
  Right (Meta m t, s)
infer _ _ Err = Right (Err, [])

infer2 :: Ops -> Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 ops env a b = do
  (ta, s1) <- infer ops env a
  (tb, s2) <- infer ops (s1 `compose` env) b
  Right ((substitute s2 ta, tb), s2 `compose` s1)

inferAll :: Ops -> Env -> [Expr] -> Either TypeError ([Expr], Substitution)
inferAll _ _ [] = Right ([], [])
inferAll ops env (a : bs) = do
  (t, s1) <- infer ops env a
  (ts, s2) <- inferAll ops (s1 `compose` env) bs
  Right (substitute s2 t : ts, s2 `compose` s1)

check :: Ops -> Env -> Expr -> Expr -> Either TypeError (Expr, Substitution)
check ops env a t = do
  (ta, s1) <- case instantiate (map fst env) t of
    (Tag k, _) -> do
      (ta, s) <- infer ops env a
      let t' = Let (s `compose` env) (App (Tag k) ta)
      Right (eval ops t', s)
    (And (Tag k) b, vars) -> do
      (ta, s) <- infer ops (vars ++ env) a
      let t' = Let (s `compose` env) (App (And (Tag k) b) ta)
      Right (eval ops (for (map fst vars) t'), s)
    (_, vars) -> infer ops (vars ++ env) a
  (t, s2) <- unify ta (substitute s1 t)
  Right (t, s2 `compose` s1)

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = apply s1 s2 `union` s1
  where
    apply :: Substitution -> Env -> Env
    apply _ [] = []
    apply s ((x, Ann a t) : env) = do
      (x, Ann (substitute s a) (substitute s t)) : apply s env
    apply s ((x, a) : env) = (x, substitute s a) : apply s env

instantiate :: [String] -> Expr -> (Expr, Substitution)
instantiate vars (For x a) | x `occurs` a = do
  let y = newName vars x
  let (b, s) = instantiate vars (substitute [(x, Var y)] a)
  (b, [(y, Var y)] `union` s)
instantiate vars (For _ a) = instantiate vars a
instantiate _ a = (a, [])

-- checkTypes :: Env -> [TypeError]
-- checkTypes env = do
--   let checkDef (_, a) = case infer env a of
--         Right _ -> []
--         Left err -> [err]
--   concatMap checkDef env

-- rename :: (Expr -> [String] -> String -> String) -> [String] -> Env -> Env -> Env
-- rename _ _ _ [] = []
-- rename f names env ((x, a) : env') = do
--   let t = case infer env a of
--         Right (t, _) -> t
--         Left _ -> Err
--   let y = f t (names ++ map fst env') x
--   (y, eval [(x, Var y)] a) : rename f (y : names) env env'

class DropMeta a where
  dropMeta :: a -> a

instance DropMeta Expr where
  dropMeta :: Expr -> Expr
  dropMeta Knd = Knd
  dropMeta IntT = IntT
  dropMeta NumT = NumT
  dropMeta (Int i) = Int i
  dropMeta (Num n) = Num n
  dropMeta (Var x) = Var x
  dropMeta (Tag k) = Tag k
  dropMeta (For x a) = For x (dropMeta a)
  dropMeta (Fix x a) = Fix x (dropMeta a)
  dropMeta (Fun a b) = Fun (dropMeta a) (dropMeta b)
  dropMeta (App a b) = App (dropMeta a) (dropMeta b)
  dropMeta (And a b) = And (dropMeta a) (dropMeta b)
  dropMeta (Or a b) = Or (dropMeta a) (dropMeta b)
  dropMeta (Ann a t) = Ann (dropMeta a) (dropMeta t)
  dropMeta (Call op args) = Call op (map dropMeta args)
  dropMeta (Meta _ a) = dropMeta a
  dropMeta Err = Err

instance DropMeta (String, Expr) where
  dropMeta :: (String, Expr) -> (String, Expr)
  dropMeta (x, a) = (x, dropMeta a)

-- Core parser
type Parser a = P.Parser String a

parseEnv :: Parser Env
parseEnv = do
  env <- P.zeroOrMore parseDef
  _ <- P.endOfFile
  return env

parseDef :: Parser (String, Expr)
parseDef = do
  x <- parseName
  _ <- P.spaces
  _ <- P.char '='
  _ <- P.spaces
  a <- parseExpr
  _ <- P.spaces
  _ <- P.char '\n'
  _ <- P.whitespaces
  return (x, a)

parseName :: Parser String
parseName =
  (P.oneOrMore . P.oneOf)
    [ P.alphanumeric,
      P.char '_',
      P.char '-'
    ]

parseExpr :: Parser Expr
parseExpr =
  P.oneOf
    [ Int <$> P.integer,
      Num <$> P.number,
      Tag <$> do
        _ <- P.char ':'
        parseName,
      do
        name <- parseName
        let expr = case name of
              "@Knd" -> Knd
              "@IntT" -> IntT
              "@NumT" -> NumT
              "@Err" -> Err
              x -> Var x
        return expr,
      do
        _ <- P.char '('
        tag <- parseName
        _ <- P.spaces
        expr <- case tag of
          "@For" -> expr2 For parseName parseExpr
          "@Fix" -> expr2 Fix parseName parseExpr
          "@Fun" -> expr2 Fun parseExpr parseExpr
          "@App" -> expr2 App parseExpr parseExpr
          "@And" -> expr2 And parseExpr parseExpr
          "@Or" -> expr2 Or parseExpr parseExpr
          "@Ann" -> expr2 Ann parseExpr parseExpr
          "@Call" -> do
            f <- parseName
            args <- P.zeroOrMore $ do
              _ <- P.spaces
              parseExpr
            return (Call f args)
          "@Meta" -> error "TODO: parseExpr Meta"
          _ -> P.fail'
        _ <- P.spaces
        _ <- P.char ')'
        return expr
    ]
  where
    expr2 f p q = do
      a <- p
      _ <- P.spaces
      f a <$> q
