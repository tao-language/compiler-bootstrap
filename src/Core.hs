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
  | Ann Expr Expr
  | And Expr Expr
  | Or Expr Expr
  | For String Expr
  | Fix String Expr
  | Fun Expr Expr
  | App Expr Expr
  | Call String [Expr]
  | Let [(String, Expr)] Expr
  | Err
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
    Any -> "_"
    Unit -> "()"
    IntT -> "!IntT"
    NumT -> "!NumT"
    Int i -> show i
    Num n -> show n
    Var x -> name x
    Tag (':' : k) -> ':' : ':' : name k
    Tag ('~' : k) -> ':' : '~' : name k
    Tag k -> ':' : name k
    Ann a b -> "(" ++ show a ++ " : " ++ show b ++ ")"
    And _ _ -> "(" ++ intercalate ", " (map show (andOf expr)) ++ ")"
    Or _ _ -> "(" ++ intercalate " | " (map show (orOf expr)) ++ ")"
    For _ _ -> do
      let (xs, a) = forOf expr
      "(@" ++ unwords (map name xs) ++ ". " ++ show a ++ ")"
    Fix x a -> "(&" ++ name x ++ ". " ++ show a ++ ")"
    Fun _ _ -> do
      let (args, ret) = funOf expr
      "(" ++ intercalate " -> " (map show args) ++ " -> " ++ show ret ++ ")"
    App a b -> do
      let (xs, a') = forOf a
      case (xs, a') of
        ([], Fun a c) -> show a ++ " = " ++ show b ++ "; " ++ show c
        (xs, Fun a c) -> "@[" ++ intercalate "," xs ++ "] " ++ show a ++ " = " ++ show b ++ "; " ++ show c
        _ -> do
          let (a', bs) = appOf (App a b)
          "(" ++ show a' ++ " " ++ unwords (map show bs) ++ ")"
    Call f args -> '%' : f ++ "(" ++ intercalate ", " (map show args) ++ ")"
    Let env b -> "@{" ++ intercalate "; " (map (\(x, a) -> name x ++ " = " ++ show a) env) ++ "} " ++ show b
    Err -> "!error"
    where
      isAlphaNumOr cs c = isAlphaNum c || c `elem` cs
      name = \case
        x | all (isAlphaNumOr "-_") x -> x
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
let' env b = Let env b

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
  freeVars (Call _ args) = foldr (union . freeVars) [] args
  freeVars (Let [] b) = freeVars b
  freeVars (Let ((x, a) : defs) b) = delete x (freeVars a `union` freeVars (Let defs b))
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
  App a b -> reduceApp ops a b
  Let env expr -> reduceLet ops env expr
  expr -> expr

reduceApp :: Ops -> Expr -> Expr -> Expr
reduceApp ops a b = case a of
  Let env (Tag k) -> case lookup k env of
    Just a -> reduce ops (App (Let env a) b)
    Nothing -> reduce ops b
  Let env (Let env' (Tag k)) ->
    reduce ops (App (Let (env ++ env') (Tag k)) b)
  a -> case (reduce ops a, reduce ops b) of
    (Any, b) -> App Any b
    (Var x, b) -> App (Var x) b
    (Ann a ta, Ann b tb) -> Ann (reduceApp ops a b) (reduceApp ops ta tb)
    (Ann a _, b) -> reduceApp ops a b
    (a, Ann b _) -> reduceApp ops a b
    (And a1 a2, b) -> case a1 of
      Let env (Tag k) -> case lookup k env of
        Just a1 -> reduceApp ops (App (Let env a1) a2) b
        Nothing -> b
      Let env (Let env' a1) ->
        reduceApp ops (And (Let (env ++ env') a1) a2) b
      _ -> Err
    (Or a1 a2, b) -> case reduceApp ops a1 b of
      Err -> reduceApp ops a2 b
      c -> c
    (For x a, b) -> for [x] (reduceApp ops (Let [(x, Var x)] a) b)
    (Fix x a, b@Var {}) -> App (Fix x a) b
    (Fix x a, b@App {}) -> App (Fix x a) b
    (Fix x a, b) -> reduceApp ops (Let [(x, Fix x a)] a) b
    (App a1 a2, b) -> App (App a1 a2) b
    (Fun a c, b) -> reduceAppFun ops a b c
    (Call f args, b) -> App (Call f args) b
    _ -> Err

reduceAppFun :: Ops -> Expr -> Expr -> Expr -> Expr
reduceAppFun ops a b c = case a of
  Let env (Tag k) -> do
    let b' = App (Let env (Tag k)) b
    reduce ops (App (Fun (Tag k) c) b')
  Let env (Let env' a) ->
    reduce ops (App (Fun (Let (env ++ env') a) c) b)
  a -> case (reduce ops a, reduce ops b) of
    (Any, _) -> reduce ops c
    (Unit, Unit) -> reduce ops c
    (IntT, IntT) -> reduce ops c
    (NumT, NumT) -> reduce ops c
    (Int i, Int i') | i == i' -> reduce ops c
    (Num n, Num n') | n == n' -> reduce ops c
    (Tag k, Tag k') | k == k' -> reduce ops c
    (Var x, b) -> reduce ops (Let [(x, b)] c)
    (Ann a ta, Ann b tb) -> reduceAppFun ops ta tb (App (Fun a c) b)
    (Ann a _, b) -> reduceAppFun ops a b c
    (a, Ann b _) -> reduceAppFun ops a b c
    (And (Let env (Tag k)) a2, b) -> do
      let b' = App (And (Let env (Tag k)) a2) b
      reduceAppFun ops (And (Tag k) a2) b' c
    (And (Let env (Let env' a1)) a2, b) -> do
      let a' = And (Let (env ++ env') a1) a2
      reduceAppFun ops a' b c
    (And a1 a2, And b1 b2) -> reduceAppFun ops a1 b1 (App (Fun a2 c) b2)
    (Or a1 a2, b) -> reduceApp ops (Or (Fun a1 c) (Fun a2 c)) b
    (a, Or b1 b2) -> case reduceAppFun ops a b1 c of
      Err -> reduceAppFun ops a b2 c
      c -> c
    (For x a, For y b) -> do
      let z = newName (freeVars a) y
      let a' = Let [(x, Var z)] a
      for [z] (reduce ops (Let [(z, Var z)] (App (Fun a' c) b)))
    (For x a, b) -> reduceAppFun ops (Let [(x, Var x)] a) b c
    (Fun a1 a2, Fun b1 b2) -> reduceAppFun ops a1 b1 (App (Fun a2 c) b2)
    (App a1 a2, App b1 b2) -> reduceAppFun ops a1 b1 (App (Fun a2 c) b2)
    (Call x args, Call x' args') | x == x' -> reduceAppFun ops (and' args) (and' args') c
    (Err, Err) -> reduce ops c
    _ -> Err

reduceLet :: Ops -> Env -> Expr -> Expr
reduceLet ops env = \case
  Var x -> case lookup x env of
    Just (Var x') | x == x' -> Var x
    Just (Ann (Var x') _) | x == x' -> Var x
    Just a -> reduce ops a
    Nothing -> Var x
  Ann a b -> Ann (reduce ops (Let env a)) (reduce ops (Let env b))
  And a b -> And (Let env a) (Let env b)
  Or a b -> Or (Let env a) (Let env b)
  For x a -> For x (Let env a)
  Fix x a -> Fix x (Let env a)
  Fun a b -> Fun (Let env a) (Let env b)
  App a b -> reduceApp ops (Let env a) (Let env b)
  Call f args -> case (lookup f ops, Let env <$> args) of
    (Just call, args) -> call (reduce ops) args
    (Nothing, args) -> Call f args
  Let env' a -> reduce ops (Let (env ++ env') a)
  expr -> expr

eval :: Ops -> Expr -> Expr
eval ops expr = case reduce ops expr of
  Ann a b -> Ann (eval ops a) (eval ops b)
  And a b -> And (eval ops a) (eval ops b)
  Or a b -> Or (eval ops a) (eval ops b)
  For x a -> For x (eval ops (Let [(x, Var x)] a))
  Fix x a -> Fix x (eval ops (Let [(x, Var x)] a))
  Fun a b -> Fun (eval ops a) (eval ops b)
  App a b -> App (eval ops a) (eval ops b)
  Call f args -> Call f (eval ops <$> args)
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
substitute s (Ann a b) = Ann (dropType (substitute s a)) (dropType (substitute s b))
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
substitute _ Err = Err

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = do
  let notIn s (x, _) = x `notElem` map fst s
  map (second (substitute s1)) s2 `union` filter (notIn s2) s1

dropType :: Expr -> Expr
dropType (Ann a _) = dropType a
dropType a = a

dropFreeTypes :: Expr -> Expr
dropFreeTypes (Ann a (Var _)) = dropFreeTypes a
dropFreeTypes (And a b) = And (dropFreeTypes a) (dropFreeTypes b)
dropFreeTypes (Or a b) = Or (dropFreeTypes a) (dropFreeTypes b)
dropFreeTypes (For x a) = For x (dropFreeTypes a)
dropFreeTypes (Fix x a) = Fix x (dropFreeTypes a)
dropFreeTypes (Fun a b) = Fun (dropFreeTypes a) (dropFreeTypes b)
dropFreeTypes (App a b) = App (dropFreeTypes a) (dropFreeTypes b)
dropFreeTypes (Call op args) = Call op (map dropFreeTypes args)
dropFreeTypes (Let env b) = Let (map (second dropFreeTypes) env) (dropFreeTypes b)
dropFreeTypes a = a

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
dropTypes (Call op args) = Call op (map dropTypes args)
dropTypes (Let defs b) = Let (map (second dropTypes) defs) (dropTypes b)
dropTypes a = a

dropAllTypes :: Expr -> Expr
dropAllTypes (Ann a _) = dropAllTypes a
dropAllTypes (And a b) = And (dropAllTypes a) (dropAllTypes b)
dropAllTypes (Or a b) = Or (dropAllTypes a) (dropAllTypes b)
dropAllTypes (For x a) = For x (dropAllTypes a)
dropAllTypes (Fix x a) = Fix x (dropAllTypes a)
dropAllTypes (Fun a b) = Fun (dropAllTypes a) (dropAllTypes b)
dropAllTypes (App a b) = App (dropAllTypes a) (dropAllTypes b)
dropAllTypes (Call op args) = Call op (map dropAllTypes args)
dropAllTypes (Let env b) = Let (map (second dropAllTypes) env) (dropAllTypes b)
dropAllTypes a = a

unify :: Expr -> Expr -> Either TypeError (Expr, Substitution)
unify a b = case (a, b) of
  (Any, b) -> Right (b, [])
  (a, Any) -> Right (a, [])
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
  (Ann a ta, Ann b tb) -> do
    ((a, ta), s) <- unify2 (a, b) (ta, tb)
    Right (Ann a ta, s)
  (Ann a _, b) -> unify a b
  (a, Ann b _) -> unify a b
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
  (a, For x b) -> do
    let (b', vars) = instantiate (freeVars a) (For x b)
    (t, s) <- unify a b'
    Right (t, s `compose` vars)
  (For x a, b) -> do
    let (a', vars) = instantiate (freeVars b) (For x a)
    (t, s) <- unify a' b
    Right (t, s `compose` vars)
  (Fix _ a, b) -> unify a b
  (a, Fix _ b) -> unify a b
  (Fun a1 b1, Fun a2 b2) -> do
    ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
    Right (Fun ta tb, s)
  (Call op args, Call op' args') | op == op' -> do
    (args, s) <- unifyAll args args'
    Right (Call op args, s)
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
infer _ _ Any = Right (Any, [])
infer _ _ Unit = Right (Unit, [])
infer _ _ IntT = Right (IntT, [])
infer _ _ NumT = Right (NumT, [])
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
infer ops env (Ann a ty) = check ops env a ty
infer ops env (And a b) = do
  ((ta, tb), s) <- infer2 ops env a b
  Right (And ta tb, s)
infer ops env (Or a b) = do
  ((ta, tb), s1) <- infer2 ops env a b
  case unify ta tb of
    Left _ -> Right (Or ta tb, s1)
    Right (t, s2) -> Right (t, s2 `compose` s1)
infer ops env (For x a) = infer ops ((x, Var x) : env) a
infer ops env (Fix x a) = do
  (t, s) <- infer ops ((x, Var x) : env) a
  Right (Fix x t, s)
infer ops env (Fun (Ann a ta) b) = do
  ((ta', tb), s1) <- infer2 ops env a b
  (ta, s2) <- unify ta ta'
  Right (Fun (Ann ta Any) (substitute s2 tb), s2 `compose` s1)
infer ops env (Fun a b) = do
  ((ta, tb), s) <- infer2 ops env a b
  Right (Fun ta tb, s)
infer ops env (App a b) = do
  ((ta, tb), s1) <- infer2 ops env a b
  case instantiate (map fst env) ta of
    (Var x, s2) -> do
      let y = newName (map fst (s2 `compose` s1 `compose` env)) x
      (t, s3) <- infer ops ([(y, Var y)] `compose` s2 `compose` s1 `compose` env) (App (Ann a (Fun tb (Var y))) b)
      Right (t, s3 `compose` s2 `compose` s1 `compose` [(y, t)])
    (Fun t1 t2, s2) -> do
      (_, s3) <- unify tb t1
      Right (substitute s3 t2, s3 `compose` s2 `compose` s1)
    (ta, _) -> Left (NotAFunction a ta)
infer ops env (Let env' a) = infer ops (env' ++ env) a
infer ops env (Call op args) = do
  (argsT, s) <- inferAll ops env args
  Right (Call op argsT, s)
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

instantiate :: [String] -> Expr -> (Expr, Substitution)
instantiate vars (For x a) | x `occurs` a = do
  let y = newName vars x
  let (b, s) = instantiate (y : vars) (substitute [(x, Var y)] a)
  (b, (y, Var y) : s)
instantiate vars (For _ a) = instantiate vars a
instantiate _ a = (a, [])

annotate :: Ops -> Env -> Expr -> ((Expr, Expr), Substitution)
annotate ops env (For x a) = do
  let ((a', ta), s) = annotate ops (pushVars [x] env) a
  ((for [x] a', ta), s)
annotate ops env (Fix x a) = do
  let ((a', ta), s) = annotate ops (pushVars [x] env) a
  ((fix [x] a', ta), s)
annotate ops env expr = do
  let (ta, s1) = case infer ops env expr of
        Right (t, s) -> (t, s)
        Left _ -> (Err, [])
  let (a, s2) = case expr of
        Ann a b -> do
          let ((a', ta), (b', tb), s2) = annotate2 ops env a b
          (Ann a' (for (map fst (s2 `compose` s1)) b'), s2)
        And a b -> do
          let ((a', ta), (b', tb), s2) = annotate2 ops env a b
          (And a' b', s2)
        Or a b -> do
          let ((a', ta), (b', tb), s2) = annotate2 ops env a b
          (Or a' b', s2)
        Fun a b -> do
          let ((a', ta), (b', tb), s2) = annotate2 ops env a b
          (Fun (Ann (dropType a') ta) b', s2)
        App a b -> do
          let ((a', ta), (b', tb), s2) = annotate2 ops env a b
          (App a' (Ann b' tb), s2)
        Call f args -> do
          let ((args', argsT), s2) = annotateAll ops env args
          (Call f args', s2)
        Let [] a -> do
          let ((a', _), s2) = annotate ops env a
          (a', s2)
        Let defs a -> do
          let ((a', _), s2) = annotate ops (defs ++ env) a
          let ((defs', defsT), s3) = annotateDefs ops (defs ++ env) defs
          (Let defs' a', s3 `compose` s2)
        _ -> (expr, [])
  let s = s2 `compose` s1
  let sub = substitute s
  ((sub a, sub ta), s)

annotate2 :: Ops -> Env -> Expr -> Expr -> ((Expr, Expr), (Expr, Expr), Substitution)
annotate2 ops env a b = do
  let ((a', ta), s1) = annotate ops env a
  let ((b', tb), s2) = annotate ops (s1 `compose` env) (substitute s1 b)
  ((a', ta), (b', tb), s2 `compose` s1)

annotateAll :: Ops -> Env -> [Expr] -> (([Expr], [Expr]), Substitution)
annotateAll _ _ [] = (([], []), [])
annotateAll ops env (a : bs) = do
  let ((a', ta), s1) = annotate ops env a
  let ((bs', bsT), s2) = annotateAll ops (s1 `compose` env) (map (substitute s1) bs)
  ((a' : bs', ta : bsT), s2 `compose` s1)

annotateDefs :: Ops -> Env -> [(String, Expr)] -> (([(String, Expr)], [(String, Expr)]), Substitution)
annotateDefs _ _ [] = (([], []), [])
annotateDefs ops env ((x, a) : defs) = do
  let ((a', ta), s1) = annotate ops env a
  let ((defs', defsT), s2) = annotateDefs ops (s1 `compose` env) (map (second (substitute s1)) defs)
  (((x, a') : defs', (x, ta) : defsT), s2 `compose` s1)

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
          "@Ann" -> expr2 Ann parseExpr parseExpr
          "@And" -> expr2 And parseExpr parseExpr
          "@Or" -> expr2 Or parseExpr parseExpr
          "@For" -> expr2 For parseName parseExpr
          "@Fix" -> expr2 Fix parseName parseExpr
          "@Fun" -> expr2 Fun parseExpr parseExpr
          "@App" -> expr2 App parseExpr parseExpr
          "@Call" -> do
            f <- parseName
            args <- P.zeroOrMore $ do
              _ <- P.spaces
              parseExpr
            return (Call f args)
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
