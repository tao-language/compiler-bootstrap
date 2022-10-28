module Tao where

import qualified Core
import Data.List (foldl')

data Expr
  = IntT
  | Typ ![Alt]
  | Int !Int
  | Var !String
  | Lam !String !Expr
  | App !Expr !Expr
  | Fun !Expr !Expr
  | Ann !Expr !Type
  | Call !String
  | Let !Env !Expr
  | Ctr !String !String
  | Match ![String] ![Case] !Expr
  deriving (Eq, Show)

data Type
  = T ![String] !Expr
  deriving (Eq, Show)

data Pattern
  = PAny
  | PInt !Int
  | PVar !String
  | PAs !Pattern !String
  | PCtr !String ![Pattern]
  -- TODO: add `PIf Pattern Expr` guard
  deriving (Eq, Show)

type Alt = (String, [String])

type Case = ([Pattern], Expr)

type Env = [(String, Expr)]

data Error
  = UndefinedVar !String
  | UndefinedType !String
  | UndefinedCtr !String
  | NotAType !Expr
  | NotACtr !Expr
  | UnmatchedPatterns ![Pattern]
  | CaseTypeMismatch !String !String
  | CaseCtrArgsMismatch ![String] ![Pattern]
  deriving (Eq, Show)

-- instance Show Expr where
--   show (Var x) = x
--   show (Int i) = show i
--   show (Let [] b) = show b
--   show (Let ((x, a) : defs) b) = "#let " ++ x ++ " = " ++ show a ++ "; " ++ show (Let defs b)
--   show (Cases cases) = do
--     let showCase (ps, a) = unwords (map show ps) ++ " -> " ++ show a
--     intercalate " | " (map showCase cases)
--   -- TODO: show parentheses when necessary
--   show (App a@(Cases _) bs) = "#match " ++ unwords (map show bs) ++ " | " ++ show a
--   show (App a bs) = show a ++ " " ++ show bs
--   show (Call f) = "#call " ++ f
--   -- show (Ann a t) = show a ++ " : " ++ show t
--   show IntT = "#Int"
--   show (Fun a b) = show a ++ " => " ++ show b

-- instance Show Pattern where
--   show PAny = "_"
--   show (PInt i) = show i
--   show (PAs PAny x) = x
--   show (PAs p x) = x ++ "@" ++ show p
--   show (PCtr ctr []) = ctr
--   show (PCtr ctr ps) = "(" ++ ctr ++ " " ++ unwords (map show ps) ++ ")"
--   show (PAnn p t) = show p ++ " : " ++ show t

-- Syntax sugar
lam :: [String] -> Expr -> Expr
lam xs a = foldr Lam a xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

fun :: [Expr] -> Expr -> Expr
fun xs a = foldr Fun a xs

add :: Expr -> Expr -> Expr
add a b = app (Call "+") [a, b]

sub :: Expr -> Expr -> Expr
sub a b = app (Call "-") [a, b]

mul :: Expr -> Expr -> Expr
mul a b = app (Call "*") [a, b]

eq :: Expr -> Expr -> Expr
eq a b = app (Call "==") [a, b]

-- let' :: [(Pattern, Expr)] -> Expr -> Expr

-- match :: [Case] -> Expr -> Expr
match :: [Case] -> Expr
-- match (([], a) : _) = a
-- match cases = Cases cases
-- match args cases = App (Cases cases) args
match _ = Var "TODO: match"

unpack :: (Pattern, Expr) -> [(String, Expr)]
-- unpack (p, a) = do
--   let bind :: (Pattern, Expr) -> String -> (String, Expr)
--       bind (PAny, a) x = (x, a)
--       bind (PAs p x, a) x' | x == x' = bind (p, a) x
--       bind (p, a) x = (x, match [a] [([p], Var x)])
--   map (bind (p, a)) (bindings p)
unpack _ = []

-- Context --
-- defineType :: String -> [String] -> [TypeAlt] -> [TypeCtr] -> Env -> ([TypeCtr], Env)
-- defineType name vars alts ctrs env = (map (\(ctr, _) -> (ctr, alts)) alts ++ ctrs, env)

compile :: Env -> Expr -> Either Error Core.Expr
compile _ IntT = Right Core.IntT
compile _ (Typ alts) = Right (Core.Typ alts)
compile _ (Int i) = Right (Core.Int i)
compile env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Right (Core.Var x)
  Just a -> case compile ((x, Var x) : env) a of
    Right a' | x `Core.occurs` a' -> Right (Core.Fix x a')
    other -> other
  Nothing -> Left (UndefinedVar x)
compile env (Lam x a) = do
  a' <- compile ((x, Var x) : env) a
  Right (Core.Lam [] x a')
compile env (App a b) = do
  a' <- compile env a
  b' <- compile env b
  Right (Core.App a' b')
compile env (Fun a b) = do
  a' <- compile env a
  b' <- compile env b
  Right (Core.Fun a' b')
compile env (Ann a (T xs t)) = do
  a' <- compile env a
  t' <- compile (map (\x -> (x, Var x)) xs ++ env) t
  Right (Core.Ann a' (Core.T xs t'))
compile _ (Call f) = Right (Core.Call f)
compile env (Let defs a) = compile (defs ++ env) a
compile env (Ctr tname cname) = do
  alts <- typeAlts env tname
  args <- altArgs alts cname
  compile env (lam (args ++ map fst alts) (app (Var cname) (map Var args)))
compile env (Match [] [] default') = compile env default'
compile env (Match [] ((_, a) : _) _) = compile env a
compile env (Match (x : xs) cases default') = case findAlts env cases of
  Right [] -> do
    let branch = Match xs (remaining (filterAny x) cases) default'
    compile env (lam [x] branch)
  Right alts -> do
    let branch (ctr, ys) = Match (ys ++ xs) (remaining (filterCtr (ctr, ys) x) cases) default'
    compile env (lam [x] (app (Var x) (map branch alts)))
  Left err -> Left err

compileEnv :: Env -> Either Error Core.Env
compileEnv env = mapM (\(x, a) -> do a <- compile env a; Right (x, a)) env

eval :: Env -> Expr -> Either Error Core.Expr
eval env expr = do
  expr' <- compile env expr
  Right (Core.eval expr' [])

-- Helper functions
ctrType :: Env -> String -> Either Error String
ctrType env cname = case lookup cname env of
  Just (Ctr tname _) -> Right tname
  Just a -> Left (NotACtr a)
  Nothing -> Left (UndefinedCtr cname)

typeAlts :: Env -> String -> Either Error [Alt]
typeAlts env tname = case lookup tname env of
  Just (Typ alts) -> Right alts
  Just a -> Left (NotAType a)
  Nothing -> Left (UndefinedType tname)

altArgs :: [Alt] -> String -> Either Error [String]
altArgs args cname = case lookup cname args of
  Just args -> Right args
  Nothing -> Left (UndefinedCtr cname)

validateCtrCases :: Env -> String -> [Case] -> Either Error ()
validateCtrCases _ _ [] = Right ()
validateCtrCases env tname ((PCtr cname ps : _, _) : cases) = do
  tname' <- ctrType env cname
  alts <- typeAlts env tname'
  args <- altArgs alts cname
  case () of
    () | tname /= tname' -> Left (CaseTypeMismatch tname tname')
    () | length args /= length ps -> Left (CaseCtrArgsMismatch args ps)
    () -> validateCtrCases env tname cases
validateCtrCases env tname ((PAs p _ : ps, a) : cases) = validateCtrCases env tname ((p : ps, a) : cases)
validateCtrCases env tname (_ : cases) = validateCtrCases env tname cases

findAlts :: Env -> [Case] -> Either Error [Alt]
findAlts _ [] = Right []
findAlts env cases@((PCtr cname _ : _, _) : _) = do
  tname <- ctrType env cname
  alts <- typeAlts env tname
  _ <- validateCtrCases env tname cases
  Right alts
findAlts env ((PAs p _ : ps, a) : cases) = findAlts env ((p : ps, a) : cases)
findAlts env (_ : cases) = findAlts env cases

filterAny :: String -> Case -> Maybe Case
filterAny _ (PAny : ps, a) = Just (ps, a)
filterAny x (PVar y : ps, a) = filterAny x (PAs PAny y : ps, a)
filterAny x (PAs p x' : ps, a) | x == x' = filterAny x (p : ps, a)
filterAny x (PAs p y : ps, a) = filterAny x (p : ps, Let [(y, Var x)] a)
filterAny _ _ = Nothing

filterCtr :: Alt -> String -> Case -> Maybe Case
filterCtr (_, args) _ (PAny : ps, a) = Just (replicate (length args) PAny ++ ps, a)
filterCtr alt x (PVar y : ps, a) = filterCtr alt x (PAs PAny y : ps, a)
filterCtr alt x (PAs p y : ps, a) = filterCtr alt x (p : ps, Let [(y, Var x)] a)
filterCtr (ctr, _) _ (PCtr ctr' qs : ps, a) | ctr == ctr' = Just (qs ++ ps, a)
filterCtr _ _ _ = Nothing

remaining :: (Case -> Maybe Case) -> [Case] -> [Case]
remaining f (case' : cases) = case f case' of
  Just case' -> case' : remaining f cases
  Nothing -> remaining f cases
remaining _ _ = []

-- bindings :: Pattern -> [String]
-- bindings (PAs p x) = x : bindings p
-- bindings (PCtr ctr (p : ps)) = bindings p ++ bindings (PCtr ctr ps)
-- bindings _ = []
