module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.List (delete, intercalate, union)

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
-- https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- https://www.youtube.com/live/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf

-- TODO: replace operators with Target or Builtin terms
data Expr
  = IntT
  | NumT
  | Int Int
  | Num Double
  | Var String
  | Typ [String]
  | Tag String [Expr]
  | For String Expr
  | Fix String Expr
  | Fun Expr Expr
  | Lam [Case]
  | App Expr Expr
  | Or Expr Expr
  | Ann Expr Expr
  | Op1 UnaryOp Expr
  | Op2 BinaryOp Expr Expr
  | Meta Metadata Expr
  | Err
  deriving (Eq)

data Case
  = Case [Pattern] Expr
  deriving (Eq, Show)

data Pattern
  = PAny
  | PIntT
  | PNumT
  | PInt Int
  | PNum Double
  | PVar String
  | PTyp [String]
  | PTag String [Pattern]
  | PFun Pattern Pattern
  | PEq Expr
  | PErr
  deriving (Eq, Show)

data BinaryOp
  = Add
  | Sub
  | Mul
  | Pow
  | Eq
  | Lt
  | Gt
  deriving (Eq)

data UnaryOp
  = Int2Num
  deriving (Eq)

data Metadata
  = Location String (Int, Int)
  | Comment String
  deriving (Eq, Show)

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
  | UndefinedVar String
  deriving (Eq, Show)

data PatternError
  = MissingCases [Expr]
  | UnreachableCase Expr
  deriving (Eq, Show)

instance Show Expr where
  showsPrec :: Int -> Expr -> ShowS
  showsPrec p expr = case expr of
    App (Fun p b) a -> prefix 1 (show p ++ " = " ++ show a ++ "; ") b
    Or a b -> infixR 1 a " | " b
    Ann a b -> infixR 2 a " : " b
    Op2 Eq a b -> infixL 3 a (op2 Eq) b
    Op2 Lt a b -> infixR 4 a (op2 Lt) b
    Op2 Gt a b -> infixR 4 a (op2 Gt) b
    For x a -> do
      let (xs, a') = asFor (For x a)
      prefix 2 ("@" ++ unwords xs ++ ". ") a'
    Fix x a -> prefix 2 ("$fix " ++ x ++ ". ") a
    Fun p b -> infixR 5 p " -> " b
    Op2 Add a b -> infixL 6 a (op2 Add) b
    Op2 Sub a b -> infixL 6 a (op2 Sub) b
    Op2 Mul a b -> infixL 7 a (op2 Mul) b
    Op1 Int2Num a -> prefix 8 (op1 Int2Num) a
    Op2 Pow a b -> infixR 10 a (show Pow) b
    App a b -> infixL 8 a " " b
    Err -> atom 12 "$error"
    Typ alts -> atom 12 ("$Type[" ++ intercalate " | " alts ++ "]")
    IntT -> atom 12 "$Int"
    NumT -> atom 12 "$Num"
    Int i -> atom 12 (show i)
    Num n -> atom 12 (show n)
    Var x | isVarName x -> atom 12 x
    Var x -> atom 12 ("($var '" ++ x ++ "')")
    Tag k [] | isTagName k -> atom 12 k
    Tag k [] -> atom 12 ("($tag '" ++ k ++ "')")
    Tag k args -> showsPrec p (app (Tag k []) args)
    Meta _ a -> showsPrec p a
    Lam [] -> showsPrec p Err
    Lam cases -> error "TODO: show Lam"
    where
      atom n k = showParen (p > n) $ showString k
      prefix n k a = showParen (p > n) $ showString k . showsPrec (n + 1) a
      infixL n a op b = showParen (p > n) $ showsPrec n a . showString op . showsPrec (n + 1) b
      infixR n a op b = showParen (p > n) $ showsPrec (n + 1) a . showString op . showsPrec n b
      isVarName ('$' : xs) = all isNameChar xs
      isVarName ('_' : xs) = all isNameChar xs
      isVarName (x : xs) = isLower x && all isNameChar xs
      isVarName [] = False
      isTagName (x : xs) = isUpper x && all isNameChar xs
      isTagName [] = False
      isNameChar '-' = True
      isNameChar '_' = True
      isNameChar c = isAlphaNum c
      op2 op = " " ++ show op ++ " "
      op1 op = show op ++ " "

instance Show BinaryOp where
  show :: BinaryOp -> String
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Pow = "^"
  show Eq = "=="
  show Lt = "<"
  show Gt = ">"

instance Show UnaryOp where
  show :: UnaryOp -> String
  show Int2Num = "@int2num"

-- Syntax sugar
bindings :: Expr -> [String]
bindings (For x a) = [x] `union` bindings a
bindings (Fun a b) = freeVars a `union` bindings b
bindings _ = []

fix :: [String] -> Expr -> Expr
fix xs a = foldr Fix a xs

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

asFor :: Expr -> ([String], Expr)
asFor (For x a) = let (xs, b) = asFor a in (x : xs, b)
asFor a = ([], a)

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

asFun :: Expr -> ([Expr], Expr)
asFun (Fun p a) = let (ps, b) = asFun a in (p : ps, b)
asFun a = ([], a)

lam :: [Expr] -> Expr -> Expr
-- TODO: use freeVars of ps
lam ps b = for (bindings (fun ps b)) (fun ps b)

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

pow :: Expr -> Expr -> Expr
pow = Op2 Pow

eq :: Expr -> Expr -> Expr
eq = Op2 Eq

lt :: Expr -> Expr -> Expr
lt = Op2 Lt

gt :: Expr -> Expr -> Expr
gt = Op2 Gt

int2num :: Expr -> Expr
int2num = Op1 Int2Num

let' :: (Expr, Expr) -> Expr -> Expr
let' (Var x, Var x') b | x == x' = b
let' (p, a) b = do
  let xs = filter (`occurs` a) (freeVars p)
  App (lam [p] b) (fix xs a)

lets :: [(Expr, Expr)] -> Expr -> Expr
lets defs b = foldr let' b defs

or' :: [Expr] -> Expr
or' [] = error "`or'` must have at least one expression"
or' [a] = a
or' (a : bs) = Or a (or' bs)

app :: Expr -> [Expr] -> Expr
app = foldl App

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = let (a', bs) = asApp a in (a', bs ++ [b])
asApp a = (a, [])

list :: Expr -> Expr -> [Expr] -> Expr
list _ nil [] = nil
list cons nil (a : bs) = app cons [a, list cons nil bs]

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
  freeVars IntT = []
  freeVars NumT = []
  freeVars (Int _) = []
  freeVars (Num _) = []
  freeVars (Var x) = [x]
  freeVars (Typ _) = []
  freeVars (Tag _ args) = foldr (union . freeVars) [] args
  freeVars (Ann a _) = freeVars a
  freeVars (For x a) = delete x (freeVars a)
  freeVars (Fix x a) = delete x (freeVars a)
  freeVars (Fun a b) = freeVars a `union` freeVars b
  freeVars (Or a b) = freeVars a `union` freeVars b
  freeVars (App a b) = freeVars a `union` freeVars b
  freeVars (Op1 _ a) = freeVars a
  freeVars (Op2 _ a b) = freeVars a `union` freeVars b
  freeVars (Meta _ a) = freeVars a
  freeVars Err = []

instance FreeVars Pattern where
  freeVars :: Pattern -> [String]
  freeVars PAny = []
  freeVars PIntT = []
  freeVars PNumT = []
  freeVars (PInt _) = []
  freeVars (PNum _) = []
  freeVars (PVar x) = [x]
  freeVars (PTyp _) = []
  freeVars (PTag _ ps) = foldr (union . freeVars) [] ps
  freeVars (PFun p q) = freeVars p `union` freeVars q
  freeVars (PEq a) = freeVars a
  freeVars PErr = []

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

newName :: [String] -> String -> String
newName existing x = head (newNames existing x)

newNames :: [String] -> String -> [String]
newNames existing x =
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
eval :: Env -> Expr -> Expr
eval _ IntT = IntT
eval _ NumT = NumT
eval _ (Int i) = Int i
eval _ (Num n) = Num n
eval env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Tag k []) -> Tag k []
  Just (Ann (Var x') _) | x == x' -> Var x
  Just a -> eval env a
  Nothing -> Var x
eval env (Tag k args) = case lookup k env of
  Just (Tag k' []) | k == k' -> Tag k (map (eval env) args)
  Just (Ann (Tag k []) ty) -> Ann (Tag k (map (eval env) args)) ty
  Just a -> eval ((k, Tag k []) : env) a
  Nothing -> Tag k (map (eval env) args)
eval _ (Typ alts) = Typ alts
eval env (For x a) = For x (eval ((x, Var x) : env) a)
eval env (Fix x a) = Fix x (eval ((x, Var x) : env) a)
eval env (Fun p b) = Fun (eval env p) (eval env b)
eval env (App a b) = case (eval env a, eval env b) of
  (For x a, b) -> eval [(x, Var x)] (App a b)
  (Fix x a, b) | isClosed b -> eval [(x, Fix x a)] (App a b)
  (Fun p a, b) -> case (p, b) of
    (Typ alts, Typ alts') | alts == alts' -> a
    (IntT, IntT) -> a
    (NumT, NumT) -> a
    (Int i, Int i') | i == i' -> a
    (Var x, b) -> eval [(x, b)] a
    (Tag k [], Tag k' []) | k == k' -> a
    (Fun p q, Fun b1 b2) -> app (fun [p, q] a) [b1, b2]
    (App p q, App b1 b2) -> app (fun [p, q] a) [b1, b2]
    _ -> Err
  (Err, _) -> Err
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err -> eval [] (App a2 b)
    Fun p a -> Or (Fun p a) (App a2 b)
    a | isOpen a -> Or a (App a2 b)
    a -> a
  (a, b) -> App a b
eval env (Ann a _) = eval env a
eval env (Or a b) = case (eval env a, eval env b) of
  (Err, b) -> b
  (a, Err) -> a
  (Or a1 a2, b) -> Or a1 (Or a2 b)
  (a, b) -> Or a b
eval env (Op1 op a) = case (op, eval env a) of
  (op, a) | isOpen a -> Op1 op a
  (op, a) -> evalOp1 op a
eval env (Op2 op a b) = case (op, eval env a, eval env b) of
  (op, a, b) | isOpen a || isOpen b -> Op2 op a b
  (op, a, b) -> evalOp2 op a b
eval env (Meta _ a) = eval env a
eval _ Err = Err

evalOp1 :: UnaryOp -> Expr -> Expr
evalOp1 Int2Num (Int b) = Num (fromIntegral b)
evalOp1 _ _ = Err

evalOp2 :: BinaryOp -> Expr -> Expr -> Expr
evalOp2 Add (Int a) (Int b) = Int (a + b)
evalOp2 Add (Num a) (Num b) = Num (a + b)
evalOp2 Sub (Int a) (Int b) = Int (a - b)
evalOp2 Sub (Num a) (Num b) = Num (a - b)
evalOp2 Mul (Int a) (Int b) = Int (a * b)
evalOp2 Mul (Num a) (Num b) = Num (a * b)
evalOp2 Pow (Int a) (Int b) = Int (a ^ b)
evalOp2 Pow (Num a) (Num b) = Num (a ** b)
evalOp2 Eq (Tag k []) (Tag k' []) | k == k' = Tag k []
evalOp2 Eq (Typ alts) (Typ alts') | alts == alts' = Typ alts
evalOp2 Eq IntT IntT = IntT
evalOp2 Eq NumT NumT = NumT
evalOp2 Eq (Int a) (Int b) | a == b = Int a
evalOp2 Eq (Num a) (Num b) | a == b = Num a
evalOp2 Eq (Var a) (Var b) | a == b = Var a
evalOp2 Lt (Int a) (Int b) | a < b = Int a
evalOp2 Lt (Num a) (Num b) | a < b = Num a
evalOp2 _ _ _ = Err

unify :: Expr -> Expr -> Either TypeError (Expr, Substitution)
unify IntT IntT = Right (IntT, [])
unify NumT NumT = Right (NumT, [])
unify (Int i) (Int i') | i == i' = Right (Int i, [])
unify (Num n) (Num n') | n == n' = Right (Num n, [])
unify (Var x) (Var x') | x == x' = Right (Var x, [])
unify (Typ alts) (Typ alts') | alts == alts' = Right (Typ alts, [])
unify (Tag k []) (Tag k' []) | k == k' = Right (Tag k [], [])
unify (Tag k args) (Tag k' args') | k == k' && length args == length args' = do
  (args, s) <- unifyAll args args'
  Right (Tag k args, s)
unify (Var x) b | x `occurs` b = Left (OccursError x b)
unify (Var x) b = Right (b, [(x, b)])
unify a (Var x) = unify (Var x) a
unify (Fun a1 a2) b@Tag {} = unify a2 (App b a1)
unify (Fun a1 a2) b@App {} = unify a2 (App b a1)
unify a@Tag {} (Fun b1 b2) = unify (App a b1) b2
unify a@App {} (Fun b1 b2) = unify (App a b1) b2
unify (Fun a1 b1) (Fun a2 b2) = do
  ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
  Right (Fun ta tb, s)
unify a (Or b1 b2) = case unify a b1 of
  Left _ -> unify a b2
  Right (a, s1) -> case unify a b2 of
    Left _ -> Right (a, s1)
    Right (a, s2) -> Right (a, s2 `compose` s1)
unify (Or a1 a2) b = case unify a1 b of
  Left _ -> unify a2 b
  Right (b, s1) -> case unify a2 b of
    Left _ -> Right (b, s1)
    Right (b, s2) -> Right (b, s2 `compose` s1)
unify (App a1 b1) (App a2 b2) = do
  ((ta, tb), s) <- unify2 (a1, a2) (b1, b2)
  Right (App ta tb, s)
unify (Op1 op a) (Op1 op' b) | op == op' = do
  (a', s) <- unify a b
  Right (Op1 op a', s)
unify (Op2 op a1 b1) (Op2 op' a2 b2) | op == op' = do
  ((a, b), s) <- unify2 (a1, a2) (b1, b2)
  Right (Op2 op a b, s)
unify (Meta _ a) b = unify a b
unify a (Meta _ b) = unify a b
unify a b = Left (TypeMismatch a b)

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either TypeError ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  (ta, s1) <- unify a1 a2
  (tb, s2) <- unify (eval s1 b1) (eval s1 b2)
  Right ((eval s2 ta, tb), s2 `compose` s1)

unifyAll :: [Expr] -> [Expr] -> Either TypeError ([Expr], Substitution)
unifyAll (a : bs) (a' : bs') = do
  (ta, s1) <- unify a a'
  (tbs, s2) <- unifyAll bs bs'
  Right (ta : tbs, s2 `compose` s1)
unifyAll _ _ = Right ([], [])

infer :: Env -> Expr -> Either TypeError (Expr, Substitution)
infer _ IntT = Right (Typ [], [])
infer _ NumT = Right (Typ [], [])
infer _ (Int _) = Right (IntT, [])
infer _ (Num _) = Right (NumT, [])
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let y = newName (map fst env) (x ++ "T")
    Right (Var y, [(y, Var y), (x, Ann (Var x) (Var y))])
  Just (Ann (Var x') ty) | x == x' -> Right (instantiate env ty)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer _ (Typ _) = Right (Typ [], [])
infer env (Tag k []) = case lookup k env of
  Just (Tag k' []) | k == k' -> Right (Tag k [], [])
  Just (Ann (Tag k' []) ty) | k == k' -> Right (instantiate env ty)
  Just a -> infer env a
  Nothing -> Right (Tag k [], [])
infer env (Tag k args) = infer env (app (Tag k []) args)
infer env (Ann a ty) = do
  let (t, vars) = instantiate env ty
  (ta, s1) <- infer (vars ++ env) a
  (t', s2) <- unify ta (eval (env `compose` s1) t)
  Right (eval env t', s2 `compose` s1 `compose` vars)
infer env (For x a) = infer ((x, Var x) : env) a
infer env (Fix x a) = infer ((x, Var x) : env) a
infer env (Fun a b) = do
  ((ta, tb), s) <- infer2 env a b
  Right (Fun ta tb, s)
infer env (Or a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case unify ta tb of
    Left _ -> Right (Or ta tb, s1)
    Right (t, s2) -> Right (eval env t, s2 `compose` s1)
infer env (App a b) = do
  ((ta, tb), s1) <- infer2 env a b
  let x = newName (map fst (s1 ++ env)) "t"
  (_, s2) <- unify (Fun tb (Var x)) ta
  Right (eval (env `compose` s2) (Var x), s2 `compose` s1 `compose` [(x, Var x)])
infer env (Op1 op a) = inferOp1 env op a
infer env (Op2 op a b) = inferOp2 env op a b
infer env (Meta _ a) = infer env a
infer _ Err = Right (Err, []) -- TODO: error?

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (env `compose` s1) b
  Right ((eval s2 ta, tb), s2 `compose` s1)

inferAll :: Env -> [Expr] -> Either TypeError ([Expr], Substitution)
inferAll _ [] = Right ([], [])
inferAll env (a : bs) = do
  (ta, s1) <- infer env a
  (tbs, s2) <- inferAll (env `compose` s1) bs
  Right (eval s2 ta : tbs, s2 `compose` s1)

inferOp1 :: Env -> UnaryOp -> Expr -> Either TypeError (Expr, Substitution)
inferOp1 env Int2Num a = do
  (_, s) <- infer env (Ann a IntT)
  Right (NumT, s)

inferOp2 :: Env -> BinaryOp -> Expr -> Expr -> Either TypeError (Expr, Substitution)
inferOp2 env Add a b = do
  (ta, s1) <- infer env (Ann a IntT)
  (t, s2) <- infer (s1 `compose` env) (Ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Sub a b = do
  (ta, s1) <- infer env (Ann a IntT)
  (t, s2) <- infer (s1 `compose` env) (Ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Mul a b = do
  (ta, s1) <- infer env (Ann a IntT)
  (t, s2) <- infer (s1 `compose` env) (Ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Pow a b = do
  (ta, s1) <- infer env (Ann a IntT)
  (t, s2) <- infer (s1 `compose` env) (Ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Eq a b = do
  (ta, s1) <- infer env a
  (t, s2) <- infer (env `compose` s1) (Ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Lt a b = do
  (ta, s1) <- infer env a
  (t, s2) <- infer (env `compose` s1) (Ann b ta)
  Right (t, s2 `compose` s1)
inferOp2 env Gt a b = do
  (ta, s1) <- infer env a
  (t, s2) <- infer (env `compose` s1) (Ann b ta)
  Right (t, s2 `compose` s1)

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = apply s1 s2 `union` s1
  where
    apply :: Substitution -> Env -> Env
    apply _ [] = []
    apply s ((x, Ann a t) : env) = do
      (x, Ann (eval s a) (eval s t)) : apply s env
    apply s ((x, a) : env) = (x, eval s a) : apply s env

instantiate :: Env -> Expr -> (Expr, Substitution)
instantiate env (For x a) = do
  let y = newName (map fst env) x
  let (b, s) = instantiate env (eval [(x, Var y)] a)
  (b, [(y, Var y)] `union` s)
instantiate env a = (eval env a, [])

checkTypes :: Env -> [TypeError]
checkTypes env = do
  let checkDef (_, a) = case infer env a of
        Right _ -> []
        Left err -> [err]
  concatMap checkDef env

rename :: (Expr -> [String] -> String -> String) -> [String] -> Env -> Env -> Env
rename _ _ _ [] = []
rename f names env ((x, a) : env') = do
  let t = case infer env a of
        Right (t, _) -> t
        Left _ -> Err
  let y = f t (names ++ map fst env') x
  (y, eval [(x, Var y)] a) : rename f (y : names) env env'
