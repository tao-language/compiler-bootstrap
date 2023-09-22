module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.Char (isAlphaNum, isLower, isUpper, toLower)
import Data.List (delete, intercalate, union)

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
-- https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- https://www.youtube.com/live/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf

data Expr
  = Typ
  | Fun
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Tag !String
  | Var !String
  | Lam !String !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Or !Expr !Expr
  | If !Expr !Expr
  | Fst !Expr
  | Snd !Expr
  | Fix !String !Expr
  | Rec ![(String, Expr)]
  | Op1 !UnaryOp
  | Op2 !BinaryOp
  | Err
  deriving (Eq)

data Type
  = For ![String] !Expr
  deriving (Eq)

data BinaryOp
  = Add
  | Sub
  | Mul
  | Pow
  | Eq
  | Lt
  deriving (Eq)

data UnaryOp
  = Int2Num
  deriving (Eq)

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

data TypeError
  = UndefinedVar !String
  | UndefinedCtr !String
  | UndefinedTyp !String
  | InconsistentCtr !String !String
  | InconsistentTyp !String !String
  | InfiniteType !String !Expr
  | MissingType !String
  | NotAFunction !Expr !Expr
  | TypeMismatch !Expr !Expr
  deriving (Eq, Show)

instance Show Expr where
  showsPrec p expr = case expr of
    Or a b -> infixR 1 a " | " b
    If a b -> infixR 1 a " ? " b
    Ann a (For xs b) -> infixR 2 a (" : " ++ for xs) b
    Lam x b -> do
      let (xs, b') = asLam (Lam x b)
      prefix 2 ("\\" ++ unwords xs ++ ". ") b'
    Fix x a -> prefix 2 ("@fix " ++ x ++ ". ") a
    App (App (Op2 Eq) a) b -> infixL 3 a (op2 Eq) b
    App (App (Op2 Lt) a) b -> infixR 4 a (op2 Lt) b
    App (App Fun a) b -> infixR 5 a " -> " b
    App (App (Op2 Add) a) b -> infixL 6 a (op2 Add) b
    App (App (Op2 Sub) a) b -> infixL 6 a (op2 Sub) b
    App (App (Op2 Mul) a) b -> infixL 7 a (op2 Mul) b
    Fst a -> prefix 8 "@fst " a
    Snd a -> prefix 8 "@snd " a
    App (App (Op2 Pow) a) b -> infixR 10 a (show Pow) b
    App a b -> infixL 8 a " " b
    Err -> atom 11 "@err"
    Typ -> atom 11 "@Type"
    Fun -> atom 11 "(->)"
    IntT -> atom 11 "@Int"
    NumT -> atom 11 "@Num"
    Int i -> atom 11 (show i)
    Num n -> atom 11 (show n)
    Tag k | isTagName k -> atom 11 k
    Tag k -> atom 11 ("(@tag '" ++ k ++ "')")
    Var x | isVarName x -> atom 11 x
    Var x -> atom 11 ("(@var '" ++ x ++ "')")
    Op1 Int2Num -> atom 11 (show Int2Num)
    Op2 op -> atom 11 ("(" ++ show op ++ ")")
    Rec kvs -> do
      let showField (x, a) = x ++ ": " ++ show a
      atom 11 ("{" ++ intercalate ", " (map showField kvs) ++ "}")
    where
      atom n k = showParen (p > n) $ showString k
      prefix n k a = showParen (p > n) $ showString k . showsPrec (n + 1) a
      infixL n a op b = showParen (p > n) $ showsPrec n a . showString op . showsPrec (n + 1) b
      infixR n a op b = showParen (p > n) $ showsPrec (n + 1) a . showString op . showsPrec n b
      for [] = ""
      for xs = "@for " ++ unwords xs ++ ". "
      isVarName ('$' : xs) = all isAlphaNum xs
      isVarName (x : xs) = isLower x && all isAlphaNum xs
      isVarName [] = False
      isTagName (x : xs) = isUpper x && all isAlphaNum xs
      isTagName [] = False
      op2 op = " " ++ show op ++ " "
      op1 op = show op ++ " "

instance Show Type where
  show (For [] t) = show t
  show (For xs t) = "@for " ++ unwords xs ++ ". " ++ show t

instance Show BinaryOp where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Pow = "^"
  show Eq = "=="
  show Lt = "<"

instance Show UnaryOp where
  show Int2Num = "@int2num"

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr (App . App Fun) b bs

-- asFun :: Expr -> ([Expr], Expr)
-- asFun (Fun a1 a2) = let (bs, b) = asFun a2 in (a1 : bs, b)
-- asFun a = ([], a)

lam :: [String] -> Expr -> Expr
lam xs b = foldr Lam b xs

asLam :: Expr -> ([String], Expr)
asLam (Lam x a) = let (xs, b) = asLam a in (x : xs, b)
asLam a = ([], a)

add :: Expr -> Expr -> Expr
add = App . App (Op2 Add)

sub :: Expr -> Expr -> Expr
sub = App . App (Op2 Sub)

mul :: Expr -> Expr -> Expr
mul = App . App (Op2 Mul)

pow :: Expr -> Expr -> Expr
pow = App . App (Op2 Pow)

eq :: Expr -> Expr -> Expr
eq = App . App (Op2 Eq)

lt :: Expr -> Expr -> Expr
lt = App . App (Op2 Lt)

gt :: Expr -> Expr -> Expr
gt a b = (App . App (Op2 Lt)) b a

int2num :: Expr -> Expr
int2num = App (Op1 Int2Num)

let' :: [(String, Expr)] -> Expr -> Expr
let' [] b = b
let' ((x, a) : defs) b = App (Lam x (let' defs b)) a

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

app :: Expr -> [Expr] -> Expr
app = foldl App

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = let (a', bs) = asApp a in (a', bs ++ [b])
asApp a = (a, [])

-- Helper functions
pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

pushAll :: [(String, Expr)] -> Env -> Env
pushAll vars env = foldr (:) env vars

popAll :: [String] -> Env -> Env
popAll xs env = foldl (flip pop) env xs

pushVars :: [String] -> Env -> Env
pushVars xs = pushAll (map (\x -> (x, Var x)) xs)

freeVars :: Expr -> [String]
freeVars Err = []
freeVars Typ = []
freeVars Fun = []
freeVars IntT = []
freeVars NumT = []
freeVars (Int _) = []
freeVars (Num _) = []
freeVars (Tag _) = []
freeVars (Rec []) = []
freeVars (Rec ((_, a) : kvs)) = freeVars a `union` freeVars (Rec kvs)
freeVars (Var x) = [x]
freeVars (Lam x a) = delete x (freeVars a)
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a _) = freeVars a
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (If a b) = freeVars a `union` freeVars b
freeVars (Fst a) = freeVars a
freeVars (Snd a) = freeVars a
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Op2 _) = []
freeVars (Op1 _) = []

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
eval _ Err = Err
eval _ Typ = Typ
eval _ Fun = Fun
eval _ IntT = IntT
eval _ NumT = NumT
eval _ (Int i) = Int i
eval _ (Num n) = Num n
eval env (Tag k) = case lookup k env of
  Just (Tag k') | k == k' -> Tag k
  Just a -> eval ((k, Tag k) : env) a
  Nothing -> Tag k
eval env (Rec kvs) = Rec (map (second (eval env)) kvs)
eval env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Tag k) -> Tag k
  Just (Ann (Var x') _) | x == x' -> Var x
  Just a -> eval env a
  Nothing -> Var x
eval env (Lam x b) = case eval ((x, Var x) : env) b of
  b -> Lam x b
eval env (App a b) = case (eval env a, eval env b) of
  (Err, _) -> Err
  (Lam x a, b) -> eval [(x, b)] a
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err -> eval [] (App a2 b)
    Lam x a -> Or (Lam x a) (App a2 b)
    a | isOpen a -> Or a (App a2 b)
    a -> a
  (Fix x a, b) | isClosed b -> eval [(x, Fix x a)] (App a b)
  (Op1 op, b) | isClosed b -> case (op, b) of
    (Int2Num, Int b) -> Num (fromIntegral b)
    _else -> Err
  (App (Op2 op) a, b) | isClosed a && isClosed b -> case (op, a, b) of
    (Add, Int a, Int b) -> Int (a + b)
    (Add, Num a, Num b) -> Num (a + b)
    (Sub, Int a, Int b) -> Int (a - b)
    (Sub, Num a, Num b) -> Num (a - b)
    (Mul, Int a, Int b) -> Int (a * b)
    (Mul, Num a, Num b) -> Num (a * b)
    (Pow, Int a, Int b) -> Int (a ^ b)
    (Pow, Num a, Num b) -> Num (a ** b)
    (Eq, Typ, Typ) -> Typ
    (Eq, IntT, IntT) -> IntT
    (Eq, NumT, NumT) -> NumT
    (Eq, Int a, Int b) | a == b -> Int a
    (Eq, Num a, Num b) | a == b -> Num a
    (Eq, Var a, Var b) | a == b -> Var a
    (Eq, App a1 a2, App b1 b2) -> If (eq a1 b1) (eq a2 b2)
    (Eq, Op2 a, Op2 b) | a == b -> Op2 a
    (Eq, Op1 a, Op1 b) | a == b -> Op1 a
    (Lt, Int a, Int b) | a < b -> Int a
    (Lt, Num a, Num b) | a < b -> Num a
    _else -> Err
  (a, b) -> App a b
eval env (Ann a (For xs t)) = case (eval env a, eval (pushVars xs env) t) of
  (a, Or t1 t2) -> eval [] (Or (Ann a (For xs t1)) (Ann a (For xs t2)))
  (Typ, Typ) -> Typ
  (Fun, Fun) -> Fun
  (IntT, Typ) -> IntT
  (NumT, Typ) -> NumT
  (Int i, IntT) -> Int i
  (Num n, NumT) -> Num n
  (Tag k, t) -> Ann (Tag k) (For xs t)
  (Var x, t) -> Ann (Var x) (For xs t)
  (Lam x b, App (App Fun t1) t2) -> Lam x (If (Ann (Var x) (For xs t1)) (eval [] $ Ann b (For xs t2)))
  (App a b, App t1 t2) -> eval [] (App (Ann a (For xs t1)) (Ann b (For xs t2)))
  (App a b, t) -> Ann (App a b) (For xs t)
  (Ann a ty, t) -> Ann (Ann a ty) (For xs t)
  (Or a b, t) -> eval [] (Or (Ann a (For xs t)) (Ann b (For xs t)))
  (If a b, t) -> If a (eval [] $ Ann b (For xs t))
  (Fst a, t) -> error "TODO: eval Ann Fst"
  (Snd a, t) -> error "TODO: eval Ann Snd"
  (Fix x a, t) -> eval ((x, Var x) : env) (Ann a (For xs t))
  (Rec kvs, Rec kvsT) -> error "TODO: eval Ann Rec"
  (Op1 op, App (App Fun _) _) -> Ann (Op1 op) (For xs t)
  (Op2 op, App (App (App Fun _) _) _) -> Ann (Op2 op) (For xs t)
  (_, _) -> Err
-- eval env (Ann (Tag k) (For xs a)) = Ann (Tag k) (For xs (eval (pushVars xs env) a))
-- eval env (Ann a _) = eval env a
eval env (Or a b) = case (eval env a, eval env b) of
  (Err, b) -> b
  (a, Err) -> a
  (Or a1 a2, b) -> Or a1 (Or a2 b)
  (a, b) -> Or a b
eval env (If a b) = case eval env a of
  Err -> Err
  a | isClosed a -> eval env b
  a -> If a (eval env b)
eval env (Fst a) = case eval env a of
  App a b | isClosed b -> a
  a -> Fst a
eval env (Snd a) = case eval env a of
  App a b | isClosed b -> b
  a -> Fst a
eval env (Fix x a) = Fix x (eval ((x, Var x) : env) a)
eval _ (Op1 op) = Op1 op
eval _ (Op2 op) = Op2 op

-- Type inference
apply :: Substitution -> Env -> Env
apply _ [] = []
apply s ((x, Ann a (For xs t)) : env) = do
  let t' = eval (pushVars xs s) t
  (x, Ann (eval s a) (For xs t')) : apply s env
apply s ((x, a) : env) = (x, eval s a) : apply s env

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = apply s1 s2 `union` s1

instantiate :: [String] -> Type -> (Expr, Substitution)
instantiate _ (For [] a) = (a, [])
instantiate existing (For (x : xs) a) = do
  let y = newName existing x
  let (b, s) = instantiate (y : x : existing) (For xs a)
  (eval [(x, Var y)] b, [(y, Var y)] `union` s)

unify :: Expr -> Expr -> Either TypeError (Expr, Substitution)
unify Typ Typ = Right (Typ, [])
unify Fun Fun = Right (Fun, [])
unify IntT IntT = Right (IntT, [])
unify NumT NumT = Right (NumT, [])
unify (Int i) (Int i') | i == i' = Right (Int i, [])
unify (Tag k) (Tag k') | k == k' = Right (Tag k, [])
unify (Tag k) (Ann (Tag k') (For [] b)) | k == k' = Right (b, [])
unify (Ann (Tag k) (For [] a)) (Tag k') | k == k' = Right (a, [])
unify (App a1 a2) (Ann (Tag k) (For [] (App (App Fun b1) b2))) = do
  (_, s1) <- unify a2 b1
  (c, s2) <- unify (eval s1 a1) (Ann (Tag k) (For [] (eval s1 b2)))
  Right (c, s2 `compose` s1)
unify a@(Ann (Tag _) _) b@(App _ _) = unify b a
unify a (Ann (Tag k) ty@(For (_ : _) _)) = do
  let (b, vars) = instantiate (freeVars a) ty
  (c, s) <- unify a (Ann (Tag k) (For [] b))
  Right (c, s `compose` vars)
unify (Ann (Tag k) ty@(For (_ : _) _)) b = unify b (Ann (Tag k) ty)
unify (Rec kvs) (Rec kvs') = do
  (kvs, s) <- unifyRec kvs kvs'
  Right (Rec kvs, s)
unify (Var x) (Var x') | x == x' = Right (Var x, [])
unify (Var x) b | x `occurs` b = Left (InfiniteType x b)
unify (Var x) b = Right (b, [(x, b)])
unify a (Var x) = unify (Var x) a
unify (App a1 b1) (App a2 b2) = do
  ((a, b), s) <- unify2 (a1, a2) (b1, b2)
  Right (App a b, s)
unify a (Or b1 b2) = case unify a b1 of
  Right (a, s1) -> case unify a (eval s1 b2) of
    Right (a, s2) -> Right (a, s2 `compose` s1)
    Left _ -> Right (a, s1)
  Left _ -> case unify a b2 of
    Left (TypeMismatch a b2) -> Left (TypeMismatch a (Or b1 b2))
    result -> result
unify (Or a1 a2) b = unify b (Or a1 a2)
unify (Op1 a) (Op1 b) | a == b = Right (Op1 a, [])
unify (Op2 a) (Op2 b) | a == b = Right (Op2 a, [])
unify a b = Left (TypeMismatch a b)

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either TypeError ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  (a, s1) <- unify a1 a2
  (b, s2) <- unify (eval s1 b1) (eval s1 b2)
  Right ((a, b), s2 `compose` s1)

unifyRec :: [(String, Expr)] -> [(String, Expr)] -> Either TypeError ([(String, Expr)], Substitution)
unifyRec [] _ = Right ([], [])
unifyRec ((x, a) : kvs) kvs' = case lookup x kvs' of
  Just b -> do
    (kvs, s1) <- unifyRec kvs kvs'
    (c, s2) <- unify (eval s1 a) (eval s1 b)
    Right ((x, c) : kvs, s2 `compose` s1)
  Nothing -> unifyRec kvs kvs'

listAlts :: Expr -> Env
listAlts (Ann (Tag k) ty) = [(k, Ann (Tag k) ty)]
listAlts (Or a b) = listAlts a ++ listAlts b
listAlts _ = []

infer :: Env -> Expr -> Either TypeError (Expr, Substitution)
infer _ Err = Right (Err, [])
infer _ Typ = Right (Typ, [])
infer _ Fun = Right (Fun, [])
infer _ IntT = Right (Typ, [])
infer _ NumT = Right (Typ, [])
infer _ (Int _) = Right (IntT, [])
infer _ (Num _) = Right (NumT, [])
infer env (Tag k) = case lookup k env of
  Just (Tag k') | k == k' -> Right (Tag k, [])
  Just (Ann (Tag k') ty) | k == k' -> Right (instantiate (map fst env) ty)
  Just a -> infer env a
  Nothing -> Right (Tag k, [])
infer env (Rec kvs) = do
  (kvsT, s) <- inferRec env kvs
  Right (Rec kvsT, s)
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let xT = newName (map fst env) (x ++ "T")
    Right (Var xT, [(xT, Var xT), (x, Ann (Var x) (For [] (Var xT)))])
  Just (Ann (Var x') ty) | x == x' -> do
    let (t, vars) = instantiate (map fst env) ty
    Right (eval (apply vars env) t, vars)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Lam x b) = do
  ((t1, t2), s) <- infer2 ((x, Var x) : env) (Var x) b
  Right (fun [t1] t2, s)
infer env (App a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case ta of
    Var x -> do
      let y = newName (map fst (s1 ++ env)) "t"
      (_, s2) <- unify (fun [tb] (Var y)) (Var x)
      Right (Var y, [(y, Var y)] `compose` s2 `compose` s1)
    Tag _ -> Right (App ta tb, s1)
    App (App Fun t1) t2 -> do
      (_, s2) <- unify tb t1
      Right (eval s2 t2, s2 `compose` s1)
    App _ _ -> Right (App ta tb, s1)
    ta -> Left (NotAFunction a ta)
infer env (Ann a ty) = do
  let (t, vars) = instantiate (map fst env) ty
  let alts = listAlts (eval (apply vars env) t)
  (ta, s1) <- infer (apply vars (alts ++ env)) a
  (t, s2) <- unify ta (eval s1 t)
  Right (t, s2 `compose` s1)
infer env (Or a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case unify ta tb of
    Right (t, s2) -> Right (t, s2 `compose` s1)
    Left _ -> Right (Or ta tb, s1)
infer env (If a b) = do
  ((_, tb), s) <- infer2 env a b
  Right (tb, s)
infer env (Fst a) = error "TODO: infer Fst"
infer env (Snd a) = error "TODO: infer Snd"
infer env (Fix x a) = infer ((x, Var x) : env) a
infer env (Op1 op) = case op of
  Int2Num -> Right (fun [IntT, IntT] IntT, [])
infer env (Op2 op) = case op of
  Add -> Right (fun [IntT, IntT] IntT, [])
  Sub -> Right (fun [IntT, IntT] IntT, [])
  Mul -> Right (fun [IntT, IntT] IntT, [])
  Pow -> Right (fun [IntT, IntT] IntT, [])
  Eq -> Right (instantiate (map fst env) (For ["eq"] (fun [Var "eq", Var "eq"] (Var "eq"))))
  Lt -> Right (instantiate (map fst env) (For ["lt"] (fun [Var "lt", Var "lt"] (Var "lt"))))

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (s1 ++ apply s1 env) b
  Right ((eval s2 ta, tb), s2 `compose` s1)

inferRec :: Env -> [(String, Expr)] -> Either TypeError ([(String, Expr)], Substitution)
inferRec _ [] = Right ([], [])
inferRec env ((x, a) : kvs) = do
  (kvsT, s1) <- inferRec env kvs
  (ta, s2) <- infer (apply s1 env) a
  Right ((x, ta) : kvsT, s2 `compose` s1)

-- -- Typed
-- typedP :: Pattern -> Expr -> Pattern
-- typedP (PVar x) IntT = PInt x
-- typedP (PVar x) NumT = PNum x
-- -- typedP (PVar x) (Typ t ks) =
-- typedP p _ = p

-- Optimize
optimize :: Expr -> Expr
optimize a = a
