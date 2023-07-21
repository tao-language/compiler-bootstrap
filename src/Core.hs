{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (first, second))
import Data.Char (isLetter)
import Data.Foldable (Foldable (foldl'))
import Data.List (delete, intercalate, union)

{- TODO:
- Rework Op to not have to include an Ops dictionary at runtime
- Add Records
- Clean up code
  * infer Case
- Consistency on variable names:
  * Expr: a, b, c
  * Type: t, t1, t2, ta, tb, tc
  * Var: x, y, z
- Remove unused errors
-}

data Expr
  = Err
  | Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Var !String
  | Ctr !String !String ![Expr]
  | Typ !String ![Expr] ![(String, Type)]
  | Lam !Pattern !Expr
  | For !String !Expr
  | Fun !Expr !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Or !Expr !Expr
  | Let !Env !Expr
  | Fix !String !Expr
  | Op !String ![Expr]
  deriving (Eq)

showParen' :: Bool -> String -> String
showParen' True a = "(" ++ a ++ ")"
showParen' False a = a

showPrefix :: Int -> Int -> String -> Expr -> String
showPrefix p q op a = showParen' (p > q) (op ++ showPrec q a)

showInfixL :: Int -> Int -> Expr -> String -> Expr -> String
showInfixL p q a op b = showParen' (p > q) (showPrec q a ++ op ++ showPrec (q + 1) b)

showInfixR :: Int -> Int -> Expr -> String -> Expr -> String
showInfixR p q a op b = showParen' (p > q) (showPrec (q + 1) a ++ op ++ showPrec q b)

showPrec :: Int -> Expr -> String
showPrec _ Err = "@error"
showPrec _ Knd = "@Kind"
showPrec _ IntT = "@Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "@Num"
showPrec _ (Num n) = show n
-- TODO: do actual check that it's a valid identifier
showPrec _ (Var "") = "_"
showPrec _ (Var x@('_' : _)) = x
showPrec _ (Var x@(ch : _)) | isLetter ch = x
showPrec _ (Var x) = "${" ++ x ++ "}"
showPrec p (Ctr tx k args) = "#" ++ showPrec p (app (Var (tx ++ "." ++ k)) args)
showPrec _ (Typ name args alts) = do
  let showAlt (k, ts) = "#" ++ show (App (Var k) ts)
  "%(" ++ unwords (name : map show args) ++ " { " ++ intercalate " | " (map showAlt alts) ++ " })"
showPrec p (Lam q a) = do
  let (ps, a') = asLam (Lam q a)
  showPrefix p 2 ("\\" ++ unwords (map show ps) ++ ". ") a'
showPrec p (For x a) = do
  let (xs, a') = asFor (For x a)
  showPrefix p 2 ("@for " ++ unwords xs ++ ". ") a'
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (App a b) = showInfixL p 3 a " " b
showPrec p (Ann a b) = showInfixL p 1 a " : " b
showPrec p (Let [] a) = showPrec p a
showPrec p (Let env a) = do
  let showDef (x, b) = x ++ " = " ++ show b
  let defs = "@let {" ++ intercalate "; " (showDef <$> env) ++ "} "
  showPrefix p 2 defs a
showPrec _ (Fix x a) = "@fix " ++ x ++ " {" ++ show a ++ "}"
showPrec p (Or a b) = showInfixR p 1 a " | " b
showPrec p (Op op args) = showPrec p (app (Var ("@op[" ++ op ++ "]")) args)

instance Show Expr where
  show :: Expr -> String
  show a = showPrec 0 a

type Type = Expr

type Operator = [Expr] -> Maybe Expr

type Ops = [(String, Operator)]

type Env = [(String, Expr)]

data Pattern
  = IntP !Int
  | VarP !String
  | CtrP !String !String ![Pattern]
  deriving (Eq)

data Branch
  = Br ![Pattern] !Expr
  deriving (Eq, Show)

instance Show Pattern where
  show :: Pattern -> String
  show (IntP i) = show i
  show (VarP x) = x
  show (CtrP tx k []) = "#" ++ tx ++ "." ++ k
  show (CtrP tx k ps) = "(#" ++ tx ++ "." ++ k ++ " " ++ unwords (map show ps) ++ ")"

data MatchStep
  = MatchEnd !Expr
  | MatchAny ![Branch]
  | MatchInt ![(Int, [Branch])] ![Branch]
  | MatchCtr ![(String, (Int, [Branch]))] ![Branch]
  deriving (Eq, Show)

data TypeError
  = CtrNotInType !String ![(String, Type)]
  | EmptyCase
  | InfiniteType !String !Expr
  | MatchCtrArgsMismatch !Int ![Pattern]
  | MatchMixIntCtrPatterns
  | MatchNumPatternsMismatch
  | MissingType !String !Expr
  | NotAFunction !Type
  | NotAUnionAlt !String !Expr
  | NotAUnionType !String !Expr
  | NotAnOp !String !Expr
  | RuntimeError
  | TooManyArgs !Expr ![Expr]
  | TypeMismatch !Expr !Expr
  | UndefinedCtr !String
  | UndefinedOp !String
  | UndefinedType !String
  | UndefinedUnionAlt !String
  | UndefinedUnionType !String
  | UndefinedVar !String
  deriving (Eq, Show)

lam :: [Pattern] -> Expr -> Expr
lam ps a = foldr Lam a ps

asLam :: Expr -> ([Pattern], Expr)
asLam (Lam p a) = first (p :) (asLam a)
asLam a = ([], a)

for :: [String] -> Expr -> Expr
for xs a = foldr (\x a -> if x `occurs` a then For x a else a) a xs

asFor :: Expr -> ([String], Expr)
asFor (For x a) = first (x :) (asFor a)
asFor (Fun a b) = second (Fun a) (asFor b)
asFor a = ([], a)

fun :: [Type] -> Type -> Type
fun bs ret = foldr Fun ret bs

asFun :: Expr -> ([Expr], Expr)
asFun (Fun a b) = first (a :) (asFun b)
asFun a = ([], a)

app :: Expr -> [Expr] -> Expr
app = foldl' App

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

let' :: Env -> Expr -> Expr
let' [] a = a
let' env a = Let env a

pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

set :: Eq k => k -> v -> [(k, v)] -> [(k, v)]
set _ _ [] = []
set x y ((x', _) : kvs) | x == x' = (x, y) : kvs
set x y (kv : kvs) = kv : set x y kvs

pushAll :: [(String, Expr)] -> Env -> Env
pushAll syms env = foldr (:) env syms

popAll :: [String] -> Env -> Env
popAll xs env = foldl' (flip pop) env xs

pushVars :: [String] -> Env -> Env
pushVars xs env = foldr (\x -> (:) (x, Var x)) env xs

popVars :: [String] -> Env -> Env
popVars xs env = foldl' (flip pop) env xs

freeVars :: Expr -> [String]
freeVars Err = []
freeVars Knd = []
freeVars IntT = []
freeVars NumT = []
freeVars (Int _) = []
freeVars (Num _) = []
freeVars (Var x) = [x]
freeVars (Ctr _ _ args) = foldr (union . freeVars) [] args
freeVars (Typ _ args alts) = foldr (union . freeVars) [] args
freeVars (Lam p a) = filter (`notElem` freeVarsP p) (freeVars a)
freeVars (For x a) = delete x (freeVars a)
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a b) = freeVars a `union` freeVars b
freeVars (Let env a) =
  filter (`notElem` map fst env) (foldr (union . freeVars . snd) (freeVars a) env)
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (Op _ args) = foldr (union . freeVars) [] args

freeVarsP :: Pattern -> [String]
freeVarsP (IntP _) = []
freeVarsP (VarP x) = [x]
freeVarsP (CtrP _ _ ps) = foldr (union . freeVarsP) [] ps

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

reduce :: Ops -> Env -> Expr -> Expr
reduce _ _ Err = Err
reduce _ _ Knd = Knd
reduce _ _ IntT = IntT
reduce _ _ NumT = NumT
reduce _ _ (Int i) = Int i
reduce _ _ (Num n) = Num n
reduce ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Let env a) -> reduce ops env a
  Just a -> reduce ops env a
  Nothing -> Var x
reduce _ env (Ctr tx k args) = Ctr tx k (Let env <$> args)
reduce _ env (Typ name args alts) = Typ name (Let env <$> args) (second (Let env) <$> alts)
reduce _ env (Lam p a) = Lam p (Let env a)
reduce _ env (For x a) = For x (Let env a)
reduce _ env (Fun a b) = Fun (Let env a) (Let env b)
reduce ops env (App a b) = case reduce ops env a of
  Err -> Err
  Lam (IntP i) a -> case reduce ops env b of
    Int i' | i == i' -> reduce ops [] a
    Int _ -> Err
    b -> App (Lam (IntP i) a) b
  Lam (VarP x) a -> reduce ops [(x, Let env b)] a
  Lam (CtrP tx k ps) a -> case reduce ops env b of
    Ctr tx' k' args | tx == tx' && k == k' -> reduce ops [] (app (lam ps a) args)
    Ctr {} -> Err
    b -> App (Lam (CtrP tx k ps) a) b
  Or a1 a2 -> case reduce ops [] (App a1 (Let env b)) of
    Err -> reduce ops [] (App a2 (Let env b))
    Var x -> Or (Var x) (App a2 (Let env b))
    App a1 b1 -> Or (App a1 b1) (App a2 (Let env b))
    c -> c
  Fix _ a -> reduce ops [] (App a (Let env b))
  a -> App a (Let env b)
reduce ops env (Ann a _) = reduce ops env a
reduce _ env (Or a b) = Or (Let env a) (Let env b)
reduce ops env (Let env' a) = reduce ops (env ++ env') a
reduce _ env (Fix x a) = Fix x (Let env a)
reduce ops env (Op op args) = do
  case (lookup op ops, eval ops env <$> args) of
    (Just f, args) -> case f args of
      Just a -> reduce ops env a
      Nothing -> Op op args
    (Nothing, args) -> Op op args

eval :: Ops -> Env -> Expr -> Expr
eval ops env term = case reduce ops env term of
  Err -> Err
  Knd -> Knd
  IntT -> IntT
  NumT -> NumT
  Int i -> Int i
  Num n -> Num n
  Var x -> Var x
  Ctr tx k args -> Ctr tx k (eval ops [] <$> args)
  Typ name args alts -> Typ name (eval ops [] <$> args) (second (eval ops [(name, Var name)]) <$> alts)
  Lam p a -> Lam p (eval ops (map (\x -> (x, Var x)) (freeVarsP p)) a)
  For x a -> for [x] (eval ops [(x, Var x)] a)
  Fun a b -> Fun (eval ops [] a) (eval ops [] b)
  App a b -> App (eval ops [] a) (eval ops [] b)
  Ann _ _ -> error "unreachable"
  Or a b -> Or (eval ops [] a) (eval ops [] b)
  Let _ _ -> error "unreachable"
  Fix x a -> case eval ops [(x, Var x)] a of
    a | x `occurs` a -> Fix x a
    a -> a
  Op op args -> Op op (eval ops [] <$> args)

subtype :: Ops -> Env -> Type -> Type -> Either TypeError (Type, Env)
subtype ops env a b = case (a, b) of
  (Knd, Knd) -> Right (Knd, env)
  (IntT, IntT) -> Right (IntT, env)
  (NumT, NumT) -> Right (NumT, env)
  (Int _, IntT) -> Right (IntT, env)
  (Int i, Int i') | i == i' -> Right (Int i, env)
  (Num _, NumT) -> Right (NumT, env)
  (Num n, Num n') | n == n' -> Right (Num n, env)
  (Var x, Var x') | x == x' -> Right (Var x, env)
  (a, Var x) | x `occurs` a -> Left (InfiniteType x a)
  (a, Var x) -> Right (apply env a, set x (apply env a) env)
  (Var x, b) -> subtype ops env b (Var x)
  (Ctr tx k args, Ctr tx' k' args') | tx == tx' && k == k' && length args == length args' -> do
    (argsT, env) <- subtypeAll ops env args args'
    Right (Ctr tx k argsT, env)
  (Ctr tx k args, Typ tx' targs alts) | tx == tx' -> case lookup k alts of
    Just altType -> do
      (_, env) <- subtypeAll ops env args (fst (asFun altType))
      Right (Typ tx' targs alts, env)
    Nothing -> Left (CtrNotInType k alts)
  (Typ tx targs alts, Typ tx' targs' alts') | tx == tx' && length targs == length targs' && map fst alts == map fst alts' -> do
    (targs, env) <- subtypeAll ops env targs targs'
    -- TODO: check alts
    Right (Typ tx targs alts, env)
  (a, For x b) -> do
    let y = newName x (map fst env)
    (a, env) <- subtype ops ((y, Var y) : env) a (substitute x y b)
    Right (for [y] a, pop y env)
  (For x a, b) -> do
    let y = newName x (map fst env)
    (a, env) <- subtype ops ((y, Var y) : env) (substitute x y a) b
    Right (for [y] a, pop y env)
  (Fun a1 b1, Fun a2 b2) -> do
    (a, env) <- subtype ops env a1 a2
    (b, env) <- subtype ops env (apply env b2) (apply env b1)
    Right (Fun (apply env a) b, env)
  (App a1 b1, App a2 b2) -> do
    (a, env) <- subtype ops env a1 a2
    (b, env) <- subtype ops env (apply env b1) (apply env b2)
    Right (App (apply env a) b, env)
  (a, Or b1 b2) -> case subtype ops env a b1 of
    Right (a, env) -> case subtype ops env a (apply env b2) of
      Right (b, env) -> case unify env a (apply env b) of
        Right (c, env) -> Right (c, env)
        Left _ -> Right (Or (apply env a) b, env)
      Left _ -> Right (a, env)
    Left _ -> subtype ops env a b2
  (Or a1 a2, b) -> do
    (a1, env) <- subtype ops env a1 b
    (a2, env) <- subtype ops env (apply env a2) (apply env b)
    case unify env a1 a2 of
      Right (a, env) -> Right (a, env)
      Left _ -> Right (Or (apply env a1) a2, env)
  (Op op args, Op op' args') | op == op' && length args == length args' -> do
    (args, env) <- subtypeAll ops env args args'
    Right (Op op args, env)
  (a, b) -> Left (TypeMismatch a b)
  where
    apply env = eval ops env
    substitute x y = eval ops [(x, Var y)]
    unify env a b = case subtype ops env b a of
      Right (c, env) -> Right (c, env)
      Left _ -> subtype ops env a b

subtypeAll :: Ops -> Env -> [Expr] -> [Expr] -> Either TypeError ([Expr], Env)
subtypeAll _ env [] _ = Right ([], env)
subtypeAll _ env _ [] = Right ([], env)
subtypeAll ops env (a1 : bs1) (a2 : bs2) = do
  (a, env) <- subtype ops env a1 a2
  (bs, env) <- subtypeAll ops env (apply env <$> bs1) (apply env <$> bs2)
  Right (apply env a : bs, env)
  where
    apply env = eval ops env

findUnionType :: Env -> String -> Either TypeError (Env, [(String, Type)])
findUnionType env tx = case lookup tx env of
  Just (Ann a _) -> findUnionType ((tx, a) : env) tx
  Just a -> do
    let varName (VarP x) = x
        varName _ = ""
    let (xs, tdef) = first (map varName) (asLam a)
    case tdef of
      Typ _ args alts -> Right (zip xs args, alts)
      a -> Left (NotAUnionType tx a)
  Nothing -> Left (UndefinedType tx)

infer :: Ops -> Env -> Expr -> Either TypeError (Type, Env)
infer ops env expr = case expr of
  Err -> Left RuntimeError
  Knd -> Right (Knd, env)
  IntT -> Right (Knd, env)
  Int _ -> Right (IntT, env)
  NumT -> Right (Knd, env)
  Num _ -> Right (NumT, env)
  Var x -> case lookup x env of
    Just (Var x') | x == x' -> Right (Knd, env)
    Just (Ann (Var x') t) | x == x' -> Right (apply env t, env)
    Just a -> infer ops env a
    Nothing -> Left (UndefinedVar x)
  Ctr tx k args -> do
    (vars, alts) <- findUnionType env tx
    let xs = map fst vars
    case lookup k alts of
      Just t -> do
        (t, env) <- inferApply ops (pushAll vars env) (k, t) args
        case (args, popAll xs env) of
          ([], env) -> Right (for xs t, env)
          (_, env) -> Right (t, env)
      Nothing -> Left (CtrNotInType k alts)
  Typ name args alts -> do
    -- TODO: check that type exists
    -- TODO: check args
    -- TODO: check alts
    Right (Knd, env)
  Lam (IntP i) a -> do
    (t2, env) <- infer ops env a
    Right (Fun (Int i) t2, env)
  Lam (VarP x) a -> do
    let xT = newName (x ++ "T") (map fst env)
    env <- Right ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env)
    (t2, env) <- infer ops env a
    (t1, env) <- infer ops env (Var x)
    case (eval ops env (Var xT), pop x env) of
      (Var xT, env) -> Right (For xT $ Fun t1 t2, env)
      (_, env) -> Right (Fun t1 t2, env)
  Lam (CtrP tx k ps) a -> do
    (t, env) <- infer ops env (lam ps a)
    (xs, (ts, t2)) <- Right (second asFun (asFor t))
    (ts1, ts2) <- Right (splitAt (length ps) ts)
    (vars, alts) <- findUnionType env tx
    case lookup k alts of
      Just altType -> do
        env <- Right (pushAll (map (\x -> (x, Var x)) xs) env)
        (_, env) <- subtypeAll ops env (fst (asFun altType)) ts1
        let ys = [x | Var x <- map (eval ops env . Var) xs]
        Right (for ys $ eval ops env (Fun (Ctr tx k ts1) (fun ts2 t2)), popAll xs env)
      Nothing -> Left (CtrNotInType k alts)
  For x a -> do
    let xT = newName (x ++ "T") (map fst env)
    env <- Right ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env)
    (aT, env) <- infer ops env a
    Right (for [xT] aT, pop x env)
  Fun a b -> do
    (_, env) <- infer ops env a
    (_, env) <- infer ops env b
    Right (Knd, env)
  App a b -> do
    (ta, env) <- infer ops env a
    (tb, env) <- infer ops env b
    let x = newName "t" (map fst env)
    env <- Right ((x, Var x) : env)
    (t, env) <- subtype ops env ta (Fun tb (Var x))
    case asFor t of
      (xs, Fun _ t) -> Right (for xs t, pop x env)
      _else -> error "unreachable"
  Ann a t -> do
    (ta, env) <- infer ops env a
    subtype ops env ta (apply env t)
  Let defs a -> infer ops (env ++ defs) a
  Fix x a -> do
    let xT = newName (x ++ "T") (map fst env)
    env <- Right ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env)
    (ta, env) <- infer ops env a
    Right (ta, pop x env)
  Or a b -> do
    (ta, env) <- infer ops env a
    (tb, env) <- infer ops env b
    case subtype ops env tb ta of
      Right (t, env) -> Right (t, env)
      Left _ -> case subtype ops env ta tb of
        Right (t, env) -> Right (t, env)
        Left _ -> Right (Or ta tb, env)
  Op op args -> case lookup op env of
    Just (Ann a t) -> inferApply ops env (op, t) args
    Just a -> Left (MissingType op a)
    Nothing -> Left (UndefinedVar op)
  where
    apply env = eval ops env

inferAll :: Ops -> Env -> [Expr] -> Either TypeError ([Type], Env)
inferAll _ env [] = Right ([], env)
inferAll ops env (a : bs) = do
  (t, env) <- infer ops env a
  (ts, env) <- inferAll ops env bs
  Right (t : ts, env)

inferApply :: Ops -> Env -> (String, Type) -> [Expr] -> Either TypeError (Type, Env)
inferApply ops env (x, t) args = do
  env <- Right ((x, Ann (Var x) t) : env)
  (t, env) <- infer ops env (app (Var x) args)
  Right (t, pop x env)

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names

newNames :: [String] -> [String] -> [String]
newNames [] _ = []
newNames (x : xs) existing = do
  let y = newName x existing
  y : newNames xs (y : existing)
