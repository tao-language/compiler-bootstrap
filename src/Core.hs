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
  | Typ !String ![(String, Expr)] ![(String, Type)]
  | Lam !Pattern !Expr
  | Fun !Expr !Expr
  | App !Expr !Expr
  | Ann !Expr !TypeScheme
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
showPrec p (Typ name args alts) = do
  -- let showAlt (k, ts) = "#" ++ show (App (Var k) ts)
  -- "%(" ++ unwords (name : map show args) ++ " { " ++ intercalate " | " (map showAlt alts) ++ " })"
  showPrec p (app (Var name) (map snd args))
showPrec p (Lam q a) = do
  let (ps, a') = asLam (Lam q a)
  showPrefix p 2 ("\\" ++ unwords (map show ps) ++ ". ") a'
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (App a b) = showInfixL p 3 a " " b
showPrec p (Ann a typ) = show a ++ " : " ++ show typ
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

data TypeScheme
  = For ![String] !Type
  deriving (Eq)

instance Show TypeScheme where
  show (For [] a) = show a
  show (For xs a) = "@forall " ++ unwords xs ++ ". " ++ show a

type Substitution = [(String, Type)]

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

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = second (++ [b]) (asApp a)
asApp a = (a, [])

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
pushAll vars env = foldr (:) env vars

popAll :: [String] -> Env -> Env
popAll xs env = foldl' (flip pop) env xs

pushVars :: [String] -> Env -> Env
pushVars xs = pushAll (map (\x -> (x, Var x)) xs)

freeVars :: Expr -> [String]
freeVars Err = []
freeVars Knd = []
freeVars IntT = []
freeVars NumT = []
freeVars (Int _) = []
freeVars (Num _) = []
freeVars (Var x) = [x]
freeVars (Ctr _ _ args) = foldr (union . freeVars) [] args
freeVars (Typ _ args _) = foldr (union . freeVars . snd) [] args
freeVars (Lam p a) = filter (`notElem` freeVarsP p) (freeVars a)
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a (For xs b)) = freeVars a `union` filter (`notElem` xs) (freeVars b)
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
reduce _ env (Typ name args alts) = Typ name (second (Let env) <$> args) alts
reduce _ env (Lam p a) = Lam p (Let env a)
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
  Typ name args alts -> Typ name (second (eval ops []) <$> args) alts
  Lam p a -> Lam p (eval ops (map (\x -> (x, Var x)) (freeVarsP p)) a)
  Fun a b -> Fun (eval ops [] a) (eval ops [] b)
  App a b -> App (eval ops [] a) (eval ops [] b)
  Ann _ _ -> error "unreachable"
  Or a b -> Or (eval ops [] a) (eval ops [] b)
  Let _ _ -> error "unreachable"
  Fix x a -> case eval ops [(x, Var x)] a of
    a | x `occurs` a -> Fix x a
    a -> a
  Op op args -> Op op (eval ops [] <$> args)

subtype :: Type -> Type -> Either TypeError (Type, [(String, Expr)])
subtype Knd Knd = Right (Knd, [])
subtype IntT IntT = Right (IntT, [])
subtype NumT NumT = Right (NumT, [])
subtype (Int _) IntT = Right (IntT, [])
subtype (Int i) (Int i') | i == i' = Right (Int i, [])
subtype (Num _) NumT = Right (NumT, [])
subtype (Num n) (Num n') | n == n' = Right (Num n, [])
subtype (Var x) (Var x') | x == x' = Right (Var x, [])
subtype a (Var x) | x `occurs` a = Left (InfiniteType x a)
subtype a (Var x) = Right (a, [(x, a)])
subtype (Var x) b = subtype b (Var x)
subtype (Ctr tx k args) (Ctr tx' k' args') | tx == tx' && k == k' && length args == length args' = do
  (argsT, s) <- subtypeAll args args'
  Right (Ctr tx k argsT, s)
subtype (Ctr tx k args) (Typ tx' targs alts) | tx == tx' = case lookup k alts of
  Just altType -> do
    let (altArgs, altReturn) = asFun altType
    let (typeName, typeArgs) = asApp altReturn
    -- TODO: check typeName
    (_, s1) <- subtypeAll args altArgs
    (typArgs, s2) <- subtypeAll (map (apply s1) typeArgs) (map snd targs)
    Right (Typ tx (zip (map fst targs) typArgs) alts, s2 `compose` s1)
  Nothing -> Left (CtrNotInType k alts)
subtype (Typ tx targs alts) (Typ tx' targs' alts') | tx == tx' && map fst targs == map fst targs' && alts == alts' = do
  (argsT, s) <- subtypeAll (map snd targs) (map snd targs')
  Right (Typ tx (zip (map fst targs) argsT) alts, s)
subtype (Fun a1 b1) (Fun a2 b2) = do
  (a, s1) <- subtype a1 a2
  (b, s2) <- subtype (apply s1 b2) (apply s1 b1)
  Right (Fun (apply s2 a) b, s2 `compose` s1)
subtype (App a1 b1) (App a2 b2) = do
  (a, s1) <- subtype a1 a2
  (b, s2) <- subtype (apply s1 b1) (apply s1 b2)
  Right (App (apply s2 a) b, s2 `compose` s1)
subtype a (Or b1 b2) = case subtype a b1 of
  Right (a, s1) -> case subtype a (apply s1 b2) of
    Right (b, s2) -> case unify (apply s2 a) b of
      Right (c, s3) -> Right (c, s3 `compose` s2 `compose` s1)
      Left _ -> Right (Or (apply s2 a) b, s2 `compose` s1)
    Left _ -> Right (a, s1)
  Left _ -> subtype a b2
subtype (Or a1 a2) b = do
  (a1, s1) <- subtype a1 b
  (a2, s2) <- subtype (apply s1 a2) (apply s1 b)
  case unify (apply s2 a1) a2 of
    Right (a, s3) -> Right (a, s3 `compose` s2 `compose` s1)
    Left _ -> Right (Or (apply s2 a1) a2, s2 `compose` s1)
subtype (Op op args) (Op op' args') | op == op' && length args == length args' = do
  (args, s) <- subtypeAll args args'
  Right (Op op args, s)
subtype a b = Left (TypeMismatch a b)

subtypeAll :: [Expr] -> [Expr] -> Either TypeError ([Expr], Env)
subtypeAll [] _ = Right ([], [])
subtypeAll _ [] = Right ([], [])
subtypeAll (a1 : bs1) (a2 : bs2) = do
  (a, s1) <- subtype a1 a2
  (bs, s2) <- subtypeAll (apply s1 <$> bs1) (apply s1 <$> bs2)
  Right (apply s2 a : bs, s2 `compose` s1)

apply :: Substitution -> Expr -> Expr
apply = eval []

applyEnv :: Substitution -> Env -> Env
applyEnv _ [] = []
applyEnv s ((x, Ann a (For xs b)) : env) = do
  let typ = For xs (apply (foldr pop s xs) b)
  (x, Ann a typ) : applyEnv s env
applyEnv s (def : env) = def : applyEnv s env

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = map (second (apply s1)) s2 `union` s1

unify :: Type -> Type -> Either TypeError (Type, Substitution)
unify a b = case subtype b a of
  Right (c, s) -> Right (c, s)
  Left _ -> subtype a b

findUnionType :: Env -> String -> Either TypeError (Env, [(String, Type)])
findUnionType env tx = case lookup tx env of
  Just (Ann a _) -> findUnionType ((tx, a) : env) tx
  Just a -> case snd (asLam a) of
    Typ _ args alts -> Right (args, alts)
    a -> Left (NotAUnionType tx a)
  Nothing -> Left (UndefinedType tx)

-- https://youtu.be/ytPAlhnAKro
infer :: Ops -> Env -> Expr -> Either TypeError (Type, Substitution)
infer _ _ Err = Left RuntimeError
infer _ _ Knd = Right (Knd, [])
infer _ _ IntT = Right (Knd, [])
infer _ _ (Int _) = Right (IntT, [])
infer _ _ NumT = Right (Knd, [])
infer _ _ (Num _) = Right (NumT, [])
infer ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Right (Knd, [])
  Just (Ann (Var x') (For xs b)) | x == x' -> do
    Right (eval ops (pushVars xs env) b, [])
  Just a -> infer ops env a
  Nothing -> Left (UndefinedVar x)
infer ops env (Ctr tx k args) = do
  (vars, alts) <- findUnionType env tx
  let xs = map fst vars
  case lookup k alts of
    Just t -> inferApply ops (pushAll vars env) (k, For xs t) args
    Nothing -> Left (CtrNotInType k alts)
infer ops env (Typ name args alts) = do
  -- TODO: check that type exists
  -- TODO: check args
  -- TODO: check alts
  Right (Knd, [])
infer ops env (Lam (IntP i) a) = do
  (t2, s) <- infer ops env a
  Right (Fun (Int i) t2, s)
infer ops env (Lam (VarP x) a) = do
  let xT = newName (x ++ "T") (map fst env)
  let env' = (x, Ann (Var x) (For [] (Var xT))) : env
  ((t2, t1), s) <- infer2 ops env' a (Var x)
  Right (Fun t1 t2, s)
infer ops env (Lam (CtrP tx k ps) a) = do
  (typeWithArgs, s1) <- infer ops env (lam ps a)
  let (argTypes, returnType) = asFun typeWithArgs
  let (ctrArgTypes, returnTypeArgs) = splitAt (length ps) argTypes
  (vars, alts) <- findUnionType env tx
  case lookup k alts of
    Just altType -> do
      (ctrArgTypes, s2) <- subtypeAll ctrArgTypes (fst (asFun altType))
      let t1 = Ctr tx k ctrArgTypes
      let t2 = fun returnTypeArgs returnType
      Right (eval ops env (Fun t1 (apply s2 t2)), s2 `compose` s1)
    Nothing -> Left (CtrNotInType k alts)
infer ops env (Fun a b) = do
  (_, s) <- infer2 ops env a b
  Right (Knd, s)
infer ops env (App a b) = do
  let returnType :: Type -> Type -> Either TypeError (Type, Substitution)
      returnType (Fun t1 t2) tb = do
        (_, s) <- subtype t1 tb
        Right (apply s t2, s)
      returnType (Or t1 t2) tb = do
        (t1, s1) <- returnType t1 tb
        (t2, s2) <- returnType (apply s1 t2) (apply s1 tb)
        (t, s3) <- unify (apply s2 t1) t2
        Right (t, s3 `compose` s2 `compose` s1)
      returnType t _ = Left (NotAFunction t)
  ((ta, tb), s1) <- infer2 ops env a b
  (t, s2) <- returnType ta tb
  Right (eval ops env t, s2 `compose` s1)
infer ops env (Ann a (For xs b)) = do
  (ta, s1) <- infer ops env a
  let env' = applyEnv s1 env
  (t, s2) <- subtype ta (eval ops (pushVars xs env') b)
  Right (t, s2 `compose` s1)
infer ops env (Let defs a) = infer ops (env ++ defs) a
infer ops env (Fix x a) = do
  let x1 = newName (x ++ "T1") (map fst env)
  let x2 = newName (x ++ "T2") (x1 : map fst env)
  let env' = (x, Ann (Var x) (For [x1, x2] (Fun (Var x1) (Var x2)))) : env
  infer ops env' a
infer ops env (Or a b) = do
  ((ta, tb), s1) <- infer2 ops env a b
  case subtype tb ta of
    Right (t, s2) -> Right (t, s2 `compose` s1)
    Left _ -> case subtype ta tb of
      Right (t, s2) -> Right (t, s2 `compose` s1)
      Left _ -> Right (Or ta tb, s1)
infer ops env (Op op args) = case lookup op env of
  Just (Ann a typ) -> inferApply ops env (op, typ) args
  Just a -> Left (MissingType op a)
  Nothing -> Left (UndefinedVar op)

infer2 :: Ops -> Env -> Expr -> Expr -> Either TypeError ((Type, Type), Substitution)
infer2 ops env a b = do
  (ta, s1) <- infer ops env a
  (tb, s2) <- infer ops (applyEnv s1 env) b
  Right ((apply s2 ta, tb), s2 `compose` s1)

inferAll :: Ops -> Env -> [Expr] -> Either TypeError ([Type], Env)
inferAll _ env [] = Right ([], env)
inferAll ops env (a : bs) = do
  (t, s1) <- infer ops env a
  (ts, s2) <- inferAll ops (applyEnv s1 env) bs
  Right (apply s2 t : ts, s2 `compose` s1)

inferApply :: Ops -> Env -> (String, TypeScheme) -> [Expr] -> Either TypeError (Type, Env)
inferApply ops env (x, typ) args = do
  let env' = (x, Ann (Var x) typ) : env
  infer ops env' (app (Var x) args)

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names

newNames :: [String] -> [String] -> [String]
newNames [] _ = []
newNames (x : xs) existing = do
  let y = newName x existing
  y : newNames xs (y : existing)
