{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (first, second))
import Data.Char (isLetter)
import Data.Foldable (Foldable (foldl'))
import Data.List (delete, intercalate, union)

{- TODO:
- Adding ((x, Var x) : env) to `eval Var` stopped recursion evaluating types,
  can this be used instead of `Fix`?

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
  | Union ![(String, Type)]
  | Typ !String ![Expr]
  | Ctr !String !String ![Expr]
  | Lam !Expr !Expr
  | Fun !Expr !Expr
  | App !Expr !Expr
  | Ann !Expr !TypeScheme
  | Or !Expr !Expr
  | Let !Env !Expr
  | Fix !String !Expr
  | Op2 !BinaryOp !Expr !Expr
  | Call !String ![Expr]
  deriving (Eq)

data BinaryOp
  = Add
  | Sub
  | Mul
  deriving (Eq, Show)

instance Show Expr where
  show :: Expr -> String
  show a = showPrec 0 a

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
showPrec p (Typ name args) = "%" ++ showPrec p (app (Var name) args)
showPrec p (Union alts) = do
  let showAlt (k, t) = "#" ++ k ++ " : " ++ show t
  "{" ++ intercalate " | " (map showAlt alts) ++ "}"
showPrec p (Lam q a) = do
  let (ps, a') = asLam (Lam q a)
  showPrefix p 2 ("\\" ++ unwords (map show ps) ++ ". ") a'
showPrec p (Ann a typ) = show a ++ " : " ++ show typ
showPrec p (Let [] a) = showPrec p a
showPrec p (Let env a) = do
  let showDef (x, b) = x ++ " = " ++ show b
  let defs = "@let {" ++ intercalate "; " (showDef <$> env) ++ "} "
  showPrefix p 2 defs a
showPrec _ (Fix x a) = "@fix " ++ x ++ " (" ++ show a ++ ")"
showPrec p (Or a b) = showInfixR p 1 a " | " b
showPrec p (Fun a b) = showInfixR p 2 a " -> " b
showPrec p (Op2 Add a b) = showInfixL p 3 a " + " b
showPrec p (Op2 Sub a b) = showInfixL p 3 a " - " b
showPrec p (Op2 Mul a b) = showInfixL p 4 a " * " b
showPrec p (App a b) = showInfixL p 5 a " " b
showPrec p (Call f args) = showPrec p (app (Var ("@call " ++ f)) args)

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

data TypeError
  = CtrNotInType !String ![(String, Type)]
  | EmptyCase
  | InfiniteType !String !Expr
  | MissingType !String !Expr
  | NotAFunction !Type
  | TooFewArgs !String !Type ![Expr]
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

lam :: [Expr] -> Expr -> Expr
lam ps a = foldr Lam a ps

asLam :: Expr -> ([Expr], Expr)
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

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

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
freeVars (Typ _ args) = foldr (union . freeVars) [] args
freeVars (Union alts) = foldr (union . freeVars . snd) [] alts
freeVars (Lam p a) = filter (`notElem` freeVars p) (freeVars a)
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a (For xs b)) = freeVars a `union` filter (`notElem` xs) (freeVars b)
freeVars (Let env a) =
  filter (`notElem` map fst env) (foldr (union . freeVars . snd) (freeVars a) env)
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars (Call _ args) = foldr (union . freeVars) [] args

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

isOpen :: Expr -> Bool
isOpen Var {} = True
isOpen App {} = True
isOpen Or {} = True
isOpen Op2 {} = True
isOpen _ = False

isClosed :: Expr -> Bool
isClosed a = not (isOpen a)

reduce :: Env -> Expr -> Expr
reduce _ Err = Err
reduce _ Knd = Knd
reduce _ IntT = IntT
reduce _ NumT = NumT
reduce _ (Int i) = Int i
reduce _ (Num n) = Num n
reduce env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Let env a) -> reduce env a
  Just a -> reduce [] a
  Nothing -> Var x
reduce env (Union alts) = Union (second (reduce env) <$> alts)
reduce env (Typ tx args) = Typ tx (reduce env <$> args)
reduce env (Ctr tx k args) = Ctr tx k (reduce env <$> args)
reduce env (Lam p a) = Lam p (reduce (pushVars (freeVars p) env) a)
reduce env (Fun a b) = Fun (reduce env a) (reduce env b)
reduce env (App a b) = case (reduce env a, reduce env b) of
  (Err, _) -> Err
  (a, b) | isOpen b -> App a b
  (Lam (Var x) a, b) -> reduce [(x, Let env b)] a
  (Lam (Int i) a, Int i') | i == i' -> reduce [] a
  (Lam (Int _) _, Int _) -> Err
  (Lam (Ctr tx k ps) a, Ctr tx' k' args) | tx == tx' && k == k' -> do
    reduce [] (app (lam ps a) args)
  (Lam Ctr {} _, Ctr {}) -> Err
  (Lam p a, b) -> App (Lam p a) b
  (Ann a _, b) -> reduce [] (App a b)
  (Or a1 a2, b) -> case reduce [] (App a1 b) of
    Err -> reduce [] (App a2 b)
    a | isOpen a -> Or a (App a2 b)
    c -> c
  (Fix x a, b) -> reduce [(x, Fix x a)] (App a b)
  (a, b) -> App a b
reduce env (Fix x a) = Fix x (reduce ((x, Var x) : env) a)
reduce env (Ann a (For xs b)) = Ann (reduce env a) (For xs (reduce (pushVars xs env) b))
reduce env (Or a b) = Or (reduce env a) (reduce env b)
reduce env (Let env' a) = reduce (env ++ env') a
reduce env (Op2 op a b) = case (op, reduce env a, reduce env b) of
  (Add, Int a, Int b) -> Int (a + b)
  (Sub, Int a, Int b) -> Int (a - b)
  (Mul, Int a, Int b) -> Int (a * b)
  (op, a, b) -> Op2 op a b
reduce env (Call f args) = Call f (reduce env <$> args)

eval :: Env -> Expr -> Expr
eval env term = case reduce env term of
  Err -> Err
  Knd -> Knd
  IntT -> IntT
  NumT -> NumT
  Int i -> Int i
  Num n -> Num n
  Var x -> Var x
  Union alts -> Union (second (eval []) <$> alts)
  Typ tx args -> Typ tx (eval [] <$> args)
  Ctr tx k args -> Ctr tx k (eval [] <$> args)
  Lam p a -> Lam p (eval (pushVars (freeVars p) []) a)
  Fun a b -> Fun (eval [] a) (eval [] b)
  App a b -> App a (eval [] b)
  Ann a _ -> a
  Or a b -> Or (eval [] a) (eval [] b)
  Let _ _ -> error "unreachable"
  Fix x a | x `occurs` a -> Fix x a
  Fix _ a -> a
  Op2 op a b -> Op2 op (eval [] a) (eval [] b)
  Call f args -> Call f (eval [] <$> args)

subtype :: Type -> Type -> Either TypeError (Type, [(String, Expr)])
subtype Knd Knd = Right (Knd, [])
subtype IntT IntT = Right (IntT, [])
subtype NumT NumT = Right (NumT, [])
-- subtype (Int _) IntT = Right (IntT, [])
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
subtype (Typ tx args) (Typ tx' args') | tx == tx' && length args == length args' = do
  (args, s) <- subtypeAll args args'
  Right (Typ tx args, s)
subtype (Union alts) (Union alts') | map fst alts == map fst alts' = do
  (altTypes, s) <- subtypeAll (map snd alts) (map snd alts')
  Right (Union (zip (map fst alts) altTypes), s)
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
subtype (Call f args) (Call f' args') | f == f' && length args == length args' = do
  (args, s) <- subtypeAll args args'
  Right (Call f args, s)
subtype a b = Left (TypeMismatch a b)

subtypeAll :: [Expr] -> [Expr] -> Either TypeError ([Expr], Env)
subtypeAll [] _ = Right ([], [])
subtypeAll _ [] = Right ([], [])
subtypeAll (a1 : bs1) (a2 : bs2) = do
  (a, s1) <- subtype a1 a2
  (bs, s2) <- subtypeAll (apply s1 <$> bs1) (apply s1 <$> bs2)
  Right (apply s2 a : bs, s2 `compose` s1)

apply :: Substitution -> Expr -> Expr
apply s (Ann a (For xs b)) = Ann (apply s a) (For xs (apply (pushVars xs s) b))
apply s a = eval s a

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

-- findUnionType :: Env -> String -> Either TypeError ([(String, Expr)], [(String, Type)])
-- findUnionType env tx = case lookup tx env of
--   -- Just a -> case asLam a of
--   --   (ps, Ann a (For xs b))
--   --   (ps, a) -> error "untyped"
--   Just (Ann a _) -> findUnionType ((tx, a) : env) tx
--   Just a -> case snd (asLam a) of
--     Typ _ args alts -> Right (args, alts)
--     a -> Left (NotAUnionType tx a)
--   Nothing -> Left (UndefinedType tx)

-- https://youtu.be/ytPAlhnAKro
infer :: Env -> Expr -> Either TypeError (Type, Substitution)
infer _ Err = Left RuntimeError
infer _ Knd = Right (Knd, [])
infer _ IntT = Right (Knd, [])
infer _ (Int _) = Right (IntT, [])
infer _ NumT = Right (Knd, [])
infer _ (Num _) = Right (NumT, [])
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Right (Knd, [])
  Just (Ann (Var x') (For xs b)) | x == x' -> Right (eval (pushVars xs env) b, [])
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Ctr tx k args) = do
  error "TODO: infer Ctr"
-- (vars, alts) <- findUnionType env tx
-- let xs = map fst vars
-- case lookup k alts of
--   Just altType -> do
--     -- (t, s) <- inferApply (pushAll vars env) (k, For xs altType) args
--     let (altArgs, altReturn) = asFun altType
--     let (typeName, typeArgs) = asApp altReturn
--     -- TODO: check typeName
--     (_, s) <- subtypeAll args altArgs
--     Right (eval env (Typ tx (zip xs (map (apply s) typeArgs)) alts), s)
--   Nothing -> Left (CtrNotInType k alts)
-- case lookup tx env of
--   Just tdef -> case asLam tdef of
--     (ps, Ann (Typ tx targs) (For ys (Union alts))) -> do
--       let xs = foldr (union . freeVars) ys ps
--       case lookup k alts of
--         Just altType -> do
--           let env' = (tx, Var tx) : pushVars xs env
--           (ts, s) <- infer env' (altType)
--           error $ intercalate "\n" [show altType]
--           inferApply env' (k, For [] altType) args
--         Nothing -> Left (CtrNotInType k alts)
--     (ps, tdef) -> error "missing type"
--   Nothing -> Left (UndefinedType tx)
infer env (Typ tx args) = do
  (tdefKind, s1) <- infer env (Var tx)
  (kind, s2) <- inferApply (applyEnv s1 env) (tx, For [] tdefKind) args
  case kind of
    Fun a b -> Left (TooFewArgs tx (Fun a b) args)
    kind -> case reduce env (app (Var tx) args) of
      Ann _ (For xs t) -> Right (eval (pushVars xs env) t, s2 `compose` s1)
      a -> do
        -- error ("infer Typ missing type: " ++ show a)
        Right (Err, [])

-- error $ intercalate "\n" ["-- infer Typ", show knd]
-- tdef <- case lookup tx env of
--   Just tdef -> Right tdef
--   Nothing -> Left (UndefinedType tx)
-- (a, xs, b) <- case eval ((tx, Var tx) : env) (app tdef args) of
--   Ann a (For xs b) -> Right (a, xs, b)
--   App a b -> error "too many arguments"
--   a -> error $ intercalate "\n" ["infer Typ: missing type annotation", show a]
-- (defArgs, defAlts) <- case (eval [] a, eval [] b) of
--   (Typ tx' args', Union alts) | tx == tx' -> Right (args', alts)
--   (a, b) -> error "infer Typ: type mismatch"
-- -- error $ intercalate "\n" ["-- infer Typ => Ann", show args, show defArgs, show defAlts]
-- Right (Union defAlts, [])
infer env (Union alts) = do
  -- (_, s) <- inferAll env (map snd alts)
  -- Right (Knd, s)
  Right (Knd, [])
infer env (Lam p a) = case p of
  Int i -> do
    (t2, s) <- infer env a
    Right (Fun IntT t2, s)
  Var x -> do
    let xT = newName (x ++ "T") (map fst env)
    let env' = (x, Ann (Var x) (For [xT] (Var xT))) : env
    ((t2, t1), s) <- infer2 env' a (Var x)
    Right (Fun t1 t2, s)
-- infer env (Lam (Ctr tx k ps) a) = do
--   -- (typeWithArgs, s1) <- infer env (lam ps a)
--   -- let (argTypes, returnType) = asFun typeWithArgs
--   -- let (ctrArgTypes, returnTypeArgs) = splitAt (length ps) argTypes
--   -- (vars, alts) <- findUnionType env tx
--   -- case lookup k alts of
--   --   Just altType -> do
--   --     -- subtype (Ctr tx k args) (Typ tx' targs alts) | tx == tx' = case lookup k alts of
--   --     --   Just altType -> do
--   --     --     let (altArgs, altReturn) = asFun altType
--   --     --     let (typeName, typeArgs) = asApp altReturn
--   --     --     -- TODO: check typeName
--   --     --     (_, s1) <- subtypeAll args altArgs
--   --     --     (typArgs, s2) <- subtypeAll (map (apply s1) typeArgs) (map snd targs)
--   --     --     Right (Typ tx (zip (map fst targs) typArgs) alts, s2 `compose` s1)
--   --     --   Nothing -> Left (CtrNotInType k alts)
--   --     let (altArgs, altReturn) = asFun altType
--   --     let (typeName, typeArgs) = asApp altReturn
--   --     -- TODO: check typeName
--   --     (ctrArgTypes, s2) <- subtypeAll ctrArgTypes (fst (asFun altType))
--   --     (typeArgs, s3) <- subtypeAll (map (apply s2) typeArgs) (map snd vars)
--   --     -- let t1 = Ctr tx k ctrArgTypes
--   --     let t1 = Typ tx (zip (map fst vars) typeArgs) alts
--   --     let t2 = fun returnTypeArgs returnType
--   --     Right (eval env (Fun t1 (apply s2 t2)), s2 `compose` s1)
--   --   Nothing -> Left (CtrNotInType k alts)
--   error "TODO: infer Lam Ctr"
infer env (Fun a b) = do
  (_, s) <- infer2 env a b
  Right (Knd, s)
infer env (App a b) = do
  let returnType :: Type -> Type -> Either TypeError (Type, Substitution)
      returnType (Fun t1 t2) tb = do
        -- TODO: The return types in Typ's alts are not being evaluated.
        -- error $ intercalate "\n" [show t1, show tb]
        (_, s) <- subtype t1 tb
        Right (apply s t2, s)
      returnType (Or t1 t2) tb = do
        (t1, s1) <- returnType t1 tb
        (t2, s2) <- returnType (apply s1 t2) (apply s1 tb)
        (t, s3) <- unify (apply s2 t1) t2
        Right (t, s3 `compose` s2 `compose` s1)
      returnType t _ = Left (NotAFunction t)
  ((ta, tb), s1) <- infer2 env a b
  (t, s2) <- returnType ta tb
  Right (eval env t, s2 `compose` s1)
infer env (Ann (Typ tx args) (For xs b)) = Right (eval (pushVars xs env) b, [])
infer env (Ann (Lam (Var x) a) (For xs (Fun t1 t2))) = do
  (t2, s) <- infer ((x, Ann (Var x) (For [] t1)) : env) (Ann a (For [] t2))
  Right (Fun t1 t2, s)
infer env (Ann a (For xs b)) = do
  (ta, s1) <- infer env a
  let env' = applyEnv s1 env
  (t, s2) <- subtype ta (eval (pushVars xs env') b)
  Right (t, s2 `compose` s1)
infer env (Let defs a) = infer (env ++ defs) a
infer env (Fix x a) = do
  let x1 = newName (x ++ "T1") (map fst env)
  let x2 = newName (x ++ "T2") (x1 : map fst env)
  let env' = (x, Ann (Var x) (For [x1, x2] (Fun (Var x1) (Var x2)))) : env
  infer env' a
infer env (Or a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case subtype (eval env tb) (eval env ta) of
    Right (t, s2) -> Right (t, s2 `compose` s1)
    Left _ -> case subtype ta tb of
      Right (t, s2) -> Right (t, s2 `compose` s1)
      Left _ -> Right (Or ta tb, s1)
infer env (Call f args) = case lookup f env of
  Just (Ann a typ) -> inferApply env (f, typ) args
  Just a -> Left (MissingType f a)
  Nothing -> Left (UndefinedVar f)
infer env (Op2 op a b) = do
  ((ta, tb), s1) <- infer2 env a b
  (t, s2) <- unify ta tb
  Right (t, s2 `compose` s1)

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Type, Type), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (applyEnv s1 env) b
  Right ((apply s2 ta, tb), s2 `compose` s1)

inferAll :: Env -> [Expr] -> Either TypeError ([Type], Env)
inferAll _ [] = Right ([], [])
inferAll env (a : bs) = do
  (t, s1) <- infer env a
  (ts, s2) <- inferAll (applyEnv s1 env) bs
  Right (apply s2 t : ts, s2 `compose` s1)

inferApply :: Env -> (String, TypeScheme) -> [Expr] -> Either TypeError (Type, Env)
inferApply env (x, typ) args = do
  let env' = (x, Ann (Var x) typ) : env
  infer env' (app (Var x) args)

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names

newNames :: [String] -> [String] -> [String]
newNames [] _ = []
newNames (x : xs) existing = do
  let y = newName x existing
  y : newNames xs (y : existing)
