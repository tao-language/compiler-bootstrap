{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable (Foldable (foldl'), foldlM)
import Data.List (delete, intercalate, union)

{- TODO:

- Make Case and CaseInt into LamC and LamI
- Move the Typ information into a Context used only on type inference
  * Only include information necessary for evaluation
  * Everything else should be part of the Context
- Rework Op to not have to include an Ops dictionary at runtime
- Add Records
- Clean up code
  * infer Case
- Consistency on variable names:
  * Expr: a, b, c
  * Type: t, t1, t2, ta, tb, tc
  * Var: x, y, z
- Show Expr with precedence
- Remove unused errors

-}

data Expr
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Var !String
  | Lam !String !Expr
  | CaseI !Expr ![(Int, Expr)] !Expr
  | Case !Expr ![(String, Expr)] !Expr
  | For !String !Expr
  | Fun !Expr !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Let !Env !Expr
  | Fix !String !Expr
  | Ctr !String ![Expr]
  | Typ !String ![(String, Expr)] ![String]
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
showPrec _ Knd = "@Type"
showPrec _ IntT = "@Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "@Num"
showPrec _ (Num n) = show n
showPrec _ (Var x) = x
showPrec p (Lam x a) = do
  let (xs, a') = asLam (Lam x a)
  showPrefix p 2 ("\\" ++ unwords xs ++ " -> ") a'
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
showPrec p (Ctr name args) = "#" ++ showPrec p (app (Var name) args)
showPrec p (Typ name args ctrs) = do
  -- let x = name ++ "[" ++ unwords (map fst args) ++ "]{" ++ intercalate "|" ctrs ++ "}"
  let x = name
  "%" ++ showPrec p (app (Var x) (map snd args))
showPrec _ (Case a brs c) = do
  let showBr (k, b) = k ++ " => " ++ show b
  let cases = map showBr brs ++ [showBr ("_", c)]
  "@LamC " ++ show a ++ " {" ++ intercalate " | " cases ++ "}"
showPrec _ (CaseI a brs c) = do
  let showBr (i, b) = show i ++ " => " ++ show b
  let cases = map showBr brs ++ [showBr ("_", c)]
  "@LamI " ++ show a ++ " {" ++ intercalate " | " cases ++ "}"
showPrec p (Op op args) = showPrec p (app (Var ("@op[" ++ op ++ "]")) args)

instance Show Expr where
  show :: Expr -> String
  show a = showPrec 0 a

type Type = Expr

type Operator = [Expr] -> Maybe Expr

type Ops = [(String, Operator)]

type Env = [(String, Expr)]

data Pattern
  = AnyP
  | VarP !String
  | IntP !Int
  | CtrP !String ![Pattern]
  deriving (Eq, Show)

data Branch
  = Br ![Pattern] !Expr
  deriving (Eq, Show)

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
  | NotAUnionType !Expr
  | TooManyArgs !Expr ![Expr]
  | TypeMismatch !Expr !Expr
  | UndefinedCtr !String
  | UndefinedOp !String
  | UndefinedType !String
  | UndefinedUnionAlt !String
  | UndefinedUnionType !String
  | UndefinedVar !String
  deriving (Eq, Show)

lam :: [String] -> Expr -> Expr
lam xs a = foldr Lam a xs

asLam :: Expr -> ([String], Expr)
asLam (Lam x a) = first (x :) (asLam a)
asLam a = ([], a)

for :: [String] -> Expr -> Expr
for xs a = foldr (\x a -> if x `occurs` a then For x a else a) a xs

asFor :: Expr -> ([String], Expr)
asFor (For x a) = first (x :) (asFor a)
asFor a = ([], a)

fun :: [Type] -> Type -> Type
fun bs ret = foldr Fun ret bs

asFun :: Expr -> ([Expr], Expr)
asFun (Fun a b) = first (a :) (asFun b)
asFun a = ([], a)

app :: Expr -> [Expr] -> Expr
app = foldl' App

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

pushVars :: [String] -> Env -> Env
pushVars xs env = foldr (\x -> (:) (x, Var x)) env xs

popVars :: [String] -> Env -> Env
popVars xs env = foldl' (flip pop) env xs

freeVars :: Expr -> [String]
freeVars Knd = []
freeVars IntT = []
freeVars NumT = []
freeVars (Int _) = []
freeVars (Num _) = []
freeVars (Var x) = [x]
freeVars (Lam x a) = delete x (freeVars a)
freeVars (For x a) = delete x (freeVars a)
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a b) = freeVars a `union` freeVars b
freeVars (Let env a) =
  filter (`notElem` map fst env) (foldr (union . freeVars . snd) (freeVars a) env)
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Ctr _ args) = foldr (union . freeVars) [] args
freeVars (Typ _ args _) = foldr (union . freeVars . snd) [] args
freeVars (Case a brs c) = foldr (union . freeVars . snd) (freeVars a `union` freeVars c) brs
freeVars (CaseI a brs c) = foldr (union . freeVars . snd) (freeVars a `union` freeVars c) brs
freeVars (Op _ args) = foldr (union . freeVars) [] args

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

reduce :: Ops -> Env -> Expr -> Expr
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
reduce _ env (Lam x a) = Lam x (Let env a)
reduce _ env (For x a) = For x (Let env a)
reduce _ env (Fun a b) = Fun (Let env a) (Let env b)
reduce ops env (App a b) = case reduce ops env a of
  Lam x a -> reduce ops [(x, Let env b)] a
  Fix _ a -> reduce ops [] (App a (Let env b))
  a -> App a (Let env b)
reduce ops env (Ann a _) = reduce ops env a
reduce ops env (Let env' a) = reduce ops (env ++ env') a
reduce _ env (Fix x a) = Fix x (Let env a)
reduce _ env (Ctr name args) = Ctr name (Let env <$> args)
reduce _ env (Typ name args ctrs) = Typ name (second (Let env) <$> args) ctrs
reduce ops env (CaseI a cases c) = case reduce ops env a of
  Int i -> case lookup i cases of
    Just b -> reduce ops env b
    Nothing -> reduce ops env c
  a -> CaseI a (second (Let env) <$> cases) (Let env c)
reduce ops env (Case a cases c) = case reduce ops env a of
  Ctr k args -> case lookup k cases of
    Just b -> reduce ops env (app b args)
    Nothing -> reduce ops env c
  a -> Case a (second (Let env) <$> cases) (Let env c)
reduce ops env (Op op args) = do
  case (lookup op ops, eval ops env <$> args) of
    (Just f, args) -> case f args of
      Just a -> reduce ops env a
      Nothing -> Op op args
    (Nothing, args) -> Op op args

eval :: Ops -> Env -> Expr -> Expr
eval ops env term = case reduce ops env term of
  Knd -> Knd
  IntT -> IntT
  NumT -> NumT
  Int i -> Int i
  Num n -> Num n
  Var x -> Var x
  Lam x a -> Lam x (eval ops [(x, Var x)] a)
  For x a -> for [x] (eval ops [(x, Var x)] a)
  Fun a b -> Fun (eval ops [] a) (eval ops [] b)
  App a b -> App (eval ops [] a) (eval ops [] b)
  Ann _ _ -> error "unreachable"
  Let _ _ -> error "unreachable"
  Fix x a -> case eval ops [(x, Var x)] a of
    a | x `occurs` a -> Fix x a
    a -> a
  Ctr name args -> Ctr name (eval ops [] <$> args)
  Typ name args ctrs -> Typ name (second (eval ops []) <$> args) ctrs
  CaseI a brs c -> CaseI (eval ops [] a) (second (eval ops []) <$> brs) (eval ops [] c)
  Case a brs c -> Case (eval ops [] a) (second (eval ops []) <$> brs) (eval ops [] c)
  Op op args -> Op op (eval ops [] <$> args)

unify :: Ops -> Env -> Expr -> Expr -> Either TypeError (Expr, Env)
unify _ env Knd Knd = Right (Knd, env)
unify _ env IntT IntT = Right (IntT, env)
unify _ env (Int i) (Int i') | i == i' = Right (Int i, env)
unify _ env NumT NumT = Right (NumT, env)
unify _ env (Num n) (Num n') | n == n' = Right (Num n, env)
unify _ env (Var x) (Var x') | x == x' = Right (Var x, env)
unify _ _ (Var x) b | x `occurs` b = Left (InfiniteType x b)
unify ops env (Var x) b = do
  let b' = eval ops env b
  Right (b', set x b' env)
unify ops env a (Var y) = unify ops env (Var y) a
unify ops env a (For x b) = do
  let y = newName x (map fst env)
  (a, env) <- unify ops ((y, Var y) : env) a (eval ops [(x, Var y)] b)
  Right (for [y] a, pop y env)
unify ops env (For x a) b = do
  let y = newName x (map fst env)
  (a, env) <- unify ops ((y, Var y) : env) (eval ops [(x, Var y)] a) b
  Right (for [y] a, pop y env)
unify ops env (Fun a1 b1) (Fun a2 b2) = do
  (a, env) <- unify ops env a1 a2
  (b, env) <- unify ops env (eval ops env b1) (eval ops env b2)
  Right (Fun (eval ops env a) b, env)
unify ops env (App a1 b1) (App a2 b2) = do
  (a, env) <- unify ops env a1 a2
  (b, env) <- unify ops env (eval ops env b1) (eval ops env b2)
  Right (App (eval ops env a) b, env)
unify ops env (Typ name args ctrs) (Typ name' args' ctrs') | name == name' && map fst args == map fst args' && ctrs == ctrs' = do
  (argsT, env) <- unifyMany ops env (map snd args) (map snd args')
  Right (Typ name (zip (map fst args) argsT) ctrs, env)
unify ops env (Op op args) (Op op' args') | op == op' && length args == length args' = do
  (args, env) <- unifyMany ops env args args'
  Right (Op op args, env)
unify _ _ a b = Left (TypeMismatch a b)

unifyMany :: Ops -> Env -> [Expr] -> [Expr] -> Either TypeError ([Expr], Env)
unifyMany _ env [] _ = Right ([], env)
unifyMany _ env _ [] = Right ([], env)
unifyMany ops env (a1 : bs1) (a2 : bs2) = do
  (a, env) <- unify ops env a1 a2
  (bs, env) <- unifyMany ops env (eval ops env <$> bs1) (eval ops env <$> bs2)
  Right (eval ops env a : bs, env)

expandType :: Ops -> Env -> String -> [(String, Expr)] -> [(String, Type)] -> Type
expandType ops env name args alts = do
  let x = newName ("$" ++ name) (foldr (union . freeVars . snd) [] alts)
  let branch :: Type -> Type
      branch (Fun a b) = Fun (eval ops (args ++ env) a) (branch b)
      branch _ = Var x
  for (x : map fst args) (fun (branch . snd <$> alts) (Var x))

findTyped :: Ops -> Env -> String -> Either TypeError (Expr, Type)
findTyped ops env x = case lookup x env of
  Just (Ann a t) -> Right (a, eval ops env t)
  Just a -> Left (MissingType x a)
  Nothing -> Left (UndefinedVar x)

instantiate :: Ops -> Env -> Type -> ([String], Type, Env)
instantiate ops env (For x t) = do
  let y = newName x (map fst env)
  let (xs, t', env') = instantiate ops ((y, Var y) : env) (eval ops [(x, Var y)] t)
  (y : xs, t', env')
instantiate ops env t = ([], eval ops env t, env)

infer :: Ops -> Env -> Expr -> Either TypeError (Type, Env)
infer _ env Knd = Right (Knd, env)
infer _ env IntT = Right (Knd, env)
infer _ env (Int _) = Right (IntT, env)
infer _ env NumT = Right (Knd, env)
infer _ env (Num _) = Right (NumT, env)
infer ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Right (Knd, env)
  Just (Ann (Var x') t) | x == x' -> Right (eval ops env t, env)
  Just a -> infer ops env a
  Nothing -> Left (UndefinedVar x)
infer ops env (Lam x a) = do
  let xT = newName (x ++ "T") (map fst env)
  env <- Right ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env)
  (t2, env) <- infer ops env a
  (t1, env) <- infer ops env (Var x)
  Right (for [xT] $ Fun t1 t2, pop x env)
infer ops env (For x a) = do
  let xT = newName (x ++ "T") (map fst env)
  env <- Right ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env)
  (aT, env) <- infer ops env a
  Right (for [xT] aT, pop x env)
infer ops env (Fun a b) = do
  (_, env) <- infer ops env (Ann a Knd)
  (_, env) <- infer ops env (Ann b Knd)
  Right (Knd, env)
infer ops env (App a b) = do
  (ta, env) <- infer ops env a
  (tb, env) <- infer ops env b
  let x = newName "t" (map fst env)
  env <- Right ((x, Var x) : env)
  (t, env) <- unify ops env (Fun tb (Var x)) ta
  case asFor t of
    (xs, Fun _ t) -> Right (for xs t, pop x env)
    _else -> error "unreachable"
infer ops env (Ann a t) = do
  (ta, env) <- infer ops env a
  unify ops env ta (eval ops env t)
infer ops env (Let env' a) = infer ops (env ++ env') a
infer ops env (Fix x a) = do
  let xT = newName (x ++ "T") (map fst env)
  env <- Right ((xT, Var xT) : (x, Ann (Var x) (Var xT)) : env)
  (ta, env) <- infer ops env a
  Right (ta, pop x env)
infer ops env (Ctr k args) = do
  (_, t) <- findTyped ops env k
  inferApply ops env (k, t) args
infer ops env (Typ name args alts) = do
  (_, t) <- findTyped ops env name
  inferApply ops env (name, t) (map snd args)
infer ops env (Case a brs c) = do
  (tname, targs, ctrs) <- case map fst brs of
    k : _ -> findCtrType ops env k
    [] -> Left EmptyCase
  let xs = map fst targs
  alts <- mapM (altBranchType ops env xs) ctrs
  env <- Right (pushVars xs env)
  (_, env) <- infer ops env (Ann a (Typ tname targs ctrs))
  env <- Right (pushVars (tname : ctrs) env)
  (t, env) <- inferBranches ops env alts brs
  (tc, env) <- infer ops env c
  (t, env) <- unify ops env t tc
  env <- Right (popVars (tname : ctrs) env)
  env <- Right (popVars xs env)
  Right (t, env)
infer ops env (CaseI a brs c) = do
  (_, env) <- infer ops env (Ann a IntT)
  (ts, env) <- inferMany ops env (map snd brs)
  (t, env) <- infer ops env c
  (t, env) <- foldlM (\(t, env) t' -> unify ops env t t') (t, env) ts
  Right (t, env)
infer ops env (Op op args) = do
  (_, t) <- findTyped ops env op
  inferApply ops env (op, t) args

inferMany :: Ops -> Env -> [Expr] -> Either TypeError ([Type], Env)
inferMany _ env [] = Right ([], env)
inferMany ops env (a : bs) = do
  (t, env) <- infer ops env a
  (ts, env) <- inferMany ops env bs
  Right (t : ts, env)

asTypeDef :: Expr -> Either TypeError (String, [(String, Expr)], [String])
asTypeDef (Ann a _) = asTypeDef a
asTypeDef (Lam _ a) = asTypeDef a
asTypeDef (Typ name args ctrs) = Right (name, args, ctrs)
asTypeDef a = Left (NotAUnionType a)

splitFun :: Type -> ([String], [Type], Type)
splitFun (For x a) = let (xs, args, ret) = splitFun a in (x : xs, args, ret)
splitFun (Fun a b) = let (xs, args, ret) = splitFun b in (xs, a : args, ret)
splitFun a = ([], [], a)

findCtrType :: Ops -> Env -> String -> Either TypeError (String, [(String, Expr)], [String])
findCtrType ops env k = do
  (_, ctrT) <- findTyped ops env k
  case splitFun ctrT of
    (_, _, Typ tname _ _) -> case lookup tname env of
      Just b -> asTypeDef b
      Nothing -> Left (UndefinedType tname)
    (_, _, a) -> Left (NotAUnionType a)

asBranchType :: [String] -> Type -> Type -> Type
asBranchType xs (For x a) c | x `elem` xs = asBranchType xs a c
asBranchType xs (For x a) c = For x (asBranchType xs a c)
asBranchType xs (Fun a b) c = Fun a (asBranchType xs b c)
asBranchType _ _ c = c

altBranchType :: Ops -> Env -> [String] -> String -> Either TypeError (String, Type)
altBranchType ops env xs k = do
  (_, ctrT) <- findTyped ops env k
  Right (k, asBranchType xs ctrT (Var k))

inferBranches :: Ops -> Env -> [(String, Type)] -> [(String, Expr)] -> Either TypeError (Type, Env)
inferBranches _ _ _ [] = Left EmptyCase
inferBranches ops env alts [br] = inferBranch ops env alts br
inferBranches ops env alts (br : brs) = do
  (t1, env) <- inferBranch ops env alts br
  (t2, env) <- inferBranches ops env alts brs
  unify ops env t1 t2

inferBranch :: Ops -> Env -> [(String, Type)] -> (String, Expr) -> Either TypeError (Type, Env)
inferBranch ops env alts (k, a) = case lookup k alts of
  Just t -> do
    (_, env) <- infer ops env (Ann a t)
    Right (eval ops env (Var k), env)
  Nothing -> Left (CtrNotInType k alts)

inferApply :: Ops -> Env -> (String, Type) -> [Expr] -> Either TypeError (Type, Env)
inferApply ops env (x, t) args = do
  env <- Right ((x, Ann (Var x) t) : env)
  (t, env) <- infer ops env (app (Var x) args)
  Right (t, pop x env)

newName :: String -> [String] -> String
newName x existing = do
  let names = x : map ((x ++) . show) [(1 :: Int) ..]
  head $ filter (`notElem` existing) names

-- Pattern matching
match :: [Branch] -> Either TypeError Expr
match brs = do
  let x = newName (matchFirstName brs) (matchFreeVars brs)
  step <- matchStep x brs
  case step of
    MatchEnd b -> Right b
    MatchAny [] -> Left EmptyCase
    MatchAny brs -> do
      b <- match brs
      Right (Lam x b)
    MatchInt cases brs -> do
      let matchCase (i, brs) = do
            b <- match brs
            Right (i, b)
      cases <- mapM matchCase cases
      b <- match brs
      Right (Lam x (CaseI (Var x) cases b))
    MatchCtr cases brs -> do
      let matchCase (k, (_, brs)) = do
            b <- match brs
            Right (k, b)
      cases <- mapM matchCase cases
      b <- match brs
      Right (Lam x (Case (Var x) cases b))

matchFreeVars :: [Branch] -> [String]
matchFreeVars [] = []
matchFreeVars (Br [] a : brs) = freeVars a `union` matchFreeVars brs
matchFreeVars (Br (AnyP : ps) a : brs) = matchFreeVars (Br ps a : brs)
matchFreeVars (Br (VarP x : ps) a : brs) = matchFreeVars (Br ps (Lam x a) : brs)
matchFreeVars (Br (IntP _ : ps) a : brs) = matchFreeVars (Br ps a : brs)
matchFreeVars (Br (CtrP _ qs : ps) a : brs) = matchFreeVars (Br (qs ++ ps) a : brs)

matchFirstName :: [Branch] -> String
matchFirstName [] = "_"
matchFirstName (Br (VarP x : _) _ : _) = x
matchFirstName (Br _ _ : brs) = matchFirstName brs

matchStep :: String -> [Branch] -> Either TypeError MatchStep
matchStep _ [] = Right (MatchAny [])
matchStep x (Br (VarP y : ps) b : brs) | x /= y = do
  matchStep x (Br (AnyP : ps) (Let [(y, Var x)] b) : brs)
matchStep x (br : brs) = do
  step <- matchStep x brs
  matchNext br step

matchNext :: Branch -> MatchStep -> Either TypeError MatchStep
matchNext (Br [] b) _ = Right (MatchEnd b)
matchNext _ (MatchEnd _) = Left MatchNumPatternsMismatch
matchNext (Br (AnyP : ps) b) (MatchAny brs) = do
  Right (MatchAny (Br ps b : brs))
matchNext (Br (AnyP : ps) b) (MatchInt cases brs) = do
  let matchCase (i, brs) = (i, Br ps b : brs)
  Right (MatchInt (map matchCase cases) (Br ps b : brs))
matchNext (Br (AnyP : ps) b) (MatchCtr cases brs) = do
  let matchCase (k, (n, brs)) = (k, (n, Br (replicate n AnyP ++ ps) b : brs))
  Right (MatchCtr (map matchCase cases) (Br ps b : brs))
matchNext (Br (VarP _ : ps) b) step = matchNext (Br (AnyP : ps) b) step
matchNext (Br (IntP i : ps) b) (MatchAny brs) = do
  matchNext (Br (IntP i : ps) b) (MatchInt [] brs)
matchNext (Br (IntP i : ps) b) (MatchInt cases brs) = case lookup i cases of
  Just brsI -> Right (MatchInt (set i (Br ps b : brsI) cases) brs)
  Nothing -> Right (MatchInt ((i, [Br ps b]) : cases) brs)
matchNext (Br (IntP _ : _) _) (MatchCtr _ _) = Left MatchMixIntCtrPatterns
matchNext (Br (CtrP k qs : ps) b) (MatchAny brs) = do
  matchNext (Br (CtrP k qs : ps) b) (MatchCtr [] brs)
matchNext (Br (CtrP _ _ : _) _) (MatchInt _ _) = Left MatchMixIntCtrPatterns
matchNext (Br (CtrP k qs : ps) b) (MatchCtr cases brs) = case lookup k cases of
  Just (n, _) | length qs /= n -> Left (MatchCtrArgsMismatch n qs)
  Just (n, brsK) -> Right (MatchCtr (set k (n, Br (qs ++ ps) b : brsK) cases) brs)
  Nothing -> Right (MatchCtr ((k, (length qs, [Br (qs ++ ps) b])) : cases) brs)
