{-# LANGUAGE InstanceSigs #-}

module Core where

import Data.Bifunctor (Bifunctor (first, second))
import Data.Char (isLetter)
import Data.Foldable (Foldable (foldl'), foldlM)
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
  = Typ
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Var !String
  | Lam !String !Expr
  | For !String !Expr
  | Fun !Expr !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Let !Env !Expr
  | Fix !String !Expr
  | Ctr !String ![Expr]
  | Case !Expr ![(String, Expr)] !Expr
  | CaseI !Expr ![(Int, Expr)] !Expr
  | Or !Expr !Expr
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
showPrec _ Typ = "@Type"
showPrec _ IntT = "@Int"
showPrec _ (Int i) = show i
showPrec _ NumT = "@Num"
showPrec _ (Num n) = show n
-- TODO: do actual check that it's a valid identifier
showPrec _ (Var "") = "_"
showPrec _ (Var x@('_' : _)) = x
showPrec _ (Var x@(ch : _)) | isLetter ch = x
showPrec _ (Var x) = "${" ++ x ++ "}"
showPrec p (Lam x a) = do
  let (xs, a') = asLam (Lam x a)
  let ys = map (show . Var) xs
  showPrefix p 2 ("\\" ++ unwords ys ++ " -> ") a'
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
showPrec _ (Case a brs c) = do
  let showBr (k, b) = k ++ " => " ++ show b
  let cases = map showBr brs ++ [showBr ("_", c)]
  "@LamC " ++ show a ++ " {" ++ intercalate " | " cases ++ "}"
showPrec _ (CaseI a brs c) = do
  let showBr (i, b) = show i ++ " => " ++ show b
  let cases = map showBr brs ++ [showBr ("_", c)]
  "@LamI " ++ show a ++ " {" ++ intercalate " | " cases ++ "}"
showPrec p (Or a b) = showInfixR p 1 a " | " b
showPrec p (Op op args) = showPrec p (app (Var ("@op[" ++ op ++ "]")) args)

instance Show Expr where
  show :: Expr -> String
  show a = showPrec 0 a

type Type = Expr

type Operator = [Expr] -> Maybe Expr

type Ops = [(String, Operator)]

type Env = [(String, Expr)]

data Symbol
  = Value !Expr
  | UnionType ![(String, Type)] ![String]
  | UnionAlt ![(String, Type)] !(String, [Expr])
  deriving (Eq, Show)

type Context = [(String, Symbol)]

data Pattern
  = VarP !String
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
  | NotAUnionAlt !String !Symbol
  | NotAUnionType !String !Symbol
  | NotAnOp !String !Symbol
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

pushVars :: [String] -> Context -> Context
pushVars xs ctx = foldr (\x -> (:) (x, Value $ Var x)) ctx xs

popVars :: [String] -> Context -> Context
popVars xs ctx = foldl' (flip pop) ctx xs

freeVars :: Expr -> [String]
freeVars Typ = []
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
freeVars (Case a brs c) = foldr (union . freeVars . snd) (freeVars a `union` freeVars c) brs
freeVars (CaseI a brs c) = foldr (union . freeVars . snd) (freeVars a `union` freeVars c) brs
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (Op _ args) = foldr (union . freeVars) [] args

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

reduce :: Ops -> Env -> Expr -> Expr
reduce _ _ Typ = Typ
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
reduce _ env (Or a b) = Or (Let env a) (Let env b)
reduce ops env (Op op args) = do
  case (lookup op ops, eval ops env <$> args) of
    (Just f, args) -> case f args of
      Just a -> reduce ops env a
      Nothing -> Op op args
    (Nothing, args) -> Op op args

eval :: Ops -> Env -> Expr -> Expr
eval ops env term = case reduce ops env term of
  Typ -> Typ
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
  CaseI a brs c -> CaseI (eval ops [] a) (second (eval ops []) <$> brs) (eval ops [] c)
  Case a brs c -> Case (eval ops [] a) (second (eval ops []) <$> brs) (eval ops [] c)
  Or a b -> case (eval ops [] a, eval ops [] b) of
    (a, b) | a == b -> a
    (a, b) -> Or a b
  Op op args -> Op op (eval ops [] <$> args)

envOf :: Context -> Env
envOf [] = []
envOf ((x, Value a) : ctx) = (x, a) : envOf ctx
envOf ((x, UnionType args _) : ctx) = do
  let xs = map fst args
  (x, lam xs $ Ctr x (map Var xs)) : envOf ctx
envOf ((x, UnionAlt args _) : ctx) = do
  let xs = map fst args
  (x, lam xs $ Ctr x (map Var xs)) : envOf ctx

subtype :: Ops -> Context -> Type -> Type -> Either TypeError (Type, Context)
subtype _ ctx Typ Typ = Right (Typ, ctx)
subtype _ ctx IntT IntT = Right (IntT, ctx)
subtype _ ctx NumT NumT = Right (NumT, ctx)
subtype _ ctx (Int i) (Int i') | i == i' = Right (Int i, ctx)
subtype _ ctx (Num n) (Num n') | n == n' = Right (Num n, ctx)
subtype _ ctx (Var x) (Var x') | x == x' = Right (Var x, ctx)
subtype _ _ (Var x) b | x `occurs` b = Left (InfiniteType x b)
subtype ops ctx (Var x) b = do
  let b' = eval ops (envOf ctx) b
  Right (b', set x (Value b') ctx)
subtype ops ctx a (Var y) = subtype ops ctx (Var y) a
subtype ops ctx a (For x b) = do
  let y = newName x (map fst ctx)
  (a, ctx) <- subtype ops ((y, Value (Var y)) : ctx) a (eval ops [(x, Var y)] b)
  Right (for [y] a, pop y ctx)
subtype ops ctx (For x a) b = do
  let y = newName x (map fst ctx)
  (a, ctx) <- subtype ops ((y, Value (Var y)) : ctx) (eval ops [(x, Var y)] a) b
  Right (for [y] a, pop y ctx)
subtype ops ctx (Fun a1 b1) (Fun a2 b2) = do
  (a, ctx) <- subtype ops ctx a1 a2
  (b, ctx) <- subtype ops ctx (eval ops (envOf ctx) b1) (eval ops (envOf ctx) b2)
  Right (Fun (eval ops (envOf ctx) a) b, ctx)
subtype ops ctx (App a1 b1) (App a2 b2) = do
  (a, ctx) <- subtype ops ctx a1 a2
  (b, ctx) <- subtype ops ctx (eval ops (envOf ctx) b1) (eval ops (envOf ctx) b2)
  Right (App (eval ops (envOf ctx) a) b, ctx)
subtype ops ctx (Ctr name args) (Ctr name' args') | name == name' && length args == length args' = do
  (argsT, ctx) <- subtypeAll ops ctx args args'
  Right (Ctr name argsT, ctx)
subtype ops ctx a (Or b1 b2) = case subtype ops ctx a b1 of
  Right (a, ctx) -> case subtype ops ctx a b2 of
    Right (b, ctx) -> Right (eval ops (envOf ctx) (Or a b), ctx)
    Left _ -> Right (a, ctx)
  Left _ -> subtype ops ctx a b2
subtype ops ctx (Or a1 a2) b = do
  (a1, ctx) <- subtype ops ctx a1 b
  (a2, ctx) <- subtype ops ctx a2 b
  Right (eval ops (envOf ctx) (Or a1 a2), ctx)
subtype ops ctx (Op op args) (Op op' args') | op == op' && length args == length args' = do
  (args, ctx) <- subtypeAll ops ctx args args'
  Right (Op op args, ctx)
subtype _ _ a b = Left (TypeMismatch a b)

subtypeAll :: Ops -> Context -> [Expr] -> [Expr] -> Either TypeError ([Expr], Context)
subtypeAll _ ctx [] _ = Right ([], ctx)
subtypeAll _ ctx _ [] = Right ([], ctx)
subtypeAll ops ctx (a1 : bs1) (a2 : bs2) = do
  (a, ctx) <- subtype ops ctx a1 a2
  (bs, ctx) <- subtypeAll ops ctx (eval ops (envOf ctx) <$> bs1) (eval ops (envOf ctx) <$> bs2)
  Right (eval ops (envOf ctx) a : bs, ctx)

findUnionType :: Context -> String -> Either TypeError ([(String, Type)], [String])
findUnionType ctx tname = case lookup tname ctx of
  Just (UnionType args ctrs) -> Right (args, ctrs)
  Just sym -> Left (NotAUnionType tname sym)
  Nothing -> Left (UndefinedType tname)

findUnionAlt :: Context -> String -> Either TypeError ([(String, Type)], (String, [Expr]))
findUnionAlt ctx k = case lookup k ctx of
  Just (UnionAlt args ret) -> Right (args, ret)
  Just sym -> Left (NotAUnionAlt k sym)
  Nothing -> Left (UndefinedType k)

infer :: Ops -> Context -> Expr -> Either TypeError (Type, Context)
infer _ ctx Typ = Right (Typ, ctx)
infer _ ctx IntT = Right (Typ, ctx)
infer _ ctx (Int _) = Right (IntT, ctx)
infer _ ctx NumT = Right (Typ, ctx)
infer _ ctx (Num _) = Right (NumT, ctx)
infer ops ctx (Var x) = case lookup x ctx of
  Just (Value (Var x')) | x == x' -> Right (Typ, ctx)
  Just (Value (Ann (Var x') t)) | x == x' -> Right (eval ops (envOf ctx) t, ctx)
  Just (Value a) -> infer ops ctx a
  Just (UnionType args ctrs) -> do
    let t = fun (map snd args) Typ
    Right (eval ops (envOf ctx) t, ctx)
  Just (UnionAlt args (tname, retArgs)) -> do
    (targs, ctrs) <- findUnionType ctx tname
    let t = fun (map snd args) (Ctr tname retArgs)
    Right (for (map fst targs) $ eval ops (envOf ctx) t, ctx)
  Nothing -> Left (UndefinedVar x)
infer ops ctx (Lam x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  ctx <- Right ((xT, Value (Var xT)) : (x, Value (Ann (Var x) (Var xT))) : ctx)
  (t2, ctx) <- infer ops ctx a
  (t1, ctx) <- infer ops ctx (Var x)
  Right (for [xT] $ Fun t1 t2, pop x ctx)
infer ops ctx (For x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  ctx <- Right ((xT, Value $ Var xT) : (x, Value $ Ann (Var x) (Var xT)) : ctx)
  (aT, ctx) <- infer ops ctx a
  Right (for [xT] aT, pop x ctx)
infer ops ctx (Fun a b) = do
  (_, ctx) <- infer ops ctx (Ann a Typ)
  (_, ctx) <- infer ops ctx (Ann b Typ)
  Right (Typ, ctx)
infer ops ctx (App a b) = do
  (ta, ctx) <- infer ops ctx a
  (tb, ctx) <- infer ops ctx b
  let x = newName "t" (map fst ctx)
  ctx <- Right ((x, Value $ Var x) : ctx)
  (t, ctx) <- subtype ops ctx (Fun tb (Var x)) ta
  case asFor t of
    (xs, Fun _ t) -> Right (for xs t, pop x ctx)
    _else -> error "unreachable"
infer ops ctx (Ann a t) = do
  (ta, ctx) <- infer ops ctx a
  subtype ops ctx ta (eval ops (envOf ctx) t)
infer ops ctx (Let defs a) = infer ops (ctx ++ map (second Value) defs) a
infer ops ctx (Fix x a) = do
  let xT = newName (x ++ "T") (map fst ctx)
  ctx <- Right ((xT, Value $ Var xT) : (x, Value $ Ann (Var x) (Var xT)) : ctx)
  (ta, ctx) <- infer ops ctx a
  Right (ta, pop x ctx)
infer ops ctx (Ctr k args) = do
  (t, ctx) <- infer ops ctx (Var k)
  inferApply ops ctx (k, t) args
infer _ _ (Case _ [] _) = Left EmptyCase
infer ops ctx (Case a brs@((k, _) : _) c) = do
  (_, (tname, _)) <- findUnionAlt ctx k
  (targs, ctrs) <- findUnionType ctx tname
  let xs = map fst targs
  alts <- mapM (altBranchType ops ctx xs) ctrs
  ctx <- Right (pushVars xs ctx)
  (_, ctx) <- infer ops ctx (Ann a (Ctr tname (map Var xs)))
  ctx <- Right (pushVars (tname : ctrs) ctx)
  (t, ctx) <- inferBranches ops ctx alts brs
  (tc, ctx) <- infer ops ctx c
  (t, ctx) <- subtype ops ctx t tc
  ctx <- Right (popVars (tname : ctrs) ctx)
  ctx <- Right (popVars xs ctx)
  Right (t, ctx)
infer ops ctx (CaseI a brs c) = do
  (_, ctx) <- infer ops ctx (Ann a IntT)
  (ts, ctx) <- inferMany ops ctx (map snd brs)
  (t, ctx) <- infer ops ctx c
  (t, ctx) <- foldlM (\(t, ctx) t' -> subtype ops ctx t t') (t, ctx) ts
  Right (t, ctx)
infer ops ctx (Or a b) = do
  (ta, ctx) <- infer ops ctx a
  (tb, ctx) <- infer ops ctx b
  case subtype ops ctx ta tb of
    Right (t, ctx) -> Right (t, ctx)
    Left _ -> Right (eval ops (envOf ctx) (Or ta tb), ctx)
infer ops ctx (Op op args) = case lookup op ctx of
  Just (Value (Ann a t)) -> inferApply ops ctx (op, t) args
  Just (Value a) -> Left (MissingType op a)
  Just sym -> Left (NotAnOp op sym)
  Nothing -> Left (UndefinedVar op)

inferMany :: Ops -> Context -> [Expr] -> Either TypeError ([Type], Context)
inferMany _ ctx [] = Right ([], ctx)
inferMany ops ctx (a : bs) = do
  (t, ctx) <- infer ops ctx a
  (ts, ctx) <- inferMany ops ctx bs
  Right (t : ts, ctx)

asBranchType :: [String] -> Type -> Type -> Type
asBranchType xs (For x a) c = for [x] (asBranchType xs a c)
asBranchType xs (Fun a b) c = Fun a (asBranchType xs b c)
asBranchType _ _ c = c

altBranchType :: Ops -> Context -> [String] -> String -> Either TypeError (String, Type)
altBranchType ops ctx xs k = do
  (args, (tname, targs)) <- findUnionAlt ctx k
  let t = fun (map snd args) (Ctr tname targs)
  Right (k, asBranchType xs t (Var k))

inferBranches :: Ops -> Context -> [(String, Type)] -> [(String, Expr)] -> Either TypeError (Type, Context)
inferBranches _ _ _ [] = Left EmptyCase
inferBranches ops ctx alts [br] = inferBranch ops ctx alts br
inferBranches ops ctx alts (br : brs) = do
  (t1, ctx) <- inferBranch ops ctx alts br
  (t2, ctx) <- inferBranches ops ctx alts brs
  subtype ops ctx t1 t2

inferBranch :: Ops -> Context -> [(String, Type)] -> (String, Expr) -> Either TypeError (Type, Context)
inferBranch ops ctx alts (k, a) = case lookup k alts of
  Just t -> do
    (_, ctx) <- infer ops ctx (Ann a t)
    Right (eval ops (envOf ctx) $ Var k, ctx)
  Nothing -> Left (CtrNotInType k alts)

inferApply :: Ops -> Context -> (String, Type) -> [Expr] -> Either TypeError (Type, Context)
inferApply ops ctx (x, t) args = do
  ctx <- Right ((x, Value $ Ann (Var x) t) : ctx)
  (t, ctx) <- infer ops ctx (app (Var x) args)
  Right (t, pop x ctx)

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
  matchStep x (Br (VarP x : ps) (Let [(y, Var x)] b) : brs)
matchStep x (br : brs) = do
  step <- matchStep x brs
  matchNext br step

matchNext :: Branch -> MatchStep -> Either TypeError MatchStep
matchNext (Br [] b) _ = Right (MatchEnd b)
matchNext _ (MatchEnd _) = Left MatchNumPatternsMismatch
matchNext (Br (VarP _ : ps) b) (MatchAny brs) = do
  Right (MatchAny (Br ps b : brs))
matchNext (Br (VarP _ : ps) b) (MatchInt cases brs) = do
  let matchCase (i, brs) = (i, Br ps b : brs)
  Right (MatchInt (map matchCase cases) (Br ps b : brs))
matchNext (Br (VarP _ : ps) b) (MatchCtr cases brs) = do
  let matchCase (k, (n, brs)) = (k, (n, Br (replicate n (VarP "") ++ ps) b : brs))
  Right (MatchCtr (map matchCase cases) (Br ps b : brs))
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

typedExpr :: Ops -> Context -> Expr -> Either TypeError Expr
typedExpr ops ctx expr = case expr of
  Typ -> Right Typ
  IntT -> Right IntT
  NumT -> Right NumT
  Int i -> Right (Int i)
  Num n -> Right (Num n)
  Var x -> Right (Var x)
  Lam x a -> do
    a <- typed a
    Right (lam ["", x] a)
  For x a -> do
    a <- typed a
    Right (For x a)
  Fun a b -> do
    a <- typed a
    b <- typed b
    Right (fun [Typ, a] b)
  App a b -> do
    a <- typed a
    (tb, _) <- infer ops ctx b
    b <- typed b
    Right (app a [tb, b])
  Ann a b -> do
    a <- typed a
    b <- typed b
    Right (Ann a b)
  Let env a -> do
    env <- mapM typedSecond env
    a <- typed a
    Right (Let env a)
  Fix x a -> do
    a <- typed a
    Right (Fix x a)
  Ctr k args -> do
    args <- mapM typed args
    Right (Ctr k args)
  Case a cases c -> do
    a <- typed a
    cases <- mapM typedSecond cases
    c <- typed c
    Right (Case a cases c)
  CaseI a cases c -> do
    a <- typed a
    cases <- mapM typedSecond cases
    c <- typed c
    Right (CaseI a cases c)
  Op op args -> do
    args <- mapM typed args
    Right (Op op args)
  where
    typed = typedExpr ops ctx
    typedSecond (x, b) = do
      b <- typed b
      Right (x, b)
    toPattern env a = case eval ops env a of
      Typ -> error "TODO" --TypP
      IntT -> error "TODO" --IntTP
      NumT -> error "TODO" --NumTP
      Int i -> IntP i
      Num n -> error "TODO"
      Var x -> VarP x
      Lam x a -> VarP ""
      For x a -> toPattern ((x, Var x) : env) a
      Fun a b -> error "TODO"
      App a b -> error "TODO"
      Ann a b -> error "unreachable"
      Let env a -> error "TODO"
      Fix x a -> error "TODO"
      Ctr k args -> error "TODO"
      Case a cases c -> error "TODO"
      CaseI a cases c -> error "TODO"
      Op op args -> error "TODO"
