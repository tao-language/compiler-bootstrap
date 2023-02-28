module Core where

import Data.Bifunctor (Bifunctor (second))
import Data.List (foldl', union)

{- TODO:
* Function / operator overloading
* Do notation
  - Overload (<-) operator
-}

data Expr
  = Nil
  | Int !Int
  | Num !Double
  | Var !String
  | Let !Env !Expr
  | Ctr !Alt ![Expr]
  | Lam !String !Expr
  | Case !Alt ![String] !Expr
  | App !Expr !Expr
  | And !Expr !Expr
  | Or !Expr !Expr
  | Fst !Expr
  | Snd !Expr
  | Fix !String !Expr
  | Op !String !Expr
  | Err !RuntimeError
  deriving (Eq, Show)

data Type
  = NilT
  | IntT
  | NumT
  | VarT !String
  | CtrT !Alt ![Type]
  | FunT !Type !Type
  | AndT !Type !Type
  | OrT !Type !Type
  deriving (Eq, Show)

data CtrArg
  = T !Type
  | E !Expr

data BinaryOp
  = Eq
  | Lt
  | Add
  | Sub
  | Mul
  deriving (Eq, Show)

data TypeError
  = RuntimeError !RuntimeError
  | InfiniteType !String !Type
  | TypeMismatch !Type !Type
  | CtrArgsMismatch !Alt ![Type] ![Type]
  | UndefinedAlt !Alt
  | UndefinedOp !String
  | UndefinedType !String
  deriving (Eq, Show)

data RuntimeError
  = Fail
  | NoFstOf !Expr
  | NoSndOf !Expr
  | NotAFunction !Expr
  | UndefinedVar !String
  deriving (Eq, Show)

type Alt = (String, String)

-- TODO: Substitution = Type -> Type
type Substitution = [(String, Type)]

-- TODO: come up with a better name for this
data Scheme = ForAll ![String] !Type

type Context = [(String, Scheme)]

type Ops = [(String, Expr -> Maybe Expr)]

type Env = [(String, Expr)]

-- for :: [String] -> Expr -> Expr
-- for xs expr = foldr For expr xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

lam :: [String] -> Expr -> Expr
lam xs body = foldr Lam body xs

or' :: [Expr] -> Expr
or' [] = Nil
or' [a] = a
or' (a : bs) = Or a (or' bs)

if' :: Alt -> Expr -> Expr -> Expr -> Expr
if' true cond then' else' =
  App (Case true [] then' `Or` Lam [] else') cond

funT :: [Type] -> Type -> Type
funT args ret = foldr FunT ret args

orT :: [Type] -> Type
orT [] = NilT
orT [a] = a
orT (a : bs) = OrT a (orT bs)

get :: Eq k => k -> [(k, v)] -> Maybe v
get _ [] = Nothing
get x ((x', a) : _) | x == x' = Just a
get x (_ : env) = get x env

set :: Eq k => (k, v) -> [(k, v)] -> [(k, v)]
set _ [] = []
set (x, a) ((x', _) : env) | x == x' = (x, a) : env
set (x, a) (def : env) = def : set (x, a) env

pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : env) | x == x' = env
pop x (_ : env) = pop x env

newName :: [String] -> String -> String
newName existing x | x `elem` existing = newName existing (x ++ "'")
newName _ x = x

occurs :: String -> Type -> Bool
occurs _ NilT = False
occurs _ IntT = False
occurs _ NumT = False
occurs x (VarT y) = x == y
occurs _ (CtrT _ []) = False
occurs x (CtrT alt (a : bs)) = occurs x a || occurs x (CtrT alt bs)
occurs x (FunT a b) = occurs x a || occurs x b
occurs x (AndT a b) = occurs x a || occurs x b
occurs x (OrT a b) = occurs x a || occurs x b

-- TODO: pass Context as an input and return the Context
--       with the applied substitution
unify :: Type -> Type -> Either TypeError Substitution
unify NilT NilT = Right []
unify IntT IntT = Right []
unify NumT NumT = Right []
unify (VarT x) b | x `occurs` b = Left (InfiniteType x b)
unify (VarT x) b = Right [(x, b)]
unify a (VarT x) | x `occurs` a = Left (InfiniteType x a)
unify a (VarT x) = Right [(x, a)]
unify (CtrT alt args1) (CtrT alt' args2) | alt == alt' = do
  if length args1 == length args2
    then unifyMany args1 args2
    else Left (CtrArgsMismatch alt args1 args2)
unify (CtrT (t1, _) _) (CtrT (t2, _) _) | t1 == t2 = Right []
unify (FunT a1 a2) (FunT b1 b2) = do
  s1 <- unify a1 b1
  s2 <- unify (apply s1 a2) (apply s1 b2)
  Right (s2 `compose` s1)
unify (AndT a1 a2) (AndT b1 b2) = do
  s1 <- unify a1 b1
  s2 <- unify (apply s1 a2) (apply s1 b2)
  Right (s2 `compose` s1)
unify (OrT a1 a2) b = do
  s1 <- unify a1 b
  s2 <- unify (apply s1 a2) (apply s1 b)
  Right (s2 `compose` s1)
unify a (OrT b1 b2) = do
  s1 <- unify a b1
  s2 <- unify (apply s1 a) (apply s1 b2)
  Right (s2 `compose` s1)
unify a b = Left (TypeMismatch a b)

unifyMany :: [Type] -> [Type] -> Either TypeError Substitution
unifyMany [] _ = Right []
unifyMany _ [] = Right []
unifyMany (a1 : bs1) (a2 : bs2) = do
  s1 <- unify a1 a2
  s2 <- unifyMany (map (apply s1) bs1) (map (apply s1) bs2)
  Right (s2 `compose` s1)

reduce :: Ops -> Env -> Expr -> Expr
reduce ops env (Var x) = case get x env of
  Just (Var x') | x == x' -> Var x
  Just a -> reduce ops [] a
  Nothing -> Err (UndefinedVar x)
reduce ops env (Let env' a) = reduce ops (env ++ env') a
reduce _ env (Ctr alt args) = Ctr alt (map (Let env) args)
reduce _ env (Lam x a) = Lam x (Let env a)
reduce _ env (Case alt x b) = Case alt x (Let env b)
reduce ops env (App a b) = case (reduce ops env a, reduce ops env b) of
  (Fix f a, b) -> reduce ops [(f, Fix f a)] (App a b)
  (Lam x (Let env' a), b) -> reduce ops ((x, b) : env') a
  (Case alt xs (Let env' a), Ctr alt' args) | alt == alt' -> do
    reduce ops (zip xs args ++ env') a
  (Case {}, _) -> Err Fail
  (Or a1 a2, b) -> case reduce ops [] (App a1 b) of
    Err Fail -> reduce ops [] (App a2 b)
    c -> c
  (Err e, _) -> Err e
  (a, _) -> Err (NotAFunction a)
reduce _ env (And a b) = And (Let env a) (Let env b)
reduce _ env (Or a b) = Or (Let env a) (Let env b)
reduce ops env (Fst a) = case reduce ops env a of
  Var x -> Fst (Var x)
  And a _ -> reduce ops [] a
  Or a _ -> reduce ops [] a
  a -> Err (NoFstOf a)
reduce ops env (Snd a) = case reduce ops env a of
  Var x -> Snd (Var x)
  And _ b -> reduce ops [] b
  Or _ b -> reduce ops [] b
  a -> Err (NoSndOf a)
reduce ops env (Op op a) = case get op ops of
  Just f -> case eval ops env a of
    Err e -> Err e
    a -> case f a of
      Just b -> b
      Nothing -> Op op a
  Nothing -> Op op (Let env a)
reduce _ _ a = a

eval :: Ops -> Env -> Expr -> Expr
eval ops env expr = case reduce ops env expr of
  Ctr alt args -> Ctr alt (map (eval ops env) args)
  Lam x a -> Lam x (eval ops ((x, Var x) : env) a)
  Case alt xs a -> Case alt xs (eval ops (map (\x -> (x, Var x)) xs ++ env) a)
  App a b -> App a (eval ops env b)
  And a b -> And (eval ops env a) (eval ops env b)
  Or a b -> Or (eval ops env a) (eval ops env b)
  Fix x a -> Fix x (eval ops ((x, Var x) : env) a)
  a -> a

-- https://youtu.be/ytPAlhnAKro
-- https://github.com/kritzcreek/fby19
-- https://github.com/kritzcreek/fby19/blob/master/src/Typechecker.hs
infer :: Context -> Env -> Expr -> Either TypeError (Type, Substitution)
infer _ _ Nil = Right (NilT, [])
infer _ _ (Int _) = Right (IntT, [])
infer _ _ (Num _) = Right (NumT, [])
infer ctx env (Var x) = case get x ctx of
  Just scheme -> Right (instantiate (map fst ctx) scheme, [])
  Nothing -> case get x env of
    Just (Var x') | x == x' -> do
      let xT = newName (map fst ctx) (x ++ "T")
      Right (instantiate (map fst ctx) (ForAll [xT] (VarT xT)), [])
    Just a -> infer ctx [] a
    Nothing -> Left (RuntimeError (UndefinedVar x))
infer ctx env (Ctr (t, k) args) = case get t ctx of
  Just scheme -> do
    let tdef = instantiate (map fst ctx) scheme
    case findAlt k tdef of
      Just _ -> do
        (argsT, s1) <- inferMany ctx env args
        s2 <- unify tdef (CtrT (t, k) argsT)
        Right (apply s2 tdef, s2 `compose` s1)
      Nothing -> Left (UndefinedAlt (t, k))
  Nothing -> Left (UndefinedType t)
infer ctx env (Let env' a) = infer ctx (env ++ env') a
infer ctx env (Lam x a) = do
  let xT = newName (map fst ctx) (x ++ "T")
  (ta, s) <- infer ((x, ForAll [xT] (VarT xT)) : ctx) env a
  Right (FunT (apply s (VarT xT)) ta, s)
infer ctx env (Case (t, k) xs b) = case get t ctx of
  Just scheme -> do
    let tdef = instantiate (map fst ctx) scheme
    case findAlt k tdef of
      Just altArgs | length xs /= length altArgs -> Left (CtrArgsMismatch (t, k) (map VarT xs) altArgs)
      Just altArgs -> do
        let ctx' = zip xs (map (ForAll []) altArgs) ++ ctx
        (tb, s) <- infer ctx' env b
        Right (FunT (apply s tdef) tb, s)
      Nothing -> Left (UndefinedAlt (t, k))
  Nothing -> Left (UndefinedType t)
infer ctx env (App a b) = do
  let xT = newName (map fst ctx) "_app"
  (funT, s1) <- infer ctx env a
  (argT, s2) <- infer (applyContext s1 ctx) env b
  s3 <- unify (FunT argT (VarT xT)) (apply s2 funT)
  Right (apply s3 (VarT xT), s3 `compose` s2 `compose` s1)
infer ctx env (And a b) = do
  (aT, s1) <- infer ctx env a
  (bT, s2) <- infer (applyContext s1 ctx) env b
  Right (AndT (apply s2 aT) bT, s2 `compose` s1)
infer ctx env (Or a b) = do
  (aT, s1) <- infer ctx env a
  (bT, s2) <- infer (applyContext s1 ctx) env b
  s3 <- unify (apply s2 aT) bT
  Right (apply s3 bT, s3 `compose` s2 `compose` s1)
infer ctx env (Fst a) = do
  (ta, s) <- infer ctx env a
  case ta of
    AndT t _ -> Right (t, s)
    OrT t _ -> Right (t, s)
    _else -> Left (RuntimeError (NoFstOf a))
infer ctx env (Snd a) = do
  (ta, s) <- infer ctx env a
  case ta of
    AndT _ t -> Right (t, s)
    OrT _ t -> Right (t, s)
    _else -> Left (RuntimeError (NoSndOf a))
infer ctx env (Fix x a) = do
  let xT = newName (map fst env) (x ++ "T")
  (_, s) <- infer ((x, ForAll [xT] (VarT xT)) : ctx) env a
  Right (apply s (VarT xT), s)
infer ctx env (Op op a) = case get op ctx of
  Just scheme -> do
    let xT = newName (map fst ctx) "_op"
    let funT = instantiate (map fst ctx) scheme
    (argT, s1) <- infer ctx env a
    s2 <- unify (FunT argT (VarT xT)) (apply s1 funT)
    Right (apply s2 (VarT xT), s2 `compose` s1)
  Nothing -> Left (UndefinedOp op)
infer _ _ (Err e) = Left (RuntimeError e)

inferMany :: Context -> Env -> [Expr] -> Either TypeError ([Type], Substitution)
inferMany _ _ [] = Right ([], [])
inferMany ctx env (a : bs) = do
  (ta, s1) <- infer ctx env a
  (tbs, s2) <- inferMany (applyContext s1 ctx) env bs
  Right (apply s2 ta : tbs, s2 `compose` s1)

findAlt :: String -> Type -> Maybe [Type]
findAlt k (CtrT (_, k') args) | k == k' = Just args
findAlt k (OrT a b) = case findAlt k a of
  Just args -> Just args
  Nothing -> findAlt k b
findAlt _ _ = Nothing

apply :: Substitution -> Type -> Type
apply _ NilT = NilT
apply _ IntT = IntT
apply _ NumT = NumT
apply sub (CtrT alt args) = CtrT alt (map (apply sub) args)
apply sub (VarT x) = case get x sub of
  Just (VarT x') | x == x' -> VarT x
  Just a -> apply sub a
  Nothing -> VarT x
apply sub (FunT a b) = FunT (apply sub a) (apply sub b)
apply sub (AndT a b) = AndT (apply sub a) (apply sub b)
apply sub (OrT a b) = OrT (apply sub a) (apply sub b)

applyScheme :: Substitution -> Scheme -> Scheme
applyScheme sub (ForAll [] a) = ForAll [] (apply sub a)
applyScheme sub (ForAll (x : xs) a) =
  applyScheme (filter (\(y, _) -> x == y) sub) (ForAll xs a)

applyContext :: Substitution -> Context -> Context
applyContext sub = map (second (applyScheme sub))

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = map (second (apply s1)) s2 `union` s1

instantiate :: [String] -> Scheme -> Type
instantiate _ (ForAll [] t) = t
instantiate names (ForAll (x : xs) t) = do
  let y = newName names x
  instantiate names (ForAll xs (apply [(x, VarT y)] t))
