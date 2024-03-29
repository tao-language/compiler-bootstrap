module Tao where

import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import Data.List (intercalate)
import Error
import qualified Parser as P

data Expr
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Tag !String
  | Var !String
  | Lam !Pattern !Expr
  | Fun !Expr !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Or !Expr !Expr
  | If !Expr !Expr
  | Rec ![(String, Expr)]
  | Fst !Expr
  | Snd !Expr
  | Add !Expr !Expr
  | Sub !Expr !Expr
  | Mul !Expr !Expr
  | Pow !Expr !Expr
  | Eq !Expr !Expr
  | Lt !Expr !Expr
  | Gt !Expr !Expr
  | Int2Num !Expr
  | Err
  | -- Syntax sugar
    Match ![([Pattern], Expr)]
  | Let ![Definition] !Expr
  | Do !(Pattern, Expr) !Expr
  | Char !Int
  | Maybe !Expr
  | Tuple ![Expr]
  | Record ![(String, Expr)]
  | Text !String
  | List ![Expr]
  | Set ![Expr]
  | Dict ![(Expr, Expr)]
  | From !Expr
  | Until !Expr
  | Range !Expr !Expr
  | IfElse !Expr !Expr !Expr
  -- TODO: Vector, Matrix, Tensor, List comprehension
  deriving (Eq, Show)

data Pattern
  = PAny
  | PTyp
  | PIntT
  | PNumT
  | PInt !Int
  | PTag !String
  | PIfEq !Expr
  | PVar !String
  | PApp !Pattern !Pattern
  | PFun !Pattern !Pattern
  deriving (Eq, Show)

data Type
  = For ![String] !Expr
  deriving (Eq, Show)

type Definition = ([(String, Type)], Pattern, Expr)

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

app :: Expr -> [Expr] -> Expr
app = foldl App

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

match :: [([Pattern], Expr)] -> Expr
match [] = Err
match [(ps, b)] = lam ps b
match brs = Match brs

pApp :: Pattern -> [Pattern] -> Pattern
pApp = foldl PApp

-- Evaluation
eval :: C.Env -> C.Expr -> C.Expr
eval = C.eval

-- Type inference
infer :: C.Env -> C.Expr -> Either Error C.Expr
infer env a = case C.infer env a of
  Right (t', _) -> Right t'
  Left err -> error ("TODO: infer error: " ++ show err) -- Left (TypeError err)

-- compile :: Env -> C.Env
-- compile =
--  toCore
--  infer
--  embed types
--  optimize

-- Sugar / desugar
toCore :: Expr -> C.Expr
toCore Err = C.Err []
toCore Knd = C.Knd
toCore IntT = C.IntT
toCore NumT = C.NumT
toCore (Int i) = C.Int i
toCore (Num n) = C.Num n
toCore (Tag k) = C.Tag k
toCore (Var x) = C.Var x
toCore (Fun a b) = C.Fun (toCore a) (toCore b)
toCore (App a b) = C.App (toCore a) (toCore b)
toCore (Ann a (For xs t)) = C.Ann (toCore a) (C.For xs (toCore t))
toCore (Or a b) = C.Or (toCore a) (toCore b)
toCore (If a b) = C.If (toCore a) (toCore b)
toCore (Rec fields) = C.Rec (toCoreRec fields)
toCore (Fst a) = C.Fst (toCore a)
toCore (Snd a) = C.Snd (toCore a)
toCore (Add a b) = C.addI (toCore a) (toCore b)
toCore (Sub a b) = C.sub (toCore a) (toCore b)
toCore (Mul a b) = C.mul (toCore a) (toCore b)
toCore (Pow a b) = C.pow (toCore a) (toCore b)
toCore (Eq a b) = C.eq (toCore a) (toCore b)
toCore (Lt a b) = C.lt (toCore a) (toCore b)
toCore (Gt a b) = C.gt (toCore a) (toCore b)
toCore (Int2Num a) = C.int2num (toCore a)
toCore (Lam p b) = case p of
  PAny -> do
    let b' = toCore b
    let x = C.newName (C.freeVars b') "_"
    C.Lam x b'
  PTyp -> toCore (Lam (PIfEq Knd) b)
  PIntT -> toCore (Lam (PIfEq IntT) b)
  PNumT -> toCore (Lam (PIfEq NumT) b)
  PInt i -> toCore (Lam (PIfEq (Int i)) b)
  PTag k -> toCore (Lam (PIfEq (Tag k)) b)
  PIfEq a -> do
    let b' = toCore b
    let x = C.newName ("$" : C.freeVars b') "$"
    C.Lam x (C.If (C.eq (C.Var x) (toCore a)) b')
  PVar x -> C.Lam x (toCore b)
  PApp p q -> do
    let b' = toCore b
    let x = C.newName ("$" : C.freeVars b') "$"
    toCore (Lam (PVar x) (Let [([], p, Fst (Var x)), ([], q, Snd (Var x))] b))
toCore (Let [] b) = toCore b
toCore (Let (([], p, a) : defs) b) = toCore (App (Lam p (Let defs b)) a)
toCore (Match brs) = C.or' (map (\(ps, b) -> toCore (lam ps b)) brs)
-- Do !(Pattern, Expr) !Expr
-- Char !Int
-- Maybe !Expr
-- Tuple ![Expr]
-- Record ![(String, Expr)]
-- Text !String
-- List ![Expr]
-- Set ![Expr]
-- Dict ![(Expr, Expr)]
-- From !Expr
-- Until !Expr
-- Range !Expr !Expr
-- IfElse !Expr !Expr !Expr
toCore a = error ("TODO toCore: " ++ show a)

toCoreRec :: [(String, Expr)] -> [(String, C.Expr)]
toCoreRec [] = []
toCoreRec ((x, a) : fields) = (x, toCore a) : toCoreRec fields

toCoreDef :: Definition -> C.Env
toCoreDef (_, PAny, _) = []
toCoreDef (_, PTyp, _) = []
toCoreDef (_, PIntT, _) = []
toCoreDef (_, PNumT, _) = []
toCoreDef (_, PInt _, _) = []
toCoreDef (_, PTag _, _) = []
toCoreDef (_, PIfEq _, _) = []
toCoreDef (types, PVar x, a) = case toCore a of
  a | x `C.occurs` a -> [(x, C.Fix x a)]
  a -> [(x, a)]
toCoreDef (types, PApp p q, a) = toCoreDef (types, p, Fst a) ++ toCoreDef (types, q, Snd a)

toCoreEnv :: [Definition] -> C.Env
toCoreEnv = concatMap toCoreDef

fromCore :: C.Expr -> Expr
fromCore C.Knd = Knd
fromCore C.IntT = IntT
fromCore C.NumT = NumT
fromCore (C.Int i) = Int i
fromCore (C.Num n) = Num n
-- fromCore (C.Ctr k) = Ctr k
-- fromCore (C.Knd t ks) = Knd t
fromCore (C.Var x) = Var x
-- fromCore (C.Fun a b) = Fun (fromCore a) (fromCore b)
fromCore (C.Lam x b) = Lam (PVar x) (fromCore b)
fromCore (C.App a b) = App (fromCore a) (fromCore b)
fromCore (C.Ann a (C.For xs t)) = Ann (fromCore a) (For xs (fromCore t))
fromCore (C.Or a b) = Or (fromCore a) (fromCore b)
fromCore (C.If a b) = If (fromCore a) (fromCore b)
fromCore (C.Fix x a) | x `C.occurs` a = Let [([], PVar x, fromCore a)] (Var x)
fromCore (C.Fix _ a) = fromCore a
-- fromCore (C.Op2 C.Add a b) = Add (fromCore a) (fromCore b)
-- fromCore (C.Op2 C.Sub a b) = Sub (fromCore a) (fromCore b)
-- fromCore (C.Op2 C.Mul a b) = Mul (fromCore a) (fromCore b)
-- fromCore (C.Op2 C.Eq a b) = Eq (fromCore a) (fromCore b)
-- fromCore (C.Op1 C.Int2Num a) = Int2Num (fromCore a)
fromCore (C.Err stack) = Err
fromCore a = error ("TODO fromCore: " ++ show a)

fromCoreDef :: (String, C.Expr) -> Definition
fromCoreDef (x, a) = ([], PVar x, fromCore a)

fromCoreEnv :: C.Env -> [Definition]
fromCoreEnv = map fromCoreDef