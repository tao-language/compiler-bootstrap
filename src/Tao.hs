module Tao where

import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import qualified Parser as P

data Expr
  = -- Core expressions
    Err
  | Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Ctr !String
  | Typ !String
  | Var !String
  | Fun !Expr !Expr
  | Lam !Pattern !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Or !Expr !Expr
  | If !Expr !Expr
  | Add !Expr !Expr
  | Sub !Expr !Expr
  | Mul !Expr !Expr
  | Eq !Expr !Expr
  | Int2Num !Expr
  | -- Syntax sugar
    Match ![([Pattern], Expr)]
  | Let !(Pattern, Expr) !Expr
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
  | PVar !String
  | PInt !String
  | PNum !String
  | PIf !String !Expr
  | PIfEq !Expr
  | PIfKnd
  | PIfIntT
  | PIfNumT
  | PIfInt !Int
  | PIfNum !Double
  | PIfCtr !String
  | PIfTyp !String
  | PFun !Pattern !Pattern
  | PApp !Pattern !Pattern
  | PErr
  deriving (Eq, Show)

data Type
  = For ![String] !Expr
  deriving (Eq, Show)

type Env = [(String, Expr)]

data CompileError
  = TypeError !C.TypeError
  | SyntaxError !P.SyntaxError
  deriving (Eq, Show)

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

app :: Expr -> [Expr] -> Expr
app = foldl App

let' :: [(Pattern, Expr)] -> Expr -> Expr
let' [] b = b
let' ((p, a) : defs) b = App (Lam p (let' defs b)) a

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

prelude :: Env
prelude =
  [ ("Type", Typ "Type"),
    ("Integer", Typ "Integer"),
    ("Number", Var "Number")
  ]

-- Evaluation
eval :: Env -> Expr -> Expr
eval env a = fromCore (C.eval (toCoreEnv env) (toCore a))

eval' :: Env -> Expr -> C.Expr
eval' env a = C.eval (toCoreEnv env) (toCore a)

-- Type inference
infer :: Env -> Expr -> Either CompileError Type
infer env a = case C.infer (toCoreEnv env) (toCore a) of
  Right (t', _) -> Right (For (C.freeVars t') (fromCore t'))
  Left err -> Left (TypeError err)

-- compile :: Env -> C.Env
-- compile =
--  toCore
--  infer
--  embed types
--  optimize

-- Sugar / desugar
toCore :: Expr -> C.Expr
toCore Err = C.Err
toCore Knd = C.Knd
toCore IntT = C.IntT
toCore NumT = C.NumT
toCore (Int i) = C.Int i
toCore (Num n) = C.Num n
-- toCore (Ctr k) = C.Ctr k
-- toCore (Typ t) = C.Typ t []
toCore (Var x) = C.Var x
toCore (Fun a b) = C.Fun (toCore a) (toCore b)
-- toCore (Lam p b) = do
--   let b' = toCore b
--   let x = C.newName (C.freeVars b') "_"
--   C.Lam (toCoreP x p) b'
toCore (App a b) = C.App (toCore a) (toCore b)
toCore (Ann a (For xs t)) = C.Ann (toCore a) (C.For xs (toCore t))
toCore (Or a b) = C.Or (toCore a) (toCore b)
toCore (If a b) = C.If (toCore a) (toCore b)
toCore (Add a b) = C.add (toCore a) (toCore b)
toCore (Sub a b) = C.sub (toCore a) (toCore b)
toCore (Mul a b) = C.mul (toCore a) (toCore b)
toCore (Eq a b) = C.eq (toCore a) (toCore b)
toCore (Int2Num a) = C.int2Num (toCore a)
toCore (Match brs) = C.or' (map (\(ps, b) -> toCore (lam ps b)) brs)
-- Let !(Pattern, Expr) !Expr
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

-- toCoreP :: String -> Pattern -> C.Pattern
-- -- toCoreP x PAny = C.PAny
-- -- toCoreP _ (PVar x) = C.PAs C.PAny x
-- -- toCoreP _ (PInt x) = C.PInt x
-- -- toCoreP _ (PNum x) = C.PNum x
-- -- toCoreP _ (PIf x a) = C.PIf x (toCore a)
-- toCoreP x (PIfEq a) = toCoreP x (PIf x (Eq (Var x) a))
-- toCoreP x PIfKnd = toCoreP x (PIfEq Knd)
-- toCoreP x PIfIntT = toCoreP x (PIfEq IntT)
-- toCoreP x PIfNumT = toCoreP x (PIfEq NumT)
-- toCoreP x (PIfInt i) = toCoreP x (PIfEq (Int i))
-- toCoreP x (PIfNum n) = toCoreP x (PIfEq (Num n))
-- toCoreP x (PIfCtr k) = toCoreP x (PIfEq (Ctr k))
-- toCoreP x (PIfTyp t) = toCoreP x (PIfEq (Typ t))
-- toCoreP x (PFun p q) = C.PFun (toCoreP x p) (toCoreP x q)
-- toCoreP x (PApp p q) = C.PApp (toCoreP x p) (toCoreP x q)
-- toCoreP _ PErr = C.PErr

fromCore :: C.Expr -> Expr
fromCore C.Err = Err
fromCore C.Knd = Knd
fromCore C.IntT = IntT
fromCore C.NumT = NumT
fromCore (C.Int i) = Int i
fromCore (C.Num n) = Num n
-- fromCore (C.Ctr k) = Ctr k
-- fromCore (C.Typ t ks) = Typ t
fromCore (C.Var x) = Var x
fromCore (C.Fun a b) = Fun (fromCore a) (fromCore b)
fromCore (C.Lam x b) = Lam (PVar x) (fromCore b)
fromCore (C.App a b) = App (fromCore a) (fromCore b)
fromCore (C.Ann a (C.For xs t)) = Ann (fromCore a) (For xs (fromCore t))
fromCore (C.Or a b) = Or (fromCore a) (fromCore b)
fromCore (C.If a b) = If (fromCore a) (fromCore b)
fromCore (C.Fix x a) | x `C.occurs` a = Let (PVar x, fromCore a) (Var x)
fromCore (C.Fix _ a) = fromCore a
fromCore (C.Op2 C.Add a b) = Add (fromCore a) (fromCore b)
fromCore (C.Op2 C.Sub a b) = Sub (fromCore a) (fromCore b)
fromCore (C.Op2 C.Mul a b) = Mul (fromCore a) (fromCore b)
fromCore (C.Op2 C.Eq a b) = Eq (fromCore a) (fromCore b)
fromCore (C.Op1 C.Int2Num a) = Int2Num (fromCore a)
fromCore a = error ("TODO fromCore: " ++ show a)

-- fromCoreP :: C.Pattern -> Pattern
-- -- fromCoreP C.PAny = PAny
-- -- fromCoreP C.PInt = PInt x
-- -- fromCoreP C.PNum = PNum x
-- -- fromCoreP (C.PAs C.PAny x) = PVar x
-- -- fromCoreP (C.PIf x a) = PIf x (fromCore a)
-- fromCoreP (C.PFun a b) = PFun (fromCoreP a) (fromCoreP b)
-- fromCoreP (C.PApp a b) = PApp (fromCoreP a) (fromCoreP b)
-- fromCoreP C.PErr = PErr

toCoreDef :: (String, Expr) -> (String, C.Expr)
toCoreDef (x, a) = case toCore a of
  a | x `C.occurs` a -> (x, C.Fix x a)
  a -> (x, a)

toCoreEnv :: Env -> C.Env
toCoreEnv = map toCoreDef

fromCoreEnv :: C.Env -> Env
fromCoreEnv = map (second fromCore)