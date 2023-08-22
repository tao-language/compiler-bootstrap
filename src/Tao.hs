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
  | Add !Expr !Expr
  | Sub !Expr !Expr
  | Mul !Expr !Expr
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
  = AnyP
  | ErrP
  | KndP
  | IntTP
  | IntP !Int
  | CtrP !String
  | TypP !String
  | VarP !String
  | IsIntP !String
  | IsNumP !String
  | FunP !Pattern !Pattern
  | AppP !Pattern !Pattern
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

-- Type inference
infer :: Env -> Expr -> Either CompileError Type
infer env a = case C.infer (toCoreEnv env) (toCore a) of
  Right (t', _) -> Right (For (C.freeVars t') (fromCore t'))
  Left err -> Left (TypeError err)

-- Compile to core
toCore :: Expr -> C.Expr
toCore Err = C.Err
toCore Knd = C.Knd
toCore IntT = C.IntT
toCore NumT = C.NumT
toCore (Int i) = C.Int i
toCore (Num n) = C.Num n
toCore (Ctr k) = C.Ctr k
toCore (Typ t) = C.Typ t
toCore (Var x) = C.Var x
toCore (Fun a b) = C.Fun (toCore a) (toCore b)
toCore (Lam AnyP b) = C.lamAny (toCore b)
toCore (Lam ErrP b) = C.lamEq C.Err (toCore b)
toCore (Lam KndP b) = C.lamEq C.Knd (toCore b)
toCore (Lam IntTP b) = C.lamEq C.IntT (toCore b)
toCore (Lam (IntP i) b) = C.lamEq (C.Int i) (toCore b)
toCore (Lam (CtrP k) b) = C.lamEq (C.Ctr k) (toCore b)
toCore (Lam (TypP t) b) = C.lamEq (C.Typ t) (toCore b)
toCore (Lam (VarP x) b) = C.Lam x (toCore b)
toCore (Lam (IsIntP x) b) = C.lamInt x (toCore b)
toCore (Lam (IsNumP x) b) = C.lamNum x (toCore b)
toCore (Lam (FunP p q) b) = toCore (Lam p (Lam q b))
-- FunP !Pattern !Pattern
-- AppP !Pattern !Pattern
toCore (App a b) = C.App (toCore a) (toCore b)
toCore (Ann a (For xs t)) = C.Ann (toCore a) (C.For xs (toCore t))
toCore (Or a b) = C.Or (toCore a) (toCore b)
toCore (Add a b) = C.Op2 C.Add (toCore a) (toCore b)
toCore (Sub a b) = C.Op2 C.Sub (toCore a) (toCore b)
toCore (Mul a b) = C.Op2 C.Mul (toCore a) (toCore b)
toCore (Int2Num a) = C.Op1 C.Int2Num (toCore a)
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

-- toCoreP :: Pattern -> C.Pattern
-- toCoreP ErrP = C.ErrP
-- toCoreP KndP = C.KndP
-- toCoreP IntTP = C.IntTP
-- toCoreP (IntP i) = C.IntP i
-- toCoreP (CtrP k) = C.CtrP k
-- toCoreP (CtrIntP x) = C.CtrIntP x
-- toCoreP (CtrNumP x) = C.CtrNumP x
-- toCoreP (TypP t) = C.TypP t
-- toCoreP (VarP x) = C.VarP x
-- toCoreP (FunP p q) = C.FunP (toCoreP p) (toCoreP q)
-- toCoreP (AppP p q) = C.AppP (toCoreP p) (toCoreP q)

toCoreEnv :: Env -> C.Env
toCoreEnv = map (second toCore)

-- Decompile from core
fromCore :: C.Expr -> Expr
fromCore C.Err = Err
fromCore C.Knd = Knd
fromCore C.IntT = IntT
fromCore C.NumT = NumT
fromCore (C.Int i) = Int i
fromCore (C.Num n) = Num n
fromCore (C.Ctr k) = Ctr k
fromCore (C.Typ t) = Typ t
fromCore (C.Var x) = Var x
fromCore (C.Fun a b) = Fun (fromCore a) (fromCore b)
fromCore (C.Lam x b) = Lam (VarP x) (fromCore b)
fromCore (C.App a b) = App (fromCore a) (fromCore b)
fromCore (C.Ann a (C.For xs t)) = Ann (fromCore a) (For xs (fromCore t))
fromCore (C.Or a b) = Or (fromCore a) (fromCore b)
fromCore (C.Fix x a) = Let (VarP x, fromCore a) (Var x)
fromCore (C.Op2 C.Add a b) = Add (fromCore a) (fromCore b)
fromCore (C.Op2 C.Sub a b) = Sub (fromCore a) (fromCore b)
fromCore (C.Op2 C.Mul a b) = Mul (fromCore a) (fromCore b)
fromCore (C.Op1 C.Int2Num a) = Int2Num (fromCore a)
fromCore a = error ("TODO fromCore: " ++ show a)

-- fromCoreP :: C.Pattern -> Pattern
-- fromCoreP C.ErrP = ErrP
-- fromCoreP C.KndP = KndP
-- fromCoreP C.IntTP = IntTP
-- fromCoreP (C.IntP i) = IntP i
-- fromCoreP (C.CtrP k) = CtrP k
-- fromCoreP (C.CtrIntP x) = CtrIntP x
-- fromCoreP (C.CtrNumP x) = CtrNumP x
-- fromCoreP (C.TypP t) = TypP t
-- fromCoreP (C.VarP x) = VarP x
-- fromCoreP (C.FunP p q) = FunP (fromCoreP p) (fromCoreP q)
-- fromCoreP (C.AppP p q) = AppP (fromCoreP p) (fromCoreP q)

fromCoreEnv :: C.Env -> Env
fromCoreEnv = map (second fromCore)