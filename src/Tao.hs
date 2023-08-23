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
  | And !Expr !Expr
  | Add !Expr !Expr
  | Sub !Expr !Expr
  | Mul !Expr !Expr
  | IsInt !Expr
  | IsNum !Expr
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
  = PErr
  | PKnd
  | PIntT
  | PNumT
  | PInt !Int
  | PNum !Double
  | PCtr !String
  | PTyp !String
  | PVar !String
  | PIsInt !String
  | PIsNum !String
  | PFun !Pattern !Pattern
  | PApp !Pattern !Pattern
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

-- Sugar / desugar
toCore :: Expr -> C.Expr
toCore Err = C.Err C.Tup
toCore Knd = C.Knd
toCore IntT = C.IntT
toCore NumT = C.NumT
toCore (Int i) = C.Int i
toCore (Num n) = C.Num n
toCore (Ctr k) = C.Ctr k
toCore (Typ t) = C.Typ t
toCore (Var x) = C.Var x
toCore (Fun a b) = C.Fun (toCore a) (toCore b)
toCore (Lam PErr b) = do
  let b' = toCore b
  let x = C.newName (C.freeVars b') "err"
  C.Lam (C.PVar x) b'
-- PKnd
-- PIntT
-- PNumT
-- PInt !Int
-- PNum !Double
toCore (Lam (PCtr k) b) = do
  let b' = toCore b
  let x = C.newName (C.freeVars b') k
  C.Lam (C.PVar x) (C.And (C.eq (C.Var x) (C.Ctr k)) b')
-- PTyp !String
toCore (Lam (PVar x) b) = C.Lam (C.PVar x) (toCore b)
toCore (Lam (PIsInt x) b) = C.Lam (C.PVar x) (C.And (C.isInt (C.Var x)) (toCore b))
toCore (Lam (PIsNum x) b) = C.Lam (C.PVar x) (C.And (C.isNum (C.Var x)) (toCore b))
toCore (Lam (PFun p q) b) = do
  let b' = toCore b
  let x = C.newName (C.freeVars b') "a"
  let y = C.newName (x : C.freeVars b') "b"
  C.Lam (C.PFun x y) (toCore (let' [(p, Var x), (q, Var y)] b))
toCore (Lam (PApp p q) b) = do
  let b' = toCore b
  let x = C.newName (C.freeVars b') "f"
  let y = C.newName (x : C.freeVars b') "x"
  C.Lam (C.PApp x y) (toCore (let' [(p, Var x), (q, Var y)] b))
-- toCore (Lam p b) = do
--   let b' = toCore b
--   C.Lam (toCoreP (C.freeVars b') p) b'
toCore (App a b) = C.App (toCore a) (toCore b)
toCore (Ann a (For xs t)) = C.Ann (toCore a) (C.For xs (toCore t))
toCore (Or a b) = C.Or (toCore a) (toCore b)
toCore (And a b) = C.And (toCore a) (toCore b)
toCore (Add a b) = C.add (toCore a) (toCore b)
toCore (Sub a b) = C.sub (toCore a) (toCore b)
toCore (Mul a b) = C.mul (toCore a) (toCore b)
toCore (IsInt a) = C.isInt (toCore a)
toCore (IsNum a) = C.isNum (toCore a)
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

fromCore :: C.Expr -> Expr
fromCore (C.Err a) = Err
fromCore C.Knd = Knd
fromCore C.IntT = IntT
fromCore C.NumT = NumT
fromCore (C.Int i) = Int i
fromCore (C.Num n) = Num n
fromCore (C.Ctr k) = Ctr k
fromCore (C.Typ t) = Typ t
fromCore (C.Var x) = Var x
fromCore (C.Fun a b) = Fun (fromCore a) (fromCore b)
-- fromCore (C.Lam p b) = Lam (fromCoreP p) (fromCore b)
fromCore (C.App a b) = App (fromCore a) (fromCore b)
fromCore (C.Ann a (C.For xs t)) = Ann (fromCore a) (For xs (fromCore t))
fromCore (C.Or a b) = Or (fromCore a) (fromCore b)
fromCore (C.And a b) = And (fromCore a) (fromCore b)
fromCore (C.Fix x a) = Let (PVar x, fromCore a) (Var x)
fromCore (C.Op2 C.Add a b) = Add (fromCore a) (fromCore b)
fromCore (C.Op2 C.Sub a b) = Sub (fromCore a) (fromCore b)
fromCore (C.Op2 C.Mul a b) = Mul (fromCore a) (fromCore b)
fromCore (C.Op1 C.Int2Num a) = Int2Num (fromCore a)
fromCore a = error ("TODO fromCore: " ++ show a)

-- toCoreP :: [String] -> Pattern -> C.Pattern
-- toCoreP existing PErr = C.PVar (C.newName existing "err")
-- toCoreP existing PKnd = C.PVar (C.newName existing "knd")
-- toCoreP existing PIntT = C.PVar (C.newName existing "intT")
-- toCoreP existing PNumT = C.PVar (C.newName existing "numT")
-- toCoreP existing (PInt i) = C.PVar (C.newName existing "int")
-- toCoreP existing (PNum n) = C.PVar (C.newName existing "num")
-- toCoreP existing (PCtr k) = C.PVar (C.newName existing "ctr")
-- toCoreP existing (PTyp t) = C.PVar (C.newName existing "typ")
-- toCoreP existing (PVar x) = C.PVar x
-- toCoreP existing (PFun p q) = do
--   let p' = toCoreP existing p
--   let q' = toCoreP (C.freeVars (C.patternExpr p') ++ existing) q
--   C.PFun p' q'
-- toCoreP existing (PApp p q) = do
--   let p' = toCoreP existing p
--   let q' = toCoreP (C.freeVars (C.patternExpr p') ++ existing) q
--   C.PApp p' q'

-- fromCoreP :: C.Pattern -> Pattern
-- fromCoreP (C.PVar x) = PVar x
-- fromCoreP (C.PFun p q) = PFun (fromCoreP p) (fromCoreP q)
-- fromCoreP (C.PApp p q) = PApp (fromCoreP p) (fromCoreP q)

toCoreEnv :: Env -> C.Env
toCoreEnv = map (second toCore)

fromCoreEnv :: C.Env -> Env
fromCoreEnv = map (second fromCore)