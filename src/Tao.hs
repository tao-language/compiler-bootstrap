module Tao where

import qualified Core as C
import qualified Parser as P

data Expr
  = -- Core expressions
    Err
  | Int !Int
  | Num !Double
  | Var !String
  | Fun !Expr !Expr
  | Match ![([Pattern], Expr)]
  | App !Expr !Expr
  | Ann !Expr !Type
  | Or !Expr !Expr
  | AddI !Expr !Expr
  | SubI !Expr !Expr
  | MulI !Expr !Expr
  | -- Syntax sugar
    Char !Int
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
  | Let !(Pattern, Expr) !Expr
  | Do !(Pattern, Expr) !Expr
  | IfElse !Expr !Expr !Expr
  -- TODO: Vector, Matrix, Tensor, List comprehension
  deriving (Eq, Show)

data Pattern
  = ErrP
  | KndP
  | IntTP
  | IntP !Int
  | CtrP !String
  | TypP !String
  | VarP !String
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

nameType :: String
nameType = "Type"

nameIntType :: String
nameIntType = "Integer"

nameNumType :: String
nameNumType = "Number"

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

lam :: [Pattern] -> Expr -> Expr
lam [] a = a
lam ps a = Match [(ps, a)]

app :: Expr -> [Expr] -> Expr
app = foldl App

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

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
toCore (Int i) = C.Int i
toCore (Num n) = C.Num n
toCore (Var x) | x == nameType = C.Knd
toCore (Var x) | x == nameIntType = C.IntT
toCore (Var x) | x == nameNumType = C.NumT
toCore (Var x) = C.Var x
toCore (Fun a b) = C.Fun (toCore a) (toCore b)
toCore (Match brs) = do
  let toCoreBr (ps, b) = C.lam (map toCoreP ps) (toCore b)
  C.or' (map toCoreBr brs)
toCore (App a b) = C.App (toCore a) (toCore b)
toCore (Ann a (For xs t)) = C.Ann (toCore a) (C.For xs (toCore t))
toCore (Or a b) = C.Or (toCore a) (toCore b)
toCore (AddI a b) = C.Op2 C.AddI (toCore a) (toCore b)
toCore (SubI a b) = C.Op2 C.SubI (toCore a) (toCore b)
toCore (MulI a b) = C.Op2 C.MulI (toCore a) (toCore b)
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
-- Let !(Pattern, Expr) !Expr
-- Do !(Pattern, Expr) !Expr
-- IfElse !Expr !Expr !Expr
toCore a = error ("TODO: " ++ show a)

toCoreP :: Pattern -> C.Pattern
toCoreP ErrP = C.ErrP
toCoreP KndP = C.KndP
toCoreP IntTP = C.IntTP
toCoreP (IntP i) = C.IntP i
toCoreP (CtrP k) = C.CtrP k
toCoreP (TypP t) = C.TypP t
toCoreP (VarP x) = C.VarP x
toCoreP (FunP p q) = C.FunP (toCoreP p) (toCoreP q)
toCoreP (AppP p q) = C.AppP (toCoreP p) (toCoreP q)

toCoreEnv :: Env -> C.Env
toCoreEnv env = error "TODO: toCoreEnv"

-- Decompile from core
fromCore :: C.Expr -> Expr
fromCore C.Err = Err
fromCore C.Knd = Var nameType
fromCore C.IntT = Var nameIntType
fromCore C.NumT = Var nameNumType
fromCore (C.Int i) = Int i
fromCore (C.Num n) = Num n
fromCore (C.Ctr k) = Var k
fromCore (C.Typ t) = Var t
fromCore (C.Var x) = Var x
fromCore (C.Fun a b) = Fun (fromCore a) (fromCore b)
fromCore (C.Lam p b) = Match [([fromCoreP p], fromCore b)]
fromCore (C.App a b) = App (fromCore a) (fromCore b)
fromCore (C.Ann a (C.For xs t)) = Ann (fromCore a) (For xs (fromCore t))
fromCore (C.Or a b) = Or (fromCore a) (fromCore b)
fromCore (C.Fix x a) = Let (VarP x, fromCore a) (Var x)
fromCore (C.Op2 C.AddI a b) = AddI (fromCore a) (fromCore b)
fromCore (C.Op2 C.SubI a b) = SubI (fromCore a) (fromCore b)
fromCore (C.Op2 C.MulI a b) = MulI (fromCore a) (fromCore b)

fromCoreP :: C.Pattern -> Pattern
fromCoreP C.ErrP = ErrP
fromCoreP C.KndP = KndP
fromCoreP C.IntTP = IntTP
fromCoreP (C.IntP i) = IntP i
fromCoreP (C.CtrP k) = CtrP k
fromCoreP (C.TypP t) = TypP t
fromCoreP (C.VarP x) = VarP x
fromCoreP (C.FunP p q) = FunP (fromCoreP p) (fromCoreP q)
fromCoreP (C.AppP p q) = AppP (fromCoreP p) (fromCoreP q)

fromCoreEnv :: C.Env -> Env
fromCoreEnv env = error "TODO: toCoreEnv"