{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Tao where

-- TODO: maybe use terms like "lower" and "lift" for conversions to/from core
import qualified Core as C
import Data.Bifunctor (second)
import Data.Function ((&))

data Expr
  = Any
  | Kind
  | IntType
  | NumType
  | Int Int
  | Num Double
  | Var String
  | Tag String [Expr]
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Trait Expr String
  | ListNil
  | ListCons
  | TextNil
  | TextCons
  | Fun Expr Expr
  | App Expr Expr
  | Let (Expr, Expr) Expr
  | Bind (Expr, Expr) Expr
  | TypeDef String [Expr] Expr
  | MatchFun [Expr]
  | Match [Expr] [Expr]
  | Or Expr Expr
  | Ann Expr Expr
  | Op1 C.UnaryOp Expr
  | Op2 C.BinaryOp Expr Expr
  | Meta C.Metadata Expr
  | Err C.Error
  deriving (Eq, Show)

data Stmt
  = Def Expr Expr
  | TypeAnn String Expr
  | Import String String [String] -- import module as alias (a, b, c)
  | Test Expr Expr
  | DocString [C.Metadata] String
  | Comment [C.Metadata] String
  deriving (Eq, Show)

data File = File
  { name :: String,
    stmts :: [Stmt]
  }
  deriving (Eq, Show)

data Module = Module
  { name :: String,
    files :: [File]
  }
  deriving (Eq, Show)

or' :: [Expr] -> Expr
or' [] = error "`or'` must have at least one expression"
or' [a] = a
or' (a : bs) = Or a (or' bs)

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

app :: Expr -> [Expr] -> Expr
app = foldl App

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = let (a', bs) = asApp a in (a', bs ++ [b])
asApp a = (a, [])

add :: Expr -> Expr -> Expr
add = Op2 C.Add

sub :: Expr -> Expr -> Expr
sub = Op2 C.Sub

mul :: Expr -> Expr -> Expr
mul = Op2 C.Mul

pow :: Expr -> Expr -> Expr
pow = Op2 C.Pow

eq :: Expr -> Expr -> Expr
eq = Op2 C.Eq

lt :: Expr -> Expr -> Expr
lt = Op2 C.Lt

gt :: Expr -> Expr -> Expr
gt = Op2 C.Gt

meta :: [C.Metadata] -> Expr -> Expr
meta ms a = foldr Meta a ms

list :: [Expr] -> Expr
list [] = ListNil
list (a : bs) = app ListCons [a, list bs]

freeVars :: Expr -> [String]
freeVars expr = C.freeVars (lowerExpr [] expr) & filter (/= "_")

-- Core conversions
lowerExpr :: [(String, Expr)] -> Expr -> C.Term
lowerExpr _ Any = C.Var "_"
lowerExpr _ Kind = C.Knd
lowerExpr _ IntType = C.IntT
lowerExpr _ NumType = C.NumT
lowerExpr _ (Int i) = C.Int i
lowerExpr _ (Num n) = C.Num n
lowerExpr _ (Var x) = C.Var x
lowerExpr defs (Tag k args) = C.app (C.Tag k) (map (lowerExpr defs) args)
lowerExpr defs (Tuple items) = lowerExpr defs (Tag "()" items)
lowerExpr defs (Record fields) = do
  let lowerField (k, v) = (k, lowerExpr defs v)
  C.Rec (map lowerField fields)
lowerExpr defs (Trait a x) = do
  let a' = lowerExpr defs a
  let env = map (second (lowerExpr defs)) defs
  let (t, _) = C.infer env a'
  C.app (C.Var $ '.' : x) [t, a']
lowerExpr _ ListNil = C.Tag "[]"
lowerExpr _ ListCons = C.Tag "[..]"
lowerExpr _ TextNil = C.Tag "\"\""
lowerExpr _ TextCons = C.Tag "\"..\""
lowerExpr defs (Fun a b) = C.Fun (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (App a b) = C.App (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Let (p, a) b) = C.let' (lowerExpr defs p, lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Bind (p, a) b) = lowerExpr defs (App (Trait a "<-") (Fun p b))
-- TODO: TypeDef
lowerExpr defs (MatchFun cases) = lowerExpr defs (or' cases)
lowerExpr defs (Match args cases) = lowerExpr defs (app (MatchFun cases) args)
lowerExpr defs (Or a b) = C.Or (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Ann a b) = C.Ann (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Op1 op a) = C.Op1 op (lowerExpr defs a)
lowerExpr defs (Op2 op a b) = C.Op2 op (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Meta m a) = C.Meta m (lowerExpr defs a)
lowerExpr _ (Err err) = C.Err err

liftExpr :: C.Term -> Expr
liftExpr C.Knd = Kind
liftExpr C.IntT = IntType
liftExpr C.NumT = NumType
liftExpr (C.Int i) = Int i
liftExpr (C.Num n) = Num n
liftExpr (C.Var "_") = Any
liftExpr (C.Var x) = Var x
liftExpr (C.Tag "()") = Tuple []
liftExpr (C.Tag "[]") = ListNil
liftExpr (C.Tag "[..]") = ListCons
liftExpr (C.Tag "\"\"") = TextNil
liftExpr (C.Tag "\"..\"") = TextCons
liftExpr (C.Tag k) = Tag k []
liftExpr (C.Rec fields) = do
  let liftField (x, a) = (x, liftExpr a)
  Record (map liftField fields)
liftExpr (C.For _ a) = liftExpr a
-- liftExpr (C.Fix String Term) = _
liftExpr (C.Fun a b) = Fun (liftExpr a) (liftExpr b)
liftExpr (C.App a b) = case asApp (App (liftExpr a) (liftExpr b)) of
  (Tag k args, args') -> Tag k (args ++ args')
  (Tuple args, args') -> Tuple (args ++ args')
  (Var ('.' : x), _ : a : args) -> app (Trait a x) args
  (Fun p a, [b]) -> Let (p, b) a
  (Trait a "<-", [Fun p b]) -> Bind (p, a) b
  (a, args) -> app a args
liftExpr (C.Or a b) = Or (liftExpr a) (liftExpr b)
liftExpr (C.Ann a b) = Ann (liftExpr a) (liftExpr b)
liftExpr (C.Op1 op a) = Op1 op (liftExpr a)
liftExpr (C.Op2 op a b) = Op2 op (liftExpr a) (liftExpr b)
liftExpr (C.Meta m a) = Meta m (liftExpr a)
liftExpr (C.Err err) = Err err
liftExpr a = error $ "TODO: liftExpr " ++ show a

stmtDefs :: Stmt -> [(String, Expr)]
stmtDefs (Def (Var x) b) = [(x, b)]
stmtDefs (Def (Trait (Ann a t) x) b) = [(x, fun [t, a] b)]
stmtDefs (Def (Trait a x) b) = stmtDefs (Def (Trait (Ann a Any) x) b)
stmtDefs (Def (App a1 a2) b) = stmtDefs (Def a1 (Fun a2 b))
stmtDefs (Def (Ann a t) b) = stmtDefs (Def a (Ann b t))
stmtDefs (Def Op1 {} _) = []
stmtDefs (Def Op2 {} _) = []
stmtDefs (Def (Meta m a) b) = stmtDefs (Def a (Meta m b))
stmtDefs (Def p b) = map (\x -> (x, Match [b] [Fun p (Var x)])) (freeVars p)
stmtDefs _ = []

fileDefs :: File -> [(String, Expr)]
fileDefs file = concatMap stmtDefs file.stmts

moduleDefs :: Module -> [(String, Expr)]
moduleDefs mod = concatMap fileDefs mod.files

lowerModule :: Module -> C.Env
lowerModule mod = do
  let defs = moduleDefs mod
  map (second (lowerExpr defs)) defs

liftModule :: String -> C.Env -> Module
liftModule name _ = error "TODO: liftModule"

eval :: Module -> Expr -> Expr
eval mod expr = do
  let env = lowerModule mod
  let term = lowerExpr (moduleDefs mod) expr
  liftExpr (C.eval env term)