module Tao2 where

import qualified Core2 as Core
import Data.Bifunctor (Bifunctor (first, second))
import Data.List (foldl')
import Flow ((|>))

data Expr
  = Err
  | Int !Int
  | Num !Double
  | Var !String
  | Ann !Expr !Expr
  | Lam !String !Expr
  | App !Expr !Expr
  | If !Expr !Expr !Expr
  | Let ![(String, Expr)] !Expr
  | SumT !String ![String] ![(String, Expr)]
  | Ctr !String !String
  | TypeOf !Expr
  | Case !Expr ![(Pattern, Expr)]
  | TypT
  | IntT
  | NumT
  | ForT !String !Expr
  | FunT !Expr !Expr
  | Add
  | Eq
  deriving (Eq, Show)

type Alt = (String, ([String], Expr))

data Pattern
  = AnyP
  | IntP !Int
  | NumP !Double
  | VarP !String
  | AnnP !Pattern !Expr
  deriving (Eq, Show)

type Env = [(String, Expr)]

lam :: [String] -> Expr -> Expr
lam xs a = foldr Lam a xs

asLam :: Expr -> ([String], Expr)
asLam a = do
  let asLam' :: [String] -> Expr -> ([String], Expr)
      asLam' xs (Lam x body) = first (x :) (asLam' xs body)
      asLam' xs body = (xs, body)
  asLam' [] a

app :: Expr -> [Expr] -> Expr
app = foldl' App

forT :: [String] -> Expr -> Expr
forT xs a = foldr ForT a xs

funT :: [Expr] -> Expr -> Expr
funT ts t = foldr FunT t ts

asFunT :: Expr -> ([Expr], Expr)
asFunT expr = do
  let asFunT' :: [Expr] -> Expr -> ([Expr], Expr)
      asFunT' args (FunT arg ret) = first (arg :) (asFunT' args ret)
      asFunT' args ret = (args, ret)
  asFunT' [] expr

add :: Expr -> Expr -> Expr
add a b = app Add [a, b]

eq :: Expr -> Expr -> Expr
eq a b = app Eq [a, b]

let' :: (String, Expr) -> Expr -> Expr
let' (x, value) body = App (Lam x body) value

-- TODO: do not inline variables
compile :: Env -> Expr -> Core.Expr
compile _ Err = Core.Err
compile _ (Int i) = Core.Int i
compile _ (Num n) = Core.Num n
compile env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Core.Var x
  Just expr -> compile env expr
  Nothing -> Core.Err
compile env (Ann expr type') = Core.Ann (compile env expr) (compile env type')
compile env (Lam x body) = Core.Lam [] x (compile ((x, Var x) : env) body)
compile env (App fun arg) = Core.App (compile env fun) (compile env arg)
compile env (If cond then' else') = compile env (app cond [then', else'])
compile env (Let env' expr) = compile (env ++ env') expr
compile env (SumT tname vars alts) = do
  let branch (_, type') = funT (fst (asFunT type')) (Var tname)
  let body = funT (map branch alts) (Var tname)
  compile ((tname, Var tname) : env) (lam vars (ForT tname body))
compile env (Ctr tname cname) = case lookup tname env of
  Just (SumT _ vars alts) -> case lookup cname alts of
    Just type' -> do
      let args = fst (asFunT type')
      let xs = take (length args) (map (: []) ['a' .. 'z'])
      let ctr = lam (xs ++ map fst alts) (app (Var cname) (map Var xs))
      compile (map (\x -> (x, Var x)) vars ++ env) (Ann ctr (forT vars type'))
    Nothing -> Core.Err
  _undefinedType -> Core.Err
compile env (TypeOf expr) = case infer env expr of
  Right (type', env) -> compile env type'
  Left _ -> Core.Err
compile _ (Case _ []) = Core.Err
compile env (Case _ ((AnyP, body) : _)) = compile env body
compile env (Case arg ((IntP i, body) : cases)) =
  compile env (If (eq arg (Int i)) body (Case arg cases))
compile env (Case arg ((NumP n, body) : cases)) =
  compile env (If (eq arg (Num n)) body (Case arg cases))
compile env (Case arg ((VarP x, body) : _)) =
  compile env (let' (x, arg) body)
compile env (Case arg ((AnnP p t, body) : cases)) =
  compile env (If (eq (TypeOf arg) t) (Case arg ((p, body) : cases)) (Case arg cases))
compile _ TypT = Core.TypT
compile _ IntT = Core.IntT
compile _ NumT = Core.NumT
compile env (ForT x a) = Core.ForT x (compile env a)
compile env (FunT a b) = Core.FunT (compile env a) (compile env b)
compile _ Add = Core.Op Core.Add
compile _ Eq = Core.Op Core.Eq

compileEnv :: Env -> Core.Env
compileEnv env = map (second (compile env)) env

decompile :: Core.Expr -> Expr
decompile Core.Err = Err
decompile (Core.Int i) = Int i
decompile (Core.Num n) = Num n
decompile (Core.Var x) = Var x
decompile (Core.Ann expr type') = Ann (decompile expr) (decompile type')
decompile (Core.Lam [] x body) = Lam x (decompile body)
decompile (Core.Lam env x body) = Let (decompileEnv env) (Lam x (decompile body))
decompile (Core.App fun arg) = App (decompile fun) (decompile arg)
decompile (Core.Fix x fun) = Let [(x, decompile fun)] (Var x)
decompile Core.TypT = TypT
decompile Core.IntT = IntT
decompile Core.NumT = NumT
decompile (Core.ForT x a) = ForT x (decompile a)
decompile (Core.FunT a b) = FunT (decompile a) (decompile b)
decompile (Core.Op Core.Add) = Add
decompile (Core.Op Core.Eq) = Eq

decompileEnv :: Core.Env -> Env
decompileEnv = map (second decompile)

occurs :: String -> Expr -> Bool
occurs x expr = Core.occurs x (compile [] expr)

infer :: Env -> Expr -> Either Core.TypeError (Expr, Env)
infer env expr = do
  (expr', env') <- Core.infer (compileEnv env) (compile env expr)
  Right (decompile expr', decompileEnv env')

reduce :: Env -> Expr -> Expr
reduce env expr = compile env expr |> Core.reduce [] |> decompile
