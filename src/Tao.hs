module Tao where

import Control.Monad (void)
import qualified Core
import Data.Bifunctor (Bifunctor (first, second))
import Data.List (delete, foldl', sort, sortOn, union, unionBy, (\\))
import Data.Maybe (fromMaybe, mapMaybe)
import Flow ((.>), (|>))
import Text.Read (readMaybe)

-- Core calculus: https://www.cse.iitk.ac.in/users/ppk/teaching/cs653/notes/lectures/Core-calculus.lhs.pdf
-- Closure calculus: https://youtu.be/ogXlQf8lDD4
-- Type inference from scratch: https://youtu.be/ytPAlhnAKro
-- Bidirectional type checking: https://youtu.be/utyBNDj7s2w

-- The Little Typer: https://thelittletyper.com
-- Epigram: http://www.e-pig.org/ http://www.e-pig.org/downloads/view.pdf
-- Implementing dependent types: https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf
-- Complete and Easy: https://arxiv.org/pdf/1306.6032.pdf https://arxiv.org/abs/1306.6032

-- TODO: TaoLang: do-notation, monadas, effects, I/O
-- TODO: TaoLang: support types (tagged unions, type alias)
-- TODO: Tao: modules and stdlib (files, parser, compiler)
-- TODO: Tao: show and pretty formatting
-- TODO: self compiling compiler
-- TODO: Core: add source code locations
-- TODO: Core: pretty print error messages

data Expr
  = Err
  | TypT
  | IntT
  | Int !Int
  | TupT ![Expr]
  | Tup ![Expr]
  | RecT ![(String, Expr)]
  | Rec ![(String, Expr)]
  | Get !Expr !String
  | Set !Expr ![(String, Expr)]
  | SumT ![(String, Expr)] ![Alt]
  | NamT !String ![Expr]
  | Ctr !String !String
  | Var !String
  | ForT !String !Expr
  | FunT !Expr !Expr
  | Lam !String !Expr
  | App !Expr !Expr
  | Ann !Expr !Expr
  | If !Expr !Expr !Expr
  | Let ![(String, Expr)] !Expr
  | Match ![Case]
  | TypeOf !Expr
  | Op !Operator
  deriving (Eq, Show)

data Operator
  = Add
  | Sub
  | Mul
  | Eq
  | Call !String !Expr
  deriving (Eq, Show)

type Env = [(String, Expr)]

type Alt = (String, ([String], Expr))

type Case = ([Pattern], Expr)

data Pattern
  = PAny
  | PVar !String
  | PAs !Pattern !String
  | PCtr !String ![Pattern]
  | PTup ![Pattern]
  | PRec ![(String, Pattern)]
  | PAnn !Pattern !Pattern
  | PEq !Expr
  | PIf !Pattern !Expr
  deriving (Eq, Show)

data TypeError
  = CtrNotInSumType !String !String ![String]
  | InfiniteType !String !Expr
  | NamedTypeArgsMismatch ![(String, Expr)] ![Expr]
  | NotACtr !String !Expr
  | NotARecord !Expr !Expr
  | NotASumType !String !Expr
  | NotATuple !Expr !Expr
  | NotAllCasesCovered
  | RedundantCases ![Case]
  | TypeMismatch !Expr !Expr
  | UndefinedCtr !String
  | UndefinedField !String ![(String, Expr)]
  | UndefinedType !String
  | UndefinedVar !String
  deriving (Eq, Show)

-- instance Show Operator where
--   show Add = "+"
--   show Sub = "-"
--   show Mul = "*"
--   show Eq = "=="
--   show (Call f t) = "@(" ++ f ++ " : " ++ show t ++ ")"

-- Syntax sugar --
forT :: [String] -> Expr -> Expr
forT xs a = foldr ForT a xs

funT :: [Expr] -> Expr -> Expr
funT xs a = foldr FunT a xs

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

asApp :: Expr -> (Expr, [Expr])
asApp a = do
  let asApp' :: Expr -> [Expr] -> (Expr, [Expr])
      asApp' (App fun arg) args = asApp' fun (arg : args)
      asApp' fun args = (fun, args)
  asApp' a []

let' :: (String, Expr) -> Expr -> Expr
let' (x, a) b = App (Lam x b) a

add :: Expr -> Expr -> Expr
add a b = app (Op Add) [a, b]

sub :: Expr -> Expr -> Expr
sub a b = app (Op Sub) [a, b]

mul :: Expr -> Expr -> Expr
mul a b = app (Op Mul) [a, b]

eq :: Expr -> Expr -> Expr
eq a b = app (Op Eq) [a, b]

boolT :: Expr
boolT = NamT "Bool" []

boolTDef :: Expr
boolTDef = SumT [] [("True", ([], boolT)), ("False", ([], boolT))]

true :: Expr
true = Ctr "Bool" "True"

false :: Expr
false = Ctr "Bool" "False"

prelude :: Env
prelude =
  [ ("Bool", boolTDef)
  ]

-- Fresh names --
newName :: [String] -> String -> String
newName existing x = case findNameIdx existing x of
  Just i -> x ++ show (i + 1)
  Nothing -> x

readNameIdx :: String -> String -> Maybe Int
readNameIdx "" x = readMaybe x
readNameIdx (ch : prefix) (ch' : x) | ch == ch' = readNameIdx prefix x
readNameIdx _ _ = Nothing

findNameIdx :: [String] -> String -> Maybe Int
findNameIdx [] _ = Nothing
findNameIdx (x : xs) prefix = case findNameIdx xs prefix of
  Just i -> case readNameIdx prefix x of
    Just j -> Just (max i j)
    Nothing -> Just i
  Nothing -> if prefix == x then Just 0 else readNameIdx prefix x

-- Type checking --
-- TODO: is this safe to do or should this be defined manually?
occurs :: String -> Expr -> Bool
occurs x a = compile [] a |> Core.occurs x

substitute :: String -> Expr -> Expr -> Expr
substitute x a b = decompile (compile [] (Let [(x, a)] b))

instantiate :: Env -> Expr -> (Expr, Env)
instantiate env (ForT x t) = do
  let y = newName (map fst env) x
  instantiate ((y, Var y) : env) (substitute x (Var y) t)
instantiate env t = (t, env)

unify :: Env -> Expr -> Expr -> Either TypeError Env
unify env a b = case (reduce env a, reduce env b) of
  (Var x, Var x') | x == x' -> Right env
  (Var x, b) | x `occurs` b -> Left (InfiniteType x b)
  (Var x, b) -> Right ((x, b) : env)
  (a, Var x) | x `occurs` a -> Left (InfiniteType x a)
  (a, Var x) -> Right ((x, a) : env)
  (ForT x a, b) -> do
    let (a', env') = instantiate env (ForT x a)
    unify env' a' b
  (a, ForT x b) -> do
    let (b', env') = instantiate env (ForT x b)
    unify env' a b'
  (FunT a1 a2, FunT b1 b2) -> unify2 env (a1, b1) (a2, b2)
  (App a1 a2, App b1 b2) -> unify2 env (a1, b1) (a2, b2)
  (a, a') | a == a' -> Right env
  (a, b) -> Left (TypeMismatch a b)

unify2 :: Env -> (Expr, Expr) -> (Expr, Expr) -> Either TypeError Env
unify2 env (a1, b1) (a2, b2) = do
  env <- unify env a1 b1
  unify env a2 b2

unifyMany :: Env -> [Expr] -> [Expr] -> Either TypeError Env
unifyMany env [] _ = Right env
unifyMany env _ [] = Right env
unifyMany env (x : xs) (y : ys) = do
  env <- unify env x y
  unifyMany env xs ys

infer :: Env -> Expr -> Either TypeError (Expr, Env)
infer env Err = Right (Err, env)
infer env TypT = Right (TypT, env)
infer env IntT = Right (TypT, env)
infer env (Int _) = Right (IntT, env)
infer env (TupT itemsT) = do
  (_, env) <- inferMany env itemsT
  Right (TypT, env)
infer env (Tup items) = do
  (itemsT, env) <- inferMany env items
  Right (TupT itemsT, env)
infer env (RecT fieldsT) = do
  (_, env) <- inferMany env (map snd fieldsT)
  Right (TypT, env)
infer env (Rec fields) = do
  let fields' = sortOn fst fields
  (fieldsT, env) <- inferMany env (map snd fields')
  Right (RecT (zip (map fst fields') fieldsT), env)
infer env (Get a x) = do
  (recT, env) <- infer env a
  case recT of
    RecT fieldsT -> case lookup x fieldsT of
      Just t -> Right (t, env)
      Nothing -> Left (UndefinedField x fieldsT)
    t -> Left (NotARecord a t)
infer env (Set a fields) = do
  (recT, env) <- infer env a
  case recT of
    RecT fieldsT -> do
      (ts, env) <- inferMany env (map snd fields)
      let fieldsT' = zip (map fst fields) ts
      let key (x, _) (y, _) = x == y
      Right (Rec (sortOn fst (unionBy key fieldsT' fieldsT)), env)
    t -> Left (NotARecord a t)
infer env (SumT vars alts) = do
  let bind (x, Var x') | x == x' = (x, Var x)
      bind (x, t) = (x, Ann (Var x) t)
  let env' = map bind vars ++ env
  let validAlt (cname, (_, t)) = do
        _ <- ctrType env cname
        infer env' t
  mapM_ validAlt alts
  Right (forT (map fst vars) (funT (map snd vars) TypT), env)
infer env (NamT name args) = case lookup name env of
  Just (SumT vars _) | length args /= length vars -> Left (NamedTypeArgsMismatch vars args)
  Just (SumT vars _) -> do
    _ <- unifyMany env (map TypeOf args) (map snd vars)
    Right (TypT, env)
  Just a -> Left (NotASumType name a)
  Nothing -> Left (UndefinedType name)
infer env (Ctr tname cname) = case lookup tname env of
  Just (SumT vars alts) -> case lookup cname alts of
    Just (_, t) -> Right (forT (map fst vars) t, env)
    Nothing -> Left (CtrNotInSumType tname cname (map fst alts))
  Just a -> Left (NotASumType tname a)
  Nothing -> Left (UndefinedType tname)
infer env (Var x) = case lookup x env of
  Just (Ann (Var x') t) | x == x' -> do
    (t, _) <- eval' env t
    Right (t, env)
  Just (Var x') | x == x' -> Right (Var x, env)
  Just a | x `occurs` a -> do
    (_, env) <- infer env (Lam x a)
    infer env (Var x)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (ForT x a) = do
  _ <- infer ((x, Var x) : env) a
  Right (TypT, env)
infer env (FunT a b) = do
  _ <- infer env a
  _ <- infer env b
  Right (TypT, env)
infer env (Lam x a) = do
  let tx = newName (map fst env) (x ++ "T")
  (t2, env) <- infer ((x, Ann (Var x) (Var tx)) : (tx, Var tx) : env) a
  (t1, env) <- infer env (Var x)
  case t1 of
    Var x -> Right (ForT x (FunT t1 t2), env)
    t1 -> Right (FunT t1 t2, env)
infer env (App a b) = do
  (ta, env) <- infer env a
  (tb, env) <- infer env b
  let tx = newName ("%" : map fst env) "%"
  env <- unify ((tx, Var tx) : env) (FunT tb (Var tx)) ta
  (t, _) <- eval' env (Var tx)
  Right (t, env)
infer env (Ann a t) = do
  (ta, env) <- infer env a
  env <- unify env t ta
  Right (t, env)
infer env (If cond then' else') = do
  (condT, env) <- infer env cond
  (thenT, env) <- infer env then'
  (elseT, env) <- infer env else'
  env <- unify env condT boolT
  env <- unify env thenT elseT
  (t, _) <- eval' env thenT
  Right (t, env)
infer env (Let env' a) = infer (env' ++ env) a
infer env (Match cases) = do
  a <- collapseCases env cases
  infer env a
infer env (TypeOf a) = do
  (t, env) <- infer env a
  infer env t
infer env (Op (Call _ t)) = Right (t, env)
infer env (Op Add) = Right (ForT "a" (funT [Var "a", Var "a"] (Var "a")), env)
infer env (Op Sub) = Right (ForT "a" (funT [Var "a", Var "a"] (Var "a")), env)
infer env (Op Mul) = Right (ForT "a" (funT [Var "a", Var "a"] (Var "a")), env)
infer env (Op Eq) = Right (ForT "a" (funT [Var "a", Var "a"] boolT), env)

inferMany :: Env -> [Expr] -> Either TypeError ([Expr], Env)
inferMany env [] = Right ([], env)
inferMany env (a : bs) = do
  (a, env) <- infer env a
  (bs, env) <- inferMany env bs
  Right (a : bs, env)

check :: Env -> Expr -> Either TypeError ()
check env expr = void (infer env expr)

checkMany :: Env -> [Expr] -> Either TypeError ()
checkMany env exprs = void (inferMany env exprs)

-- Pattern unpacking --
bindings :: Pattern -> [String]
bindings PAny = []
bindings (PVar x) = [x]
bindings (PAs p x) = x : bindings p
bindings (PCtr _ ps) = concatMap bindings ps
bindings (PTup ps) = concatMap bindings ps
bindings (PRec items) = concatMap (bindings . snd) items
bindings (PAnn p t) = bindings p ++ bindings t
bindings (PEq _) = []
bindings (PIf p _) = bindings p

unpack :: (Pattern, Expr) -> [(String, Expr)]
unpack (p, a) = map (\x -> (x, App (Match [([p], Var x)]) a)) (bindings p)

-- Pattern matching --
freeVars :: Expr -> [String]
freeVars Err = []
freeVars TypT = []
freeVars IntT = []
freeVars (Int _) = []
freeVars (TupT itemsT) = concatMap freeVars itemsT
freeVars (Tup items) = concatMap freeVars items
freeVars (RecT fieldsT) = concatMap (snd .> freeVars) fieldsT
freeVars (Rec fields) = concatMap (snd .> freeVars) fields
freeVars (Get a _) = freeVars a
freeVars (Set a fields) = freeVars a `union` concatMap (snd .> freeVars) fields
freeVars (SumT vars alts) = concatMap (snd .> snd .> freeVars) alts \\ map fst vars
freeVars (NamT _ args) = concatMap freeVars args
freeVars (Ctr _ _) = []
freeVars (Var x) = [x]
freeVars (ForT x a) = delete x (freeVars a)
freeVars (FunT a b) = freeVars a `union` freeVars b
freeVars (Lam x a) = delete x (freeVars a)
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Ann a b) = freeVars a `union` freeVars b
freeVars (If cond then' else') = freeVars (app cond [then', else'])
freeVars (Let env a) = freeVars a \\ map fst env
freeVars (Match cases) = concatMap freeVarsCase cases
freeVars (TypeOf a) = freeVars a
freeVars (Op (Call _ t)) = freeVars t
freeVars (Op _) = []

freeVarsCase :: Case -> [String]
freeVarsCase ([], a) = freeVars a
freeVarsCase (PAny : ps, a) = freeVarsCase (ps, a)
freeVarsCase (PVar x : ps, a) = delete x (freeVarsCase (ps, a))
freeVarsCase (PAs p x : ps, a) = delete x (freeVarsCase (p : ps, a))
freeVarsCase (PCtr _ qs : ps, a) = freeVarsCase (qs ++ ps, a)
freeVarsCase (PTup qs : ps, a) = freeVarsCase (qs ++ ps, a)
freeVarsCase (PRec items : ps, a) = freeVarsCase (map snd items ++ ps, a)
freeVarsCase (PAnn p t : ps, a) = freeVarsCase (p : t : ps, a)
freeVarsCase (PEq _ : ps, a) = freeVarsCase (ps, a)
freeVarsCase (PIf p _ : ps, a) = freeVarsCase (p : ps, a)

findName :: [Case] -> String
findName cases = do
  let firstPattern ([], _) = Nothing
      firstPattern (p : _, _) = Just p
  let patternName (PVar x) = Just x
      patternName (PAs _ x) = Just x
      patternName _ = Nothing
  let unique [] = []
      unique (x : xs) = x : unique (filter (/= x) xs)
  case unique (mapMaybe firstPattern cases |> mapMaybe patternName) of
    [x] -> x
    _inconsistentNames -> newName ("%" : freeVars (Match cases)) "%"

ctrType :: Env -> String -> Either TypeError String
ctrType env cname = case lookup cname env of
  Just (Ctr tname _) -> Right tname
  Just a -> Left (NotACtr cname a)
  Nothing -> Left (UndefinedCtr cname)

typeAlts :: Env -> String -> Either TypeError [Alt]
typeAlts env tname = case lookup tname env of
  Just (SumT _ alts) -> Right alts
  Just a -> Left (NotASumType tname a)
  Nothing -> Left (UndefinedType tname)

findAlts :: Env -> [Case] -> Either TypeError [Alt]
findAlts _ [] = Right []
findAlts env ((PCtr cname _ : _, _) : _) = do
  tname <- ctrType env cname
  typeAlts env tname
findAlts env ((PAs p _ : ps, a) : cases) = findAlts env ((p : ps, a) : cases)
findAlts env (_ : cases) = findAlts env cases

collapse :: String -> Alt -> [Case] -> [Case]
collapse _ _ [] = []
collapse x alt (([], _) : cases) = collapse x alt cases
collapse x alt ((PAny : ps, a) : cases) = (map (const PAny) ((snd .> fst) alt) ++ ps, a) : collapse x alt cases
collapse x alt ((PVar y : ps, a) : cases) = collapse x alt ((PAs PAny y : ps, a) : cases)
collapse x alt ((PAs p x' : ps, a) : cases) | x == x' = collapse x alt ((p : ps, a) : cases)
collapse x alt ((PAs p y : ps, a) : cases) = collapse x alt ((p : ps, Let [(y, Var x)] a) : cases)
collapse x alt ((PCtr ctr qs : ps, a) : cases) | fst alt == ctr = (qs ++ ps, a) : collapse x alt cases
collapse x alt ((PCtr _ _ : _, _) : cases) = collapse x alt cases
collapse x alt ((PTup qs : ps, a) : cases) | fst alt == "()" = (qs ++ ps, a) : collapse x alt cases
collapse x alt ((PTup _ : _, _) : cases) = collapse x alt cases
collapse x alt ((PRec fields : ps, a) : cases) | fst alt == "()" = do
  let def (y, p) = unpack (p, Get (Var x) y)
  case concatMap def fields of
    [] -> (ps, a) : collapse x alt cases
    defs -> (ps, Let defs a) : collapse x alt cases
collapse x alt ((PRec _ : _, _) : cases) = collapse x alt cases
collapse x alt ((PAnn p t : ps, a) : cases) = collapse x alt ((p : ps, App (Match [([t], a)]) (TypeOf a)) : cases)
collapse x alt ((PIf p cond : ps, a) : cases) = collapse x alt [(p : ps, If cond a (Match (collapse x alt cases)))]
collapse x alt ((PEq expr : ps, a) : cases) = collapse x alt ((PIf PAny (eq (Var x) expr) : ps, a) : cases)

collapseCases :: Env -> [Case] -> Either TypeError Expr
collapseCases _ [] = Left NotAllCasesCovered
collapseCases _ (([], a) : _) = Right a
collapseCases env cases = do
  let x = findName cases
  alts <- findAlts env cases
  case alts of
    [] -> Right (lam [x] (Match (collapse x ("", ([], TypT)) cases)))
    alts -> do
      let branch alt = Match (collapse x alt cases)
      Right (lam [x] (app (Var x) (map branch alts)))

-- Core conversions --
compile :: Env -> Expr -> Core.Term
compile _ Err = Core.Err
compile _ TypT = Core.TypT
compile _ IntT = Core.IntT
compile _ (Int i) = Core.Int i
compile env (TupT itemsT) = compile env (ForT "()" (funT itemsT (Var "()")))
compile env (Tup items) = compile env (Lam "()" (app (Var "()") items))
compile env (RecT fieldsT) = do
  let fieldsT' = sortOn fst fieldsT
  compile env (ForT "()" (funT (map snd fieldsT') (Var "()")))
compile env (Rec fields) = do
  let fields' = sortOn fst fields
  compile env (Lam "()" (app (Var "()") (map snd fields')))
compile env (Get a x) = case infer env a of
  Right (RecT fieldsT, _) -> do
    let xs = map fst fieldsT
    let getter = lam xs (Var x)
    compile env (App a getter)
  _notARecord -> Core.Err
compile env (Set a fields) = case infer env a of
  Right (RecT fieldsT, _) -> do
    let xs = map fst fieldsT
    let ys = xs `union` sort (map fst fields)
    let set x = (x, fromMaybe (Var x) (lookup x fields))
    let setter = lam xs (Rec (map set ys))
    compile env (App a setter)
  _notARecord -> Core.Err
compile env (SumT vars alts) = do
  let compileVar (x, a) = (x, compile env a)
  let compileAlt (cname, (args, t)) = (cname, (args, compile env t))
  Core.SumT (map compileVar vars) (map compileAlt alts)
compile env (NamT name args) = Core.NamT name (map (compile env) args)
compile env (Ctr tname cname) = do
  let alts = case typeAlts env tname of
        Right alts -> alts
        Left _ -> []
  let (args, _) = fromMaybe ([], TypT) (lookup cname alts)
  let xs = map (newName (map fst env)) args
  compile env (lam (xs ++ map fst alts) (app (Var cname) (map Var xs)))
compile env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Core.Var x
  Just a -> case compile ((x, Var x) : env) a of
    Core.Lam env y a' | x `Core.occurs` a' -> Core.Fix x (Core.Lam env y a')
    a' -> a'
  Nothing -> Core.Var x
compile env (ForT x a) = Core.ForT x (compile ((x, Var x) : env) a)
compile env (FunT a b) = Core.FunT (compile env a) (compile env b)
compile env (Lam x a) = Core.Lam [] x (compile ((x, Var x) : env) a)
compile env (App a b) = Core.App (compile env a) (compile env b)
compile env (Ann a _) = compile env a
compile env (If cond then' else') = compile env (app cond [then', else'])
compile env (Let env' a) = compile (env' ++ env) a
compile env (Match cases) = case collapseCases env cases of
  Right a -> compile env a
  Left _ -> Core.Err
compile env (TypeOf a) = case infer env a of
  Right (t, _) -> compile env t
  Left _ -> Core.Err
compile _ (Op Add) = Core.Op Core.Add
compile _ (Op Sub) = Core.Op Core.Sub
compile _ (Op Mul) = Core.Op Core.Mul
compile _ (Op Eq) = Core.Op Core.Eq
compile env (Op (Call f t)) = Core.Op (Core.Call f (compile env t))

decompile :: Core.Term -> Expr
decompile Core.Err = Err
decompile Core.TypT = TypT
decompile Core.IntT = IntT
decompile (Core.Int i) = Int i
decompile ((Core.NamT name args)) = NamT name (map decompile args)
decompile ((Core.SumT vars alts)) = do
  let decompileVar (x, a) = (x, decompile a)
  let decompileAlt (cname, (args, t)) = (cname, (args, decompile t))
  SumT (map decompileVar vars) (map decompileAlt alts)
decompile (Core.Var x) = Var x
decompile (Core.ForT x a) = ForT x (decompile a)
decompile ((Core.FunT a b)) = FunT (decompile a) (decompile b)
decompile (Core.Lam [] x a) = Lam x (decompile a)
decompile (Core.Lam env x a) = Lam x (Let (map (second decompile) env) (decompile a))
decompile (Core.App a b) = App (decompile a) (decompile b)
decompile (Core.Fix x a) = Let [(x, decompile a)] (Var x)
decompile (Core.Op Core.Add) = Op Add
decompile (Core.Op Core.Sub) = Op Sub
decompile (Core.Op Core.Mul) = Op Mul
decompile (Core.Op Core.Eq) = Op Eq
decompile (Core.Op (Core.Call f t)) = Op (Call f (decompile t))

canonicalize :: Env -> Expr -> Expr -> Either TypeError Expr
canonicalize env (Lam x body) (TupT itemsT) = case asApp body of
  (Var x', items) | x == x' -> do
    (itemsT', _) <- inferMany env items
    case () of
      () | length itemsT /= length itemsT' -> Left (TypeMismatch (Tup itemsT') (Tup itemsT))
      () -> do
        _ <- unifyMany env itemsT' itemsT
        Right (Tup items)
  _notATuple -> Left (NotATuple (Lam x body) (Tup itemsT))
canonicalize env (Lam x body) (RecT fieldsT) = case canonicalize env (Lam x body) (TupT (map snd fieldsT)) of
  Right (Tup items) -> Right (Rec (zip (map fst fieldsT) items))
  Right expr -> Left (NotARecord expr (Rec fieldsT))
  Left (TypeMismatch (Tup itemsT) (Tup _)) -> Left (TypeMismatch (Tup itemsT) (Rec fieldsT))
  Left err -> Left err
-- canonicalize env expr (NamT tname targs) = do
--   let (xs, body) = asLam expr
--   alts <- typeAlts env tname
--   case asApp body of
--     (Var cname, args)

-- canonicalize env (Lam x body) = do
--   let (xs, body') = asLam (Lam x body)
--   case asApp body' of
--     (Var cname, _) -> do
--       let ctrResult = do
--             tname <- ctrType env cname
--             alts <- typeAlts env tname
--             case map fst alts of
--               ctrs | ctrs == xs -> Right (Ctr tname cname)
--               _notACtr -> Left (NotACtr cname body')
--       case ctrResult of
--         Right ctr -> ctr
--         Left err -> Var (show err)
--     _notACtr -> Lam x (canonicalize env body)
canonicalize env expr type' = do
  check env (Ann expr type')
  Right expr

-- Evaluation --
reduce :: Env -> Expr -> Expr
reduce env expr = compile env expr |> Core.reduce [] |> decompile

eval :: Env -> Expr -> Expr
eval env a = compile env a |> Core.eval [] |> decompile

eval' :: Env -> Expr -> Either TypeError (Expr, Expr)
eval' env (RecT fieldsT) = do
  let fieldsT' = sortOn fst fieldsT
  itemsT <- evalMany env (map snd fieldsT')
  Right (RecT (zip (map fst fieldsT') (map fst itemsT)), TypT)
eval' env expr = do
  (type', env) <- infer env expr
  result <- canonicalize env (reduce env expr) type'
  Right (result, type')

evalMany :: Env -> [Expr] -> Either TypeError [(Expr, Expr)]
evalMany _ [] = Right []
evalMany env (a : bs) = do
  result <- eval' env a
  results <- evalMany env bs
  Right (result : results)