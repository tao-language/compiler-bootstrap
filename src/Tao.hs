module Tao where

import qualified Core
import Data.Bifunctor (Bifunctor (second))
import Data.List (foldl')

data Expr
  = IntT
  | Typ !Int
  | Bool !Bool
  | Int !Int
  | Var !String
  | Lam !String !Expr
  | App !Expr !Expr
  | Fun !Expr !Expr
  | Ann !Expr !Expr
  | For !String !Expr
  | TypeDef !String ![Alt]
  | If !Expr !Expr !Expr
  | Ctr !String !String
  | Match ![Case]
  | Let ![(String, Expr)] !Expr
  | Call !String !Expr
  | TypeOf !Expr
  | Add
  | Sub
  | Mul
  | Eq
  deriving (Eq, Show)

data Pattern
  = PAny
  | PVar !String
  | PAs !Pattern !String
  | PCtr !String ![Pattern]
  | PAnn !Pattern !Pattern
  | PIf !Pattern !Expr
  | PEq !Expr
  deriving (Eq, Show)

type Alt = (String, [String])

type Case = ([Pattern], Expr)

type Env = [(String, Expr)]

data Error
  = UndefinedType !String
  | UndefinedCtr !String
  | NotAType !Expr
  | NotACtr !Expr
  | NotAllCasesCovered
  | CaseNumPatternsMismatch !Int !Int
  | UnmatchedPatterns ![Pattern]
  | CaseTypeMismatch !String !String
  | CaseCtrArgsMismatch ![String] ![Pattern]
  | TypeError !Core.TypeError !Core.Expr
  deriving (Eq, Show)

-- instance Show Expr where
--   show (Var x) = x
--   show (Int i) = show i
--   show (Let [] b) = show b
--   show (Let ((x, a) : defs) b) = "#let " ++ x ++ " = " ++ show a ++ "; " ++ show (Let defs b)
--   show (Cases cases) = do
--     let showCase (ps, a) = unwords (map show ps) ++ " -> " ++ show a
--     intercalate " | " (map showCase cases)
--   -- TODO: show parentheses when necessary
--   show (App a@(Cases _) bs) = "#match " ++ unwords (map show bs) ++ " | " ++ show a
--   show (App a bs) = show a ++ " " ++ show bs
--   show (Call f) = "#call " ++ f
--   -- show (Ann a t) = show a ++ " : " ++ show t
--   show IntT = "#Int"
--   show (Fun a b) = show a ++ " => " ++ show b

-- instance Show Pattern where
--   show PAny = "_"
--   show (PInt i) = show i
--   show (PAs PAny x) = x
--   show (PAs p x) = x ++ "@" ++ show p
--   show (PCtr ctr []) = ctr
--   show (PCtr ctr ps) = "(" ++ ctr ++ " " ++ unwords (map show ps) ++ ")"
--   show (PAnn p t) = show p ++ " : " ++ show t

-- Syntax sugar
lam :: [String] -> Expr -> Expr
lam xs a = foldr Lam a xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

fun :: [Expr] -> Expr -> Expr
fun xs a = foldr Fun a xs

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

add :: Expr -> Expr -> Expr
add a b = app Add [a, b]

sub :: Expr -> Expr -> Expr
sub a b = app Sub [a, b]

mul :: Expr -> Expr -> Expr
mul a b = app Mul [a, b]

eq :: Expr -> Expr -> Expr
eq a b = app Eq [a, b]

bindings :: Pattern -> [String]
bindings PAny = []
bindings (PVar x) = [x]
bindings (PAs p x) = x : bindings p
bindings (PCtr _ []) = []
bindings (PCtr ctr (p : ps)) = bindings p ++ bindings (PCtr ctr ps)
bindings (PAnn p t) = bindings p ++ bindings t
bindings (PIf p _) = bindings p
bindings (PEq _) = []

unpack :: (Pattern, Expr) -> [(String, Expr)]
unpack (p, a) = map (\x -> (x, App (Match [([p], Var x)]) a)) (bindings p)

-- Context --
-- defineType :: String -> [String] -> [TypeAlt] -> [TypeCtr] -> Env -> ([TypeCtr], Env)
-- defineType name vars alts ctrs env = (map (\(ctr, _) -> (ctr, alts)) alts ++ ctrs, env)

ctrType :: Env -> String -> Either Error String
ctrType env cname = case lookup cname env of
  Just (Ctr tname _) -> Right tname
  Just a -> Left (NotACtr a)
  Nothing -> Left (UndefinedCtr cname)

typeAlts :: Env -> String -> Either Error [Alt]
typeAlts env tname = case lookup tname env of
  Just (TypeDef _ alts) -> Right alts
  Just a -> Left (NotAType a)
  Nothing -> Left (UndefinedType tname)

altArgs :: [Alt] -> String -> Either Error [String]
altArgs args cname = case lookup cname args of
  Just args -> Right args
  Nothing -> Left (UndefinedCtr cname)

inferName :: [Case] -> String
inferName cases = do
  let infer' :: String -> [Case] -> String
      infer' x [] = x
      infer' "" ((PVar x : _, _) : cases) = infer' x cases
      infer' x ((PVar x' : _, _) : cases) | x == x' = infer' x cases
      infer' _ ((PVar _ : _, _) : _) = ""
      infer' x ((PAs _ y : ps, a) : cases) = infer' x ((PVar y : ps, a) : cases)
      infer' x (_ : cases) = infer' x cases
  let freeVars :: Case -> [String]
      freeVars (_, a) = case compile [] a of
        Right a' -> Core.freeVariables a'
        Left _ -> []
  case infer' "" cases of
    "" -> Core.newName ("%" : concatMap freeVars cases) "%"
    x -> x

validatePatterns :: [Case] -> Either Error ()
validatePatterns [] = Right ()
validatePatterns ((ps, _) : cases) = do
  let validate :: Int -> [Case] -> Either Error ()
      validate _ [] = Right ()
      validate n ((ps, _) : _) | length ps /= n = Left (CaseNumPatternsMismatch n (length ps))
      validate n (_ : cases) = validate n cases
  validate (length ps) cases

validateCases :: Env -> String -> [Case] -> Either Error ()
validateCases _ _ [] = Right ()
validateCases env tname ((PCtr cname ps : _, _) : cases) = do
  tname' <- ctrType env cname
  alts <- typeAlts env tname'
  args <- altArgs alts cname
  case () of
    () | tname /= tname' -> Left (CaseTypeMismatch tname tname')
    () | length args /= length ps -> Left (CaseCtrArgsMismatch args ps)
    () -> validateCases env tname cases
validateCases env tname ((PAs p _ : ps, a) : cases) = validateCases env tname ((p : ps, a) : cases)
validateCases env tname (_ : cases) = validateCases env tname cases

findAlts :: Env -> [Case] -> Either Error [Alt]
findAlts _ [] = Right []
findAlts env cases@((PCtr cname _ : _, _) : _) = do
  tname <- ctrType env cname
  alts <- typeAlts env tname
  _ <- validateCases env tname cases
  Right alts
findAlts env ((PAs p _ : ps, a) : cases) = findAlts env ((p : ps, a) : cases)
findAlts env (_ : cases) = findAlts env cases

collapse :: String -> Alt -> [Case] -> [Case]
collapse _ _ [] = []
collapse x alt ((PAny : ps, a) : cases) = (map (const PAny) (snd alt) ++ ps, a) : collapse x alt cases
collapse x alt ((PVar y : ps, a) : cases) = collapse x alt ((PAs PAny y : ps, a) : cases)
collapse x alt ((PAs p x' : ps, a) : cases) | x == x' = collapse x alt ((p : ps, a) : cases)
collapse x alt ((PAs p y : ps, a) : cases) = collapse x alt ((p : ps, Let [(y, Var x)] a) : cases)
collapse x alt ((PCtr ctr qs : ps, a) : cases) | fst alt == ctr = (qs ++ ps, a) : collapse x alt cases
collapse x alt ((PAnn p t : ps, a) : cases) = collapse x alt ((p : ps, App (Match [([t], a)]) (TypeOf a)) : cases)
collapse x alt ((PIf p cond : ps, a) : cases) = collapse x alt [(p : ps, If cond a (Match (collapse x alt cases)))]
collapse x alt ((PEq expr : ps, a) : cases) = collapse x alt ((PIf PAny (eq (Var x) expr) : ps, a) : cases)
collapse x alt (_ : cases) = collapse x alt cases

fromCore :: Core.Expr -> Expr
fromCore Core.IntT = IntT
fromCore (Core.Typ u) = Typ u
fromCore (Core.Int i) = Int i
fromCore (Core.Var x) = Var x
fromCore (Core.Lam env x a) = Let (map (second fromCore) env) (Lam x (fromCore a))
fromCore (Core.App a b) = App (fromCore a) (fromCore b)
fromCore (Core.Fun a b) = Fun (fromCore a) (fromCore b)
fromCore (Core.Ann a t) = Ann (fromCore a) (fromCore t)
fromCore (Core.For x a) = For x (fromCore a)
fromCore (Core.Fix x a) = Let [(x, fromCore a)] (Var x)
fromCore (Core.Call f t) = Call f (fromCore t)
fromCore Core.Add = Add
fromCore Core.Sub = Sub
fromCore Core.Mul = Mul
fromCore Core.Eq = Eq

compile :: Env -> Expr -> Either Error Core.Expr
compile _ IntT = Right Core.IntT
compile _ (Typ u) = Right (Core.Typ u)
compile _ (TypeDef x alts) = compile [] (For x (fun (map (const (Var x)) alts) (Var x)))
compile _ (Bool True) = compile [] (lam ["True", "False"] (Var "True"))
compile _ (Bool False) = compile [] (lam ["True", "False"] (Var "False"))
compile _ (Int i) = Right (Core.Int i)
compile env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Right (Core.Var x)
  Just a -> case compile ((x, Var x) : env) a of
    Right a' | x `Core.occurs` a' -> Right (Core.Fix x a')
    other -> other
  Nothing -> Right (Core.Var x)
compile env (Lam x a) = do
  a' <- compile ((x, Var x) : env) a
  Right (Core.Lam [] x a')
compile env (App a b) = do
  a' <- compile env a
  b' <- compile env b
  Right (Core.App a' b')
compile env (Fun a b) = do
  a' <- compile env a
  b' <- compile env b
  Right (Core.Fun a' b')
compile env (Ann a t) = do
  a' <- compile env a
  t' <- compile env t
  Right (Core.Ann a' t')
compile env (For x a) = do
  a' <- compile ((x, Var x) : env) a
  Right (Core.For x a')
compile env (If cond then_ else_) = do
  cond' <- compile env cond
  then' <- compile env then_
  else' <- compile env else_
  Right (Core.App (Core.App cond' then') else')
compile env (Ctr tname cname) = do
  alts <- typeAlts env tname
  args <- altArgs alts cname
  let xs = map (Core.newName (map fst env)) args
  compile env (lam (xs ++ map fst alts) (app (Var cname) (map Var xs)))
compile _ (Match []) = Left NotAllCasesCovered
compile env (Match (([], a) : _)) = compile env a
compile env (Match cases) = do
  _ <- validatePatterns cases
  let x = inferName cases
  case findAlts env cases of
    Right [] -> compile env (lam [x] (Match (collapse x ("", []) cases)))
    Right alts -> compile env (lam [x] (app (Var x) (map (\alt -> Match (collapse x alt cases)) alts)))
    Left err -> Left err
compile env (Let env' a) = compile (env ++ env') a
compile env (Call f t) = do
  t' <- compile env t
  Right (Core.Call f t')
compile env (TypeOf a) = do
  a' <- compile env a
  case Core.infer [] a' of
    Right (t, _) -> Right t
    Left err -> Left (TypeError err a')
compile _ Add = Right Core.Add
compile _ Sub = Right Core.Sub
compile _ Mul = Right Core.Mul
compile _ Eq = Right Core.Eq

compileEnv :: Env -> Either Error Core.Env
compileEnv env = do
  let compileDef :: (String, Expr) -> Either Error (String, Core.Expr)
      compileDef (x, a) = do
        a' <- compile env a
        Right (x, Core.eval [] a')
  mapM compileDef env

eval :: Env -> Expr -> Either Error Core.Expr
eval env expr = do
  expr' <- compile env expr
  case Core.infer [] expr' of
    Right _ -> Right (Core.eval [] expr')
    Left err -> Left (TypeError err expr')
