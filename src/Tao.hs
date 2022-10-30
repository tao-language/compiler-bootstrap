module Tao where

import qualified Core
import Data.List (foldl')

data Expr
  = BoolT
  | IntT
  | Typ ![Alt]
  | Bool !Bool
  | Int !Int
  | Var !String
  | Lam !String !Expr
  | App !Expr !Expr
  | Fun !Expr !Expr
  | Ann !Expr !Type
  | Call !Core.Primitive !Type
  | If !Expr !Expr !Expr
  | Ctr !String !String
  | Match ![Case]
  | Let ![(String, Expr)] !Expr
  deriving (Eq, Show)

data Type
  = T ![String] !Expr
  deriving (Eq, Show)

data Pattern
  = PAny
  | PAs !Pattern !String
  | PCtr !String ![Pattern]
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
  | UnmatchedPatterns ![Pattern]
  | CaseTypeMismatch !String !String
  | CaseCtrArgsMismatch ![String] ![Pattern]
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

let' :: (String, Expr) -> Expr -> Expr
let' (x, a) b = App (Lam x b) a

pvar :: String -> Pattern
pvar = PAs PAny

add' :: Expr
add' = Call Core.Add (T ["a", "b"] (fun [Var "a", Var "a"] (Var "b")))

add :: Expr -> Expr -> Expr
add a b = app add' [a, b]

sub' :: Expr
sub' = Call Core.Sub (T ["a", "b"] (fun [Var "a", Var "a"] (Var "b")))

sub :: Expr -> Expr -> Expr
sub a b = app sub' [a, b]

mul' :: Expr
mul' = Call Core.Mul (T ["a", "b"] (fun [Var "a", Var "a"] (Var "b")))

mul :: Expr -> Expr -> Expr
mul a b = app mul' [a, b]

eq' :: Expr
eq' = Call Core.Eq (T ["a"] (fun [Var "a", Var "a"] BoolT))

eq :: Expr -> Expr -> Expr
eq a b = app eq' [a, b]

bindings :: Pattern -> [String]
bindings PAny = []
bindings (PAs p x) = x : bindings p
bindings (PCtr _ []) = []
bindings (PCtr ctr (p : ps)) = bindings p ++ bindings (PCtr ctr ps)
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
  Just (Typ alts) -> Right alts
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
      infer' "" ((PAs _ x : _, _) : cases) = infer' x cases
      infer' x ((PAs _ x' : _, _) : cases) | x == x' = infer' x cases
      infer' _ ((PAs _ _ : _, _) : _) = ""
      infer' x (_ : cases) = infer' x cases
  let freeVars :: Case -> [String]
      freeVars (_, a) = case compile a of
        Right a' -> Core.freeVariables a'
        Left _ -> []
  case infer' "" cases of
    "" -> Core.newName ("%" : concatMap freeVars cases) "%"
    x -> x

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
collapse x alt ((PAs p x' : ps, a) : cases) | x == x' = collapse x alt ((p : ps, a) : cases)
collapse x alt ((PAs p y : ps, a) : cases) = collapse x alt ((p : ps, let' (y, Var x) a) : cases)
collapse x alt ((PCtr ctr qs : ps, a) : cases) | fst alt == ctr = (qs ++ ps, a) : collapse x alt cases
collapse x alt ((PIf p cond : ps, a) : cases) = collapse x alt [(p : ps, If cond a (Match (collapse x alt cases)))]
collapse x alt ((PEq expr : ps, a) : cases) = collapse x alt ((PIf PAny (eq (Var x) expr) : ps, a) : cases)
collapse x alt (_ : cases) = collapse x alt cases

compile :: Expr -> Either Error Core.Expr
compile (Let _ BoolT) = compile (Typ [("True", []), ("False", [])])
compile (Let _ IntT) = Right Core.IntT
compile (Let _ (Typ alts)) = Right (Core.Typ alts)
compile (Let _ (Bool True)) = compile (lam ["True", "False"] (Var "True"))
compile (Let _ (Bool False)) = compile (lam ["True", "False"] (Var "False"))
compile (Let _ (Int i)) = Right (Core.Int i)
compile (Let env (Var x)) = case lookup x env of
  Just (Var x') | x == x' -> Right (Core.Var x)
  Just a -> case compile (Let ((x, Var x) : env) a) of
    Right a' | x `Core.occurs` a' -> Right (Core.Fix x a')
    other -> other
  Nothing -> Right (Core.Var x)
compile (Let env (Lam x a)) = do
  a' <- compile (Let ((x, Var x) : env) a)
  Right (Core.Lam [] x a')
compile (Let env (App a b)) = do
  a' <- compile (Let env a)
  b' <- compile (Let env b)
  Right (Core.App a' b')
compile (Let env (Fun a b)) = do
  a' <- compile (Let env a)
  b' <- compile (Let env b)
  Right (Core.Fun a' b')
compile (Let env (Ann a (T xs t))) = do
  a' <- compile (Let env a)
  t' <- compile (Let (map (\x -> (x, Var x)) xs ++ env) t)
  Right (Core.Ann a' (Core.T xs t'))
compile (Let env (Call f (T xs t))) = do
  t' <- compile (Let (map (\x -> (x, Var x)) xs ++ env) t)
  Right (Core.Call f (Core.T xs t'))
compile (Let env (If cond then_ else_)) = do
  cond' <- compile (Let env cond)
  then' <- compile (Let env then_)
  else' <- compile (Let env else_)
  Right (Core.App (Core.App cond' then') else')
compile (Let env (Ctr tname cname)) = do
  alts <- typeAlts env tname
  args <- altArgs alts cname
  let xs = map (Core.newName (map fst env)) args
  compile (lam (xs ++ map fst alts) (app (Var cname) (map Var xs)))
compile (Let _ (Match [])) = Left NotAllCasesCovered
compile (Let _ (Match (([], a) : _))) = compile a
compile (Let env (Match cases)) = do
  let x = inferName cases
  case findAlts env cases of
    Right [] -> compile (lam [x] (Match (collapse x ("", []) cases)))
    Right alts -> compile (lam [x] (app (Var x) (map (\alt -> Match (collapse x alt cases)) alts)))
    Left err -> Left err
compile (Let env (Let env' a)) = compile (Let (env ++ env') a)
compile a = compile (Let [] a)

eval :: Expr -> Either Error Core.Expr
eval expr = do
  expr' <- compile expr
  Right (Core.eval expr' [])
