module Core where

import Data.List (intercalate)
import qualified Lambda as L

data Expr
  = Var String
  | Int Int
  | App Expr [Expr]
  | Let [(String, Expr)] Expr
  | Cases [Case]
  | Call String
  deriving (Eq)

data Pattern
  = PAny
  | PInt Int
  | PAs Pattern String
  | PCtr String [Pattern]
  deriving (Eq)

type Case = ([Pattern], Expr)

-- TODO: make Context opaque
type Context = [(String, [(String, Int)])]

instance Show Expr where
  show (Var x) = x
  show (Int i) = show i
  show (Let [] b) = show b
  show (Let ((x, a) : vars) b) = "#let " ++ x ++ " = " ++ show a ++ "; " ++ show (Let vars b)
  show (Cases cases) = do
    let showCase (ps, a) = unwords (map show ps) ++ " -> " ++ show a
    intercalate " | " (map showCase cases)
  -- TODO: show parentheses when necessary
  show (App a@(Cases _) bs) = "#match " ++ unwords (map show bs) ++ " | " ++ show a
  show (App a bs) = show a ++ " " ++ show bs
  show (Call f) = "#call " ++ f

instance Show Pattern where
  show PAny = "_"
  show (PInt i) = show i
  show (PAs PAny x) = x
  show (PAs p x) = x ++ "@" ++ show p
  show (PCtr ctr []) = ctr
  show (PCtr ctr ps) = "(" ++ ctr ++ " " ++ unwords (map show ps) ++ ")"

-- Syntax sugar
match :: [Expr] -> [Case] -> Expr
match [] (([], a) : _) = a
match [] cases = Cases cases
match args cases = App (Cases cases) args

lambda :: [Pattern] -> Expr -> Expr
lambda ps a = match [] [(ps, a)]

unpack :: (Pattern, Expr) -> [(String, Expr)]
unpack (p, a) = do
  let bind :: (Pattern, Expr) -> String -> (String, Expr)
      bind (PAny, a) x = (x, a)
      bind (PAs p x, a) x' | x == x' = bind (p, a) x
      bind (p, a) x = (x, match [a] [([p], Var x)])
  map (bind (p, a)) (bindings p)

add :: Expr -> Expr -> Expr
add a b = App (Call "+") [a, b]

sub :: Expr -> Expr -> Expr
sub a b = App (Call "-") [a, b]

mul :: Expr -> Expr -> Expr
mul a b = App (Call "*") [a, b]

eq :: Expr -> Expr -> Expr
eq a b = App (Call "==") [a, b]

-- Context
empty :: Context
empty = []

defineType :: String -> [String] -> [(String, Int)] -> Context -> Context
defineType _ _ alts ctx = map (\(ctr, _) -> (ctr, alts)) alts ++ ctx

-- Compile to Lambda calculus
compile :: Context -> Expr -> Maybe L.Term
compile _ (Var x) = Just (L.Var x)
compile _ (Int i) = Just (L.Int i)
compile ctx (App a bs) = do
  a' <- compile ctx a
  bs' <- mapM (compile ctx) bs
  Just (L.app a' bs')
compile ctx (Let vars b) = do
  let varToLambda (x, a) = do a' <- compile ctx a; Just (x, a')
  vars' <- mapM varToLambda vars
  b' <- compile ctx b
  Just (L.let' vars' b')
compile ctx (Cases cases) = compileCases ctx "" cases
compile _ (Call f) = Just (L.Call f)

compileCases :: Context -> String -> [Case] -> Maybe L.Term
compileCases _ _ [] = Nothing
compileCases ctx _ (([], a) : _) = compile ctx a
compileCases ctx "" cases = do
  let x = case inferName "" cases of
        "" -> do
          let freeVars (_, a) = maybe [] L.freeVariables (compile ctx a)
          L.newName "%" (concatMap freeVars cases)
        x -> x
  compileCases ctx x cases
compileCases ctx x cases =
  case findAlts ctx cases of
    Just alts -> do
      let compileAlt alt = compileCases ctx "" (remaining (matchCtr x alt) cases)
      alts' <- mapM compileAlt alts
      Just (L.Lam x (L.app (L.Var x) alts'))
    Nothing -> case cases of
      (PAs p x' : ps, a) : cases | x == x' -> compileCases ctx x ((p : ps, a) : cases)
      (PAs p y : ps, a) : cases -> compileCases ctx x ((p : ps, Let [(y, Var x)] a) : cases)
      (PInt i : ps, a) : cases -> do
        let cond = L.eq (L.Var x) (L.Int i)
        then' <- compileCases ctx "" [(ps, a)]
        else' <- compileCases ctx "" cases
        Just (L.Lam x (L.app cond [then', L.App else' (L.Var x)]))
      _ -> do
        cases' <- compileCases ctx x (remaining (matchAny x) cases)
        Just (L.Lam x cases')

-- Helper functions
inferName :: String -> [Case] -> String
inferName "" ((PAs _ x : _, _) : cases) = inferName x cases
inferName x ((PAs _ x' : _, _) : cases) | x == x' = inferName x' cases
inferName _ ((PAs _ _ : _, _) : _) = ""
inferName x _ = x

findAlts :: Context -> [([Pattern], Expr)] -> Maybe [(String, Int)]
findAlts _ [] = Nothing
findAlts ctx ((PCtr ctr _ : _, _) : _) = lookup ctr ctx
findAlts ctx (_ : cases) = findAlts ctx cases

matchAny :: String -> Case -> Maybe Case
matchAny _ (PAny : ps, a) = Just (ps, a)
matchAny _ _ = Nothing

matchCtr :: String -> (String, Int) -> Case -> Maybe Case
matchCtr _ (_, n) (PAny : ps, a) = Just (replicate n PAny ++ ps, a)
matchCtr x (ctr, n) (PAs p y : ps, a) = matchCtr x (ctr, n) (p : ps, Let [(y, Var x)] a)
matchCtr _ (ctr, _) (PCtr ctr' qs : ps, a) | ctr == ctr' = Just (qs ++ ps, a)
matchCtr _ _ _ = Nothing

remaining :: (Case -> Maybe Case) -> [Case] -> [Case]
remaining f (case' : cases) = case f case' of
  Just case' -> case' : remaining f cases
  Nothing -> remaining f cases
remaining _ _ = []

bindings :: Pattern -> [String]
bindings (PAs p x) = x : bindings p
bindings (PCtr ctr (p : ps)) = bindings p ++ bindings (PCtr ctr ps)
bindings _ = []
