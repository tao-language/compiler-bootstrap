module Core where

import Data.List (intercalate)
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Lambda as L

data Expr
  = Var String
  | Int Int
  | App Expr [Expr]
  | Let [(String, Expr)] Expr
  | Cases [Case]
  | Call String
  | Ann Expr Type
  | For [String] Type
  deriving (Eq)

type Type = Expr

data Pattern
  = PAny
  | PInt Int
  | PCtr String [Pattern]
  | PAs Pattern String
  | PAnn Pattern Pattern
  deriving (Eq)

type Case = ([Pattern], Expr)

-- TODO: make Context opaque
type Context = [(String, [(String, Int)])]

instance Show Expr where
  show (Var x) = x
  show (Int i) = show i
  show (Let [] b) = show b
  show (Let ((x, a) : defs) b) = "#let " ++ x ++ " = " ++ show a ++ "; " ++ show (Let defs b)
  show (Cases cases) = do
    let showCase (ps, a) = unwords (map show ps) ++ " -> " ++ show a
    intercalate " | " (map showCase cases)
  -- TODO: show parentheses when necessary
  show (App a@(Cases _) bs) = "#match " ++ unwords (map show bs) ++ " | " ++ show a
  show (App a bs) = show a ++ " " ++ show bs
  show (Call f) = "#call " ++ f
  show (Ann a t) = show a ++ " : " ++ show t
  show (For [] t) = show t
  show (For xs t) = "@" ++ unwords xs ++ ". " ++ show t

instance Show Pattern where
  show PAny = "_"
  show (PInt i) = show i
  show (PAs PAny x) = x
  show (PAs p x) = x ++ "@" ++ show p
  show (PCtr ctr []) = ctr
  show (PCtr ctr ps) = "(" ++ ctr ++ " " ++ unwords (map show ps) ++ ")"
  show (PAnn p t) = show p ++ " : " ++ show t

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
  let expandAnn (Ann a t) = [a, t]
      expandAnn a = [a]
  a' <- compile ctx a
  bs' <- mapM (compile ctx) (concatMap expandAnn bs)
  Just (L.app a' bs')
compile ctx (Let defs b) = do
  let varToLambda (x, a) = do a' <- compile ctx a; Just (x, a')
  defs' <- mapM varToLambda defs
  b' <- compile ctx b
  Just (L.let' defs' b')
compile ctx (Cases cases) = compileCases ctx cases
compile _ (Call f) = Just (L.Call f)
compile ctx (Ann a t) = do
  a' <- compile ctx a
  t' <- compile ctx t
  Just (L.Ann a' t')
compile ctx (For [] t) = compile ctx t
compile ctx (For (x : xs) t) = do
  t' <- compile ctx (For xs t)
  Just (L.For x t')

compileCases :: Context -> [Case] -> Maybe L.Term
compileCases _ [] = Nothing
compileCases ctx (([], a) : _) = compile ctx a
compileCases ctx cases = do
  let ps = mapMaybe (\(ps, _) -> listToMaybe ps) cases
  let x = case inferName "" ps of
        "" -> L.newName "%" (concatMap (\(_, a) -> maybe [] L.freeVariables (compile ctx a)) cases)
        x -> x
  let isAnn (PAnn _ _) = True
      isAnn _ = False
  let expandAnn ([], a) = ([], a)
      expandAnn (PAnn p t : ps, a) = (p : t : ps, a)
      expandAnn (p : ps, a) = (p : PAny : ps, a)
  let cases' = if any isAnn ps then map expandAnn cases else cases
  case findAlts ctx ps of
    Just alts -> do
      let compileAlt alt = compileCases ctx (mapMaybe (chompCtr x alt) cases')
      alts' <- mapM compileAlt alts
      Just (L.Lam x (L.app (L.Var x) alts'))
    Nothing -> case cases' of
      (PInt i : ps, a) : cases' -> do
        let cond = L.eq (L.Var x) (L.Int i)
        then' <- compileCases ctx [(ps, a)]
        else' <- compileCases ctx cases'
        case else' of
          L.Lam x' else' | x == x' -> Just (L.Lam x (L.app cond [then', else']))
          _ -> Just (L.Lam x (L.app cond [then', L.App else' (L.Var x)]))
      _ -> fmap (L.Lam x) (compileCases ctx (mapMaybe (chompDefault x) cases'))

-- Helper functions
inferName :: String -> [Pattern] -> String
inferName x [] = x
inferName "" (PAs _ x : ps) = inferName x ps
inferName x (PAs _ x' : ps) | x == x' = inferName x' ps
inferName _ (PAs _ _ : _) = ""
inferName x (PAnn p _ : ps) = inferName x (p : ps)
inferName x (_ : ps) = inferName x ps

findAlts :: Context -> [Pattern] -> Maybe [(String, Int)]
findAlts _ [] = Nothing
findAlts ctx (PCtr ctr _ : _) = lookup ctr ctx
findAlts ctx (PAs p _ : ps) = findAlts ctx (p : ps)
findAlts ctx (PAnn p _ : ps) = findAlts ctx (p : ps)
findAlts ctx (_ : ps) = findAlts ctx ps

chompDefault :: String -> Case -> Maybe Case
chompDefault _ (PAny : ps, a) = Just (ps, a)
chompDefault x (PAs p x' : ps, a) | x == x' = chompDefault x (p : ps, a)
chompDefault x (PAs p y : ps, a) = chompDefault x (p : ps, Let [(y, Var x)] a)
-- chompDefault x (PAnn p _ : ps, a) = chompDefault x (p : ps, a)
chompDefault _ _ = Nothing

chompCtr :: String -> (String, Int) -> Case -> Maybe Case
chompCtr _ (_, n) (PAny : ps, a) = Just (replicate n PAny ++ ps, a)
chompCtr x (ctr, n) (PAs p x' : ps, a) | x == x' = chompCtr x (ctr, n) (p : ps, a)
chompCtr x (ctr, n) (PAs p y : ps, a) = chompCtr x (ctr, n) (p : ps, Let [(y, Var x)] a)
chompCtr _ (ctr, _) (PCtr ctr' qs : ps, a) | ctr == ctr' = Just (qs ++ ps, a)
-- TODO: chompCtr PAnn
chompCtr _ _ _ = Nothing

bindings :: Pattern -> [String]
bindings (PAs p x) = x : bindings p
bindings (PCtr ctr (p : ps)) = bindings p ++ bindings (PCtr ctr ps)
bindings _ = []
