module Tao where

import Control.Monad (mapAndUnzipM)
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap), second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (intercalate, isPrefixOf, union)
import Data.List.Split (splitWhen)
import Data.Maybe (fromMaybe)

data Expr
  = Int Int
  | Num Double
  | Var String
  | Tag String [Expr]
  | Tuple [Expr]
  | Record [(String, (Maybe Expr, Maybe Expr))]
  | Fun Expr Expr
  | App Expr Expr
  | Or Expr Expr
  | Ann Expr Type
  | Call String [Expr]
  | Let [(String, Type)] Pattern Expr Expr
  | Bind [(String, Type)] Pattern Expr Expr
  | Match [Expr] [Case]
  | MatchFun [Case]
  | Trait Expr String
  | TraitFun String
  | Select Expr [(String, Expr)]
  | SelectFun [(String, Expr)]
  | With Expr [(String, Expr)]
  | WithFun [(String, Expr)]
  | IfElse Expr Expr Expr
  | Meta C.Metadata Expr
  | Err
  deriving (Eq, Show)

data Case
  = Case [Pattern] (Maybe Expr) Expr
  deriving (Eq, Show)

data Pattern
  = PAny
  | PInt Int
  | PNum Double
  | PVar String
  | PTag String [Pattern]
  | PTuple [Pattern]
  | PFun Pattern Pattern
  | POr Pattern Pattern
  | PEq Expr
  | PMeta C.Metadata Pattern
  | PErr
  deriving (Eq, Show)

data Stmt
  = Import String String [(String, String)] -- import @pkg:module as alias (a, b, c)
  | Define [(String, Type)] Pattern Expr
  | Test Expr Pattern
  | MetaStmt C.Metadata Stmt
  deriving (Eq, Show)

data Module = Module
  { name :: String,
    stmts :: [Stmt]
  }
  deriving (Eq, Show)

data Package = Package
  { name :: String,
    modules :: [Module]
  }
  deriving (Eq, Show)

type Type = Expr

type Context = [(String, Expr)]

data TestError
  = TestEqError Expr Expr Pattern
  deriving (Eq, Show)

-- Syntax sugar
kind :: Expr
kind = Tag "Type" []

intT :: Expr
intT = Tag "Int" []

intT' :: Int -> Expr
intT' i = Int i `Or` intT

pIntT :: Pattern
pIntT = PTag "Int" []

numT :: Expr
numT = Tag "Num" []

numT' :: Double -> Expr
numT' n = Num n `Or` numT

pNumT :: Pattern
pNumT = PTag "Num" []

ok :: Expr -> Expr
ok x = Tag "Ok" [x]

err :: Expr -> Expr
err e = Tag "Error" [e]

record :: [(String, Expr)] -> Expr
record fields = Record (map (\(x, v) -> (x, (Just v, Nothing))) fields)

pRecord :: [(String, Pattern)] -> Pattern
pRecord = error "TODO: Tao.pRecord"

match :: [Expr] -> [Case] -> Expr
match [] (Case [] Nothing b : _) = b
match (Var x : args) cases = do
  let matchVar (Case (PVar x' : ps) guard b) | x == x' = Just (Case ps guard b)
      matchVar (Case (PAny : ps) guard b) | x `notElem` freeVars b = Just (Case ps guard b)
      matchVar _ = Nothing
  case mapM matchVar cases of
    Just cases' -> match args cases'
    Nothing -> app (MatchFun cases) (Var x : args)
match args cases = app (MatchFun cases) args

lambda :: [String] -> Expr -> Expr
lambda xs b = match [] [Case (map PVar xs) Nothing b]

lambdaOf :: String -> Expr -> ([String], Expr)
lambdaOf _ (MatchFun []) = ([], Err)
lambdaOf prefix (MatchFun cases) = do
  let xs = lambdaArgs prefix cases
  (xs, match (map Var xs) cases)
lambdaOf prefix (Meta m a) = do
  let (xs, a') = lambdaOf prefix a
  (xs, Meta m a')
lambdaOf _ a = ([], a)

lambdaArgs :: String -> [Case] -> [String]
lambdaArgs prefix cases = case popCases cases of
  Just (ps, cases') -> do
    let x = case patternsName ps of
          Just x -> x
          Nothing -> C.newName (prefix : freeVars cases') prefix
    x : lambdaArgs prefix cases'
  Nothing -> []

popCases :: [Case] -> Maybe ([Pattern], [Case])
popCases = mapAndUnzipM popCase

popCase :: Case -> Maybe (Pattern, Case)
popCase (Case [] guard a) = Nothing
popCase (Case (p : ps) guard a) = Just (p, Case ps guard a)

patternsName :: [Pattern] -> Maybe String
patternsName [] = Nothing
patternsName (p : ps) = case p of
  PVar x -> case patternsName ps of
    Just y | x /= y -> Nothing
    _ -> Just x
  PMeta _ p -> patternsName (p : ps)
  _ -> patternsName ps

let' :: Pattern -> Expr -> Expr -> Expr
let' = Let []

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

funOf :: Expr -> ([Expr], Expr)
funOf (Fun p a) = let (ps, b) = funOf a in (p : ps, b)
funOf (Meta _ a) = funOf a
funOf a = ([], a)

add :: Expr -> Expr -> Expr
add a b = Call "+" [a, b]

sub :: Expr -> Expr -> Expr
sub a b = Call "-" [a, b]

mul :: Expr -> Expr -> Expr
mul a b = Call "*" [a, b]

pow :: Expr -> Expr -> Expr
pow a b = Call "^" [a, b]

eq :: Expr -> Expr -> Expr
eq a b = Call "==" [a, b]

lt :: Expr -> Expr -> Expr
lt a b = Call "<" [a, b]

gt :: Expr -> Expr -> Expr
gt a b = Call ">" [a, b]

int2num :: Expr -> Expr
int2num a = Call "i2n" [a]

meta :: [C.Metadata] -> Expr -> Expr
meta ms a = foldr Meta a ms

var :: String -> Expr -> Stmt
var name = Define [] (PVar name)

varT :: String -> Expr -> Expr -> Stmt
varT name typ = Define [(name, typ)] (PVar name)

fn :: String -> [Pattern] -> Expr -> Stmt
fn name args value = Define [] (PVar name) (match [] [Case args Nothing value])

app :: Expr -> [Expr] -> Expr
app = foldl App

appOf :: Expr -> (Expr, [Expr])
appOf (App a b) = let (a', bs) = appOf a in (a', bs ++ [b])
appOf (Meta _ a) = appOf a
appOf a = (a, [])

import' :: String -> Stmt
import' m = Import m "" []

importAs :: String -> String -> Stmt
importAs m n = Import m n []

importFrom :: String -> [String] -> Stmt
importFrom m names = Import m "" (map (,"") names)

importAll :: String -> Stmt
importAll m = Import m "" [("*", "")]

isImport :: Stmt -> Bool
isImport Import {} = True
isImport _ = False

isTest :: Stmt -> Bool
isTest Test {} = True
isTest (MetaStmt _ stmt) = isTest stmt
isTest _ = False

isDefine :: Stmt -> Bool
isDefine Define {} = True
isDefine (MetaStmt _ stmt) = isDefine stmt
isDefine _ = False

isTypeDef :: Expr -> Bool
isTypeDef (Fun _ b) = isTypeDef b
isTypeDef (App a _) = isTypeDef a
isTypeDef (Ann a _) = isTypeDef a
isTypeDef (Meta _ a) = isTypeDef a
isTypeDef _ = False

isTagDef :: Expr -> Bool
isTagDef (Tag _ _) = True
isTagDef (Fun _ b) = isTagDef b
isTagDef (App a _) = isTagDef a
isTagDef (Ann a _) = isTagDef a
isTagDef (Meta _ a) = isTagDef a
isTagDef _ = False

isFunctionDef :: Expr -> Bool
isFunctionDef (Fun _ _) = True
isFunctionDef (Ann a _) = isFunctionDef a
isFunctionDef (Meta _ a) = isFunctionDef a
isFunctionDef _ = False

toExpr :: Pattern -> Expr
toExpr PAny = error "TODO: toExpr PAny"
toExpr (PInt i) = Int i
toExpr (PNum n) = Num n
toExpr (PVar x) = Var x
toExpr (PTag k ps) = Tag k (map toExpr ps)
toExpr (PFun p q) = Fun (toExpr p) (toExpr q)
toExpr (POr p q) = Or (toExpr p) (toExpr q)
toExpr (PEq a) = a
toExpr (PMeta m p) = Meta m (toExpr p)
toExpr PErr = Err

class FreeVars a where
  freeVars :: a -> [String]

instance FreeVars Expr where
  freeVars :: Expr -> [String]
  freeVars a = C.freeVars (lower [] a :: C.Expr)

instance FreeVars Pattern where
  freeVars :: Pattern -> [String]
  freeVars p = C.freeVars (lower [] p :: C.Pattern)

instance FreeVars Case where
  freeVars :: Case -> [String]
  freeVars case' = C.freeVars (lower [] case' :: C.Expr)

instance FreeVars [Case] where
  freeVars :: [Case] -> [String]
  freeVars = foldr (union . freeVars) []

class Lower a b where
  lower :: C.Env -> a -> b

instance Lower Expr C.Expr where
  lower :: C.Env -> Expr -> C.Expr
  lower _ (Int i) = C.Int i
  lower _ (Num n) = C.Num n
  lower _ (Var x) = C.Var x
  lower env (Tag k args)
    | Tag k args == kind = C.Knd
    | Tag k args == intT = C.IntT
    | Tag k args == numT = C.NumT
    | otherwise = C.Tag k (map (lower env) args)
  lower env (Tuple items) = lower env (Tag "" items)
  lower env (Record fields) = do
    let k = '~' : intercalate "," (map fst fields)
    let args = map (fromMaybe Err . fst . snd) fields
    lower env (Tag k args)
  lower env (Trait a x) = do
    let a' = lower env a
    case C.infer env a' of
      Left _ -> C.Err
      Right (t, _) -> C.app (C.Var $ '.' : x) [t, a']
  lower env (TraitFun x) = lower env (lambda ["_"] (Trait (Var "_") x))
  lower env (Fun a b) = C.Fun (lower env a) (lower env b)
  lower env (App a b) = C.App (lower env a) (lower env b)
  lower env (Or a b) = C.Or (lower env a) (lower env b)
  lower env (Let ts p a b) = lower env (Match [a] [Case [p] Nothing b])
  lower env (Bind ts p a b) = lower env (App (Trait a "<-") (match [] [Case [p] Nothing b]))
  lower env (Match args cases) = lower env (app (MatchFun cases) args)
  lower env (MatchFun cases) = C.or' (map (lower env) cases)
  lower env (Ann a b) = C.Ann (lower env a) (lower env b)
  lower env (Call op args) = C.Op op (map (lower env) args)
  lower env (Meta m a) = C.Meta m (lower env a)
  lower _ Err = C.Err
  lower _ a = error $ "TODO: lower " ++ show a

instance Lower Case C.Expr where
  lower :: C.Env -> Case -> C.Expr
  lower env (Case ps guard b) = C.lam (map (lower env) ps) (lower env b)

instance Lower Pattern C.Pattern where
  lower :: C.Env -> Pattern -> C.Pattern
  lower _ PAny = C.PAny
  lower _ (PInt i) = C.PInt i
  lower _ (PNum n) = C.PNum n
  lower _ (PVar x) = C.PVar x
  lower env (PTag k ps)
    | PTag k ps == pIntT = C.PIntT
    | PTag k ps == pNumT = C.PNumT
    | otherwise = C.PTag k (map (lower env) ps)
  lower env (PFun p q) = C.PFun (lower env p) (lower env q)
  lower env (POr p q) = error "TODO"
  lower env (PEq a) = C.PEq (lower env a)
  lower env (PMeta m p) = C.PMeta m (lower env p)
  lower _ PErr = C.PErr

instance Lower Stmt C.Env where
  lower :: C.Env -> Stmt -> C.Env
  lower env (Import m n xs) = case xs of
    [] -> [(n, C.Var m)]
    (x, y) : xs -> (y, C.Var x) : lower env (Import m n xs)
  lower env (Define ts p a) = case p of
    PVar x -> [(x, lower env a)]
    _ -> error $ "TODO: lower Define " ++ show (ts, p, a)
  lower env (Test a p) = do
    let expect = Case [p] Nothing (ok $ Tuple [])
    let error = Case [PVar "e"] Nothing (err $ Var "e")
    let test = match [a] [expect, error]
    [("> " ++ show a, lower env test)]
  lower env (MetaStmt _ stmt) = lower env stmt

instance Lower Module C.Env where
  lower :: C.Env -> Module -> C.Env
  lower env mod = concatMap (lower env) mod.stmts

instance Lower Package C.Env where
  lower :: C.Env -> Package -> C.Env
  lower env pkg = concatMap (lower env) pkg.modules

class Lift a b where
  lift :: a -> b

instance Lift C.Expr Expr where
  lift :: C.Expr -> Expr
  lift C.Knd = kind
  lift C.IntT = intT
  lift C.NumT = numT
  lift (C.Int i) = Int i
  lift (C.Num n) = Num n
  lift (C.Var x) = Var x
  lift (C.Tag "" args) = Tuple (map lift args)
  lift (C.Tag ('~' : names) args) = do
    let keys = split ',' names
    let values = map (\a -> (Just $ lift a, Nothing)) args
    Record (zip keys values)
  lift (C.Tag k args) = Tag k (map lift args)
  lift (C.For _ a) = lift a
  lift (C.Fix _ a) = lift a
  lift (C.Fun a b) = Fun (lift a) (lift b)
  lift (C.Lam p b) = MatchFun [Case [lift p] Nothing (lift b)]
  lift (C.App a b) = case appOf (App (lift a) (lift b)) of
    (Var ('.' : x), _ : a : args) -> app (Trait a x) args
    (Trait a "<-", [MatchFun [Case [p] Nothing b]]) -> Bind [] p a b
    (a, args) -> app a args
  lift (C.Or a b) = Or (lift a) (lift b)
  lift (C.Ann a b) = Ann (lift a) (lift b)
  lift (C.Op op args) = Call op (map lift args)
  lift (C.Meta m a) = Meta m (lift a)
  lift C.Err = Err

instance Lift C.Pattern Pattern where
  lift :: C.Pattern -> Pattern
  lift C.PAny = PAny
  lift (C.PInt i) = PInt i
  lift (C.PNum n) = PNum n
  lift (C.PVar x) = PVar x
  lift p = error $ "TODO: lift " ++ show p

splitWith :: (Char -> Bool) -> String -> [String]
splitWith f text = case dropWhile f text of
  "" -> []
  text -> do
    let (word, remaining) = break f text
    word : splitWith f remaining

split :: Char -> String -> [String]
split delim = splitWith (== delim)

split2 :: Char -> String -> (String, String)
split2 delim text = case split delim text of
  [] -> ("", "")
  [x] -> (x, "")
  x : y : _ -> (x, y)

splitName :: String -> (String, String, String)
splitName ('@' : pkgModName) = do
  let (pkg, modName) = split2 ':' pkgModName
  let (mod, name) = split2 '.' modName
  (pkg, mod, name)
splitName name = ("", "", name)

class ResolveNames a b where
  resolveNames :: a -> b -> [(String, String)]

instance ResolveNames () Package where
  resolveNames :: () -> Package -> [(String, String)]
  resolveNames () pkg = do
    let p = '@' : pkg.name
    concatMap (resolveNames p) pkg.modules

instance ResolveNames String Module where
  resolveNames :: String -> Module -> [(String, String)]
  resolveNames p mod = do
    let m = p ++ ':' : mod.name
    concatMap (resolveNames m) mod.stmts

instance ResolveNames String Stmt where
  resolveNames :: String -> Stmt -> [(String, String)]
  resolveNames m (Import m' n exposed) = case exposed of
    [] -> [(m, n)]
    (_, y) : exposed ->
      (m, y) : resolveNames m (Import m' n exposed)
  resolveNames m (Define ts p a) = resolveNames m p
  resolveNames _ (Test _ _) = []
  resolveNames m (MetaStmt _ stmt) = resolveNames m stmt

instance ResolveNames String Pattern where
  resolveNames :: String -> Pattern -> [(String, String)]
  resolveNames m (PVar x) = [(m, x)]
  resolveNames m p = error $ "TODO: resolveNames " ++ show (m, p)

link :: Package -> [Substitution]
link pkg = do
  let s (m, x) = ((m, x), m ++ '.' : x)
  map s (resolveNames () pkg)

stmtTests :: Stmt -> [(Expr, Pattern)]
stmtTests (Test expr expected) = [(expr, expected)]
stmtTests (MetaStmt _ stmt) = stmtTests stmt
stmtTests _ = []

moduleTests :: Module -> [(Expr, Pattern)]
moduleTests mod = concatMap stmtTests mod.stmts

packageTests :: Package -> [(Expr, Pattern)]
packageTests pkg = concatMap moduleTests pkg.modules

nameSplit :: String -> [String]
nameSplit name =
  splitWhen (not . isAlphaNum) name
    & filter (/= "")
    & concatMap splitCamelCase
    & map (map toLower)

splitCamelCase :: String -> [String]
splitCamelCase [] = []
splitCamelCase (x : xs) = case splitCamelCase xs of
  [] -> [[x]]
  part : parts -> case part of
    (y : z : _) | isUpper x && isUpper y && isLower z -> split
    (y : _) | isUpper x || isLower y -> cat
    _ -> split
    where
      split = [x] : part : parts
      cat = (x : part) : parts

capitalize :: String -> String
capitalize "" = ""
capitalize (x : xs) = toUpper x : xs

nameCamelCaseUpper :: String -> String
nameCamelCaseUpper name =
  nameSplit name
    & map capitalize
    & intercalate ""

nameCamelCaseLower :: String -> String
nameCamelCaseLower name = case nameSplit name of
  [] -> ""
  (x : xs) -> intercalate "" (x : map capitalize xs)

nameSnakeCase :: String -> String
nameSnakeCase name = nameSplit name & intercalate "_"

nameDashCase :: String -> String
nameDashCase name = nameSplit name & intercalate "-"

isImported :: String -> Stmt -> Bool
isImported x (Import _ n exposed) = x == n || x `elem` map fst exposed
isImported _ _ = False

class Apply a where
  apply :: (Expr -> Expr) -> a -> a

instance Apply Expr where
  apply :: (Expr -> Expr) -> Expr -> Expr
  apply _ (Int i) = Int i
  apply _ (Num n) = Num n
  apply _ (Var x) = Var x
  apply f (Tag k args) = Tag k (map f args)
  apply f (Tuple items) = Tuple (map f items)
  apply f (Record fields) = Record (map (\(x, (a, b)) -> (x, (fmap f a, fmap f b))) fields)
  apply f (Fun a b) = Fun (f a) (f b)
  apply f (App a b) = App (f a) (f b)
  apply f (Or a b) = Or (f a) (f b)
  apply f (Let ts p a b) = Let (map (second $ apply f) ts) (apply f p) (apply f a) (apply f b)
  apply f (Bind ts p a b) = Bind (map (second $ apply f) ts) (apply f p) (apply f a) (apply f b)
  apply f (MatchFun cases) = MatchFun (map (apply f) cases)
  apply f (Trait a x) = Trait (f a) x
  apply _ (TraitFun x) = TraitFun x
  apply f (Ann a b) = Ann (f a) (f b)
  apply f (Call op args) = Call op (map (apply f) args)
  apply f (Meta m a) = Meta m (f a)
  apply _ Err = Err
  apply _ a = error $ "TODO: apply " ++ show a

instance Apply Pattern where
  apply :: (Expr -> Expr) -> Pattern -> Pattern
  apply _ PAny = PAny
  apply _ (PInt i) = PInt i
  apply _ (PNum n) = PNum n
  apply _ (PVar x) = PVar x
  apply f (PTag k ps) = PTag k (map (apply f) ps)
  apply f (PFun p q) = PFun (apply f p) (apply f q)
  apply f (POr p q) = POr (apply f p) (apply f q)
  apply f (PEq a) = PEq (f a)
  apply f (PMeta m p) = PMeta m (apply f p)
  apply _ PErr = PErr

instance Apply Case where
  apply :: (Expr -> Expr) -> Case -> Case
  apply f (Case ps guard b) =
    Case (map (apply f) ps) (fmap f guard) (apply f b)

instance Apply Stmt where
  apply :: (Expr -> Expr) -> Stmt -> Stmt
  apply _ stmt@Import {} = stmt
  apply f (Define ts p a) = Define (map (second $ apply f) ts) (apply f p) (apply f a)
  apply f (Test a b) = Test (apply f a) (apply f b)
  apply f (MetaStmt m a) = MetaStmt m (apply f a)

type Substitution = ((String, String), String)

class Rename path a where
  rename :: path -> [Substitution] -> a -> a

instance Rename () Package where
  rename :: () -> [Substitution] -> Package -> Package
  rename () s pkg = pkg {modules = map (rename pkg.name s) pkg.modules}

instance Rename String Module where
  rename :: String -> [Substitution] -> Module -> Module
  rename p s mod = do
    let m = '@' : p ++ ':' : mod.name
    mod {stmts = map (rename m s) mod.stmts}

instance Rename String Stmt where
  rename :: String -> [Substitution] -> Stmt -> Stmt
  rename m s (Import m' n vars) =
    Import m' (rename m s n) (map (bimap (rename m' s) (rename m s)) vars)
  rename m s (Define ts p a) = Define (map (bimap (rename m s) (rename m s)) ts) (rename m s p) (rename m s a)
  rename m s (Test a p) = Test (rename m s a) (rename m s p)
  rename m s (MetaStmt m' stmt) = MetaStmt m' (rename m s stmt)

instance Rename String Pattern where
  rename :: String -> [Substitution] -> Pattern -> Pattern
  rename _ _ PAny = PAny
  rename _ _ (PInt i) = PInt i
  rename _ _ (PNum n) = PNum n
  rename m s (PVar x) = PVar (rename m s x)
  rename m s (PTag k ps) = PTag k (map (rename m s) ps)
  rename m s p = error $ "TODO: rename Pattern " ++ show p

instance Rename String Expr where
  rename :: String -> [Substitution] -> Expr -> Expr
  rename _ _ (Int i) = Int i
  rename _ _ (Num n) = Num n
  rename m s (Var x) = Var (rename m s x)
  rename m s (Tag k args) = Tag k (map (rename m s) args)
  rename m s (Trait a x) = Trait (rename m s a) (rename m s x)
  rename m s a = error $ "TODO: rename Expr " ++ show a

instance Rename String String where
  rename :: String -> [Substitution] -> String -> String
  rename _ [] x = x
  rename m ((sub, y) : s) x
    | sub == (m, x) = y
    | otherwise = rename m s x

-- TODO: RenameModule
-- TODO: RenamePackage

-- class Rename a b where
--   rename :: a -> String -> String -> b -> b

-- instance Rename () Package where
--   rename :: () -> String -> String -> Package -> Package
--   rename () old new pkg =
--     pkg {modules = map (rename pkg.name old new) pkg.modules}

-- instance Rename String Module where
--   rename :: String -> String -> String -> Module -> Module
--   rename pkg old new mod =
--     mod {stmts = map (rename (pkg, mod.name) old new) mod.stmts}

-- instance Rename (String, String) Stmt where
--   rename :: (String, String) -> String -> String -> Stmt -> Stmt
--   rename path old new (Import name alias exposed) = do
--     let alias' = rename () old new alias
--     let exposed' = map (bimap (rename () old new) (rename () old new)) exposed
--     -- Import name alias' exposed'
--     error "rename Import check path for imported module and exposed"
--   rename path old new (Define def) = Define (rename () old new def)
--   rename path old new (Test a b) = Test (rename () old new a) (rename () old new b)
--   rename path old new (MetaStmt m stmt) = MetaStmt m (rename path old new stmt)

-- instance Rename () Definition where
--   rename :: () -> String -> String -> Definition -> Definition
--   rename () old new (Def ts p val) = do
--     let ts' = map (bimap (rename () old new) (rename () old new)) ts
--     let p' = rename () old new p
--     let val' = rename () old new val
--     Def ts' p' val'
--   rename () old new (TraitDef ts (t, a) x val) = do
--     let ts' = map (bimap (rename () old new) (rename () old new)) ts
--     let x' = rename () old new x
--     let val' = rename () old new val
--     TraitDef ts' (t, a) x' val'

-- instance Rename () Context where
--   rename :: () -> String -> String -> Context -> Context
--   rename () old new ctx =
--     foldr (\_ ctx -> map (rename () old new) ctx) ctx ctx

-- instance Rename () Expr where
--   rename :: () -> String -> String -> Expr -> Expr
--   rename () old new (Var x) = Var (rename () old new x)
--   rename () old new (Tag k args) = Tag (rename () old new k) (map (rename () old new) args)
--   rename () old new (Trait a x) = Trait (rename () old new a) x
--   rename () old new (Let def a) = Let (rename () old new def) (rename () old new a)
--   rename () old new (Match cases) = Match (map (rename () old new) cases)
--   rename () old new (Meta m a) = Meta m (rename () old new a)
--   rename () old new expr = apply (rename () old new) expr

-- instance Rename () (String, Expr) where
--   rename :: () -> String -> String -> (String, Expr) -> (String, Expr)
--   rename () old new (name, value) =
--     (rename () old new name, rename () old new value)

-- instance Rename () Case where
--   rename :: () -> String -> String -> Case -> Case
--   rename () old new (Case ps guard b) =
--     Case (map (rename () old new) ps) (fmap (rename () old new) guard) (rename () old new b)

-- instance Rename () Pattern where
--   rename :: () -> String -> String -> Pattern -> Pattern
--   rename () old new (PVar x) = PVar (rename () old new x)
--   rename () old new (PTag k ps) = PTag (rename () old new k) (map (second $ rename () old new) ps)
--   rename () old new (PMeta m p) = PMeta m (rename () old new p)
--   rename () old new p = apply (rename () old new) p

-- instance Rename () String where
--   rename :: () -> String -> String -> String -> String
--   rename () old new str
--     | str == old = new
--     | otherwise = str

-- substitute :: (Rename a) => [(String, String)] -> a -> a
-- substitute subs a = foldr (uncurry rename) a subs

refactorName :: ([String] -> Expr -> String -> String) -> Package -> Package
refactorName f pkg = do
  let refactor :: Module -> Package -> Package
      refactor mod pkg = do
        -- let ctx = concatMap (getContext (pkg.name, mod.name)) mod.stmts
        -- foldr (\(x, a) -> rename () x (f (map fst ctx) a x)) pkg ctx
        error "TODO: refactorName"
  foldr refactor pkg pkg.modules

class RefactorModuleName a where
  refactorModuleName :: (FilePath -> FilePath) -> a -> a

instance RefactorModuleName Package where
  refactorModuleName :: (FilePath -> FilePath) -> Package -> Package
  refactorModuleName f pkg = pkg {modules = map (refactorModuleName f) pkg.modules}

instance RefactorModuleName Module where
  refactorModuleName :: (FilePath -> FilePath) -> Module -> Module
  refactorModuleName f mod = mod {name = f mod.name, stmts = map (refactorModuleName f) mod.stmts}

instance RefactorModuleName Stmt where
  refactorModuleName :: (FilePath -> FilePath) -> Stmt -> Stmt
  refactorModuleName f (Import m n exposed) = error "TODO"
  -- refactorModuleName f (Import name alias exposed) = Import (f name) alias exposed
  refactorModuleName _ stmt = stmt

class RefactorModuleAlias a where
  refactorModuleAlias :: (FilePath -> FilePath) -> a -> a

instance RefactorModuleAlias Package where
  refactorModuleAlias :: (FilePath -> FilePath) -> Package -> Package
  refactorModuleAlias f pkg = pkg {modules = map (refactorModuleAlias f) pkg.modules}

instance RefactorModuleAlias Module where
  refactorModuleAlias :: (FilePath -> FilePath) -> Module -> Module
  refactorModuleAlias f mod = do
    let names = concatMap importAlias mod.stmts
    -- let refactor stmt = foldr (\x -> rename () x (f x)) stmt names
    -- mod {name = mod.name, stmts = map (refactor ()) mod.stmts}
    error "TODO"

importAlias :: Stmt -> [String]
importAlias (Import _ alias _) = [alias]
importAlias _ = []

replace :: (Eq a) => a -> a -> [a] -> [a]
replace x y (x' : xs)
  | x == x' = y : replace x y xs
  | otherwise = x' : replace x y xs
replace _ _ [] = []

replaceString :: String -> String -> String -> String
replaceString _ _ "" = ""
replaceString old new text | old `isPrefixOf` text = do
  new ++ replaceString old new (drop (length old) text)
replaceString old new (c : text) = c : replaceString old new text

in' :: String -> String -> Bool
in' _ "" = False
in' substring string | substring `isPrefixOf` string = True
in' substring (_ : string) = in' substring string

class DropMeta a where
  dropMeta :: a -> a

instance DropMeta Expr where
  dropMeta :: Expr -> Expr
  dropMeta (Meta _ a) = dropMeta a
  dropMeta (MatchFun cases) = MatchFun (map dropMeta cases)
  dropMeta a = apply dropMeta a

instance DropMeta Pattern where
  dropMeta :: Pattern -> Pattern
  dropMeta (PMeta _ p) = dropMeta p
  dropMeta a = apply dropMeta a

instance DropMeta Case where
  dropMeta :: Case -> Case
  dropMeta (Case ps guard a) =
    Case (map dropMeta ps) (fmap dropMeta guard) (dropMeta a)

instance DropMeta Stmt where
  dropMeta :: Stmt -> Stmt
  dropMeta stmt@Import {} = stmt
  dropMeta (Define ts p a) = Define (map (second dropMeta) ts) (dropMeta p) (dropMeta a)
  dropMeta (Test a b) = Test (dropMeta a) (dropMeta b)
  dropMeta (MetaStmt _ stmt) = dropMeta stmt

instance DropMeta Module where
  dropMeta :: Module -> Module
  dropMeta mod = mod {stmts = map dropMeta mod.stmts}

instance DropMeta Package where
  dropMeta :: Package -> Package
  dropMeta pkg = pkg {modules = map dropMeta pkg.modules}

instance DropMeta TestError where
  dropMeta :: TestError -> TestError
  dropMeta (TestEqError a b p) = TestEqError (dropMeta a) (dropMeta b) (dropMeta p)

eval :: Package -> String -> Expr -> Either (Expr, C.TypeError) (Expr, Expr)
eval pkg m expr = do
  let s = link pkg
  let env = lower [] (rename () s pkg)
  let expr' = lower env (rename m s expr)
  let result = C.eval env expr'
  case C.infer env expr' of
    Right (type', _) -> Right (lift result, lift type')
    Left e -> Left (lift result, e)

test :: Package -> [TestError]
test pkg = do
  let s = link pkg
  let pkg' = rename () s pkg
  let env = lower [] pkg'
  concatMap (testEq env) (packageTests pkg')

testEq :: C.Env -> (Expr, Pattern) -> [TestError]
testEq env (expr, expected) = do
  -- let env = lower ctx
  -- let actual = C.eval env (lower ctx expr)
  -- let expected = C.eval env (lower ctx result)
  -- case C.eval [] (actual `C.eq` expected) of
  --   C.Err -> [TestEqError expr (liftExpr actual) (liftExpr expected)]
  --   C.Op2 C.Eq _ _ -> [TestEqError expr (liftExpr actual) (liftExpr expected)]
  --   _ -> []
  let unitTest = lower env (let' expected expr (Tuple []))
  let passed = case C.eval env unitTest of
        C.Err -> False
        -- C.Op2 C.Eq _ _ -> False
        _ -> True
  if passed
    then []
    else do
      let actual = lower env expr & C.eval env & lift
      [TestEqError expr actual expected]
