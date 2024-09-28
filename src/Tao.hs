module Tao where

import Control.Monad (mapAndUnzipM)
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap), second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (elemIndex, intercalate, isInfixOf, isPrefixOf, union)
import Data.List.Split (splitWhen, startsWith)
import Data.Maybe (fromMaybe)

data Expr
  = Int Int
  | Num Double
  | Var String
  | Tag String [Expr]
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Fun Expr Expr
  | App Expr Expr
  | Or Expr Expr
  | Ann Expr Type
  | Call String [Expr]
  | Let Definition Expr
  | Bind Definition Expr
  | Function [Pattern] Expr
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

type Definition = ([(String, Type)], Pattern, Expr)

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
  | PRecord [(String, Pattern)]
  | PTrait Pattern String
  | POp1 String Pattern
  | POp2 String Pattern Pattern
  | PFun Pattern Pattern
  | POr Pattern Pattern
  | PEq Expr
  | PMeta C.Metadata Pattern
  | PErr
  deriving (Eq, Show)

data Stmt
  = Import String [(String, String)]
  | Def Definition
  | Test String Expr Pattern
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

data TestError
  = NoTestsFound String
  | TestEqError String C.Expr C.Expr
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

pRecord :: [(String, Pattern)] -> Pattern
pRecord = error "TODO: Tao.pRecord"

function :: [Pattern] -> Expr -> Expr
function [] b = b
function ps b = Function ps b

match :: [Expr] -> [Case] -> Expr
match [] cases = matchFun cases
match (Var x : args) cases = do
  let matchVar (Case (PVar x' : ps) guard b) | x == x' = Just (Case ps guard b)
      matchVar (Case (PAny : ps) guard b) | x `notElem` freeVars b = Just (Case ps guard b)
      matchVar _ = Nothing
  case mapM matchVar cases of
    Just cases' -> match args cases'
    Nothing -> app (MatchFun cases) (Var x : args)
match args cases = app (MatchFun cases) args

matchFun :: [Case] -> Expr
matchFun (Case [] Nothing b : _) = b
matchFun cases = MatchFun cases

select :: Expr -> [String] -> Expr
select a xs = Select a (map (\x -> (x, Var x)) xs)

selectFun :: [String] -> Expr
selectFun xs = SelectFun (map (\x -> (x, Var x)) xs)

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

app :: Expr -> [Expr] -> Expr
app = foldl App

appOf :: Expr -> (Expr, [Expr])
appOf (App a b) = let (a', bs) = appOf a in (a', bs ++ [b])
appOf (Meta _ a) = appOf a
appOf a = (a, [])

import' :: String -> [String] -> Stmt
import' m names = Import m (map (\x -> (x, x)) names)

defVar :: String -> Expr -> Definition
defVar x a = ([], PVar x, a)

defVarT :: String -> Type -> Expr -> Definition
defVarT x t a = ([(x, t)], PVar x, a)

-- \| DefTag [(String, Type)] String [Pattern] Expr
-- \| DefTuple [(String, Type)] [Pattern] Expr
-- \| DefRecord [(String, Type)] [(String, Pattern)] Expr
-- \| DefTrait Pattern String (Maybe Type) Expr
-- \| DefMeta C.Metadata Definition

isImport :: Stmt -> Bool
isImport Import {} = True
isImport _ = False

isTest :: Stmt -> Bool
isTest Test {} = True
isTest (MetaStmt _ stmt) = isTest stmt
isTest _ = False

isDefine :: Stmt -> Bool
isDefine Def {} = True
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
    lower env (Tag k (map snd fields))
  lower env (Trait a x) = do
    let a' = lower env a
    case C.infer env a' of
      Right (t, _) -> C.app (C.Var $ '.' : x) [t, a']
      Left _ -> C.Err
  lower env (TraitFun x) = lower env (lambda ["_"] (Trait (Var "_") x))
  lower env (Fun a b) = C.Fun (lower env a) (lower env b)
  lower env (App a b) = do
    let a' = lower env a
    case C.infer env a' of
      Right (C.Fun (C.Tag ('~' : xs) _) _, _) ->
        C.App a' (lower env (select b (split ',' xs)))
      _ -> C.App a' (lower env b)
  lower env (Or a b) = C.Or (lower env a) (lower env b)
  lower env (Let def b) = lower (lower env def ++ env) b
  lower env (Bind (ts, p, a) b) = lower env (App (Trait a "<-") (Function [p] b))
  lower env (Function ps a) = lower env (MatchFun [Case ps Nothing a])
  lower env (Match args cases) = lower env (app (MatchFun cases) args)
  lower env (MatchFun cases) = C.or' (map (lower env) cases)
  lower env (Select a kvs) = case a of
    Record fields -> do
      let sub = map (second $ lower env) fields
      let lowerFields [] = []
          lowerFields ((x, b) : xs) | x `elem` map fst fields = do
            let b' = lower env b
            (x, C.substitute sub b') : lowerFields xs
          lowerFields (_ : xs) = lowerFields xs
      let fields' = lowerFields kvs
      let k = '~' : intercalate "," (map fst fields')
      C.Tag k (map snd fields')
    a -> error $ "TODO: lower Select " ++ show a
  lower env (Ann a b) = C.Ann (lower env a) (lower env b)
  lower env (Call op args) = C.Op op (map (lower env) args)
  lower env (Meta m a) = C.Meta m (lower env a)
  lower _ Err = C.Err
  lower _ a = error $ "TODO: lower " ++ show a

instance Lower Definition C.Env where
  lower :: C.Env -> Definition -> C.Env
  lower env (ts, PVar x, a) = case lookup x ts of
    Just t -> [(x, lower env (Ann a t))]
    Nothing -> [(x, lower env a)]
  lower env (ts, PMeta m p, a) = do
    lower env (ts, p, a) & map (second $ C.Meta m)
  lower env (ts, p, a) = error $ "TODO lower Definition " ++ show p

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
  lower env (PTuple ps) = lower env (PTag "" ps)
  lower env (PFun p q) = C.PFun (lower env p) (lower env q)
  lower env (POr p q) = error "TODO"
  lower env (PEq a) = C.PEq (lower env a)
  lower env (PMeta m p) = C.PMeta m (lower env p)
  lower _ PErr = C.PErr

instance Lower Stmt C.Env where
  lower :: C.Env -> Stmt -> C.Env
  lower env (Import m xs) = case xs of
    [] -> []
    (x, y) : xs -> (y, C.Var x) : lower env (Import m xs)
  lower env (Def def) = lower env def
  lower env (Test name a p) = do
    let test' =
          C.match'
            [lower env a]
            [ ([lower env p], C.Tag "pass" []),
              ([C.PVar "_"], C.Tag "fail" [C.Var "_"])
            ]
    [(name, test')]
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
    Record (zip keys (map lift args))
  lift (C.Tag k args) = Tag k (map lift args)
  lift (C.For _ a) = lift a
  lift (C.Fix _ a) = lift a
  lift (C.Fun a b) = Fun (lift a) (lift b)
  lift (C.Lam p b) = Function [lift p] (lift b)
  lift (C.App a b) = case appOf (App (lift a) (lift b)) of
    (Var ('.' : x), _ : a : args) -> app (Trait a x) args
    (Trait a "<-", [Function [p] b]) -> Bind ([], p, a) b
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
  resolveNames () pkg = concatMap (resolveNames pkg.name) pkg.modules

instance ResolveNames String Module where
  resolveNames :: String -> Module -> [(String, String)]
  resolveNames p mod = do
    let m = '@' : p ++ '/' : mod.name
    concatMap (resolveNames m) mod.stmts

instance ResolveNames String Stmt where
  resolveNames :: String -> Stmt -> [(String, String)]
  resolveNames m (Import m' exposed) = case exposed of
    [] -> []
    (_, y) : exposed ->
      ('@' : m, y) : resolveNames m (Import m' exposed)
  resolveNames m (Def def) = resolveNames m def
  resolveNames _ Test {} = []
  resolveNames m (MetaStmt _ stmt) = resolveNames m stmt

instance ResolveNames String Definition where
  resolveNames :: String -> Definition -> [(String, String)]
  resolveNames m (_, p, _) = case p of
    PVar ('_' : x) -> [('_' : '@' : m, x)]
    PVar x | "/_" `isInfixOf` m -> [('_' : '@' : m, x)]
    PVar x -> case split2 '/' m of
      (pkg, '@' : pkg') | pkg == pkg' -> [('@' : pkg, x)]
      _ -> [('@' : m, x)]
    PTag _ ps -> concatMap (resolveNames m) ps
    PTuple ps -> concatMap (resolveNames m) ps
    PRecord kvs -> concatMap (resolveNames m . snd) kvs
    PTrait p x -> [('.' : '@' : m ++ ':' : show p, x)]
    PMeta _ p -> resolveNames m p
    p -> error $ "TODO: resolveNames " ++ show p

instance ResolveNames String Pattern where
  resolveNames :: String -> Pattern -> [(String, String)]
  resolveNames m (PVar x) = [(m, x)]
  resolveNames m (PMeta _ p) = resolveNames m p
  resolveNames m p = error $ "TODO: resolveNames " ++ show (m, p)

resolve :: Package -> [Substitution]
resolve pkg = do
  let sub (m, x) = ((m, x), m ++ '.' : x)
  map sub (resolveNames () pkg)

linkPackage :: Package -> Package
linkPackage pkg = do
  let s = resolve pkg
  rename () s pkg

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
isImported x (Import _ exposed) = x `elem` map fst exposed
isImported _ _ = False

class Apply a where
  apply :: (Expr -> Expr) -> a -> a

instance Apply Expr where
  apply :: (Expr -> Expr) -> Expr -> Expr
  apply _ (Int i) = Int i
  apply _ (Num n) = Num n
  apply _ (Var x) = Var x
  apply f (Tag k args) = Tag k (map (apply f) args)
  apply f (Tuple items) = Tuple (map (apply f) items)
  apply f (Record fields) = Record (map (second (apply f)) fields)
  apply f (Fun a b) = Fun (apply f a) (apply f b)
  apply f (App a b) = App (apply f a) (apply f b)
  apply f (Or a b) = Or (apply f a) (apply f b)
  apply f (Let def b) = Let (apply f def) (apply f b)
  apply f (Bind (ts, p, a) b) = Bind (map (second $ apply f) ts, apply f p, apply f a) (apply f b)
  apply f (Function ps b) = Function (map (apply f) ps) (apply f b)
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
  apply f (PTuple ps) = PTuple (map (apply f) ps)
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
  apply f (Def def) = Def (apply f def)
  apply f (Test name a b) = Test name (apply f a) (apply f b)
  apply f (MetaStmt m a) = MetaStmt m (apply f a)

instance Apply Definition where
  apply :: (Expr -> Expr) -> Definition -> Definition
  apply f (ts, p, a) = do
    let ts' = second (apply f) <$> ts
    let p' = apply f p
    let a' = apply f a
    (ts', p', a')

type Substitution = ((String, String), String)

class Rename path a where
  rename :: path -> [Substitution] -> a -> a

instance Rename () Package where
  rename :: () -> [Substitution] -> Package -> Package
  rename () s pkg =
    pkg {modules = map (rename ('@' : pkg.name) s) pkg.modules}

instance Rename String Module where
  rename :: String -> [Substitution] -> Module -> Module
  rename p s mod = do
    let m = p ++ '/' : mod.name
    mod {stmts = map (rename m s) mod.stmts}

instance Rename String Stmt where
  rename :: String -> [Substitution] -> Stmt -> Stmt
  rename m s (Import m' vars) =
    Import m' (map (bimap (rename m' s) (rename m s)) vars)
  rename m s (Def def) = Def (rename m s def)
  rename m s (Test name a p) = do
    let name' = case name of
          '>' : _ -> name
          _ -> '>' : m ++ ':' : name
    Test name' (rename m s a) (rename m s p)
  rename m s (MetaStmt m' stmt) = MetaStmt m' (rename m s stmt)

instance Rename String Definition where
  rename :: String -> [Substitution] -> Definition -> Definition
  rename m s (ts, p, a) = do
    let ts' = bimap (rename m s) (rename m s) <$> ts
    let p' = rename m s p
    let a' = rename m s a
    (ts', p', a')

instance Rename String Pattern where
  rename :: String -> [Substitution] -> Pattern -> Pattern
  rename _ _ PAny = PAny
  rename _ _ (PInt i) = PInt i
  rename _ _ (PNum n) = PNum n
  rename m s (PVar x) = PVar (rename m s x)
  rename m s (PTag k ps) = PTag k (map (rename m s) ps)
  rename m s (PTuple ps) = PTuple (map (rename m s) ps)
  rename m s (PMeta m' p) = PMeta m' (rename m s p)
  rename m s p = error $ "TODO: rename Pattern " ++ show p

instance Rename String Expr where
  rename :: String -> [Substitution] -> Expr -> Expr
  rename _ _ (Int i) = Int i
  rename _ _ (Num n) = Num n
  rename m s (Var x) = Var (rename m s x)
  rename m s (Tag k args) = Tag k (map (rename m s) args)
  rename m s (Tuple args) = Tuple (map (rename m s) args)
  rename m s (Record fields) = Record (map (second $ rename m s) fields)
  rename m s (App a b) = App (rename m s a) (rename m s b)
  rename m s (Fun a b) = Fun (rename m s a) (rename m s b)
  rename m s (Function ps a) = Function (map (rename m s) ps) (rename m s a)
  rename m s (MatchFun cases) = MatchFun (map (rename m s) cases)
  rename m s (Trait a x) = Trait (rename m s a) (rename m s x)
  rename m s (TraitFun x) = TraitFun (rename m s x)
  rename m s (Call f args) = Call f (map (rename m s) args)
  rename m s (Meta m' a) = Meta m' (rename m s a)
  rename m s a = error $ "TODO: rename Expr " ++ show a

instance Rename String Case where
  rename :: String -> [Substitution] -> Case -> Case
  rename m s (Case ps cond a) =
    Case (map (rename m s) ps) (fmap (rename m s) cond) (rename m s a)

instance Rename String String where
  rename :: String -> [Substitution] -> String -> String
  rename _ [] x = x
  rename m ((path, y) : s) x
    | path == (m, x) = y
    | otherwise = rename m s x

refactorName :: (Type -> String -> String) -> Package -> Package
refactorName f pkg = do
  let refactor :: C.Env -> Module -> Package -> Package
      refactor env mod pkg = do
        -- let ctx = concatMap (getContext (pkg.name, mod.name)) mod.stmts
        -- foldr (\(x, a) -> rename () x (f (map fst ctx) a x)) pkg ctx
        let names = resolveNames pkg.name mod
        -- let s = map (\(m, x) -> ((m, x), f (map snd names))) names
        -- let s (m, x) = ((m, x), m ++ '.' : x)
        -- map s (resolveNames () pkg)
        error "TODO: refactorName"
  let env = lower [] pkg :: C.Env
  foldr (refactor env) pkg pkg.modules

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
  refactorModuleName f (Import m exposed) = error "TODO"
  -- refactorModuleName f (Import name exposed) = Import (f name) alias exposed
  refactorModuleName _ stmt = stmt

class RefactorModuleAlias a where
  refactorModuleAlias :: (FilePath -> FilePath) -> a -> a

instance RefactorModuleAlias Package where
  refactorModuleAlias :: (FilePath -> FilePath) -> Package -> Package
  refactorModuleAlias f pkg = pkg {modules = map (refactorModuleAlias f) pkg.modules}

instance RefactorModuleAlias Module where
  refactorModuleAlias :: (FilePath -> FilePath) -> Module -> Module
  refactorModuleAlias f mod = do
    -- let refactor stmt = foldr (\x -> rename () x (f x)) stmt names
    -- mod {name = mod.name, stmts = map (refactor ()) mod.stmts}
    error "TODO"

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
  dropMeta (Def def) = Def (dropMeta def)
  dropMeta (Test name a b) = Test name (dropMeta a) (dropMeta b)
  dropMeta (MetaStmt _ stmt) = dropMeta stmt

instance DropMeta Definition where
  dropMeta :: Definition -> Definition
  dropMeta (ts, p, a) = do
    let ts' = second dropMeta <$> ts
    let p' = dropMeta p
    let a' = dropMeta a
    (ts', p', a')

instance DropMeta Module where
  dropMeta :: Module -> Module
  dropMeta mod = mod {stmts = map dropMeta mod.stmts}

instance DropMeta Package where
  dropMeta :: Package -> Package
  dropMeta pkg = pkg {modules = map dropMeta pkg.modules}

instance DropMeta TestError where
  dropMeta :: TestError -> TestError
  dropMeta (NoTestsFound x) = NoTestsFound x
  dropMeta (TestEqError name got expected) = TestEqError name got expected

eval :: Package -> String -> Expr -> Either (Expr, C.TypeError) (Expr, Expr)
eval pkg m expr = do
  let s = resolve pkg
  let env = lower [] (rename () s pkg)
  let expr' = lower env (rename m s expr)
  let result = C.eval env expr'
  case C.infer env expr' of
    Right (type', _) -> Right (lift result, lift type')
    Left e -> Left (lift result, e)

test :: C.Env -> String -> [TestError]
test env name = do
  let match ('>' : x, _) | name `isInfixOf` x = True
      match _ = False
  let test' (name, expr) = case C.eval env expr of
        C.Tag "pass" [] -> []
        C.Tag "fail" [actual] -> [TestEqError name expr actual]
        unexpected -> error $ show (expr, unexpected)
  concatMap test' (filter match env)

-- test :: Package -> String -> [TestError]
-- test pkg filter = do
--   let s = resolve pkg
--   let pkg' = rename () s pkg
--   let env = lower [] pkg'
--   -- case packageTests filter pkg' of
--   --   [] -> [NoTestsFound filter]
--   --   tests -> concatMap (testEq env) tests
--   error $ show (env :: C.Env)

-- stmtTests :: Stmt -> [(Expr, Pattern)]
-- stmtTests (Test expr expected) = [(expr, expected)]
-- stmtTests (MetaStmt _ stmt) = stmtTests stmt
-- stmtTests _ = []

-- moduleTests :: String -> String -> Module -> [(Expr, Pattern)]
-- moduleTests filter p mod
--   | filter `isInfixOf` (p ++ '/' : mod.name) =
--       concatMap stmtTests mod.stmts
-- moduleTests _ _ _ = []

-- packageTests :: String -> Package -> [(Expr, Pattern)]
-- packageTests filter pkg = concatMap (moduleTests filter pkg.name) pkg.modules

-- testEq :: C.Env -> (Expr, Pattern) -> [TestError]
-- testEq env (expr, expected) = do
--   let unitTest = lower env $ Match [expr] [Case [expected] Nothing (Tuple [])]
--   let passed = case C.eval env unitTest of
--         C.Err -> False
--         -- C.Op2 C.Eq _ _ -> False
--         _ -> True
--   if passed
--     then []
--     else do
--       let actual = lower env expr & C.eval env & lift
--       [TestEqError expr actual expected]
