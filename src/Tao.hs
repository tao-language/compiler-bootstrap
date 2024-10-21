module Tao where

import Control.Monad (mapAndUnzipM)
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap), second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (elemIndex, intercalate, isInfixOf, isPrefixOf, union)
import Data.List.Split (splitWhen, startsWith)
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import System.FilePath (takeBaseName)

data Expr
  = Int Int
  | Num Double
  | Var String
  | Name String String String
  | Tag String [Expr]
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Fun Expr Expr
  | App Expr Expr
  | Or Expr Expr
  | Ann Expr Type
  | Call String [Expr]
  | Let (Pattern, Expr) Expr
  | Bind (Pattern, Expr) Expr
  | Function [Pattern] Expr
  | Match [Expr] [Case]
  | MatchFun [Case]
  | Trait Expr String
  | Select Expr [(String, Expr)]
  | Update Expr [(String, Expr)]
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
  = Import String String [(String, String)]
  | Def (Pattern, Expr)
  | TestStmt String Expr Pattern
  | MetaStmt C.Metadata Stmt
  deriving (Eq, Show)

data Module = Module
  { name :: String,
    stmts :: [Stmt]
  }
  deriving (Eq, Show)

data Package = Package
  { name :: String,
    modules :: [(String, Module)]
  }
  deriving (Eq, Show)

type Type = Expr

buildOps :: C.Ops
buildOps = []

runtimeOps :: C.Ops
runtimeOps = buildOps

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

lets :: [(String, Expr)] -> Expr -> Expr
lets [] b = b
lets ((x, a) : defs) b = Let (PVar x, a) (lets defs b)

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

traitFun :: String -> Expr
traitFun x = lambda ["_"] (Trait (Var "_") x)

select :: Expr -> [String] -> Expr
select a xs = Select a (map (\x -> (x, Var x)) xs)

selectFun :: [String] -> Expr
selectFun xs = lambda ["_"] (Select (Var "_") (map (\x -> (x, Var x)) xs))

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
import' m names = Import m (takeBaseName m) (map (\x -> (x, x)) names)

isImport :: Stmt -> Bool
isImport Import {} = True
isImport _ = False

isTest :: Stmt -> Bool
isTest TestStmt {} = True
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
toExpr (PInt i) = Int i
toExpr (PNum n) = Num n
toExpr (PVar x) = Var x
toExpr (PTag k ps) = Tag k (map toExpr ps)
toExpr (PTuple items) = Tuple (map toExpr items)
toExpr (PFun p q) = Fun (toExpr p) (toExpr q)
toExpr (POr p q) = Or (toExpr p) (toExpr q)
toExpr (PEq a) = a
toExpr (PMeta m p) = Meta m (toExpr p)
toExpr PErr = Err
toExpr p = error $ "TODO: toExpr " ++ show p

class FreeVars a where
  freeVars :: a -> [String]

instance FreeVars Expr where
  freeVars :: Expr -> [String]
  freeVars a = C.freeVars (lower [] a :: C.Expr)

instance FreeVars Pattern where
  freeVars :: Pattern -> [String]
  freeVars p = C.freeVars (lower [] p :: C.Expr)

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
  lower _ (Name pkg mod x) = C.Var (pkg ++ '/' : mod ++ '.' : x)
  lower env (Tag k args)
    | Tag k args == kind = C.Knd
    | Tag k args == intT = C.IntT
    | Tag k args == numT = C.NumT
    | otherwise = C.tag k (map (lower env) args)
  lower env (Tuple items) = lower env (Tag "" items)
  lower env (Record fields) = do
    let k = '~' : intercalate "," (map fst fields)
    lower env (Tag k (map snd fields))
  lower env (Trait a x) = do
    let a' = lower env a
    case C.infer buildOps env a' of
      Right (t, _) -> C.app (C.Var $ '.' : x) [t, a']
      Left _ -> C.Err
  lower env (Fun a b) = C.Fun (lower env a) (lower env b)
  lower env (App a b) = do
    let a' = lower env a
    case C.infer buildOps env a' of
      Right (C.Fun t _, _) -> case t of
        C.Tag "~" -> C.App a' (C.Tag "~")
        C.And (C.Tag ('~' : xs)) _ ->
          C.App a' (lower env (select b (split ',' xs)))
      _ -> C.App a' (lower env b)
  lower env (Or a b) = C.Or (lower env a) (lower env b)
  -- lower env (Let def b) = lower (lower env def ++ env) b
  -- lower env (Bind (ts, p, a) b) = lower env (App (Trait a "<-") (Function [p] b))
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
      C.tag k (map snd fields')
    a -> error $ "TODO: lower Select " ++ show a
  lower env (Ann a b) = C.Ann (lower env a) (lower env b)
  lower env (Call op args) = C.Call op (map (lower env) args)
  lower env (Meta m a) = C.Meta m (lower env a)
  lower _ Err = C.Err
  lower _ a = error $ "TODO: lower " ++ show a

-- instance Lower Definition C.Env where
--   lower :: C.Env -> Definition -> C.Env
--   lower env (ts, PAny, a) = []
--   lower env (ts, PVar x, a) = case lookup x ts of
--     Just t -> [(x, lower env (Ann a t))]
--     Nothing -> [(x, lower env a)]
--   lower env (ts, PMeta m p, a) = do
--     lower env (ts, p, a) & map (second $ C.Meta m)
--   lower env (ts, p, a) = error $ "TODO lower Definition " ++ show p

instance Lower Case C.Expr where
  lower :: C.Env -> Case -> C.Expr
  lower env (Case ps guard b) = C.fun (map (lower env) ps) (lower env b)

instance Lower Pattern C.Expr where
  lower :: C.Env -> Pattern -> C.Expr
  lower _ PAny = C.Var "_"
  lower _ (PInt i) = C.Int i
  lower _ (PNum n) = C.Num n
  lower _ (PVar x) = C.Var x
  lower env (PTag k ps)
    | PTag k ps == pIntT = C.IntT
    | PTag k ps == pNumT = C.NumT
    | otherwise = C.tag k (map (lower env) ps)
  lower env (PTuple ps) = lower env (PTag "" ps)
  lower env (PFun p q) = C.Fun (lower env p) (lower env q)
  lower env (POr p q) = error "TODO"
  lower env (PEq a) = error "TODO"
  lower env (PMeta m p) = C.Meta m (lower env p)
  lower _ PErr = C.Err

instance Lower Stmt C.Env where
  lower :: C.Env -> Stmt -> C.Env
  lower env (Import m n xs) = case xs of
    [] -> []
    (x, y) : xs -> (y, C.Var x) : lower env (Import m n xs)
  -- lower env (Def p b) = lower env def
  lower env (TestStmt name a p) = [(name, C.And (lower env a) (lower env p))]
  lower env (MetaStmt _ stmt) = lower env stmt

instance Lower Module C.Env where
  lower :: C.Env -> Module -> C.Env
  lower env mod = concatMap (lower env) mod.stmts

-- instance Lower Package C.Env where
--   lower :: C.Env -> Package -> C.Env
--   lower env pkg = concatMap (lower env) pkg.modules

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
  lift (C.Tag "") = Tuple []
  lift (C.Tag "~") = Record []
  lift (C.Tag k) = Tag k []
  lift (C.For _ a) = lift a
  lift (C.Fix _ a) = lift a
  lift (C.Fun a b) = Fun (lift a) (lift b)
  lift (C.App a b) = case appOf (App (lift a) (lift b)) of
    (Var ('.' : x), _ : a : args) -> app (Trait a x) args
    -- (Trait a "<-", [Fun p b]) -> Bind ([], toPattern p, a) b
    (a, args) -> app a args
  lift (C.And a b) = case (a, map lift (C.andOf b)) of
    (C.Tag "", items) -> Tuple items
    (C.Tag ('~' : names), values) -> do
      let keys = split ',' names
      Record (zip keys values)
    (C.Tag k, args) -> Tag k args
    (a, items) -> Tuple (lift a : items)
  lift (C.Or a b) = Or (lift a) (lift b)
  lift (C.Ann a b) = Ann (lift a) (lift b)
  lift (C.Call op args) = Call op (map lift args)
  lift (C.Meta m a) = Meta m (lift a)
  lift C.Err = Err

toPattern :: Expr -> Pattern
toPattern (Var x) = PVar x

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
  [x] -> ("", x)
  [x, y] -> (x, y)
  x : ys -> (x, intercalate [delim] ys)

nameWords :: String -> [String]
nameWords name =
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

nameSplit :: String -> (String, String, String)
nameSplit ('@' : pkgModName) = nameSplit pkgModName
nameSplit pkgModName = do
  let (pkgMod, name) =
        if '.' `elem` pkgModName
          then split2 '.' pkgModName
          else (pkgModName, "")
  let (pkg, mod) = case pkgMod of
        '/' : mod -> ("", mod)
        _ -> split2 '/' pkgMod
  (pkg, mod, name)

nameIdentifier :: String -> String
nameIdentifier name = split2 '.' name & snd

nameModule :: String -> String
nameModule name = let (_, m, _) = nameSplit name in m

namePackage :: String -> String
namePackage name = let (p, _, _) = nameSplit name in p

namePrefix :: String -> String
namePrefix name = split2 '.' name & fst

nameCamelCaseUpper :: String -> String
nameCamelCaseUpper name =
  nameWords name
    & map capitalize
    & intercalate ""

nameCamelCaseLower :: String -> String
nameCamelCaseLower name = case nameWords name of
  [] -> ""
  (x : xs) -> intercalate "" (x : map capitalize xs)

nameSnakeCase :: String -> String
nameSnakeCase name = nameWords name & intercalate "_"

nameDashCase :: String -> String
nameDashCase name = nameWords name & intercalate "-"

isImported :: String -> Stmt -> Bool
isImported x (Import _ _ exposed) = x `elem` map fst exposed
isImported _ _ = False

in' :: String -> String -> Bool
in' _ "" = False
in' substring string | substring `isPrefixOf` string = True
in' substring (_ : string) = in' substring string

class DropMeta a where
  dropMeta :: a -> a

instance DropMeta Expr where
  dropMeta :: Expr -> Expr
  dropMeta = \case
    Int i -> Int i
    Meta _ a -> dropMeta a
    MatchFun cases -> MatchFun (map dropMeta cases)
    expr -> error $ "TODO: dropMeta " ++ show expr

instance DropMeta Pattern where
  dropMeta :: Pattern -> Pattern
  dropMeta = \case
    PAny -> PAny
    PInt i -> PInt i
    PNum n -> PNum n
    PVar x -> PVar x
    PTag k ps -> PTag k (dropMeta <$> ps)
    PTuple ps -> PTuple (dropMeta <$> ps)
    PRecord kps -> PRecord (second dropMeta <$> kps)
    PTrait p x -> PTrait (dropMeta p) x
    PMeta _ p -> dropMeta p
    PErr -> PErr
    p -> error $ "TODO: dropMeta " ++ show p

instance DropMeta Case where
  dropMeta :: Case -> Case
  dropMeta (Case ps guard a) =
    Case (map dropMeta ps) (fmap dropMeta guard) (dropMeta a)

instance DropMeta Stmt where
  dropMeta :: Stmt -> Stmt
  dropMeta stmt@Import {} = stmt
  dropMeta (Def (p, b)) = Def (dropMeta p, dropMeta b)
  dropMeta (TestStmt name a b) = TestStmt name (dropMeta a) (dropMeta b)
  dropMeta (MetaStmt _ stmt) = dropMeta stmt

instance DropMeta Module where
  dropMeta :: Module -> Module
  dropMeta mod = mod {stmts = map dropMeta mod.stmts}

instance DropMeta Package where
  dropMeta :: Package -> Package
  dropMeta pkg = pkg {modules = map (second dropMeta) pkg.modules}

-- eval :: Package -> String -> Expr -> Either (Expr, C.TypeError) (Expr, Expr)
-- eval pkg m expr = do
--   let s = resolve () pkg
--   let env = lower [] (replace () s pkg)
--   let expr' = lower env (replace (pkg.name, m) s expr)
--   let result = C.eval env expr'
--   case C.infer env expr' of
--     Right (type', _) -> Right (lift result, lift type')
--     Left e -> Left (lift result, e)

-- data UnitTest = UnitTest
--   { name :: String,
--     expr :: Expr,
--     expect :: Pattern
--   }

-- data TestError
--   = NoTestsFound String
--   | TestEqError String C.Expr C.Expr C.Expr
--   | NotATest String C.Expr
--   deriving (Eq, Show)

-- test :: C.Env -> String -> [TestError]
-- test env name = do
--   let match ('>' : x, _) | name `isInfixOf` x = True
--       match _ = False
--   let test' (name, expr) = case expr of
--         C.And a p -> do
--           let run =
--                 C.match' [a] $
--                   [ ([p], C.Tag "Pass"),
--                     ([C.Var "_"], C.Var "_")
--                   ]
--           case C.eval env run of
--             C.Tag "Pass" -> []
--             actual -> [TestEqError name a p actual]
--   case filter match env of
--     [] -> [NoTestsFound name]
--     tests -> concatMap test' tests

-- test :: Package -> String -> [TestError]
-- test pkg filter = do
--   let s = resolve' pkg
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

-- class Find a where
--   find :: String -> a -> Maybe Expr

-- instance Find Module where
--   find :: String -> Module -> Maybe Expr
--   find x mod = case mod.stmts of
--     [] -> Nothing
--     stmt : stmts -> case find x stmt of
--       Just a -> Just a
--       Nothing -> find x (mod {stmts = stmts})

-- instance Find Stmt where
--   find :: String -> Stmt -> Maybe Expr
--   find x = \case
--     Def (p, b) -> case p of
--       PVar x' | x == x' -> Just b
--       PVar _ -> Nothing
--     _ -> Nothing

-- class Compile a b where
--   compile :: a -> b

-- instance Compile Package [(String, C.Module)] where
--   compile :: Package -> [(String, C.Module)]
--   compile pkg = error "TODO"

-- instance Compile (Package, Module) C.Module where
--   compile :: (Package, Module) -> C.Module
--   compile (pkg, mod) =
--     C.Module
--       { values = [],
--         types = [],
--         tests = []
--       }

-- instance Compile (Package, Stmt) (C.Module -> C.Module) where
--   compile :: (Package, Stmt) -> C.Module -> C.Module
--   compile (pkg, stmt) mod = case stmt of
--     Import path alias names -> case lookup path pkg.modules of
--       Just imported -> do
--         let imported' = compile (pkg, imported) :: C.Module
--         case names of
--           [] -> mod -- TODO: make record of imported'
--           (x, y) : names -> do
--             let mod' = compile (pkg, Import path alias names) mod :: C.Module
--             case lookup x imported'.values of
--               Just a -> mod' {C.values = (y, a) : mod'.values}
--               Nothing -> mod'
--       Nothing -> mod
--     Def (p, b) -> case p of
--       PAny -> error "TODO"
--       PVar x -> mod {C.values = (x, compile (pkg, b)) : mod.values}
--     TestStmt name a p -> error "TODO"
--     MetaStmt m stmt -> error "TODO"

-- instance Compile (Package, Expr) C.Expr where
--   compile :: (Package, Expr) -> C.Expr
--   compile (pkg, expr) = case expr of
--     Err -> C.Err

-- class ContextOf a b where
--   contextOf :: String -> a -> b

-- instance ContextOf Package' Context where
--   contextOf :: String -> Package' -> Context
--   contextOf name =
--     map
--       ( \(path, stmts) -> do
--           let path' = name ++ '/' : path
--           (path', contextOf path' stmts)
--       )

-- instance ContextOf [Stmt] [(String, Symbol)] where
--   contextOf :: String -> [Stmt] -> [(String, Symbol)]
--   contextOf path = concatMap (contextOf path)

-- instance ContextOf Stmt [(String, Symbol)] where
--   contextOf :: String -> Stmt -> [(String, Symbol)]
--   contextOf path stmt = case stmt of
--     Import path' alias names -> case names of
--       [] -> [(alias, Imported path' "")]
--       (x, y) : names ->
--         (y, Imported path' x) : contextOf path (Import path' alias names)
--     Def (p, b) -> case p of
--       PVar x -> [(x, Defined b)]
--     TestStmt {} -> []
--     MetaStmt _ stmt -> contextOf path stmt

data Symbol
  = Defined Expr
  | Imported String String
  | Test String Expr Expr

type Package' = (String, [Module'])

type Module' = (String, [Stmt])

class Compile a b where
  compile :: Package' -> a -> b

instance Compile Package' [(String, C.Module)] where
  compile :: Package' -> Package' -> [(String, C.Module)]
  compile ctx (name, modules) =
    map (compile ctx) modules

instance Compile Module' (String, C.Module) where
  compile :: Package' -> Module' -> (String, C.Module)
  compile ctx (path, stmts) = do
    let mod =
          C.Module
            { path = path,
              values = [],
              types = [],
              tests = []
            }
    (path, foldl (compile ctx) mod stmts)

instance Compile C.Module (Stmt -> C.Module) where
  compile :: Package' -> C.Module -> Stmt -> C.Module
  compile ctx mod stmt = case stmt of
    Import {} -> mod
    Def (p, b) -> foldl (compile ctx) mod (map (,b) (freeVars p))
    TestStmt name expr expect -> mod
    MetaStmt _ stmt -> compile ctx mod stmt

instance Compile C.Module ((String, Expr) -> C.Module) where
  compile :: Package' -> C.Module -> (String, Expr) -> C.Module
  compile ctx mod (name, expr) = case lookup name mod.values of
    Just _ -> mod
    Nothing -> do
      mod {C.values = (name, compile ctx mod.path expr) : mod.values}

instance Compile String (Expr -> C.Expr) where
  compile :: Package' -> String -> Expr -> C.Expr
  compile ctx path expr = do
    let xs = freeVars expr
    C.Err

class FindName a where
  findName :: [Module'] -> String -> String -> a

instance FindName (Maybe (String, Expr)) where
  findName :: [Module'] -> String -> String -> Maybe (String, Expr)
  findName ctx path name = do
    stmts <- lookup path ctx
    findName ctx path name stmts

instance FindName ([Stmt] -> Maybe (String, Expr)) where
  findName :: [Module'] -> String -> String -> [Stmt] -> Maybe (String, Expr)
  findName ctx path name stmts = case stmts of
    [] -> Nothing
    stmt : stmts -> case findName ctx path name stmt of
      Just def -> Just def
      Nothing -> findName ctx path name stmts

instance FindName (Stmt -> Maybe (String, Expr)) where
  findName :: [Module'] -> String -> String -> Stmt -> Maybe (String, Expr)
  findName ctx path name stmt = case stmt of
    Import path' alias names -> case names of
      [] | alias == name -> Just (path, Tag path' [])
      (x, y) : _ | y == name -> findName ctx path' x
      _ : names -> findName ctx path name (Import path' alias names)
      _ -> Nothing
    Def (p, b) -> case p of
      PVar x | x == name -> Just (path, b)
      _ -> Nothing
    TestStmt {} -> Nothing
    MetaStmt _ stmt -> findName ctx path name stmt

dependencies :: [Module'] -> String -> Expr -> [(String, Expr)]
dependencies ctx path expr =
  map (\x -> (x, resolve ctx path x)) (freeVars expr)

resolve :: [Module'] -> String -> String -> Expr
resolve ctx path name = do
  let (path', expr) =
        findName ctx path name
          & fromMaybe (path, Err)
  lets (dependencies ctx path' expr) expr
