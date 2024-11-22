module Tao where

import Control.Monad (mapAndUnzipM)
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap), second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (delete, elemIndex, intercalate, isInfixOf, isPrefixOf, nub, union, (\\))
import Data.List.Split (splitWhen, startsWith)
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import System.FilePath (takeBaseName)

data Expr
  = Any
  | Unit
  | IntType
  | NumType
  | Int Int
  | Num Double
  | Var String
  | Tag String
  | For [String] Expr
  | Fun Expr Expr
  | App Expr Expr
  | And Expr Expr
  | Or Expr Expr
  | Ann Expr Type
  | Call String [Expr]
  | Op1 Op1 Expr
  | Op2 Op2 Expr Expr
  | Let (Expr, Expr) Expr
  | Bind (Expr, Expr) Expr
  | If Expr Expr Expr
  | Match [Expr] [Expr]
  | Record [(String, Expr)]
  | Trait Expr String
  | Select Expr [(String, Expr)]
  | With Expr [(String, Expr)]
  | Err
  deriving (Eq, Show)

data Op1
  = Neg
  deriving (Eq, Show)

data Op2
  = Eq
  | Lt
  | Gt
  | Add
  | Sub
  | Mul
  | Div
  | Pow
  deriving (Eq, Show)

data Case
  = Case [Pattern] (Maybe Expr) Expr
  deriving (Eq, Show)

type Pattern = Expr

data Stmt
  = Import String String [(String, String)]
  | Def (Expr, Expr)
  | TypeDef (String, [Expr], Expr)
  | Test String Expr Pattern
  deriving (Eq, Show)

type Type = Expr

type Package = (String, [Module])

type Module = (String, [Stmt])

data UnitTest = UnitTest
  { path :: String,
    name :: String,
    expr :: Expr,
    expect :: Expr
  }
  deriving (Eq, Show)

data TestError = TestError
  { test :: UnitTest,
    got :: Expr
  }
  deriving (Eq, Show)

buildOps :: C.Ops
buildOps = []

runtimeOps :: C.Ops
runtimeOps = buildOps

-- Syntax sugar
tag :: String -> [Expr] -> Expr
tag k args = and' (Tag k : args)

for :: [String] -> Expr -> Expr
for xs a = case filter (`occurs` a) xs of
  [] -> a
  xs -> For xs a

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

funOf :: Expr -> ([Expr], Expr)
funOf (Fun arg ret) = let (args, ret') = funOf ret in (arg : args, ret')
funOf a = ([], a)

app :: Expr -> [Expr] -> Expr
app = foldl App

appOf :: Expr -> (Expr, [Expr])
appOf (App a b) = let (a', bs) = appOf a in (a', bs ++ [b])
appOf a = (a, [])

and' :: [Expr] -> Expr
and' [] = Unit
and' [a] = a
and' (a : bs) = And a (and' bs)

andOf :: Expr -> [Expr]
andOf (And a b) = a : andOf b
andOf a = [a]

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

orOf :: Expr -> [Expr]
orOf (Or a b) = a : orOf b
orOf a = [a]

letVar :: (String, Expr) -> Expr -> Expr
letVar (x, a) = Let (Var x, a)

letVars :: [(String, Expr)] -> Expr -> Expr
letVars defs b = foldr letVar b defs

defVar :: (String, Expr) -> Stmt
defVar (x, a) = Def (Var x, a)

neg :: Expr -> Expr
neg = Op1 Neg

eq :: Expr -> Expr -> Expr
eq = Op2 Eq

lt :: Expr -> Expr -> Expr
lt = Op2 Lt

gt :: Expr -> Expr -> Expr
gt = Op2 Gt

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

pow :: Expr -> Expr -> Expr
pow = Op2 Pow

traitFun :: String -> Expr
traitFun x = lambda ["_"] (Trait (Var "_") x)

select :: Expr -> [String] -> Expr
select a xs = Select a (map (\x -> (x, Var x)) xs)

selectFun :: [String] -> Expr
selectFun xs = lambda ["_"] (Select (Var "_") (map (\x -> (x, Var x)) xs))

lambda :: [String] -> Expr -> Expr
lambda xs = fun (map Var xs)

lambdaOf :: String -> Expr -> ([String], Expr)
lambdaOf _ (Match [] []) = ([], Err)
-- lambdaOf _ (Match [] (([], b) : _)) = ([], b)
-- lambdaOf prefix (Match [] cases) = do
--   let x = lambdaArg prefix cases
--   let matchCase x (ps, b) = case ps of
--         Any : _ -> Just (ps, b)
--         Var x' : ps | x == x' -> Just (ps, b)
--         _ -> Nothing
--   let matchCases x (case' : cases) = do
--         case' <- matchCase x case'
--         cases <- matchCases x cases
--         Just (case' : cases)
--       matchCases _ _ = Just []
--   case matchCases x cases of
--     Just cases -> do
--       let (ys, b) = lambdaOf prefix (match [] cases)
--       (x : ys, b)
--     Nothing -> ([x], Match [Var x] cases)
-- lambdaOf prefix (Meta m a) = do
--   let (xs, a') = lambdaOf prefix a
--   (xs, Meta m a')
-- lambdaOf _ a = ([], a)
lambdaOf x a = error $ "TODO lambdaOf" ++ show (x, a)

lambdaArg :: String -> [([Expr], Expr)] -> String
lambdaArg prefix cases = case popCases cases of
  Just (ps, cases') -> do
    let x = case patternsName ps of
          Just x -> x
          Nothing -> do
            let vars (ps, b) = freeVars (fun ps b)
            C.newName (prefix : concatMap vars cases') prefix
    x
  Nothing -> ""

lambdaArgs :: String -> [([Expr], Expr)] -> [String]
lambdaArgs prefix cases = case popCases cases of
  Just (ps, cases') -> do
    let x = case patternsName ps of
          Just x -> x
          Nothing -> do
            let vars (ps, b) = freeVars (fun ps b)
            C.newName (prefix : concatMap vars cases') prefix
    x : lambdaArgs prefix cases'
  Nothing -> []

popCases :: [([Expr], Expr)] -> Maybe ([Pattern], [([Expr], Expr)])
popCases = mapAndUnzipM popCase

popCase :: ([Expr], Expr) -> Maybe (Pattern, ([Expr], Expr))
popCase ([], _) = Nothing
popCase (p : ps, a) = Just (p, (ps, a))

patternsName :: [Pattern] -> Maybe String
patternsName [] = Nothing
patternsName (p : ps) = case p of
  Var x -> case patternsName ps of
    Just y | x /= y -> Nothing
    _ -> Just x
  _ -> patternsName ps

import' :: String -> [String] -> Stmt
import' m names = Import m (takeBaseName m) (map (\x -> (x, x)) names)

isImport :: Stmt -> Bool
isImport Import {} = True
isImport _ = False

isTest :: Stmt -> Bool
isTest Test {} = True
isTest _ = False

class FreeVars a where
  freeVars :: a -> [String]

instance FreeVars Expr where
  freeVars :: Expr -> [String]
  freeVars (Trait a _) = freeVars a
  freeVars a = C.freeVars (lower [] a :: C.Expr)

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

class Lower a b where
  lower :: C.Env -> a -> b

instance Lower Expr C.Expr where
  lower :: C.Env -> Expr -> C.Expr
  lower _ Any = C.Any
  lower _ Unit = C.Unit
  lower _ IntType = C.IntT
  lower _ NumType = C.NumT
  lower _ (Int i) = C.Int i
  lower _ (Num n) = C.Num n
  lower _ (Var x) = C.Var x
  lower env (Tag k) = C.Tag k
  lower env (For xs a) = C.for xs (lower (C.pushVars xs env) a)
  lower env (Fun a b) = do
    let (args, body) = funOf (Fun a b)
    C.for (concatMap freeVars args) (C.fun (lower env <$> args) (lower env body))
  lower env (App a b) = do
    let a' = lower env a
    case C.infer buildOps env a' of
      Right (C.Fun t _, _) -> case t of
        C.Tag "~" -> C.App a' (C.Tag "~")
        C.And (C.Tag ('~' : xs)) _ ->
          C.App a' (lower env (select b (split ',' xs)))
        _ -> C.App a' (lower env b)
      _ -> C.App a' (lower env b)
  lower env (And a b) = C.And (lower env a) (lower env b)
  lower env (Or a b) = C.Or (lower env a) (lower env b)
  -- lower env (Let def b) = lower (lower env def ++ env) b
  -- lower env (Bind (ts, p, a) b) = lower env (App (Trait a "<-") (Function [p] b))
  lower env (Match [] cases) = lower env (or' cases)
  lower env (Match args cases) =
    lower env (app (Match [] cases) args)
  lower env (Record fields) = do
    let k = '~' : intercalate "," (map fst fields)
    lower env (tag k (map snd fields))
  lower env (Trait a x) = do
    let a' = lower env a
    case C.infer buildOps env a' of
      Right (t, _) -> C.app (C.Var $ '.' : x) [t, a']
      Left _ -> C.Err
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
  lower env (Case ps guard b) = do
    let ps' = map (lower env) ps
    C.for (C.freeVars ps') (C.fun ps' (lower env b))

-- instance Lower Pattern C.Expr where
--   lower :: C.Env -> Pattern -> C.Expr
--   lower _ PAny = C.Var "_"
--   lower _ (PInt i) = C.Int i
--   lower _ (PNum n) = C.Num n
--   lower _ (PVar x) = C.Var x
--   lower env (PTag k ps)
--     | PTag k ps == pIntT = C.IntT
--     | PTag k ps == pNumT = C.NumT
--     | otherwise = C.tag k (map (lower env) ps)
--   lower env (PTuple ps) = lower env (PTag "" ps)
--   lower env (PFun p q) = C.Fun (lower env p) (lower env q)
--   lower env (POr p q) = error "TODO"
--   lower env (PEq a) = error "TODO"
--   lower env (PMeta m p) = C.Meta m (lower env p)
--   lower _ PErr = C.Err

instance Lower Stmt C.Env where
  lower :: C.Env -> Stmt -> C.Env
  lower env (Import m n xs) = case xs of
    [] -> []
    (x, y) : xs -> (y, C.Var x) : lower env (Import m n xs)
  -- lower env (Def p b) = lower env def
  lower env (Test name a p) = [(name, C.And (lower env a) (lower env p))]

instance Lower Module C.Env where
  lower :: C.Env -> Module -> C.Env
  lower env (name, stmts) = concatMap (lower env) stmts

-- instance Lower Package C.Env where
--   lower :: C.Env -> Package -> C.Env
--   lower env pkg = concatMap (lower env) pkg.modules

class Lift a b where
  lift :: a -> b

instance Lift C.Expr Expr where
  lift :: C.Expr -> Expr
  lift C.Any = Any
  lift C.Unit = Unit
  lift C.IntT = IntType
  lift C.NumT = NumType
  lift (C.Int i) = Int i
  lift (C.Num n) = Num n
  lift (C.Var x) = Var x
  lift (C.Tag "~") = Record []
  lift (C.Tag k) = Tag k
  lift (C.For x a) = case lift a of
    For xs a -> For (x : xs) a
    a -> For [x] a
  lift (C.Fix _ a) = lift a
  lift (C.Fun a b) = Fun (lift a) (lift b)
  lift (C.App a b) = case appOf (App (lift a) (lift b)) of
    (Var ('.' : x), _ : a : args) -> app (Trait a x) args
    -- (Trait a "<-", [Fun p b]) -> Bind ([], toPattern p, a) b
    (For x a, args) -> Match args [For x a]
    (Fun a1 a2, args) -> Match args [Fun a1 a2]
    (Or a1 a2, args) -> Match args (orOf (Or a1 a2))
    (a, args) -> app a args
  lift (C.And a b) = case (a, map lift (C.andOf b)) of
    (C.Tag ('~' : names), values) -> do
      let keys = split ',' names
      Record (zip keys values)
    (a, items) -> and' (lift a : items)
  lift (C.Or a b) = Or (lift a) (lift b)
  lift (C.Ann a b) = Ann (lift a) (lift b)
  lift (C.Call op args) = Call op (map lift args)
  lift C.Err = Err

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

class Resolve a where
  resolve :: [Module] -> String -> a -> Maybe (String, Expr)

instance Resolve String where
  resolve :: [Module] -> String -> String -> Maybe (String, Expr)
  resolve ctx path name = do
    stmts <- lookup path ctx
    resolve ctx path (stmts, name)

instance Resolve ([Stmt], String) where
  resolve :: [Module] -> String -> ([Stmt], String) -> Maybe (String, Expr)
  resolve ctx path (stmts, name) = case stmts of
    [] -> Nothing
    stmt : stmts -> case resolve ctx path (stmt, name) of
      Just def -> Just def
      Nothing -> resolve ctx path (stmts, name)

instance Resolve (Stmt, String) where
  resolve :: [Module] -> String -> (Stmt, String) -> Maybe (String, Expr)
  resolve ctx path (stmt, name) = case stmt of
    Import path' alias names -> case names of
      (x, y) : _ | y == name -> resolve ctx path' x
      _ : names -> resolve ctx path (Import path' alias names, name)
      [] | alias == name -> Just (path, Tag path')
      [] -> Nothing
    Def (pattern', body) -> case pattern' of
      Var x | x == name -> Just (path, body)
      _ -> Nothing
    TypeDef (name', args, body) ->
      if name == name'
        then Just (path, body)
        else Nothing
    Test {} -> Nothing

class Compile a where
  compile :: [Module] -> String -> a

instance Compile (String -> (String, C.Expr)) where
  compile :: [Module] -> String -> String -> (String, C.Expr)
  compile ctx path name = do
    let (path', expr) = fromMaybe (path, Err) (resolve ctx path name)
    (name, compile ctx path' expr)

instance Compile ([String] -> C.Env) where
  compile :: [Module] -> String -> [String] -> C.Env
  compile ctx path = map (compile ctx path)

instance Compile (Expr -> C.Expr) where
  compile :: [Module] -> String -> Expr -> C.Expr
  compile ctx path expr = do
    let env = compile ctx path (freeVars expr)
    C.letVars env (lower env expr)

eval :: [Module] -> String -> Expr -> Expr
eval ctx path expr = do
  let ops = []
  compile ctx path expr
    & C.eval ops
    & lift

class RunTest a where
  test :: [Module] -> a -> [TestError]

instance RunTest Package where
  test :: [Module] -> Package -> [TestError]
  test ctx (_, mods) =
    concatMap (test ctx) mods

instance RunTest Module where
  test :: [Module] -> Module -> [TestError]
  test ctx (path, stmts) =
    concatMap (\stmt -> test ctx (path, stmt)) stmts

instance RunTest (String, Stmt) where
  test :: [Module] -> (String, Stmt) -> [TestError]
  test ctx (path, stmt) = case stmt of
    Import {} -> []
    Def {} -> []
    Test name expr expect -> test ctx (UnitTest path name expr expect)

instance RunTest UnitTest where
  test :: [Module] -> UnitTest -> [TestError]
  test ctx t = do
    let test' =
          Match
            [t.expr]
            [ Fun t.expect (Tag "Pass"),
              fun [Var "_"] (Var "_")
            ]
    case eval ctx t.path test' of
      Tag "Pass" -> []
      got -> [TestError {test = t, got = got}]

class FindTests a where
  findTests :: ((String, String) -> Bool) -> a -> [UnitTest]

instance FindTests Package

instance FindTests Module
