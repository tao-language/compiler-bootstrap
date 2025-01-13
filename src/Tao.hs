{-# OPTIONS_GHC -Wno-type-defaults #-}

module Tao where

import Control.Monad (mapAndUnzipM)
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap), second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (delete, elemIndex, intercalate, isInfixOf, isPrefixOf, nub, sort, union, unionBy, (\\))
import Data.List.Split (splitWhen, startsWith)
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import System.FilePath (takeBaseName)

data Expr
  = Any
  | Unit
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Tag String
  | Var String
  | Ann Expr Type
  | And Expr Expr
  | Or Expr Expr
  | For [String] Expr
  | Fun Pattern Expr
  | App Expr Expr
  | Call String [Expr]
  | Op1 Op1 Expr
  | Op2 Op2 Expr Expr
  | Match [Expr] [Case]
  | If Expr Expr Expr
  | Let (Pattern, Expr) Expr
  | Bind (Pattern, Expr) Expr
  | Record [(String, Expr)]
  | Select Expr [(String, Expr)]
  | With Expr [(String, Expr)]
  | Err
  deriving (Eq, Show)

data Op1
  = Neg
  deriving (Eq)

data Op2
  = Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge
  | Add
  | Sub
  | Mul
  | Div
  | DivI
  | Pow
  deriving (Eq)

instance Show Op1 where
  show :: Op1 -> String
  show = \case
    Neg -> "-"

instance Show Op2 where
  show :: Op2 -> String
  show = \case
    Eq -> "=="
    Ne -> "!="
    Lt -> "<"
    Le -> "<="
    Gt -> ">"
    Ge -> ">="
    Add -> "+"
    Sub -> "-"
    Mul -> "*"
    Div -> "/"
    DivI -> "//"
    Pow -> "^"

type Case = ([String], [Pattern], Expr)

type Pattern = Expr

data Stmt
  = Import String String [(String, String)]
  | Def (Expr, Expr)
  | TypeDef (String, [Expr], [(Expr, Maybe Type)])
  | Test (Int, Int) String Expr Pattern
  deriving (Eq, Show)

type Type = Expr

type Package = (String, [Module])

type Module = (String, [Stmt])

type Context = [Module]

data UnitTest = UnitTest
  { filename :: String,
    pos :: (Int, Int),
    name :: String,
    expr :: Expr,
    expect :: Expr
  }
  deriving (Eq, Show)

data TestResult
  = TestPass
      { filename :: String,
        pos :: (Int, Int),
        name :: String
      }
  | TestFail
      { filename :: String,
        pos :: (Int, Int),
        name :: String,
        test :: Expr,
        expected :: Expr,
        got :: Expr
      }
  deriving (Eq)

instance Show TestResult where
  show :: TestResult -> String
  show result = case result of
    TestPass filename (row, col) name -> "✅ " ++ filename ++ ":" ++ show row ++ ":" ++ show col ++ " -- " ++ name ++ "\n"
    TestFail filename (row, col) name test expect got -> "❌ " ++ filename ++ ":" ++ show row ++ ":" ++ show col ++ " -- " ++ name ++ "\n  > " ++ show test ++ "\n  " ++ show expect ++ "\n* " ++ show got ++ "\n"

buildOps :: C.Ops
buildOps = do
  let call op f = (op, \eval args -> f (map (C.dropTypes . eval) args))
  let intOp1 op f = call op $ \case
        [C.Int x] -> Just (f x)
        _ -> Nothing
  let numOp1 op f = call op $ \case
        [C.Num x] -> Just (f x)
        _ -> Nothing
  let intOp2 op f = call op $ \case
        [C.Int x, C.Int y] -> Just (f x y)
        _ -> Nothing
  let numOp2 op f = call op $ \case
        [C.Num x, C.Num y] -> Just (f x y)
        _ -> Nothing
  [ intOp1 "int_neg" (\x -> C.Int (-x)),
    numOp1 "num_neg" (\x -> C.Num (-x)),
    intOp2 "int_lt" (\x y -> C.Tag (if x < y then "True" else "False")),
    intOp2 "int_add" (\x y -> C.Int (x + y)),
    intOp2 "int_sub" (\x y -> C.Int (x - y)),
    intOp2 "int_mul" (\x y -> C.Int (x * y)),
    intOp2 "int_div" (\x y -> C.Num (fromIntegral x / fromIntegral y)),
    intOp2 "int_divi" (\x y -> C.Int (Prelude.div x y)),
    intOp2 "int_pow" (\x y -> C.Int (x ^ y)),
    numOp2 "num_lt" (\x y -> C.Tag (if x < y then "True" else "False")),
    numOp2 "num_add" (\x y -> C.Num (x + y)),
    numOp2 "num_sub" (\x y -> C.Num (x - y)),
    numOp2 "num_mul" (\x y -> C.Num (x * y)),
    numOp2 "num_div" (\x y -> C.Num (x / y)),
    numOp2 "num_divi" (\x y -> C.Num (fromIntegral (floor (x / y)))),
    numOp2 "num_pow" (\x y -> C.Num (x ** y))
    ]

runtimeOps :: C.Ops
runtimeOps = buildOps

-- Syntax sugar
tag :: String -> [Expr] -> Expr
tag k args = and' (Tag k : args)

tag1 :: String -> Expr -> Expr
tag1 k a = tag k [a]

tag2 :: String -> Expr -> Expr -> Expr
tag2 k a b = tag k [a, b]

var1 :: String -> Expr -> Expr
var1 x = App (Var x)

var2 :: String -> Expr -> Expr -> Expr
var2 x a = App (var1 x a)

for :: [String] -> Expr -> Expr
for xs (For ys a) = for (xs ++ ys) a
for [] (Fun a b) = For [] (Fun a b)
for xs (Fun a b) = do
  let args = funArgsOf (Fun a b)
  let xs' = filter (\x -> x `occurs` and' args) xs
  For xs' (Fun a b)
for xs a = case filter (`occurs` a) xs of
  [] -> a
  xs -> For xs a

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

funOf :: Expr -> ([Expr], Expr)
funOf (Fun arg ret) = let (args, ret') = funOf ret in (arg : args, ret')
funOf a = ([], a)

funArgsOf :: Expr -> [Expr]
funArgsOf = fst . funOf

app' :: [Expr] -> Expr
app' [] = Err
app' [a] = a
app' (a : bs) = app a bs

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

let' :: (Expr, Expr) -> Expr -> Expr
let' (Var x, b) (Var x') | x == x' = b
let' (a, b) c = Let (a, b) c

letVar :: (String, Expr) -> Expr -> Expr
letVar (x, a) = Let (Var x, a)

letVars :: [(String, Expr)] -> Expr -> Expr
letVars defs b = foldr letVar b defs

neg :: Expr -> Expr
neg = Op1 Neg

eq :: Expr -> Expr -> Expr
eq = Op2 Eq

ne :: Expr -> Expr -> Expr
ne = Op2 Ne

lt :: Expr -> Expr -> Expr
lt = Op2 Lt

le :: Expr -> Expr -> Expr
le = Op2 Le

gt :: Expr -> Expr -> Expr
gt = Op2 Gt

ge :: Expr -> Expr -> Expr
ge = Op2 Ge

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

div' :: Expr -> Expr -> Expr
div' = Op2 Div

divI :: Expr -> Expr -> Expr
divI = Op2 DivI

pow :: Expr -> Expr -> Expr
pow = Op2 Pow

lets :: [(Pattern, Expr)] -> Expr -> Expr
lets defs b = foldr Let b defs

letOf :: Expr -> ([(Pattern, Expr)], Expr)
letOf (Let def a) = let (defs, a') = letOf a in (def : defs, a')
letOf a = ([], a)

select :: Expr -> [String] -> Expr
select a xs = Select a (map (\x -> (x, Var x)) xs)

selectFun :: [(String, Expr)] -> Expr
selectFun fields = lambda ["_"] (Select (Var "_") fields)

with :: Expr -> [String] -> Expr
with a xs = With a (map (\x -> (x, Var x)) xs)

withFun :: [(String, Expr)] -> Expr
withFun fields = lambda ["_"] (With (Var "_") fields)

list :: [Expr] -> Expr
list [] = Tag "[]"
list (x : xs) = tag "::" [x, list xs]

lambda :: [String] -> Expr -> Expr
lambda xs = fun (map Var xs)

lambdaOf :: String -> Expr -> ([String], Expr)
lambdaOf _ (Match [] []) = ([], Err)
lambdaOf _ (Match [] ((_, [], b) : _)) = ([], b)
lambdaOf prefix (Match [] cases) = do
  let x = lambdaArg prefix cases
  let matchCase x (xs, ps, b) = case ps of
        Any : _ -> Just (xs, ps, b)
        Var x' : ps | x == x' && x `elem` xs -> Just (xs, ps, b)
        _ -> Nothing
  let matchCases x (case' : cases) = do
        case' <- matchCase x case'
        cases <- matchCases x cases
        Just (case' : cases)
      matchCases _ _ = Just []
  case matchCases x cases of
    Just cases -> do
      let (ys, b) = lambdaOf prefix (Match [] cases)
      (x : ys, b)
    Nothing -> ([x], Match [Var x] cases)
-- lambdaOf prefix (Meta m a) = do
--   let (xs, a') = lambdaOf prefix a
--   (xs, Meta m a')
lambdaOf _ a = ([], a)

lambdaArg :: String -> [Case] -> String
lambdaArg prefix cases = case popCases cases of
  Just (ps, cases') -> do
    let x = case patternsName ps of
          Just x -> x
          Nothing -> do
            C.newName (prefix : concatMap (\(xs, _, _) -> xs) cases') prefix
    x
  Nothing -> ""

lambdaArgs :: String -> [Case] -> [String]
lambdaArgs prefix cases = case popCases cases of
  Just (ps, cases') -> do
    let x = case patternsName ps of
          Just x -> x
          Nothing -> do
            C.newName (prefix : concatMap (\(xs, _, _) -> xs) cases') prefix
    x : lambdaArgs prefix cases'
  Nothing -> []

popCases :: [Case] -> Maybe ([Pattern], [Case])
popCases = mapAndUnzipM popCase

popCase :: Case -> Maybe (Pattern, Case)
popCase (_, [], _) = Nothing
popCase (xs, p : ps, a) = Just (p, (xs, ps, a))

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

isDef :: Stmt -> Bool
isDef Def {} = True
isDef _ = False

asDef :: Stmt -> Maybe (Pattern, Expr)
asDef (Def def) = Just def
asDef _ = Nothing

isTest :: Stmt -> Bool
isTest Test {} = True
isTest _ = False

asTest :: Stmt -> Maybe (String, Expr, Pattern)
asTest (Test _ name a p) = Just (name, a, p)
asTest _ = Nothing

freeNames :: (Bool, Bool, Bool) -> Expr -> [String]
freeNames (vars, tags, calls) = \case
  Any -> []
  Unit -> []
  IntT -> []
  NumT -> []
  Int _ -> []
  Num _ -> []
  Var x
    | vars -> [x]
    | otherwise -> []
  Tag k
    | tags -> [k]
    | otherwise -> []
  Ann a b -> freeNames' a `union` freeNames' b
  And a b -> freeNames' a `union` freeNames' b
  Or a b -> freeNames' a `union` freeNames' b
  For xs a -> filter (`notElem` xs) (freeNames' a)
  Fun a b -> freeNames' a `union` freeNames' b
  App a b -> freeNames' a `union` freeNames' b
  Call f args
    | calls -> [f] `union` freeNames' (and' args)
    | otherwise -> freeNames' (and' args)
  Op1 op a
    | vars -> [show op] `union` freeNames' a
    | otherwise -> freeNames' a
  Op2 op a b
    | vars -> [show op] `union` freeNames' a `union` freeNames' b
    | otherwise -> freeNames' a `union` freeNames' b
  Let (a, b) c -> freeNames' a `union` freeNames' b `union` freeNames' c
  Bind (a, b) c -> freeNames' a `union` freeNames' b `union` freeNames' c
  If a b c -> freeNames' a `union` freeNames' b `union` freeNames' c
  Match args cases -> freeNames' (and' args) `union` freeNames' (and' (map (\(xs, ps, b) -> for xs (fun ps b)) cases))
  Record fields -> freeNames' (and' (map snd fields))
  Select a fields -> freeNames' a `union` freeNames' (and' (map snd fields))
  With a fields -> freeNames' a `union` freeNames' (and' (map snd fields))
  Err -> []
  where
    freeNames' = freeNames (vars, tags, calls)

freeVars :: Expr -> [String]
freeVars = freeNames (True, False, False)

freeTags :: Expr -> [String]
freeTags = freeNames (False, True, False)

bindings :: Expr -> [String]
bindings = \case
  For xs _ -> xs
  App a _ -> bindings a
  Op1 op _ -> [show op]
  Op2 op _ _ -> [show op]
  a -> freeVars a

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

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

lower :: Expr -> C.Expr
lower = \case
  Any -> C.Any
  Unit -> C.Unit
  IntT -> C.IntT
  NumT -> C.NumT
  Int i -> C.Int i
  Num n -> C.Num n
  Var x -> C.Var x
  Tag k -> C.Tag k
  Ann a b -> C.Ann (lower a) (lower b)
  And a b -> C.And (lower a) (lower b)
  Or a b -> C.Or (lower a) (lower b)
  For xs (For ys a) -> lower (For (xs ++ ys) a)
  For [] (Fun a b) -> do
    let (args, body) = funOf (Fun a b)
    C.fun (map lower args) (lower body)
  For [] a -> lower a
  For xs a -> C.for xs (lower (For [] a))
  Fun a b -> do
    let (args, body) = funOf (Fun a b)
    lower (For (freeVars (and' args)) (fun args body))
  App a b -> C.App (lower a) (lower b)
  Call op args -> C.Call op (map lower args)
  Op1 op a -> lower (App (Var (show op)) a)
  Op2 op a b -> lower (app (Var (show op)) [a, b])
  Let (a, b) c -> case a of
    Var x | c == Var x -> lower b
    Var x -> C.App (lower (Fun a c)) (C.fix [x] (lower b))
    Ann (Or a1 a2) t -> lower (lets [(Ann a1 t, b), (Ann a2 t, b)] c)
    Ann (App a1 a2) t -> lower (Let (Ann a1 t, Fun a2 b) c)
    Ann (Op1 op a) t -> lower (Let (Ann (Var (show op)) t, Fun a b) c)
    Ann (Op2 op a1 a2) t -> lower (Let (Ann (Var (show op)) t, fun [a1, a2] b) c)
    Ann a t -> lower (Let (a, Ann b t) c)
    Or a1 a2 -> lower (lets [(a1, b), (a2, b)] c)
    App a1 a2 -> lower (Let (a1, Fun a2 b) c)
    Op1 op a -> lower (Let (Var (show op), Fun a b) c)
    Op2 op a1 a2 -> lower (Let (Var (show op), fun [a1, a2] b) c)
    For xs a -> lower (App (For xs (Fun a c)) b)
    a -> lower (App (Fun a c) b)
  -- lower env (Bind (ts, p, a) b) = lower env (App (Trait a "<-") (Function [p] b))
  If a b c -> lower (Match [a] [([], [Tag "True"], b), ([], [], c)])
  Match args [(xs, ps, b)] -> lower (app (For xs $ fun ps b) args)
  Match args cases -> do
    let n = foldl max 0 (map (\(_, ps, _) -> length ps) cases)
    let rpad :: Int -> a -> [a] -> [a]
        rpad n x xs = xs ++ replicate (n - length xs) x
    let cases' = map (\(xs, ps, b) -> for xs $ fun (rpad n Any ps) b) cases
    let args' = map (\i -> Var ("$" ++ show i)) [length args + 1 .. n]
    let match' = fun args' (app (or' cases') (args ++ args'))
    lower match'
  Record fields -> do
    let k = '~' : intercalate "," (map fst fields)
    lower (tag k (map snd fields))
  Select a kvs -> do
    let sub = case a of
          Record fields -> map (second lower) fields
          a -> do
            let xs = freeVars (and' (map snd kvs))
            map (\x -> (x, C.App (C.Var x) (lower a))) xs
    let k = '~' : intercalate "," (map fst kvs)
    let args = map ((C.substitute sub . lower) . snd) kvs
    C.tag k args
  Err -> C.Err
  a -> error $ "TODO: lower " ++ show a

lift :: C.Expr -> Expr
lift = \case
  C.Any -> Any
  C.Unit -> Unit
  C.IntT -> IntT
  C.NumT -> NumT
  C.Int i -> Int i
  C.Num n -> Num n
  C.Var x -> Var x
  C.Tag "~" -> Record []
  C.Tag k -> Tag k
  C.Ann a b -> Ann (lift a) (lift b)
  C.And a b -> case (a, map lift (C.andOf b)) of
    (C.Tag ('~' : names), values) -> do
      let keys = split ',' names
      Record (zip keys values)
    (a, items) -> and' (lift a : items)
  C.Or a b -> Or (lift a) (lift b)
  C.For x a -> case lift a of
    For xs a -> for (x : xs) a
    a -> for [x] a
  C.Fix x a
    | x `C.occurs` a -> Let (Var x, lift a) (lift a)
    | otherwise -> lift a
  C.Fun a b -> Fun (lift a) (lift b)
  C.App a b -> App (lift a) (lift b)
  C.Call op args -> Call op (map lift args)
  C.Let [] b -> lift b
  C.Let ((x, b) : env) c -> Let (Var x, lift b) (lift (C.Let env c))
  C.Err -> Err

simplify :: Expr -> Expr
-- C.App a b -> case appOf (App (lift a) (lift b)) of
--   -- (Var ('.' : x), _ : a : args) -> app (Trait a x) args
--   -- (Trait a "<-", [Fun p b]) -> Bind ([], toPattern p, a) b
--   (Var "==", [And a b]) -> Op2 Eq a b
--   (Var "<", [And a b]) -> Op2 Lt a b
--   (Var ">", [And a b]) -> Op2 Gt a b
--   (Var "+", [And a b]) -> Op2 Add a b
--   (Var "-", [And a b]) -> Op2 Sub a b
--   (Var "*", [And a b]) -> Op2 Mul a b
--   (Var "/", [And a b]) -> Op2 Div a b
--   (Var "^", [And a b]) -> Op2 Pow a b
--   (Var "-", [a]) -> Op1 Neg a
--   (For xs (Fun a c), [b]) -> Let (for xs a, b) c
--   (For xs (Fun a c), [b])
--     | sort (bindings a) == sort xs -> Let (a, b) c
--     | otherwise -> Let (For xs a, b) c
--   (Fun a c, [b])
--     | null (bindings a) -> Let (a, b) c
--     | otherwise -> Let (For [] a, b) c
--   (For xs a, args) -> Match args [For xs a]
--   (Fun a1 a2, args) -> Match args [Fun a1 a2]
--   (Or a1 a2, args) -> Match args (orOf (Or a1 a2))
--   (a, args) -> app a args
simplify a = a

eval :: Context -> String -> Expr -> Expr
eval ctx path expr = do
  let (env, expr') = compile ctx path expr
  lift (C.eval runtimeOps (C.let' env expr'))

class Resolve a where
  resolve :: Context -> String -> a -> [(String, Expr)]

instance Resolve String where
  resolve :: Context -> String -> String -> [(String, Expr)]
  resolve ctx path name = case lookup path ctx of
    Just stmts -> resolve ctx path (name, stmts)
    Nothing -> []

instance Resolve (String, [Stmt]) where
  resolve :: Context -> String -> (String, [Stmt]) -> [(String, Expr)]
  resolve ctx path (name, stmts) =
    concatMap (\stmt -> resolve ctx path (name, stmt)) stmts

instance Resolve (String, Stmt) where
  resolve :: Context -> String -> (String, Stmt) -> [(String, Expr)]
  resolve ctx path (name, stmt) = case stmt of
    Import path' alias names -> case names of
      (x, y) : names -> do
        let defs = if y == name then resolve ctx path' x else []
        defs ++ resolve ctx path (name, Import path' alias names)
      [] | alias == name -> [(path, Tag path')]
      [] -> []
    Def (p, b) | name `elem` bindings p -> [(path, Let (p, b) (Var name))]
    TypeDef (name', args, alts) | name == name' -> do
      let resolveAlt (a, Just b) = Fun a b
          resolveAlt (a, Nothing) = Fun a (tag name' args)
      [(path, fun args (or' (map resolveAlt alts)))]
    _ -> []

class Compile a where
  compile :: Context -> String -> a

instance Compile (String -> C.Env) where
  compile :: Context -> String -> String -> C.Env
  -- compile ctx path name@"+" = do
  --   let compileDef :: (FilePath, Expr) -> (C.Env, [C.Expr]) -> (C.Env, [C.Expr])
  --       compileDef (path, alt) (env, alts) = do
  --         let (env', alt') = compile ctx path (name, alt)
  --         (unionBy (\a b -> fst a == fst b) env' env, alt' : alts)
  --   let (env, alts) = foldr compileDef ([], []) (resolve ctx path name)
  --   let def = case alts of
  --         [] -> []
  --         [C.Var x] | x == name -> [(name, C.Var x)]
  --         [C.Ann (C.Var x) t] | x == name -> [(name, C.Ann (C.Var x) t)]
  --         alts -> [(name, C.fix [name] (C.or' alts))]
  --   -- unionBy (\a b -> fst a == fst b) def env
  --   let ((a, t), s, e) = C.infer buildOps env (C.or' alts)
  --   error . intercalate "\n" $
  --     [ "-- compile/1 " ++ name,
  --       show env,
  --       -- show $ map C.format alts,
  --       C.format a,
  --       C.format t,
  --       ""
  --     ]
  compile ctx path name = do
    let compileDef :: (FilePath, Expr) -> (C.Env, [C.Expr]) -> (C.Env, [C.Expr])
        compileDef (path, alt) (env, alts) = do
          let (env', alt') = compile ctx path (name, alt)
          (unionBy (\a b -> fst a == fst b) env' env, C.let' env' alt' : alts)
    let (env, alts) = foldr compileDef ([], []) (resolve ctx path name)
    let def = case alts of
          [] -> []
          [C.Var x] | x == name -> [(name, C.Var x)]
          [C.Ann (C.Var x) t] | x == name -> [(name, C.Ann (C.Var x) t)]
          alts -> [(name, C.fix [name] (C.or' alts))]
    unionBy (\a b -> fst a == fst b) def env

instance Compile ((String, Expr) -> (C.Env, C.Expr)) where
  compile :: Context -> String -> (String, Expr) -> (C.Env, C.Expr)
  -- compile ctx path (name@"", expr) = do
  --   let a = lower expr
  --   let env = concatMap (compile ctx path) (delete name (C.freeNames (True, True, False) a))
  --   let ((a', t), s, e) = C.infer buildOps env a
  --   let xs = filter (`notElem` map fst env) (map fst s)
  --   error . intercalate "\n" $
  --     [ "-- compile/2 " ++ name,
  --       -- show ctx,
  --       C.format a,
  --       C.format (C.Let env C.Any),
  --       show (map fst env),
  --       C.format a',
  --       -- C.format (C.for xs $ C.dropTypes a'),
  --       -- C.format t,
  --       ""
  --     ]
  compile ctx path (name, expr) = do
    let a = lower expr
    let env = concatMap (compile ctx path) (delete name (C.freeNames (True, True, False) a))
    let ((a', t), s, e) = C.infer buildOps env a
    let xs = filter (`notElem` map fst env) (map fst s)
    (env, C.for xs $ C.dropTypes a')

instance Compile (Expr -> (C.Env, C.Expr)) where
  compile :: Context -> String -> Expr -> (C.Env, C.Expr)
  compile ctx path expr =
    compile ctx path (C.newName (freeVars expr) "", expr)

class TestSome a where
  testSome :: Context -> ((String, String) -> Bool) -> a -> [TestResult]

instance TestSome Package where
  testSome :: Context -> ((String, String) -> Bool) -> Package -> [TestResult]
  testSome ctx filter (_, mods) = do
    concatMap (testSome (ctx ++ mods) filter) mods

instance TestSome Module where
  testSome :: Context -> ((String, String) -> Bool) -> Module -> [TestResult]
  testSome ctx filter (path, stmts) =
    concatMap (\stmt -> testSome ctx filter (path, stmt)) stmts

instance TestSome (String, Stmt) where
  testSome :: Context -> ((String, String) -> Bool) -> (String, Stmt) -> [TestResult]
  testSome ctx filter (path, stmt) = case stmt of
    Import {} -> []
    Def {} -> []
    TypeDef {} -> []
    Test pos name expr expect | filter (path, name) -> do
      testSome ctx filter (UnitTest path pos name expr expect)
    Test {} -> []

instance TestSome UnitTest where
  testSome :: Context -> ((String, String) -> Bool) -> UnitTest -> [TestResult]
  testSome ctx _ t = do
    let (env, expr) = compile ctx t.filename t.expr
    let expect = let (env', a) = compile ctx t.filename (Fun t.expect (Tag ":Ok")) in C.let' (env' ++ env) a
    let test' = expect `C.Or` C.For "got" (C.Fun (C.Var "got") (C.Var "got"))
    -- error . intercalate "\n" $
    --   [ "-- testSome",
    --     "env = " ++ C.format (C.Let env C.Any),
    --     "      " ++ show (map fst env),
    --     "expr = " ++ C.format expr,
    --     "expect = " ++ C.format expect,
    --     "eval expect: " ++ C.format (C.eval runtimeOps expect),
    --     "eval expr:   " ++ C.format (C.eval runtimeOps (C.let' env expr)),
    --     "eval test:   " ++ C.format (C.eval runtimeOps (C.App test' (C.let' env expr))),
    --     ""
    --   ]
    case C.eval runtimeOps (C.App test' (C.let' env expr)) of
      C.Tag ":Ok" -> [TestPass t.filename t.pos t.name]
      got -> [TestFail t.filename t.pos t.name t.expr t.expect (lift got)]

testAll :: (TestSome a) => Context -> a -> [TestResult]
testAll ctx = testSome ctx (const True)

class Patch a where
  patch :: Context -> [Stmt] -> a -> a

instance Patch Expr where
  patch :: Context -> [Stmt] -> Expr -> Expr
  patch _ [] a = a
  patch ctx (rule : rules) expr = case rule of
    Import {} -> expr
    Def (pattern', body) -> do
      let patch' = patch ctx (rule : rules)
      let expr' = case expr of
            Ann a b -> Ann (patch' a) (patch' b)
            And a b -> And (patch' a) (patch' b)
            a -> a
      case eval ctx "" (Let (pattern', expr') body) of
        Err -> expr'
        result -> result
    -- Def (p, b) -> case (p, a) of
    --   (Any, Any) -> b
    --   (Unit, Unit) -> b
    --   (IntT, IntT) -> b
    --   (NumT, NumT) -> b
    --   (Int i, Int i') -> if i == i' then b else a
    --   (Num n, Num n') -> if n == n' then b else a
    --   (Tag k, Tag k') -> if k == k' then b else a
    --   (Var x, Var x') -> if x == x' then b else a
    --   -- Ann Expr Type
    --   -- And Expr Expr
    --   -- Or Expr Expr
    --   -- Fix String Expr
    --   -- For [String] Expr
    --   -- Fun Expr Expr
    --   -- App Expr Expr
    --   -- Call String [Expr]
    --   -- Op1 Op1 Expr
    --   -- Op2 Op2 Expr Expr
    --   -- Match [Expr] [Expr]
    --   -- If Expr Expr Expr
    --   -- Let (Expr, Expr) Expr
    --   -- Bind (Expr, Expr) Expr
    --   -- Record [(String, Expr)]
    --   -- Select Expr [(String, Expr)]
    --   -- With Expr [(String, Expr)]
    --   -- Err
    --   (Err, Err) -> Err
    TypeDef {} -> expr
    Test {} -> expr
