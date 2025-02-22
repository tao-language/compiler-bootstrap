{-# OPTIONS_GHC -Wno-type-defaults #-}

module Tao where

import Control.Monad (mapAndUnzipM)
import qualified Core as C
import Data.Bifunctor (second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (intercalate, isPrefixOf, union)
import Data.List.Split (splitWhen)
import Location (Position (..))
import Stdlib (split2)
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
  | Meta C.Metadata Expr
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
  | Def (Pattern, Expr)
  | TypeDef (String, [Expr], [(Expr, Maybe Type)])
  | Test UnitTest
  deriving (Eq, Show)

type Type = Expr

type Package = (String, [Module])

type Module = (FilePath, [Stmt])

type Context = [Module]

data ParserContext
  = CModule
  | CDefinition
  | CImport
  | CTest
  | CComment
  | CCommentMultiLine
  | CDocString
  | CRecordField String
  | CCase
  | CMatch
  deriving (Eq, Show)

data UnitTest = UnitTest
  { filename :: FilePath,
    pos :: Position,
    name :: String,
    expr :: Expr,
    expect :: Pattern
  }
  deriving (Eq, Show)

data TestResult
  = TestPass
      { filename :: String,
        pos :: Position,
        name :: String
      }
  | TestFail
      { filename :: String,
        pos :: Position,
        name :: String,
        test :: Expr,
        expected :: Expr,
        got :: Expr
      }
  deriving (Eq)

instance Show TestResult where
  show :: TestResult -> String
  show result = case result of
    TestPass filename pos name -> "✅ " ++ filename ++ ":" ++ show pos.row ++ ":" ++ show pos.col ++ " -- " ++ name ++ "\n"
    TestFail filename pos name test expect got -> "❌ " ++ filename ++ ":" ++ show pos.row ++ ":" ++ show pos.col ++ " -- " ++ name ++ "\n  > " ++ show test ++ "\n  " ++ show expect ++ "\n* " ++ show got ++ "\n"

buildOps :: C.Ops
buildOps = do
  let call op f =
        (op, \eval args -> f (eval . C.dropTypes . C.dropMeta <$> args))
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
    intOp2 "int_lt" (\x y -> C.Tag (if x < y then "True" else "False")),
    intOp2 "int_add" (\x y -> C.Int (x + y)),
    intOp2 "int_sub" (\x y -> C.Int (x - y)),
    intOp2 "int_mul" (\x y -> C.Int (x * y)),
    intOp2 "int_div" (\x y -> C.Num (fromIntegral x / fromIntegral y)),
    intOp2 "int_divi" (\x y -> C.Int (Prelude.div x y)),
    intOp2 "int_pow" (\x y -> C.Int (x ^ y)),
    numOp1 "num_neg" (\x -> C.Num (-x)),
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
funOf (Meta _ a) = funOf a
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
appOf (Meta _ a) = appOf a
appOf a = (a, [])

and' :: [Expr] -> Expr
and' [] = Unit
and' [a] = a
and' (a : bs) = And a (and' bs)

andOf :: Expr -> [Expr]
andOf (And a b) = a : andOf b
andOf (Meta _ a) = andOf a
andOf a = [a]

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

orOf :: Expr -> [Expr]
orOf (Or a b) = a : orOf b
orOf (Meta _ a) = orOf a
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

asImport :: Stmt -> Maybe (FilePath, String, [(String, String)])
asImport (Import path alias names) = Just (path, alias, names)
asImport _ = Nothing

isDef :: Stmt -> Bool
isDef Def {} = True
isDef _ = False

asDef :: Stmt -> Maybe (Pattern, Expr)
asDef (Def def) = Just def
asDef _ = Nothing

isTest :: Stmt -> Bool
isTest Test {} = True
isTest _ = False

asTest :: Stmt -> Maybe UnitTest
asTest (Test t) = Just t
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
  Meta _ a -> freeNames' a
  Err -> []
  where
    freeNames' = freeNames (vars, tags, calls)

freeVars :: Expr -> [String]
freeVars = freeNames (True, False, False)

freeTags :: Expr -> [String]
freeTags = freeNames (False, True, False)

class DropMeta a where
  dropMeta :: a -> a

instance DropMeta Module where
  dropMeta :: Module -> Module
  dropMeta (path, stmts) = (path, map dropMeta stmts)

instance DropMeta Stmt where
  dropMeta :: Stmt -> Stmt
  dropMeta = \case
    stmt@Import {} -> stmt
    Def (p, b) -> Def (dropMeta p, dropMeta b)
    TypeDef (k, args, alts) -> do
      let dropMetaAlt (a, mt) = case mt of
            Just t -> (dropMeta a, Just (dropMeta t))
            Nothing -> (dropMeta a, Nothing)
      TypeDef (k, map dropMeta args, map dropMetaAlt alts)
    Test t -> Test t -- TODO

instance DropMeta Expr where
  dropMeta :: Expr -> Expr
  dropMeta = \case
    Ann a b -> Ann (dropMeta a) (dropMeta b)
    And a b -> And (dropMeta a) (dropMeta b)
    Or a b -> Or (dropMeta a) (dropMeta b)
    For xs a -> For xs (dropMeta a)
    Fun a b -> Fun (dropMeta a) (dropMeta b)
    App a b -> App (dropMeta a) (dropMeta b)
    Call f args -> Call f (map dropMeta args)
    Op1 op a -> Op1 op (dropMeta a)
    Op2 op a b -> Op2 op (dropMeta a) (dropMeta b)
    Let (a, b) c -> Let (dropMeta a, dropMeta b) (dropMeta c)
    Bind (a, b) c -> Bind (dropMeta a, dropMeta b) (dropMeta c)
    If a b c -> If (dropMeta a) (dropMeta b) (dropMeta c)
    Match args cases -> Match (map dropMeta args) (map (\(xs, ps, b) -> (xs, map dropMeta ps, dropMeta b)) cases)
    Record fields -> Record (second dropMeta <$> fields)
    Select a fields -> Select (dropMeta a) (second dropMeta <$> fields)
    With a fields -> With (dropMeta a) (second dropMeta <$> fields)
    Meta _ a -> dropMeta a
    a -> a

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

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
