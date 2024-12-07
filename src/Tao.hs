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
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Var String
  | Tag String
  | Ann Expr Type
  | And Expr Expr
  | Or Expr Expr
  | For [String] Expr
  | Fun Expr Expr
  | App Expr Expr
  | Call String [Expr]
  | Op1 Op1 Expr
  | Op2 Op2 Expr Expr
  | Let (Expr, Expr) Expr
  | Bind (Expr, Expr) Expr
  | If Expr Expr Expr
  | Match [Expr] [Expr]
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
  | Lt
  | Gt
  | Add
  | Sub
  | Mul
  | Div
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
    Lt -> "<"
    Gt -> ">"
    Add -> "+"
    Sub -> "-"
    Mul -> "*"
    Div -> "/"
    Pow -> "^"

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

data TestResult
  = TestPass String String
  | TestFail String String (Expr, Expr) C.Expr Expr
  deriving (Eq)

instance Show TestResult where
  show :: TestResult -> String
  show result = case result of
    TestPass path name -> "✅ " ++ path ++ " -- " ++ name
    TestFail path name t tc got -> "❌ " ++ path ++ " -- " ++ name ++ " test=" ++ show t ++ " core=" ++ show tc ++ " got=" ++ show got

buildOps :: C.Ops
buildOps = do
  let intOp1 op f =
        ( op,
          \eval args -> case C.dropTypes . eval <$> args of
            [C.Int x] -> C.Int (f x)
            args -> C.Call op args
        )
  let intOp2 op f =
        ( op,
          \eval args -> case C.dropTypes . eval <$> args of
            [C.Int x, C.Int y] -> C.Int (f x y)
            args -> C.Call op args
        )
  [ intOp1 "int_neg" (\x -> -x),
    intOp2 "int_add" (+),
    intOp2 "int_sub" (-),
    intOp2 "int_mul" (*),
    intOp2 "int_div" div,
    intOp2 "int_pow" (^)
    ]

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

lets :: [(Expr, Expr)] -> Expr -> Expr
lets defs b = foldr Let b defs

select :: Expr -> [String] -> Expr
select a xs = Select a (map (\x -> (x, Var x)) xs)

selectFun :: [(String, Expr)] -> Expr
selectFun fields = lambda ["_"] (Select (Var "_") fields)

with :: Expr -> [String] -> Expr
with a xs = With a (map (\x -> (x, Var x)) xs)

withFun :: [(String, Expr)] -> Expr
withFun fields = lambda ["_"] (With (Var "_") fields)

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
  freeVars = \case
    Any -> []
    Unit -> []
    IntT -> []
    NumT -> []
    Int _ -> []
    Num _ -> []
    Var x -> [x]
    Tag _ -> []
    Ann a b -> freeVars a `union` freeVars b
    And a b -> freeVars a `union` freeVars b
    Or a b -> freeVars a `union` freeVars b
    For xs a -> filter (`notElem` xs) (freeVars a)
    Fun a b -> freeVars a `union` freeVars b
    App a b -> freeVars a `union` freeVars b
    Call _ args -> freeVars (and' args)
    Op1 op a -> [show op] `union` freeVars a
    Op2 op a b -> [show op] `union` freeVars a `union` freeVars b
    Let (a, b) c -> filter (`notElem` freeVars a) (freeVars b `union` freeVars c)
    Bind (a, b) c -> filter (`notElem` freeVars a) (freeVars b `union` freeVars c)
    If a b c -> freeVars (and' [a, b, c])
    Match args cases -> freeVars (and' args) `union` freeVars (and' cases)
    Record fields -> freeVars (and' (map snd fields))
    Select a fields -> freeVars a `union` freeVars (and' (map snd fields))
    With a fields -> freeVars a `union` freeVars (and' (map snd fields))
    Err -> []

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

class Resolve a where
  resolve :: [Module] -> String -> a -> [(String, Expr)]

instance Resolve String where
  resolve :: [Module] -> String -> String -> [(String, Expr)]
  resolve ctx path name = case lookup path ctx of
    Just stmts -> resolve ctx path (name, stmts)
    Nothing -> []

instance Resolve (String, [Stmt]) where
  resolve :: [Module] -> String -> (String, [Stmt]) -> [(String, Expr)]
  resolve ctx path (name, stmts) =
    concatMap (\stmt -> resolve ctx path (name, stmt)) stmts

instance Resolve (String, Stmt) where
  resolve :: [Module] -> String -> (String, Stmt) -> [(String, Expr)]
  resolve ctx path (name, stmt) = case stmt of
    Import path' alias names -> case names of
      (x, y) : names -> do
        let defs = if y == name then resolve ctx path' x else []
        defs ++ resolve ctx path (name, Import path' alias names)
      [] | alias == name -> [(path, Tag path')]
      [] -> []
    -- Def (Var x, b) | x == name -> [(path, b)]
    -- Def (Ann p t, b) ->
    --   resolve ctx path (Def (p, Ann b t), name)
    -- Def (For xs p, b) | name `elem` xs -> do
    --   [(path, Let (For xs p, b) (Var name))]
    -- Def (Or p1 p2, b) -> do
    --   let defs = resolve ctx path (Def (p1, b), name)
    --   defs ++ resolve ctx path (Def (p2, b), name)
    -- Def (App p1 p2, b) -> case appOf (App p1 p2) of
    --   (p, ps) -> resolve ctx path (Def (p, fun ps b), name)
    Def (p, b) | name `elem` bindings p -> [(path, Let (p, b) (Var name))]
    Def _ -> []
    TypeDef (name', args, body) ->
      ([(path, fun args body) | name == name'])
    Test {} -> []

class Compile a where
  compile :: [Module] -> String -> a

instance Compile (String -> (String, C.Expr)) where
  compile :: [Module] -> String -> String -> (String, C.Expr)
  compile ctx path name = do
    let defs = resolve ctx path name
    let alts = map (\(path, a) -> compile ctx path (name, a)) defs :: [C.Expr]
    (name, C.or' alts)

instance Compile ((String, Expr) -> (C.Env, C.Expr)) where
  compile :: [Module] -> String -> (String, Expr) -> (C.Env, C.Expr)
  compile ctx path (name, expr) = do
    let a = lower expr
    let env = map (compile ctx path) (delete name (C.freeVars a))
    (env, annotate env a)

annotate :: C.Env -> C.Expr -> C.Expr
annotate env = \case
  C.Ann a b -> C.Ann (annotate env a) (annotate env b)
  C.And a b -> C.And (annotate env a) (annotate env b)
  C.Or a b -> C.Or (annotate env a) (annotate env b)
  C.For x a -> C.for [x] (annotate ((x, C.Var x) : env) a)
  C.Fix x a -> C.fix [x] (annotate ((x, C.Var x) : env) a)
  C.Fun a b -> do
    let (args, body) = C.funOf (C.Fun a b)
    case C.inferAll buildOps env args of
      Right (argsT, s) ->
        C.for (C.freeVars argsT) (C.fun (zipWith C.Ann args argsT) (annotate env body))
      Left _ -> C.fun args (annotate env body)
  C.App a b -> case C.infer2 buildOps env a b of
    Right ((ta, tb), s) -> C.App (annotate env a) (C.Ann (annotate env b) tb)
    Left _ -> C.App (annotate env a) (annotate env b)
  C.Call f args -> case C.inferAll buildOps env args of
    Right (argsT, s) -> C.Call f (zipWith C.Ann args argsT)
    Left _ -> C.Call f args
  C.Let defs b -> C.Let (map (second (annotate env)) defs) (annotate env b)
  a -> a

instance Compile ((String, Expr) -> C.Expr) where
  compile :: [Module] -> String -> (String, Expr) -> C.Expr
  compile ctx path (name, expr) = do
    let (env, a) = compile ctx path (name, expr)
    C.let' env a

instance Compile (Expr -> C.Expr) where
  compile :: [Module] -> String -> Expr -> C.Expr
  compile ctx path expr = do
    let (env, a) = compile ctx path (C.newName (freeVars expr) "", expr)
    C.let' env a

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
  For [] (Fun a b) -> do
    let (args, body) = funOf (Fun a b)
    C.fun (map lower args) (lower body)
  For [] a -> lower a
  For (x : xs) a -> do
    C.for [x] (lower (For xs a))
  Fun a b -> do
    let (args, body) = funOf (Fun a b)
    lower (For (freeVars (and' args)) (fun args body))
  App a b -> C.App (lower a) (lower b)
  Call op args -> C.Call op (map lower args)
  -- lower env (Let def b) = lower (lower env def ++ env) b
  -- lower env (Bind (ts, p, a) b) = lower env (App (Trait a "<-") (Function [p] b))
  Op1 op a -> lower (App (Var (show op)) a)
  Op2 op a b -> lower (App (Var (show op)) (And a b))
  Let (Var x, b) (Var x') | x == x' -> lower b
  Let (a, b) c -> case a of
    Var x -> C.Let [(x, lower b)] (lower c)
    For xs a -> lower (App (For xs (Fun a c)) b)
    Or a1 a2 -> lower (lets [(a1, b), (a2, b)] c)
    App a1 a2 -> lower (Let (a1, Fun a2 b) c)
    a -> lower (App (For (freeVars a) (Fun a c)) b)
  Match [] cases -> lower (or' cases)
  Match args cases -> lower (app (Match [] cases) args)
  -- lower env (Record fields) = do
  --   let k = '~' : intercalate "," (map fst fields)
  --   lower env (tag k (map snd fields))
  -- lower env (Select a kvs) = case a of
  --   Record fields -> do
  --     let sub = map (second $ lower env) fields
  --     let lowerFields [] = []
  --         lowerFields ((x, b) : xs) | x `elem` map fst fields = do
  --           let b' = lower env b
  --           (x, C.substitute sub b') : lowerFields xs
  --         lowerFields (_ : xs) = lowerFields xs
  --     let fields' = lowerFields kvs
  --     let k = '~' : intercalate "," (map fst fields')
  --     C.tag k (map snd fields')
  --   a -> error $ "TODO: lower Select " ++ show a
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
    For xs a -> For (x : xs) a
    a -> For [x] a
  C.Fix _ a -> lift a
  C.Fun a b -> do
    let (args, body) = C.funOf (C.Fun a b)
    For [] (fun (map lift args) (lift body))
  C.App a b -> case appOf (App (lift a) (lift b)) of
    -- (Var ('.' : x), _ : a : args) -> app (Trait a x) args
    -- (Trait a "<-", [Fun p b]) -> Bind ([], toPattern p, a) b
    (Var "==", [And a b]) -> Op2 Eq a b
    (Var "<", [And a b]) -> Op2 Lt a b
    (Var ">", [And a b]) -> Op2 Gt a b
    (Var "+", [And a b]) -> Op2 Add a b
    (Var "-", [And a b]) -> Op2 Sub a b
    (Var "*", [And a b]) -> Op2 Mul a b
    (Var "/", [And a b]) -> Op2 Div a b
    (Var "^", [And a b]) -> Op2 Pow a b
    (Var "-", [a]) -> Op1 Neg a
    (For x a, args) -> Match args [For x a]
    (Fun a1 a2, args) -> Match args [Fun a1 a2]
    (Or a1 a2, args) -> Match args (orOf (Or a1 a2))
    (a, args) -> app a args
  C.Call op args -> Call op (map lift args)
  C.Let [] b -> lift b
  C.Let ((x, a) : env) b -> Let (Var x, lift a) (lift (C.Let env b))
  C.Err -> Err

eval :: [Module] -> String -> Expr -> Expr
eval ctx path expr = do
  compile ctx path expr
    & C.eval runtimeOps
    & lift

class TestSome a where
  testSome :: [Module] -> ((String, String) -> Bool) -> a -> [TestResult]

instance TestSome Package where
  testSome :: [Module] -> ((String, String) -> Bool) -> Package -> [TestResult]
  testSome ctx filter (_, mods) = do
    concatMap (testSome (ctx ++ mods) filter) mods

instance TestSome Module where
  testSome :: [Module] -> ((String, String) -> Bool) -> Module -> [TestResult]
  testSome ctx filter (path, stmts) =
    concatMap (\stmt -> testSome ctx filter (path, stmt)) stmts

instance TestSome (String, Stmt) where
  testSome :: [Module] -> ((String, String) -> Bool) -> (String, Stmt) -> [TestResult]
  testSome ctx filter (path, stmt) = case stmt of
    Import {} -> []
    Def {} -> []
    TypeDef {} -> []
    Test name expr expect | filter (path, name) -> do
      testSome ctx filter (UnitTest path name expr expect)
    Test {} -> []

instance TestSome UnitTest where
  testSome :: [Module] -> ((String, String) -> Bool) -> UnitTest -> [TestResult]
  testSome ctx _ t = do
    let test' =
          Match
            [t.expr]
            [ Fun t.expect (Tag ":Ok"),
              Fun (Var "got") (Var "got")
            ]
    case eval ctx t.path test' of
      Tag ":Ok" -> [TestPass t.path t.name]
      got -> [TestFail t.path t.name (t.expr, t.expect) (compile ctx t.path t.expr) got]

testAll :: (TestSome a) => [Module] -> a -> [TestResult]
testAll ctx = testSome ctx (const True)
