module Tao where

-- TODO: maybe use terms like "lower" and "lift" for conversions to/from core
import qualified Core as C
import Data.Bifunctor (second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (intercalate)
import Data.List.Split (split, splitOneOf, splitWhen, whenElt)

data Expr
  = Any
  | IntType
  | NumType
  | Int Int
  | Num Double
  | Var String
  | Tag String [Expr]
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Trait Expr String
  | ListNil
  | ListCons
  | TextNil
  | TextCons
  | Type [String]
  | Fun Expr Expr
  | App Expr Expr
  | Let Definition Expr
  | Bind (Expr, Expr) Expr
  | TypeDef String [Expr] Expr
  | MatchFun [Expr]
  | Match [Expr] [Expr]
  | Or Expr Expr
  | Ann Expr Expr
  | Op1 C.UnaryOp Expr
  | Op2 C.BinaryOp Expr Expr
  | Meta C.Metadata Expr
  | Err
  deriving (Eq, Show)

data Definition
  = DefName [(String, Expr)] String [Expr] Expr
  | DefUnpack [(String, Expr)] String [Expr] Expr
  | DefTrait [(String, Expr)] (Expr, Expr) String [Expr] Expr
  deriving (Eq, Show)

data Stmt
  = Import [String] String String [(String, String)] -- import path/package as alias (a, b, c)
  | Def Definition
  | Test Expr Expr
  | MetaStmt C.Metadata Stmt
  deriving (Eq, Show)

data Module = Module
  { path :: [String],
    name :: String,
    stmts :: [Stmt]
  }
  deriving (Eq, Show)

data Package = Package
  { name :: String,
    modules :: [Module]
  }
  deriving (Eq, Show)

or' :: [Expr] -> Expr
or' [] = error "`or'` must have at least one expression"
or' [a] = a
or' (a : bs) = Or a (or' bs)

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

asFun :: Expr -> ([Expr], Expr)
asFun (Fun p a) = let (ps, b) = asFun a in (p : ps, b)
asFun a = ([], a)

app :: Expr -> [Expr] -> Expr
app = foldl App

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = let (a', bs) = asApp a in (a', bs ++ [b])
asApp a = (a, [])

add :: Expr -> Expr -> Expr
add = Op2 C.Add

sub :: Expr -> Expr -> Expr
sub = Op2 C.Sub

mul :: Expr -> Expr -> Expr
mul = Op2 C.Mul

pow :: Expr -> Expr -> Expr
pow = Op2 C.Pow

eq :: Expr -> Expr -> Expr
eq = Op2 C.Eq

lt :: Expr -> Expr -> Expr
lt = Op2 C.Lt

gt :: Expr -> Expr -> Expr
gt = Op2 C.Gt

meta :: [C.Metadata] -> Expr -> Expr
meta ms a = foldr Meta a ms

list :: [Expr] -> Expr
list [] = ListNil
list (a : bs) = app ListCons [a, list bs]

freeVars :: Expr -> [String]
freeVars expr = C.freeVars (lowerExpr [] expr) & filter (/= "_")

-- Core conversions
lowerExpr :: [(String, Expr)] -> Expr -> C.Term
lowerExpr _ Any = C.Var "_"
lowerExpr _ (Type alts) = C.Typ alts
lowerExpr _ IntType = C.IntT
lowerExpr _ NumType = C.NumT
lowerExpr _ (Int i) = C.Int i
lowerExpr _ (Num n) = C.Num n
lowerExpr _ (Var x) = C.Var x
lowerExpr defs (Tag k args) = C.app (C.Tag k) (map (lowerExpr defs) args)
lowerExpr defs (Tuple items) = lowerExpr defs (Tag "()" items)
lowerExpr defs (Record fields) = do
  let lowerField (k, v) = (k, lowerExpr defs v)
  C.Rec (map lowerField fields)
lowerExpr defs (Trait a x) = do
  let a' = lowerExpr defs a
  let env = lowerDefs defs
  case C.infer env a' of
    Left _ -> C.Err
    Right (t, _) -> C.app (C.Var $ '.' : x) [t, a']
lowerExpr _ ListNil = C.Tag "[]"
lowerExpr _ ListCons = C.Tag "[..]"
lowerExpr _ TextNil = C.Tag "\"\""
lowerExpr _ TextCons = C.Tag "\"..\""
lowerExpr defs (Fun a b) = C.Fun (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (App a b) = C.App (lowerExpr defs a) (lowerExpr defs b)
-- lowerExpr defs (Let (p, a) b) = C.let' (lowerExpr defs p, lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Bind (p, a) b) = lowerExpr defs (App (Trait a "<-") (Fun p b))
-- TODO: TypeDef
lowerExpr defs (MatchFun cases) = lowerExpr defs (or' cases)
lowerExpr defs (Match args cases) = lowerExpr defs (app (MatchFun cases) args)
lowerExpr defs (Or a b) = C.Or (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Ann a b) = C.Ann (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Op1 op a) = C.Op1 op (lowerExpr defs a)
lowerExpr defs (Op2 op a b) = C.Op2 op (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Meta m a) = C.Meta m (lowerExpr defs a)
lowerExpr _ Err = C.Err

liftExpr :: C.Term -> Expr
liftExpr (C.Typ alts) = Type alts
liftExpr C.IntT = IntType
liftExpr C.NumT = NumType
liftExpr (C.Int i) = Int i
liftExpr (C.Num n) = Num n
liftExpr (C.Var "_") = Any
liftExpr (C.Var x) = Var x
liftExpr (C.Tag "()") = Tuple []
liftExpr (C.Tag "[]") = ListNil
liftExpr (C.Tag "[..]") = ListCons
liftExpr (C.Tag "\"\"") = TextNil
liftExpr (C.Tag "\"..\"") = TextCons
liftExpr (C.Tag k) = Tag k []
liftExpr (C.Rec fields) = do
  let liftField (x, a) = (x, liftExpr a)
  Record (map liftField fields)
liftExpr (C.For _ a) = liftExpr a
liftExpr (C.Fix _ a) = liftExpr a
liftExpr (C.Fun a b) = Fun (liftExpr a) (liftExpr b)
liftExpr (C.App a b) = case asApp (App (liftExpr a) (liftExpr b)) of
  (Tag k args, args') -> Tag k (args ++ args')
  (Tuple args, args') -> Tuple (args ++ args')
  (Var ('.' : x), _ : a : args) -> app (Trait a x) args
  -- (Fun p a, [b]) -> Let (p, b) a
  (Trait a "<-", [Fun p b]) -> Bind (p, a) b
  (a, args) -> app a args
liftExpr (C.Or a b) = Or (liftExpr a) (liftExpr b)
liftExpr (C.Ann a b) = Ann (liftExpr a) (liftExpr b)
liftExpr (C.Op1 op a) = Op1 op (liftExpr a)
liftExpr (C.Op2 op a b) = Op2 op (liftExpr a) (liftExpr b)
liftExpr (C.Meta m a) = Meta m (liftExpr a)
liftExpr C.Err = Err

lowerDefs :: [(String, Expr)] -> C.Env
lowerDefs defs = map (second (lowerExpr defs)) defs

liftDefs :: C.Env -> [(String, Expr)]
liftDefs env = error "TODO: liftDefs"

lowerPackage :: Package -> C.Env
lowerPackage pkg = lowerDefs (packageDefs pkg)

liftPackage :: String -> C.Env -> Package
liftPackage name _ = error "TODO: liftPackage"

stmtDefs :: Stmt -> [(String, Expr)]
stmtDefs (Def (DefName ts x (a : args) b)) = stmtDefs (Def (DefName ts x args (Fun a b)))
stmtDefs (Def (DefName ts x [] b)) = case lookup x ts of
  Just t -> [(x, Ann b t)]
  Nothing -> [(x, b)]
stmtDefs (Def (DefUnpack ts k args b)) = do
  let def x = Match [b] [Fun (Tag k args) (Var x)]
  let typedDef x = case lookup x ts of
        Just t -> (x, Ann (def x) t)
        Nothing -> (x, def x)
  map typedDef (freeVars (Tuple args))
stmtDefs (Def (DefTrait ts self x (a : args) b)) = stmtDefs (Def (DefTrait ts self x args (Fun a b)))
stmtDefs (Def (DefTrait ts (t, a) x [] b)) = [('.' : x, fun [t, a] b)]
stmtDefs (MetaStmt _ stmt) = stmtDefs stmt
stmtDefs _ = []

stmtTests :: Stmt -> [(Expr, Expr)]
stmtTests (Test a b) = [(a, b)]
stmtTests (MetaStmt _ stmt) = stmtTests stmt
stmtTests _ = []

moduleDefs :: Module -> [(String, Expr)]
moduleDefs mod = concatMap stmtDefs mod.stmts

packageDefs :: Package -> [(String, Expr)]
packageDefs pkg = concatMap moduleDefs pkg.modules

moduleTests :: Module -> [(Expr, Expr)]
moduleTests mod = concatMap stmtTests mod.stmts

packageTests :: Package -> [(Expr, Expr)]
packageTests pkg = concatMap moduleTests pkg.modules

run :: Package -> Expr -> Expr
run pkg expr = do
  let env = lowerPackage pkg
  let term = lowerExpr (packageDefs pkg) expr
  liftExpr (C.eval env term)

data TestError
  = TestEqError Expr Expr Expr
  deriving (Eq, Show)

testEq :: [(String, Expr)] -> (Expr, Expr) -> [TestError]
testEq defs (expr, result) = do
  let env = lowerDefs defs
  let actual = C.eval env (lowerExpr defs expr)
  let expected = C.eval env (lowerExpr defs result)
  case C.eval [] (actual `C.eq` expected) of
    C.Err -> [TestEqError expr (liftExpr actual) (liftExpr expected)]
    _ -> []

test :: Package -> [TestError]
test pkg = do
  let defs = packageDefs pkg
  concatMap (testEq defs) (packageTests pkg)

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
