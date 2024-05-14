module Tao where

-- TODO: maybe use terms like "lower" and "lift" for conversions to/from core
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap, first), second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (intercalate, union)
import Data.List.Split (split, splitOneOf, splitWhen, whenElt)

data Expr
  = Any
  | Int Int
  | Num Double
  | Var String
  | Tag String
  | Type [String]
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Trait Expr String
  | Fun Expr Expr
  | App Expr Expr
  | Let Definition Expr
  | Bind (Expr, Expr) Expr
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
  = NameDef [(String, Expr)] String [Expr] Expr
  | UnpackDef [(String, Expr)] String [Expr] Expr
  | TraitDef [(String, Expr)] (Expr, Expr) String [Expr] Expr
  -- TODO: TypeDef
  deriving (Eq, Show)

data Stmt
  = Import String String [(String, String)] -- import path/package as alias (a, b, c)
  | Def Definition
  | Test Expr Expr
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

tag :: String -> [Expr] -> Expr
tag k = app (Tag k)

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

isTypeDef :: Expr -> Bool
isTypeDef (Type _) = True
isTypeDef (Fun _ b) = isTypeDef b
isTypeDef (App a _) = isTypeDef a
isTypeDef (Ann a _) = isTypeDef a
isTypeDef _ = False

isTagDef :: Expr -> Bool
isTagDef (Tag _) = True
isTagDef (Fun _ b) = isTagDef b
isTagDef (App a _) = isTagDef a
isTagDef (Ann a _) = isTagDef a
isTagDef _ = False

isFunctionDef :: Expr -> Bool
isFunctionDef (Fun _ _) = True
isFunctionDef (Ann a _) = isFunctionDef a
isFunctionDef _ = False

list :: [Expr] -> Expr
list [] = Tag "[]"
list (a : bs) = app (Tag "[..]") [a, list bs]

freeVars :: Expr -> [String]
freeVars expr = C.freeVars (lowerExpr [] expr) & filter (/= "_")

-- Core conversions
lowerExpr :: [(String, Expr)] -> Expr -> C.Term
lowerExpr _ Any = C.Var "_"
lowerExpr _ (Int i) = C.Int i
lowerExpr _ (Num n) = C.Num n
lowerExpr _ (Var x) = C.Var x
lowerExpr _ (Tag "Int") = C.IntT
lowerExpr _ (Tag "Num") = C.NumT
lowerExpr _ (Tag k) = C.Tag k
lowerExpr _ (Type alts) = C.Typ alts
lowerExpr defs (Tuple items) = lowerExpr defs (tag "()" items)
lowerExpr defs (Record fields) = do
  let lowerField (k, v) = (k, lowerExpr defs v)
  C.Rec (map lowerField fields)
lowerExpr defs (Trait a x) = do
  let a' = lowerExpr defs a
  let env = lowerDefs defs
  case C.infer env a' of
    Left _ -> C.Err
    Right (t, _) -> C.app (C.Var $ '.' : x) [t, a']
lowerExpr defs (Fun a b) = C.Fun (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (App a b) = C.App (lowerExpr defs a) (lowerExpr defs b)
-- lowerExpr defs (Let (p, a) b) = C.let' (lowerExpr defs p, lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Bind (p, a) b) = lowerExpr defs (App (Trait a "<-") (Fun p b))
lowerExpr defs (MatchFun cases) = lowerExpr defs (or' cases)
lowerExpr defs (Match args cases) = lowerExpr defs (app (MatchFun cases) args)
lowerExpr defs (Or a b) = C.Or (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Ann a b) = C.Ann (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Op1 op a) = C.Op1 op (lowerExpr defs a)
lowerExpr defs (Op2 op a b) = C.Op2 op (lowerExpr defs a) (lowerExpr defs b)
lowerExpr defs (Meta m a) = C.Meta m (lowerExpr defs a)
lowerExpr _ Err = C.Err

liftExpr :: C.Term -> Expr
liftExpr C.IntT = Tag "Int"
liftExpr C.NumT = Tag "Num"
liftExpr (C.Int i) = Int i
liftExpr (C.Num n) = Num n
liftExpr (C.Var "_") = Any
liftExpr (C.Var x) = Var x
liftExpr (C.Tag "()") = Tuple []
liftExpr (C.Tag k) = Tag k
liftExpr (C.Typ alts) = Type alts
liftExpr (C.Rec fields) = do
  let liftField (x, a) = (x, liftExpr a)
  Record (map liftField fields)
liftExpr (C.For _ a) = liftExpr a
liftExpr (C.Fix _ a) = liftExpr a
liftExpr (C.Fun a b) = Fun (liftExpr a) (liftExpr b)
liftExpr (C.App a b) = case asApp (App (liftExpr a) (liftExpr b)) of
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
stmtDefs (Def (NameDef ts x (a : args) b)) = stmtDefs (Def (NameDef ts x args (Fun a b)))
stmtDefs (Def (NameDef ts x [] b)) = case lookup x ts of
  Just t -> [(x, Ann b t)]
  Nothing -> [(x, b)]
stmtDefs (Def (UnpackDef ts k args b)) = do
  let def x = Match [b] [Fun (tag k args) (Var x)]
  let typedDef x = case lookup x ts of
        Just t -> (x, Ann (def x) t)
        Nothing -> (x, def x)
  map typedDef (freeVars (Tuple args))
stmtDefs (Def (TraitDef ts self x (a : args) b)) = stmtDefs (Def (TraitDef ts self x args (Fun a b)))
stmtDefs (Def (TraitDef ts (t, a) x [] b)) = [('.' : x, fun [t, a] b)]
stmtDefs (MetaStmt _ stmt) = stmtDefs stmt
stmtDefs _ = []

stmtTests :: Stmt -> [(Expr, Expr)]
stmtTests (Test a b) = [(a, b)]
stmtTests (MetaStmt _ stmt) = stmtTests stmt
stmtTests _ = []

moduleDefs :: Module -> [(String, Expr)]
moduleDefs mod = do
  -- let prefix = intercalate "/" mod.path ++ "/" ++ mod.name ++ ":"
  -- renameDefs (prefix ++) (concatMap stmtDefs mod.stmts)
  concatMap stmtDefs mod.stmts

packageDefs :: Package -> [(String, Expr)]
packageDefs pkg = do
  -- let prefix = pkg.name ++ "!"
  -- renameDefs (prefix ++) (concatMap moduleDefs pkg.modules)
  concatMap moduleDefs pkg.modules

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

-- instance Apply String where
--   apply :: (Expr -> Expr) -> String -> String
--   apply f x = case f (Var x) of
--     Var y -> y
--     _ -> x

class Apply a where
  apply :: (Expr -> Expr) -> a -> a

instance Apply Expr where
  apply :: (Expr -> Expr) -> Expr -> Expr
  apply _ Any = Any
  apply _ (Int i) = Int i
  apply _ (Num n) = Num n
  apply _ (Var x) = Var x
  apply _ (Tag k) = Tag k
  apply _ (Type alts) = Type alts
  apply f (Tuple args) = Tuple (map (apply f) args)
  apply f (Record fields) = Record (map (second $ apply f) fields)
  apply f (Trait a x) = Trait (apply f a) x
  apply f (Fun a b) = Fun (apply f a) (apply f b)
  apply f (App a b) = App (apply f a) (apply f b)
  apply f (Let def a) = Let (apply f def) (apply f a)
  apply f (Bind (a, b) c) = Bind (apply f a, apply f b) (apply f c)
  apply f (MatchFun cases) = MatchFun (map (apply f) cases)
  apply f (Match args cases) = Match (map (apply f) args) (map (apply f) cases)
  apply f (Or a b) = Or (apply f a) (apply f b)
  apply f (Ann a b) = Ann (apply f a) (apply f b)
  apply f (Op1 op a) = Op1 op (apply f a)
  apply f (Op2 op a b) = Op2 op (apply f a) (apply f b)
  apply f (Meta m a) = Meta m (apply f a)
  apply _ Err = Err

instance Apply Definition where
  apply :: (Expr -> Expr) -> Definition -> Definition
  apply f (NameDef ts x args val) = do
    let ts' = map (second $ apply f) ts
    let args' = map (apply f) args
    NameDef ts' x args' (f val)
  apply f (UnpackDef ts k args val) = do
    let ts' = map (second $ apply f) ts
    let args' = map (apply f) args
    UnpackDef ts' k args' (f val)
  apply f (TraitDef ts (t, a) x args val) = do
    let ts' = map (second $ apply f) ts
    let args' = map (apply f) args
    TraitDef ts' (f t, f a) x args' (f val)

instance Apply Stmt where
  apply :: (Expr -> Expr) -> Stmt -> Stmt
  apply _ stmt@Import {} = stmt
  apply f (Def def) = Def (apply f def)
  apply f (Test a b) = Test (apply f a) (apply f b)
  apply f (MetaStmt m a) = MetaStmt m (apply f a)

isImported :: String -> Stmt -> Bool
isImported x (Import _ alias exposed) = x == alias || x `elem` map fst exposed
isImported _ _ = False

class Rename a where
  rename :: FilePath -> String -> String -> a -> a

instance Rename Package where
  rename :: FilePath -> String -> String -> Package -> Package
  rename path old new pkg =
    pkg {modules = map (rename path old new) pkg.modules}

defined :: Stmt -> [String]
defined (Import _ alias exposed) = alias : map snd exposed
defined (Def def) = case def of
  NameDef _ x _ _ -> [x]
  UnpackDef _ _ args _ -> foldr (union . freeVars) [] args
  TraitDef _ _ x _ _ -> [x]
defined (Test _ _) = []
defined (MetaStmt _ a) = defined a

instance Rename Module where
  rename :: FilePath -> String -> String -> Module -> Module
  rename path old new mod | mod.name == path = do
    let new' = C.newName (concatMap defined mod.stmts) new
    mod {stmts = map (renameDefined path old new') mod.stmts}
  rename path old new mod | any (isImported old) mod.stmts = do
    let new' = C.newName (concatMap defined mod.stmts) new
    mod {stmts = map (renameImported path old new') mod.stmts}
  rename _ _ _ mod = mod

renameDefined :: FilePath -> String -> String -> Stmt -> Stmt
renameDefined path old new (Def def) = do
  let def' = case def of
        NameDef ts x args val -> do
          let ts' = map (bimap (rename path old new) (rename path old new)) ts
          let x' = rename path old new x
          NameDef ts' x' args val
        UnpackDef ts k args val -> do
          let ts' = map (bimap (rename path old new) (rename path old new)) ts
          let k' = rename path old new k
          UnpackDef ts' k' args val
        TraitDef ts (t, a) x args val -> do
          let ts' = map (bimap (rename path old new) (rename path old new)) ts
          let x' = rename path old new x
          TraitDef ts' (t, a) x' args val
  rename path old new (Def def')
renameDefined path old new stmt = rename path old new stmt

renameImported :: FilePath -> String -> String -> Stmt -> Stmt
renameImported path old new (Import name alias exposed) = do
  let alias' = rename path old new alias
  let exposed' = map (bimap (rename path old new) (rename path old new)) exposed
  rename path old new (Import name alias' exposed')
renameImported path old new stmt = rename path old new stmt

instance Rename Stmt where
  rename :: FilePath -> String -> String -> Stmt -> Stmt
  rename path old new = apply (rename path old new)

instance Rename Expr where
  rename :: FilePath -> String -> String -> Expr -> Expr
  rename path old new (Var x) = Var (rename path old new x)
  rename path old new (Tag k) = Tag (rename path old new k)
  rename path old new (Type alts) = Type (map (rename path old new) alts)
  rename path old new (Trait a x) = Trait (rename path old new a) (rename path old new x)
  rename path old new expr = apply (rename path old new) expr

instance Rename String where
  rename :: FilePath -> String -> String -> String -> String
  rename _ old new str
    | str == old = new
    | otherwise = str
