module Tao where

-- TODO: maybe use terms like "lower" and "lift" for conversions to/from core
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap, first), second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (intercalate, union)
import Data.List.Split (split, splitOn, splitOneOf, splitWhen, whenElt)
import Data.Maybe (fromMaybe)

data Expr
  = Any
  | Int Int
  | Num Double
  | Var String
  | Type [String]
  | Tag String [Expr]
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Trait Expr String
  | Fun Expr Expr
  | Lam String Expr
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
  = NameDef [(String, Expr)] String [String] Expr
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

or' :: [Expr] -> Expr
or' [] = error "`or'` must have at least one expression"
or' [a] = a
or' (a : bs) = Or a (or' bs)

fun :: [Expr] -> Expr -> Expr
fun ps b = foldr Fun b ps

asFun :: Expr -> ([Expr], Expr)
asFun (Fun p a) = let (ps, b) = asFun a in (p : ps, b)
asFun (Meta _ a) = asFun a
asFun a = ([], a)

app :: Expr -> [Expr] -> Expr
app = foldl App

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = let (a', bs) = asApp a in (a', bs ++ [b])
asApp (Meta _ a) = asApp a
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

defName :: String -> Expr -> Stmt
defName name value = Def (NameDef [] name [] value)

isTypeDef :: Expr -> Bool
isTypeDef (Type _) = True
isTypeDef (Fun _ b) = isTypeDef b
isTypeDef (App a _) = isTypeDef a
isTypeDef (Ann a _) = isTypeDef a
isTypeDef _ = False

isTagDef :: Expr -> Bool
isTagDef (Tag _ _) = True
isTagDef (Fun _ b) = isTagDef b
isTagDef (App a _) = isTagDef a
isTagDef (Ann a _) = isTagDef a
isTagDef _ = False

isFunctionDef :: Expr -> Bool
isFunctionDef (Fun _ _) = True
isFunctionDef (Ann a _) = isFunctionDef a
isFunctionDef _ = False

list :: [Expr] -> Expr
list [] = Tag "[]" []
list (a : bs) = Tag "[..]" [a, list bs]

freeVars :: Expr -> [String]
freeVars expr = C.freeVars (lowerExpr [] expr) & filter (/= "_")

-- Core conversions
lowerExpr :: [(String, Expr)] -> Expr -> C.Expr
lowerExpr _ Any = C.Var "_"
lowerExpr _ (Int i) = C.Int i
lowerExpr _ (Num n) = C.Num n
lowerExpr _ (Var x) = C.Var x
lowerExpr _ (Tag "Int" []) = C.IntT
lowerExpr _ (Tag "Num" []) = C.NumT
lowerExpr _ (Type alts) = C.Typ alts
lowerExpr defs (Tag k args) = C.Tag k (map (lowerExpr defs) args)
lowerExpr defs (Tuple items) = lowerExpr defs (Tag "()" items)
-- lowerExpr defs (Record fields) = do
--   let lowerField (k, v) = (k, lowerExpr defs v)
--   C.Rec (map lowerField fields)
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

liftExpr :: C.Expr -> Expr
liftExpr C.IntT = Tag "Int" []
liftExpr C.NumT = Tag "Num" []
liftExpr (C.Int i) = Int i
liftExpr (C.Num n) = Num n
liftExpr (C.Var "_") = Any
liftExpr (C.Var x) = Var x
liftExpr (C.Tag "()" args) = Tuple (map liftExpr args)
liftExpr (C.Tag k args) = Tag k (map liftExpr args)
liftExpr (C.Typ alts) = Type alts
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

takePackageName :: String -> Maybe String
takePackageName name = case break (== ':') name of
  (_, "") -> Nothing
  (pkgName, _) -> Just pkgName

stmtDefs :: String -> Stmt -> [(String, Expr)]
stmtDefs pkgName (Import path alias exposed) = case exposed of
  (x, y) : exposed -> do
    let fullName = case path of
          path | ':' `elem` path -> path ++ "#" ++ x
          path -> pkgName ++ ":" ++ path ++ "#" ++ x
    let def = (y, Var fullName)
    def : stmtDefs pkgName (Import path alias exposed)
  [] -> [] -- TODO: import module "Record"
stmtDefs pkgName (Def (NameDef ts x (y : ys) b)) = stmtDefs pkgName (Def (NameDef ts x ys (Fun (Var y) b)))
stmtDefs _ (Def (NameDef ts x [] b)) = case lookup x ts of
  Just t -> [(x, Ann b t)]
  Nothing -> [(x, b)]
stmtDefs _ (Def (UnpackDef ts k args b)) = do
  let def x = Match [b] [Fun (Tag k args) (Var x)]
  let typedDef x = case lookup x ts of
        Just t -> (x, Ann (def x) t)
        Nothing -> (x, def x)
  map typedDef (freeVars (Tuple args))
stmtDefs pkgName (Def (TraitDef ts self x (a : args) b)) = stmtDefs pkgName (Def (TraitDef ts self x args (Fun a b)))
stmtDefs _ (Def (TraitDef ts (t, a) x [] b)) = [('.' : x, fun [t, a] b)]
stmtDefs pkgName (MetaStmt _ stmt) = stmtDefs pkgName stmt
stmtDefs _ _ = []

stmtTests :: Stmt -> [(Expr, Expr)]
stmtTests (Test a b) = [(a, b)]
stmtTests (MetaStmt _ stmt) = stmtTests stmt
stmtTests _ = []

moduleFullNames :: String -> Module -> [(String, String)]
moduleFullNames pkgName mod = do
  let defs = concatMap (stmtDefs pkgName) mod.stmts
  map (\(x, _) -> (x, pkgName ++ ":" ++ mod.name ++ "#" ++ x)) defs

moduleDefs :: String -> Module -> [(String, Expr)]
moduleDefs pkgName mod = do
  let defs = concatMap (stmtDefs pkgName) mod.stmts
  let subs = moduleFullNames pkgName mod
  substitute subs defs

packageDefs :: Package -> [(String, Expr)]
packageDefs pkg = concatMap (moduleDefs pkg.name) pkg.modules

moduleTests :: String -> Module -> [(Expr, Expr)]
moduleTests pkgName mod = do
  let tests = concatMap stmtTests mod.stmts
  let subs = moduleFullNames pkgName mod
  map (bimap (substitute subs) (substitute subs)) tests

packageTests :: Package -> [(Expr, Expr)]
packageTests pkg = concatMap (moduleTests pkg.name) pkg.modules

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
    C.Op2 C.Eq _ _ -> [TestEqError expr (liftExpr actual) (liftExpr expected)]
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

isImported :: String -> Stmt -> Bool
isImported x (Import _ alias exposed) = x == alias || x `elem` map fst exposed
isImported _ _ = False

defined :: Stmt -> [String]
defined (Import _ alias exposed) = alias : map snd exposed
defined (Def def) = case def of
  NameDef _ x _ _ -> [x]
  UnpackDef _ _ args _ -> foldr (union . freeVars) [] args
  TraitDef _ _ x _ _ -> [x]
defined (Test _ _) = []
defined (MetaStmt _ a) = defined a

class Apply a where
  apply :: (Expr -> Expr) -> a -> a

instance Apply Expr where
  apply :: (Expr -> Expr) -> Expr -> Expr
  apply _ Any = Any
  apply _ (Int i) = Int i
  apply _ (Num n) = Num n
  apply _ (Var x) = Var x
  apply _ (Type alts) = Type alts
  apply f (Tag k args) = Tag k (map f args)
  apply f (Tuple args) = Tuple (map f args)
  apply f (Record fields) = Record (map (second f) fields)
  apply f (Trait a x) = Trait (f a) x
  apply f (Fun a b) = Fun (f a) (f b)
  apply f (App a b) = App (f a) (f b)
  apply f (Let def a) = Let (apply f def) (f a)
  apply f (Bind (a, b) c) = Bind (f a, f b) (f c)
  apply f (MatchFun cases) = MatchFun (map f cases)
  apply f (Match args cases) = Match (map f args) (map f cases)
  apply f (Or a b) = Or (f a) (f b)
  apply f (Ann a b) = Ann (f a) (f b)
  apply f (Op1 op a) = Op1 op (f a)
  apply f (Op2 op a b) = Op2 op (f a) (f b)
  apply f (Meta m a) = Meta m (f a)
  apply _ Err = Err

instance Apply Definition where
  apply :: (Expr -> Expr) -> Definition -> Definition
  apply f (NameDef ts x args val) = do
    let ts' = map (second $ apply f) ts
    NameDef ts' x args (f val)
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

class Rename a where
  rename :: FilePath -> String -> String -> a -> a

instance Rename Package where
  rename :: FilePath -> String -> String -> Package -> Package
  rename path old new pkg =
    pkg {modules = map (rename path old new) pkg.modules}

instance Rename Module where
  rename :: FilePath -> String -> String -> Module -> Module
  rename path old new mod | mod.name == path = do
    mod {stmts = map (renameDefined path old new) mod.stmts}
  rename path old new mod | any (isImported old) mod.stmts = do
    mod {stmts = map (renameImported path old new) mod.stmts}
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

instance Rename (String, Expr) where
  rename :: FilePath -> String -> String -> (String, Expr) -> (String, Expr)
  rename path old new (name, value) =
    (rename path old new name, rename path old new value)

instance Rename [(String, Expr)] where
  rename :: FilePath -> String -> String -> [(String, Expr)] -> [(String, Expr)]
  rename path old new defs =
    foldr (\_ defs -> map (rename path old new) defs) defs defs

instance Rename Stmt where
  rename :: FilePath -> String -> String -> Stmt -> Stmt
  rename path old new (Import name alias exposed) = do
    let rename' = rename path old new
    Import name (rename' alias) (map (bimap rename' rename') exposed)
  rename path old new stmt = apply (rename path old new) stmt

instance Rename Expr where
  rename :: FilePath -> String -> String -> Expr -> Expr
  rename _ _ _ Any = Any
  rename _ _ _ (Int i) = Int i
  rename _ _ _ (Num n) = Num n
  rename path old new (Var x) = Var (rename path old new x)
  rename path old new (Type alts) = Type (map (rename path old new) alts)
  rename path old new (Tag k args) = Tag (rename path old new k) (map (rename path old new) args)
  rename path old new (Trait a x) = Trait (rename path old new a) (rename path old new x)
  rename _ _ _ Err = Err
  rename path old new expr = apply (rename path old new) expr

instance Rename String where
  rename :: FilePath -> String -> String -> String -> String
  rename _ old new str
    | str == old = new
    | otherwise = str

substitute :: (Rename a) => [(String, String)] -> a -> a
substitute subs a = foldr (uncurry (rename "")) a subs

refactorName :: ([String] -> Expr -> String -> String) -> Package -> Package
refactorName f pkg = do
  let refactor :: Module -> Package -> Package
      refactor mod pkg = do
        let defs = concatMap (stmtDefs pkg.name) mod.stmts
        foldr (\(x, a) -> rename mod.name x (f (map fst defs) a x)) pkg defs
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
  refactorModuleName f (Import path alias exposed) = Import (f path) alias exposed
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
    let refactor stmt = foldr (\x -> rename "" x (f x)) stmt names
    mod {name = mod.name, stmts = map refactor mod.stmts}

importAlias :: Stmt -> [String]
importAlias (Import _ alias _) = [alias]
importAlias _ = []

replace :: (Eq a) => a -> a -> [a] -> [a]
replace x y (x' : xs)
  | x == x' = y : replace x y xs
  | otherwise = x' : replace x y xs
replace _ _ [] = []

class DropMeta a where
  dropMeta :: a -> a

instance DropMeta Expr where
  dropMeta :: Expr -> Expr
  dropMeta (Meta _ a) = apply dropMeta a
  dropMeta a = apply dropMeta a
