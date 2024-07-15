module Tao where

-- TODO: maybe use terms like "lower" and "lift" for conversions to/from core
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap), second)
import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (intercalate, isPrefixOf, union)
import Data.List.Split (splitWhen)

data Expr
  = Int Int
  | Num Double
  | Var String
  | Type [String]
  | Tag String [Expr]
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Trait Expr String
  | TraitFun String
  | Fun Expr Expr
  | App Expr Expr
  | Let Definition Expr
  | Bind (Expr, Expr) Expr
  | Lambda [String] Expr
  | Match [Expr] [Case]
  | If Expr Expr Expr
  | Or Expr Expr
  | Ann Expr Expr
  | Op1 C.UnaryOp Expr
  | Op2 C.BinaryOp Expr Expr
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
  | PType [String]
  | PTuple [Pattern]
  | PRecord [(String, Pattern)]
  | PTag String [Pattern]
  | PFun Pattern Pattern
  | POr [Pattern]
  | PEq Expr
  | PMeta C.Metadata Pattern
  | PErr
  deriving (Eq, Show)

data Definition
  = Def [(String, Type)] Pattern Expr
  | TraitDef [(String, Type)] (Expr, Expr) String Expr
  -- TODO: TypeDef
  deriving (Eq, Show)

data Stmt
  = Import String String String [(String, String)] -- import pkg:path/package as alias (a, b, c)
  | Define Definition
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

intT :: Expr
intT = Tag "Int" []

pIntT :: Pattern
pIntT = PTag "Int" []

numT :: Expr
numT = Tag "Num" []

pNumT :: Pattern
pNumT = PTag "Num" []

lambda :: [String] -> [Case] -> Expr
lambda xs cases = Lambda xs (Match (map Var xs) cases)

match0 :: [Pattern] -> Expr -> Expr
match0 ps b = match [] [Case ps Nothing b]

match :: [Expr] -> [Case] -> Expr
match _ [] = Err
match [] (Case [] Nothing b : _) = b
match args cases = Match args cases

let' :: Pattern -> Expr -> Expr -> Expr
let' p a = Let (Def [] p a)

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

var :: String -> Expr -> Stmt
var name value = Define (Def [] (PVar name) value)

varT :: String -> Expr -> Expr -> Stmt
varT name typ value = Define (Def [(name, typ)] (PVar name) value)

fn :: String -> [Pattern] -> Expr -> Stmt
fn name args value = Define (Def [] (PVar name) (match0 args value))

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = let (a', bs) = asApp a in (a', bs ++ [b])
asApp (Meta _ a) = asApp a
asApp a = (a, [])

asLambda :: String -> Expr -> ([String], Expr)
asLambda _ (Lambda xs b) = (xs, b)
asLambda _ (Match _ []) = ([], Err)
asLambda prefix (Match [] cases@(Case ps _ _ : _)) = do
  let xs = C.newNames (prefix : freeVars (Match [] cases)) (replicate (length ps) prefix)
  asLambda prefix (lambda xs cases)
asLambda prefix (Meta _ a) = asLambda prefix a
asLambda _ a = ([], a)

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

toExpr :: Pattern -> Expr
toExpr PAny = error "TODO: toExpr PAny"
toExpr (PInt i) = Int i
toExpr (PNum n) = Num n
toExpr (PVar x) = Var x
toExpr (PType alts) = Type alts
toExpr (PTuple ps) = Tuple (map toExpr ps)
toExpr (PRecord fields) = Record (map (second toExpr) fields)
toExpr (PTag k ps) = Tag k (map toExpr ps)
toExpr (PFun p q) = Fun (toExpr p) (toExpr q)
toExpr (POr ps) = or' (map toExpr ps)
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
  freeVars case' = C.freeVars (lower [] case' :: C.Case)

class Lower a b where
  lower :: Context -> a -> b

class Lift a b where
  lift :: a -> b

instance Lower Expr C.Expr where
  lower :: Context -> Expr -> C.Expr
  lower _ (Int i) = C.Int i
  lower _ (Num n) = C.Num n
  lower _ (Var x) = C.Var x
  lower _ (Type alts) = C.Typ alts
  lower ctx (Tag k args)
    | Tag k args == intT = C.IntT
    | Tag k args == numT = C.NumT
    | otherwise = C.Tag k (map (lower ctx) args)
  lower ctx (Tuple items) = lower ctx (Tag "()" items)
  -- lower ctx (Record fields) = do
  --   let lowerField (k, v) = (k, lower ctx v)
  --   C.Rec (map lowerField fields)
  lower ctx (Trait a x) = do
    let a' = lower ctx a
    let env = lower ctx ctx
    case C.infer env a' of
      Left _ -> C.Err
      Right (t, _) -> C.app (C.Var $ '.' : x) [t, a']
  lower ctx (Fun a b) = C.Fun (lower ctx a) (lower ctx b)
  lower ctx (App a b) = C.App (lower ctx a) (lower ctx b)
  lower ctx (Let def b) = case def of
    Def ts p a -> lower ctx (match [a] [Case [p] Nothing b])
  lower ctx (Bind (p, a) b) = lower ctx (App (Trait a "<-") (Fun p b))
  lower ctx (Match args cases) = C.app (C.Lam (map (lower ctx) cases)) (map (lower ctx) args)
  lower ctx (Or a b) = C.Or (lower ctx a) (lower ctx b)
  lower ctx (Ann a b) = C.Ann (lower ctx a) (lower ctx b)
  lower ctx (Op1 op a) = C.Op1 op (lower ctx a)
  lower ctx (Op2 op a b) = C.Op2 op (lower ctx a) (lower ctx b)
  lower ctx (Meta m a) = C.Meta m (lower ctx a)
  lower _ Err = C.Err
  lower _ a = error $ "TODO: lower " ++ show a

infer :: Context -> Expr -> Expr
infer ctx expr = do
  case C.infer (lower ctx ctx) (lower ctx expr) of
    Left _ -> Err
    Right (t, _) -> lift t

instance Lift C.Expr Expr where
  lift :: C.Expr -> Expr
  lift C.IntT = intT
  lift C.NumT = numT
  lift (C.Int i) = Int i
  lift (C.Num n) = Num n
  lift (C.Var x) = Var x
  lift (C.Tag k args)
    | k == "()" = Tuple (map lift args)
    | otherwise = Tag k (map lift args)
  lift (C.Typ alts) = Type alts
  lift (C.For _ a) = lift a
  lift (C.Fix _ a) = lift a
  lift (C.Fun a b) = Fun (lift a) (lift b)
  lift (C.App a b) = case asApp (App (lift a) (lift b)) of
    (Tuple args, args') -> Tuple (args ++ args')
    (Var ('.' : x), _ : a : args) -> app (Trait a x) args
    -- (Fun p a, [b]) -> Let (p, b) a
    (Trait a "<-", [Fun p b]) -> Bind (p, a) b
    (a, args) -> app a args
  lift (C.Or a b) = Or (lift a) (lift b)
  lift (C.Ann a b) = Ann (lift a) (lift b)
  lift (C.Op1 op a) = Op1 op (lift a)
  lift (C.Op2 op a b) = Op2 op (lift a) (lift b)
  lift (C.Meta m a) = Meta m (lift a)
  lift C.Err = Err
  lift a = error $ "TODO: lift " ++ show a

instance Lower Case C.Case where
  lower :: Context -> Case -> C.Case
  lower ctx (Case ps cond b) =
    C.Case (map (lower ctx) ps) (lower ctx b)

instance Lower Pattern C.Pattern where
  lower :: Context -> Pattern -> C.Pattern
  lower _ PAny = C.PAny
  lower _ (PInt i) = C.PInt i
  lower _ (PNum n) = C.PNum n
  lower _ (PVar x) = C.PVar x
  lower _ (PType alts) = C.PTyp alts
  lower ctx (PTag k ps)
    | PTag k ps == pIntT = C.PIntT
    | PTag k ps == pNumT = C.PNumT
    | otherwise = C.PTag k (map (lower ctx) ps)
  lower ctx (PFun p q) = C.PFun (lower ctx p) (lower ctx q)
  lower ctx (POr ps) = error "TODO"
  lower ctx (PEq a) = C.PEq (lower ctx a)
  lower ctx (PMeta m p) = C.PMeta m (lower ctx p)
  lower _ PErr = C.PErr
  lower _ p = error $ "TODO: lower " ++ show p

instance Lower Context C.Env where
  lower :: Context -> Context -> C.Env
  lower ctx = map (second (lower ctx))

instance Lower Package C.Env where
  lower :: Context -> Package -> C.Env
  lower ctx pkg = lower ctx (getContext pkg)

stmtTests :: Stmt -> [(Expr, Pattern)]
stmtTests (Test expr expected) = [(expr, expected)]
stmtTests (MetaStmt _ stmt) = stmtTests stmt
stmtTests _ = []

fullName :: String -> String -> String -> String
fullName pkg mod "" = '@' : pkg ++ "." ++ mod
fullName pkg mod name = fullName pkg mod "" ++ '.' : name

class FullNames a b where
  fullNames :: a -> b -> [(String, String)]

instance FullNames (String, String) Stmt where
  fullNames :: (String, String) -> Stmt -> [(String, String)]
  fullNames (pkg, mod) (Import "" mod' alias existing) =
    fullNames (pkg, mod) (Import pkg mod' alias existing)
  fullNames (pkg, mod) (Import pkg' mod' alias []) =
    [(alias, fullName pkg' mod' "")]
  fullNames (pkg, mod) (Import pkg' mod' alias ((x, y) : existing)) =
    (y, fullName pkg mod x) : fullNames (pkg, mod) (Import pkg' mod' alias existing)
  fullNames (pkg, mod) (Define def) =
    map (\(x, _) -> (x, fullName pkg mod x)) (getContext def)
  fullNames _ (Test _ _) = []
  fullNames (pkg, mod) (MetaStmt _ stmt) = fullNames (pkg, mod) stmt

instance FullNames String Module where
  fullNames :: String -> Module -> [(String, String)]
  fullNames pkg mod = concatMap (fullNames (pkg, mod.name)) mod.stmts

moduleFullNames :: String -> Module -> [(String, String)]
moduleFullNames pkgName mod = do
  let ctx = concatMap getContext mod.stmts
  map (\(x, _) -> (x, fullName pkgName mod.name x)) ctx

splitWith :: (Char -> Bool) -> String -> [String]
splitWith f text = case dropWhile f text of
  "" -> []
  text -> do
    let (word, remaining) = break f text
    word : splitWith f remaining

split :: Char -> String -> [String]
split delim = splitWith (== delim)

splitIdentifier :: String -> (String, String, String)
splitIdentifier ('@' : identifier) = case split '.' identifier of
  [] -> ("", "", "")
  [pkg] -> (pkg, "", "")
  [pkg, mod] -> (pkg, mod, "")
  pkg : mod : name : _ -> (pkg, mod, name)
splitIdentifier name = ("", "", name)

class Link a b where
  link :: a -> b -> b

instance Link () Package where
  link :: () -> Package -> Package
  link _ pkg = do
    pkg {modules = map (link pkg.name) pkg.modules}

instance Link String Module where
  link :: String -> Module -> Module
  link pkg mod = do
    let subs = fullNames pkg mod
    mod {stmts = map (link (pkg, subs)) mod.stmts}

instance Link (String, [(String, String)]) Stmt where
  link :: (String, [(String, String)]) -> Stmt -> Stmt
  link (pkg, subs) (Import "" mod alias exposed) =
    link (pkg, subs) (Import pkg mod alias exposed)
  link (pkg, subs) (Import pkg' mod alias exposed) = do
    let stmt = Import pkg' mod (substitute subs alias) exposed
    substitute subs stmt
  link (_, subs) stmt = substitute subs stmt

class GetContext a where
  getContext :: a -> Context

instance GetContext Stmt where
  getContext :: Stmt -> Context
  getContext (Import pkg path alias exposed) = case exposed of
    (x, y) : exposed -> do
      let def = (y, Var x)
      def : getContext (Import pkg path alias exposed)
    [] -> []
  getContext (Define def) = getContext def
  getContext (Test _ _) = []
  getContext (MetaStmt _ stmt) = getContext stmt

instance GetContext Definition where
  getContext :: Definition -> Context
  getContext (Def ts (PVar x) b) = case lookup x ts of
    Just t -> [(x, Ann b t)]
    Nothing -> [(x, b)]
  getContext (Def ts p b) = do
    let def x = let' p b (Var x)
    let typedDef x = case lookup x ts of
          Just t -> (x, Ann (def x) t)
          Nothing -> (x, def x)
    map typedDef (freeVars p)
  getContext (TraitDef ts (t, a) x b) =
    [('.' : x, fun [t, a] b)]

instance GetContext Module where
  getContext :: Module -> Context
  getContext mod = concatMap getContext mod.stmts

instance GetContext Package where
  getContext :: Package -> Context
  getContext pkg = concatMap getContext pkg.modules

moduleTests :: Module -> [(Expr, Pattern)]
moduleTests mod = concatMap stmtTests mod.stmts

packageTests :: Package -> [(Expr, Pattern)]
packageTests pkg = concatMap moduleTests pkg.modules

run :: Package -> Expr -> Expr
run pkg expr = do
  let pkg' = link () pkg
  let ctx = getContext pkg'
  let env = lower ctx pkg'
  let term = lower (getContext pkg') expr
  lift (C.eval env term)

testEq :: Context -> (Expr, Pattern) -> [TestError]
testEq ctx (expr, expected) = do
  -- let env = lower ctx
  -- let actual = C.eval env (lower ctx expr)
  -- let expected = C.eval env (lower ctx result)
  -- case C.eval [] (actual `C.eq` expected) of
  --   C.Err -> [TestEqError expr (liftExpr actual) (liftExpr expected)]
  --   C.Op2 C.Eq _ _ -> [TestEqError expr (liftExpr actual) (liftExpr expected)]
  --   _ -> []
  let env = lower ctx ctx
  let unitTest = lower ctx (let' expected expr (Tuple []))
  let passed = case C.eval env unitTest of
        C.Err -> False
        C.Op2 C.Eq _ _ -> False
        _ -> True
  if passed
    then []
    else do
      let actual = lower ctx expr & C.eval env & lift
      [TestEqError expr actual expected]

test :: Package -> [TestError]
test pkg = do
  let pkg' = link () pkg
  let ctx = getContext pkg'
  concatMap (testEq ctx) (packageTests pkg')

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
isImported x (Import _ _ alias exposed) = x == alias || x `elem` map fst exposed
isImported _ _ = False

defined :: Stmt -> [String]
defined (Import _ _ alias exposed) = alias : map snd exposed
defined (Define def) = case def of
  Def _ p _ -> freeVars p
  TraitDef _ _ x _ -> [x]
defined (Test _ _) = []
defined (MetaStmt _ a) = defined a

class Apply a where
  apply :: (Expr -> Expr) -> a -> a

instance Apply Expr where
  apply :: (Expr -> Expr) -> Expr -> Expr
  apply _ (Int i) = Int i
  apply _ (Num n) = Num n
  apply _ (Var x) = Var x
  apply _ (Type alts) = Type alts
  apply f (Tag k args) = Tag k (map f args)
  apply f (Tuple args) = Tuple (map f args)
  apply f (Record fields) = Record (map (second f) fields)
  apply f (Trait a x) = Trait (f a) x
  apply _ (TraitFun x) = TraitFun x
  apply f (Fun a b) = Fun (f a) (f b)
  apply f (App a b) = App (f a) (f b)
  apply f (Let def a) = Let (apply f def) (f a)
  apply f (Bind (a, b) c) = Bind (f a, f b) (f c)
  apply f (Match args cases) = Match (map f args) (map (apply f) cases)
  apply f (Or a b) = Or (f a) (f b)
  apply f (Ann a b) = Ann (f a) (f b)
  apply f (Op1 op a) = Op1 op (f a)
  apply f (Op2 op a b) = Op2 op (f a) (f b)
  apply f (Meta m a) = Meta m (f a)
  apply _ Err = Err
  apply _ a = error $ "TODO: apply " ++ show a

instance Apply Pattern where
  apply :: (Expr -> Expr) -> Pattern -> Pattern
  apply _ PAny = PAny
  apply _ (PInt i) = PInt i
  apply _ (PNum n) = PNum n
  apply _ (PVar x) = PVar x
  apply _ (PType alts) = PType alts
  apply f (PTuple ps) = PTuple (map (apply f) ps)
  apply f (PRecord fields) = PRecord (map (second $ apply f) fields)
  apply f (PTag k ps) = PTag k (map (apply f) ps)
  apply f (PFun p q) = PFun (apply f p) (apply f q)
  apply f (POr ps) = POr (map (apply f) ps)
  apply f (PEq a) = PEq (f a)
  apply f (PMeta m p) = PMeta m (apply f p)
  apply _ PErr = PErr

instance Apply Case where
  apply :: (Expr -> Expr) -> Case -> Case
  apply f (Case ps cond b) = Case (map (apply f) ps) (fmap f cond) (f b)

instance Apply Definition where
  apply :: (Expr -> Expr) -> Definition -> Definition
  apply f (Def ts p val) = do
    let ts' = map (second f) ts
    Def ts' (apply f p) (f val)
  apply f (TraitDef ts (t, a) x val) = do
    let ts' = map (second f) ts
    TraitDef ts' (f t, f a) x (f val)

instance Apply Stmt where
  apply :: (Expr -> Expr) -> Stmt -> Stmt
  apply _ stmt@Import {} = stmt
  apply f (Define def) = Define (apply f def)
  apply f (Test a b) = Test (apply f a) (apply f b)
  apply f (MetaStmt m a) = MetaStmt m (apply f a)

class Rename a where
  rename :: String -> String -> a -> a

instance Rename Package where
  rename :: String -> String -> Package -> Package
  rename old new pkg =
    pkg {modules = map (rename old new) pkg.modules}

instance Rename Module where
  rename :: String -> String -> Module -> Module
  rename old new mod =
    mod {stmts = map (rename old new) mod.stmts}

instance Rename Stmt where
  rename :: String -> String -> Stmt -> Stmt
  rename old new (Import pkg name alias exposed) = do
    let alias' = rename old new alias
    let exposed' = map (bimap (rename old new) (rename old new)) exposed
    Import pkg name alias' exposed'
  rename old new (Define def) = Define (rename old new def)
  rename old new (Test a b) = Test (rename old new a) (rename old new b)
  rename old new (MetaStmt m stmt) = MetaStmt m (rename old new stmt)

instance Rename Definition where
  rename :: String -> String -> Definition -> Definition
  rename old new (Def ts p val) = do
    let ts' = map (bimap (rename old new) (rename old new)) ts
    let p' = rename old new p
    let val' = rename old new val
    Def ts' p' val'
  rename old new (TraitDef ts (t, a) x val) = do
    let ts' = map (bimap (rename old new) (rename old new)) ts
    let x' = rename old new x
    let val' = rename old new val
    TraitDef ts' (t, a) x' val'

instance Rename (String, Expr) where
  rename :: String -> String -> (String, Expr) -> (String, Expr)
  rename old new (name, value) =
    (rename old new name, rename old new value)

instance Rename Context where
  rename :: String -> String -> Context -> Context
  rename old new ctx =
    foldr (\_ ctx -> map (rename old new) ctx) ctx ctx

instance Rename Expr where
  rename :: String -> String -> Expr -> Expr
  rename old new (Var x) = Var (rename old new x)
  rename old new (Type alts) = Type (map (rename old new) alts)
  rename old new (Tag k args) = Tag (rename old new k) (map (rename old new) args)
  rename old new (Trait a x) = Trait (rename old new a) x
  rename old new (Let def a) = Let (rename old new def) (rename old new a)
  rename old new (Match args cases) = Match (map (rename old new) args) (map (rename old new) cases)
  rename old new (Meta m a) = Meta m (rename old new a)
  rename old new expr = apply (rename old new) expr

instance Rename Pattern where
  rename :: String -> String -> Pattern -> Pattern
  rename old new (PVar x) = PVar (rename old new x)
  rename old new (PType alts) = PType (map (rename old new) alts)
  rename old new (PTag k ps) = PTag (rename old new k) (map (rename old new) ps)
  rename old new (PMeta m p) = PMeta m (rename old new p)
  rename old new p = apply (rename old new) p

instance Rename Case where
  rename :: String -> String -> Case -> Case
  rename old new (Case ps cond b) =
    Case (map (rename old new) ps) (fmap (rename old new) cond) (rename old new b)

instance Rename String where
  rename :: String -> String -> String -> String
  rename old new str
    | str == old = new
    | otherwise = str

substitute :: (Rename a) => [(String, String)] -> a -> a
substitute subs a = foldr (uncurry rename) a subs

refactorName :: ([String] -> Expr -> String -> String) -> Package -> Package
refactorName f pkg = do
  let refactor :: Module -> Package -> Package
      refactor mod pkg = do
        let ctx = concatMap getContext mod.stmts
        foldr (\(x, a) -> rename x (f (map fst ctx) a x)) pkg ctx
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
  refactorModuleName f (Import pkg path alias exposed) = Import (f pkg) (f path) alias exposed
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
    let refactor stmt = foldr (\x -> rename x (f x)) stmt names
    mod {name = mod.name, stmts = map refactor mod.stmts}

importAlias :: Stmt -> [String]
importAlias (Import _ _ alias _) = [alias]
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
  dropMeta (Match args cases) = Match (map dropMeta args) (map dropMeta cases)
  dropMeta a = apply dropMeta a

instance DropMeta Pattern where
  dropMeta :: Pattern -> Pattern
  dropMeta (PMeta _ p) = dropMeta p
  dropMeta a = apply dropMeta a

instance DropMeta Case where
  dropMeta :: Case -> Case
  dropMeta (Case ps guard a) = Case (map dropMeta ps) (fmap dropMeta guard) (dropMeta a)

instance DropMeta Definition where
  dropMeta :: Definition -> Definition
  dropMeta (Def ts p b) = do
    let ts' = map (second dropMeta) ts
    Def ts' (dropMeta p) (dropMeta b)
  dropMeta (TraitDef ts (t, a) x b) = do
    let ts' = map (second dropMeta) ts
    TraitDef ts' (dropMeta t, dropMeta a) x (dropMeta b)

instance DropMeta Stmt where
  dropMeta :: Stmt -> Stmt
  dropMeta stmt@Import {} = stmt
  dropMeta (Define def) = Define (dropMeta def)
  dropMeta (Test a b) = Test (dropMeta a) (dropMeta b)
  dropMeta (MetaStmt _ stmt) = dropMeta stmt

instance DropMeta Module where
  dropMeta :: Module -> Module
  dropMeta mod = mod {stmts = map dropMeta mod.stmts}

instance DropMeta Package where
  dropMeta :: Package -> Package
  dropMeta pkg = pkg {modules = map dropMeta pkg.modules}

caseSplit :: Case -> (Pattern, Case)
caseSplit (Case [] cond a) = (PAny, Case [] cond a)
caseSplit (Case (p : ps) cond a) = (p, Case ps cond a)

patternsName :: [Pattern] -> Maybe String
patternsName [] = Nothing
patternsName (p : ps) = case p of
  PVar x -> case patternsName ps of
    Just y | x /= y -> Nothing
    _ -> Just x
  PMeta _ p -> patternsName (p : ps)
  _ -> patternsName ps
