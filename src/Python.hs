module Python where

import Control.Monad (unless, when)
import qualified Core as C
import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable (foldlM, foldrM)
import Data.Function ((&))
import Data.List (intercalate, union)
import Data.Maybe (fromMaybe)
import qualified Debug.Trace as Debug
import qualified PrettyPrint as PP
import System.Directory (createDirectory, createDirectoryIfMissing, doesPathExist, removeDirectoryRecursive)
import System.FilePath (joinPath, splitDirectories, splitFileName, splitPath, takeDirectory, takeFileName, (</>))
import qualified Tao as T

-- TODO: abstract into an `Imperative` language
-- https://en.wikipedia.org/wiki/Imperative_programming

-- https://docs.python.org/3/library/ast.html
-- https://docs.python.org/3/reference/grammar.html

-- https://docs.python.org/3/library/ast.html#ast.Module
data Module = Module
  { name :: String,
    body :: [Stmt]
  }
  deriving (Eq, Show)

newModule :: String -> [Stmt] -> Module
newModule name body =
  Module
    { name = name,
      body = body
    }

data Package
  = Package
  { name :: String,
    src :: [Module],
    test :: [Module]
  }
  deriving (Eq, Show)

--- Expressions ---
-- https://docs.python.org/3/library/ast.html#expressions
data Expr
  = None -- None
  | Bool Bool -- True
  | Integer Int -- 42
  | Float Double -- 3.14
  | Imaginary Double -- 3.14j
  | List [Expr] -- [x, y, z]
  | Tuple [Expr] -- (x, y, z)
  | Set [Expr] -- {x, y, z}
  | Dict [(Expr, Expr)] -- {x: 1, y: 2, z: 3}
  | Bytes String -- b'hello'
  | String String -- 'Hello'
  | FString [FormattedValue] -- f"hello {x}"
  | Name String -- x
  | Starred Expr -- _, *x = _
  | UnaryOp UnaryOp Expr -- not x
  | BinOp Expr BinOp Expr -- x + y
  | BoolOp Expr BoolOp Expr -- x and y
  | Compare Expr Compare Expr -- x == y
  | Lambda [String] Expr -- lambda x, y: z
  | Call Expr [Expr] [(String, Expr)] -- func(*args, **kwargs)
  | IfExp Expr Expr Expr -- a if b else c
  | Attribute Expr String -- x.y
  | NamedExpr Expr Expr -- x := y
  | Subscript Expr Expr -- x[y]
  | Slice Expr Expr -- x:y
  | ListComp Expr Expr Expr [Expr] -- [x for x in xs (if y)*]
  | SetComp Expr Expr Expr [Expr] -- {x for x in xs (if y)*}
  | GeneratorExp Expr Expr Expr [Expr] -- (x for x in xs (if y)*)
  | DictComp Expr Expr Expr [Expr] -- {x: x for x in xs (if y)*}
  | Meta C.Metadata Expr
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.FormattedValue
data FormattedValue
  = Str String
  | Val Expr
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.UnaryOp
data UnaryOp
  = UAdd -- +x
  | USub -- -x
  | Not -- not x
  | Invert -- ~x
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.BinOp
data BinOp
  = Add -- x + y
  | Sub -- x - y
  | Mult -- x * y
  | Div -- x / y
  | FloorDiv -- x // y
  | Mod -- x % y
  | Pow -- x ** y
  | LShift -- x << y
  | RShift -- x >> y
  | BitOr -- x | y
  | BitXor -- x ^ y
  | BitAnd -- x & y
  | MatMult -- x @ y
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.BoolOp
data BoolOp
  = And -- x and y
  | Or -- x or y
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.Compare
data Compare
  = Eq -- x == y
  | NotEq -- x = y
  | Lt -- x < y
  | LtE -- x <= y
  | Gt -- x > y
  | GtE -- x >= y
  | Is -- x is y
  | IsNot -- x is not y
  | In -- x in y
  | NotIn -- x not in y
  deriving (Eq, Show)

--- Statements ---
-- https://docs.python.org/3/library/ast.html#statements
data Stmt
  = Assign [Expr] Expr -- x = y = z
  | AnnAssign Expr Expr (Maybe Expr) -- x: T = y
  | AugAssign Expr BinOp Expr -- x += y
  | Raise Expr (Maybe Expr) -- raise x [from y]
  | Assert Expr Expr -- assert x, y
  | Delete [Expr] -- del x, y
  | Pass -- pass
  | TypeAlias String [TypeParam] Expr -- type Alias = int
  | Import String (Maybe String) -- import mod [as m]
  | ImportFrom String [(String, Maybe String)] -- from mod import x, y as z
  | Break -- break
  | Continue -- continue
  | Match Expr [(Pattern, Maybe Expr, [Stmt])] -- match x: case p: y; ...
  | Return Expr -- return x
  | Yield Expr -- yield x
  | YieldFrom Expr -- yield from x
  | Global [String] -- global x
  | Nonlocal [String] -- nonlocal x
  | Await Expr -- await x
  | If
      { test :: Expr,
        body :: [Stmt],
        orelse :: [Stmt]
      }
  | For
      { target :: Expr,
        iter :: Expr,
        body :: [Stmt],
        orelse :: [Stmt],
        async :: Bool
      }
  | While
      { test :: Expr,
        body :: [Stmt],
        orelse :: [Stmt]
      }
  | With
      { items :: [(Expr, Maybe Expr)],
        body :: [Stmt],
        async :: Bool
      }
  | FunctionDef
      { name :: String,
        args :: [(String, Maybe Expr, Maybe Expr)],
        body :: [Stmt],
        decorators :: [Expr],
        returns :: Maybe Expr,
        typeParams :: [TypeParam],
        async :: Bool
      }
  | ClassDef
      { name :: String,
        bases :: [Expr],
        body :: [Stmt],
        decorators :: [Expr],
        typeParams :: [TypeParam]
      }
  | Try
      { body :: [Stmt],
        handlers :: [(Maybe Expr, String, Expr)],
        else' :: [Stmt],
        finally :: [Stmt]
      }
  deriving (Eq, Show)

newFunctionDef :: String -> [(String, Maybe Expr, Maybe Expr)] -> [Stmt] -> Stmt
newFunctionDef name args body =
  FunctionDef
    { name = name,
      args = args,
      body = body,
      decorators = [],
      returns = Nothing,
      typeParams = [],
      async = False
    }

newClassDef :: String -> [TypeParam] -> [Stmt] -> Stmt
newClassDef name args body =
  ClassDef
    { name = name,
      bases = [],
      body = body,
      decorators = [],
      typeParams = args
    }

--- Pattern Matching ---
-- https://docs.python.org/3/library/ast.html#pattern-matching
data Pattern
  = MatchValue Expr -- case 1
  | MatchSequence [Pattern] -- case [p, q]
  | MatchStar String -- case [p, *ps]
  | MatchMapping [(String, Pattern)] (Maybe String) -- case {p: q, [, **kvs]}
  | MatchClass String [Pattern] [(String, Pattern)] -- ClassName(p, x=q)
  | MatchAs (Maybe Pattern) String -- case p as x
  | MatchOr [Pattern] -- case p | q
  | MatchMeta C.Metadata Pattern
  deriving (Eq, Show)

--- Type parameters ---
-- https://docs.python.org/3/library/ast.html#ast-type-params
data TypeParam
  = TypeVar String -- T[a]
  | TypeVarTuple String -- T[*ts]
  | ParamSpec String -- T[**ts]
  deriving (Eq, Show)

data BuildOptions = BuildOptions
  { version :: (Int, Int),
    packageName :: String,
    testPath :: FilePath,
    docsPath :: FilePath,
    maxLineLength :: Int,
    indent :: String
  }
  deriving (Eq, Show)

-- Taken from help("keywords") in thon 3.12 REPL
keywords :: [String]
keywords =
  [ "False",
    "None",
    "True",
    "and",
    "as",
    "assert",
    "async",
    "await",
    "break",
    "class",
    "continue",
    "def",
    "del",
    "elif",
    "else",
    "except",
    "finally",
    "for",
    "from",
    "global",
    "if",
    "import",
    "in",
    "is",
    "lambda",
    "nonlocal",
    "not",
    "or",
    "pass",
    "raise",
    "return",
    "try",
    "while",
    "with",
    "yield"
  ]

-- https://docs.python.org/3/library/functions.html
builtinFunctions :: [String]
builtinFunctions =
  [ "__import__",
    "abs",
    "aiter",
    "all",
    "anext",
    "any",
    "ascii",
    "bin",
    "bool",
    "breakpoint",
    "bytearray",
    "bytes",
    "callable",
    "chr",
    "classmethod",
    "compile",
    "complex",
    "delattr",
    "dict",
    "dir",
    "divmod",
    "enumerate",
    "eval",
    "exec",
    "filter",
    "float",
    "format",
    "frozenset",
    "getattr",
    "globals",
    "hasattr",
    "hash",
    "help",
    "hex",
    "id",
    "input",
    "int",
    "isinstance",
    "issubclass",
    "iter",
    "len",
    "list",
    "locals",
    "map",
    "max",
    "memoryview",
    "min",
    "next",
    "object",
    "oct",
    "open",
    "ord",
    "pow",
    "print",
    "property",
    "range",
    "repr",
    "reversed",
    "round",
    "set",
    "setattr",
    "slice",
    "sorted",
    "staticmethod",
    "str",
    "sum",
    "super",
    "tuple",
    "type",
    "vars",
    "zip"
  ]

reservedNames :: [String]
reservedNames = keywords ++ builtinFunctions

addUnique :: (Eq a) => a -> [a] -> [a]
addUnique x [] = [x]
addUnique x (x' : ys) | x == x' = x : ys
addUnique x (y : ys) = y : addUnique x ys

--- Syntax sugar ---

int :: Expr
int = Name "int"

float :: Expr
float = Name "float"

call :: String -> [Expr] -> Expr
call f args = Call (Name f) args []

dict :: [(String, Expr)] -> Expr
dict fields = Dict (map (first String) fields)

callable :: [Expr] -> Expr -> Expr
callable args ret =
  Subscript (Name "Callable") (Tuple [List args, ret])

bitOr :: Expr -> Expr -> Expr
bitOr a = BinOp a BitOr

import' :: String -> Stmt
import' name = Import name Nothing

assign :: String -> Expr -> Stmt
assign name = Assign [Name name]

raise :: Expr -> Stmt
raise x = Raise x Nothing

--- Build target ---
defaultBuildOptions :: BuildOptions
defaultBuildOptions =
  BuildOptions
    { version = (3, 12),
      packageName = "",
      testPath = "test",
      docsPath = "docs",
      maxLineLength = 79,
      indent = "    "
    }

stmtNames :: Stmt -> [String]
stmtNames (Assign [] _) = []
stmtNames (Assign (var : vars) value) = case var of
  Name x -> x : stmtNames (Assign vars value)
  _ -> stmtNames (Assign vars value)
stmtNames (AnnAssign var _ _) = case var of
  Name x -> [x]
  _ -> []
stmtNames (TypeAlias x _ _) = [x]
stmtNames (Import name maybeAlias) = case maybeAlias of
  Just alias -> [alias]
  Nothing -> [name]
stmtNames (ImportFrom _ exposed) = do
  let exposedNames (_, Just alias) = [alias]
      exposedNames (name, Nothing) = [name]
  concatMap exposedNames exposed
stmtNames (Global names) = names
stmtNames (Nonlocal names) = names
stmtNames (FunctionDef {name}) = [name]
stmtNames (ClassDef {name}) = [name]
stmtNames _ = []

pyName :: [String] -> T.Expr -> String -> String
pyName existing expr identifier = do
  let (_, _, name) = T.splitIdentifier identifier
  case name of
    name | T.isTagDef expr -> T.nameCamelCaseUpper name
    name | T.isTypeDef expr -> T.nameCamelCaseUpper name
    name -> T.nameSnakeCase name

build :: BuildOptions -> FilePath -> T.Package -> IO FilePath
build options base pkg = do
  let pyPkg =
        T.link () pkg
          & T.refactorName pyName
          & T.refactorModuleName (T.replace '/' '.' . T.replace '-' '_')
          & T.refactorModuleAlias T.nameSnakeCase

  let pkgPath = base </> "python"
  let srcPath = pkgPath </> pyPkg.name
  let testPath = pkgPath </> options.testPath
  let docsPath = pkgPath </> options.docsPath

  -- Initialize build path
  pkgPathExists <- doesPathExist pkgPath
  when pkgPathExists (removeDirectoryRecursive pkgPath)
  createDirectoryIfMissing True pkgPath

  -- Create pyproject.toml
  writeFile (pkgPath </> "pyproject.toml") ""
  -- TODO: create README.md
  -- TODO: create LICENSE

  -- Create source files
  files <- mapM (buildModule options pyPkg.name srcPath) pyPkg.modules

  createDirectory testPath
  writeFile (testPath </> "__init__.py") ""
  files <- mapM (buildTests options pyPkg.name testPath) pyPkg.modules

  -- TODO: Create docs
  createDirectory docsPath

  return pkgPath

buildDir :: FilePath -> [FilePath] -> IO ()
buildDir base dirs = do
  exists <- doesPathExist base
  unless exists $ do
    createDirectoryIfMissing True base
    writeFile (base </> "__init__.py") ""
  case dirs of
    [] -> return ()
    (dir : subdirs) -> buildDir (base </> dir) subdirs

buildModule :: BuildOptions -> String -> FilePath -> T.Module -> IO FilePath
buildModule options pkgName base mod = do
  -- Initialize the file path recursively.
  let filename = T.replace '.' '/' mod.name ++ ".py"
  buildDir base (splitPath $ takeDirectory filename)

  -- Write the source file contents.
  let mod' = mod {T.stmts = filter (not . T.isTest) mod.stmts}
  let options' = options {packageName = pkgName}
  writeFile (base </> filename) $
    (emit options' mod' :: Module)
      & layout
      & pretty options'
  return filename

buildTests :: BuildOptions -> String -> FilePath -> T.Module -> IO FilePath
buildTests options pkgName base mod = do
  -- Initialize the file path recursively.
  let (dir, name) = splitFileName (T.replace '.' '/' mod.name)
  let filename = dir </> "test_" ++ name ++ ".py"
  buildDir base (splitPath $ takeDirectory filename)

  -- Write the test file contents.
  let options' = options {packageName = pkgName}
  writeFile (base </> filename) $
    buildModuleTests options' mod
      & layout
      & pretty options'
  return filename

buildModuleTests :: BuildOptions -> T.Module -> Module
buildModuleTests options mod = do
  let path = splitDirectories mod.name & filter (/= ".")
  let importPath = intercalate "." (options.packageName : path)
  let importNames = case map fst (concatMap T.getContext mod.stmts) of
        [] -> []
        names -> [ImportFrom importPath (map (,Nothing) names)]
  let stmts =
        Import "unittest" Nothing
          : Import importPath Nothing
          : importNames
          ++ emit options (filter T.isImport mod.stmts)
          ++ [ ClassDef
                 { name = "Test" ++ T.nameCamelCaseUpper (takeFileName mod.name),
                   bases = [Attribute (Name "unittest") "TestCase"],
                   body = emit options (filter T.isTest mod.stmts),
                   decorators = [],
                   typeParams = []
                 },
               If
                 { test = Compare (Name "__name__") Eq (String "__main__"),
                   body = [Assign [] (Call (Attribute (Name "unittest") "main") [] [])],
                   orelse = []
                 }
             ]
  Module {name = "test_" ++ mod.name, body = stmts}

-- TODO: rename to Emit
class Emit a b where
  emit :: BuildOptions -> a -> b

instance Emit Package Package where
  emit :: BuildOptions -> Package -> Package
  emit options pkg = do
    Package
      { name = T.nameDashCase pkg.name,
        src = [],
        test = []
      }

instance Emit T.Module Module where
  emit :: BuildOptions -> T.Module -> Module
  emit options mod = do
    let stmts = emit options (filter (not . T.isTest) mod.stmts)
    Module {name = mod.name, body = stmts}

instance Emit T.Stmt [Stmt] where
  emit :: BuildOptions -> T.Stmt -> [Stmt]
  emit options (T.Import pkg path alias exposed) = do
    let mod = pkg ++ "." ++ path
    case exposed of
      [] -> do
        let alias' = if '@' : mod == alias then Nothing else Just alias
        [Import mod alias']
      exposed -> do
        let expose (x, x') | x == x' = (x, Nothing)
            expose (x, y) = (x, Just y)
        let stmts = emit options (T.Import pkg path alias [])
        stmts ++ [ImportFrom mod (map expose exposed)]
  emit options (T.Define def) = emit options def
  emit options (T.Test a p) = do
    let (stmts1, a') = emit options a
    let (stmts2, b') = emit options (T.toExpr p) -- TODO: do a match instead
    let def =
          FunctionDef
            { name = "test_" ++ T.nameSnakeCase (show (T.dropMeta a)),
              args = [("self", Nothing, Nothing)],
              body = [Assign [] (Call (Attribute (Name "self") "assertEqual") [a', b'] [])],
              decorators = [],
              returns = Nothing,
              typeParams = [],
              async = False
            }
    stmts1 ++ stmts2 ++ [def]
  emit options (T.MetaStmt _ stmt) = emit options stmt

instance Emit [T.Stmt] [Stmt] where
  emit :: BuildOptions -> [T.Stmt] -> [Stmt]
  emit _ [] = []
  emit options (stmt : stmts) = emit options stmt ++ emit options stmts

instance Emit T.Definition [Stmt] where
  emit :: BuildOptions -> T.Definition -> [Stmt]
  emit options (T.Def ts (T.PVar x) b) = case (lookup x ts, T.lambdaOf "_" b) of
    (Nothing, ([], b)) -> do
      let (stmts, b') = emit options b
      let def = Assign [Name x] b'
      stmts ++ [def]
    (Just t, ([], b)) -> do
      let (stmts1, t') = emit options t
      let (stmts2, b') = emit options b
      let def = AnnAssign (Name x) t' (Just b')
      stmts1 ++ stmts2 ++ [def]
    (Nothing, (xs, b)) -> do
      let (body, b') = emit options b
      let def =
            FunctionDef
              { name = x,
                args = map (,Nothing,Nothing) xs,
                body = body ++ [Return b'],
                decorators = [],
                returns = Nothing,
                typeParams = [],
                async = False
              }
      [def]
    (Just t, (xs, b)) -> do
      let emitArg :: (String, T.Expr) -> ([Stmt], [(String, Maybe Expr, Maybe Expr)]) -> ([Stmt], [(String, Maybe Expr, Maybe Expr)])
          emitArg (x, t) (stmts, args) = do
            let (stmts', t') = emit options t
            (stmts' ++ stmts, (x, Just t', Nothing) : args)
      let (ts, ret) = T.funOf t
      let (stmts1, args) = foldr emitArg ([], []) (zip xs ts)
      let (stmts2, ret') = emit options ret
      let (body, b') = emit options b
      let def =
            FunctionDef
              { name = x,
                args = args,
                body = body ++ [Return b'],
                decorators = [],
                returns = Just ret',
                typeParams = [],
                async = False
              }
      stmts1 ++ stmts2 ++ [def]
  emit options (T.Def ts (T.PMeta _ p) b) = emit options (T.Define (T.Def ts p b))
  emit options def = error $ "TODO: emit " ++ show def

instance Emit T.Expr ([Stmt], Expr) where
  emit :: BuildOptions -> T.Expr -> ([Stmt], Expr)
  emit _ (T.Int i) = ([], Integer i)
  emit _ (T.Num n) = ([], Float n)
  emit _ (T.Var x) = ([], Name x)
  emit options (T.Tag k args) = case (k, args) of
    ("Type", []) -> ([], Name "type")
    ("Int", []) -> ([], Name "int")
    ("Num", []) -> ([], Name "float")
    ("True", []) -> ([], Name "True")
    ("False", []) -> ([], Name "False")
    ("Nothing", []) -> ([], Name "None")
    ("", args) | null args || any ((== "") . fst) args -> do
      let (stmts, items) = emit options (map snd args)
      (stmts, Tuple items)
    ("", args) -> do
      let (stmts, items) = emit options args
      (stmts, Dict (map (first String) items))
    (k, args) -> do
      let (posArgs, kwArgs) = span ((== "") . fst) args
      let (stmts1, posArgs') = emit options (map snd posArgs)
      let (stmts2, kwArgs') = emit options kwArgs
      (stmts1 ++ stmts2, Call (Name k) posArgs' kwArgs')
  emit options (T.Trait a x) = do
    let (stmts, a') = emit options a
    (stmts, Attribute a' x)
  emit _ (T.TraitFun x) = do
    let a = "_"
    ([], Lambda [a] (Attribute (Name a) x))
  emit options (T.Fun a b) = do
    let (args, ret) = T.funOf (T.Fun a b)
    let (stmts1, args') = emit options args
    let (stmts2, ret') = emit options ret
    (stmts1 ++ stmts2, callable args' ret')
  emit options (T.App a b) = do
    let (f, args) = T.appOf (T.App a b)
    let (stmts1, f') = emit options f
    let (stmts2, args') = emit options args
    (stmts1 ++ stmts2, Call f' args' [])
  emit options (T.Or a b) = do
    let (stmts1, a') = emit options a
    let (stmts2, b') = emit options b
    (stmts1 ++ stmts2, bitOr a' b')
  emit options (T.Let def b) = do
    let stmts1 = emit options def
    let (stmts2, b') = emit options b
    (stmts1 ++ stmts2, b')
  -- Bind (Expr, Expr) Expr
  emit options (T.Match [] cases) = do
    let (xs, b) = T.lambdaOf "_arg" (T.Match [] cases)
    let (stmts, b') = emit options b
    let expr = Lambda xs b'
    (stmts, expr)
  emit options (T.Match [arg] cases) = do
    let (stmts1, arg') = emit options arg
    let (stmts2, cases') = emit options cases
    let x = C.newName (concatMap stmtNames $ stmts1 ++ stmts2) "_match"
    let stmt = Match arg' (cases' x)
    let expr = Name x
    (stmts1 ++ stmts2 ++ [stmt], expr)
  -- If Expr Expr Expr
  -- Or Expr Expr
  -- Ann Expr Expr
  -- Op1 C.UnaryOp Expr
  emit options (T.Op op args) = case (op, args) of
    ("+", [a, b]) -> emitBinOp Add a b
    ("-", [a, b]) -> emitBinOp Sub a b
    ("*", [a, b]) -> emitBinOp Mult a b
    ("^", [a, b]) -> emitBinOp Pow a b
    _ -> error $ "TODO: emit Op " ++ show (T.Op op args)
    where
      emitBinOp :: BinOp -> T.Expr -> T.Expr -> ([Stmt], Expr)
      emitBinOp op a b = do
        let (stmts1, a') = emit options a
        let (stmts2, b') = emit options b
        (stmts1 ++ stmts2, BinOp a' op b')
  emit options (T.Meta _ a) = emit options a
  -- Err
  emit options expr = error $ "TODO: emit " ++ show (T.dropMeta expr)

instance Emit [T.Expr] ([Stmt], [Expr]) where
  emit :: BuildOptions -> [T.Expr] -> ([Stmt], [Expr])
  emit options items = do
    let items' :: [(String, Expr)]
        (stmts, items') = emit options (map ("",) items)
    (stmts, map snd items')

instance Emit [(String, T.Expr)] ([Stmt], [(String, Expr)]) where
  emit :: BuildOptions -> [(String, T.Expr)] -> ([Stmt], [(String, Expr)])
  emit _ [] = ([], [])
  emit options ((x, a) : args) = do
    let (stmts1, a') = emit options a
    let (stmts2, args') = emit options args
    (stmts1 ++ stmts2, (x, a') : args')

instance Emit T.Case ([Stmt], String -> (Pattern, Maybe Expr, [Stmt])) where
  emit :: BuildOptions -> T.Case -> ([Stmt], String -> (Pattern, Maybe Expr, [Stmt]))
  emit options (T.Case [p] guard b) = do
    let (stmts, p') = emit options p
    let (body, b') = emit options b
    case guard of
      Just cond -> do
        error $ "TODO: emit [p] " ++ show (T.Case [p] guard b)
      Nothing -> do
        let case' x = (p', Nothing, body ++ [Assign [Name x] b'])
        (stmts, case')
  emit options (T.Case ps guard b) = error $ "TODO: emit ps " ++ show (T.Case ps guard b)

instance Emit [T.Case] ([Stmt], String -> [(Pattern, Maybe Expr, [Stmt])]) where
  emit :: BuildOptions -> [T.Case] -> ([Stmt], String -> [(Pattern, Maybe Expr, [Stmt])])
  emit _ [] = ([], const [])
  emit options (case_ : cases) = do
    let (stmts1, case') = emit options case_
    let (stmts2, cases') = emit options cases
    (stmts1 ++ stmts2, \x -> case' x : cases' x)

instance Emit T.Pattern ([Stmt], Pattern) where
  emit :: BuildOptions -> T.Pattern -> ([Stmt], Pattern)
  emit _ T.PAny = ([], MatchValue (Name "_"))
  emit _ (T.PInt i) = ([], MatchValue (Integer i))
  -- -- PNum Double
  emit _ (T.PVar x) = ([], MatchValue (Name x))
  -- -- PType [String]
  -- -- PTuple [Pattern]
  -- -- PRecord [(String, Pattern)]
  -- -- PTag String [Pattern]
  -- -- PFun Pattern Pattern
  -- -- POr [Pattern]
  -- -- PEq Expr
  emit options (T.PMeta _ p) = emit options p
  -- -- PErr
  emit options p = error $ "TODO: emit " ++ show p

--- Pretty printing layouts ---
pretty :: BuildOptions -> PP.Layout -> String
pretty options = PP.pretty options.maxLineLength options.indent

class Layout a where
  layout :: a -> PP.Layout

instance Layout Module where
  layout :: Module -> PP.Layout
  layout Module {body} = layout body

instance Layout [Stmt] where
  layout :: [Stmt] -> PP.Layout
  layout stmts = PP.join [PP.Text "\n"] (map layout stmts)

instance Layout Stmt where
  layout :: Stmt -> PP.Layout
  layout (Assign xs y) = case xs of
    [] -> layout y
    x : xs -> layout x ++ (PP.Text " = " : layout (Assign xs y))
  layout (AnnAssign a t maybeValue) = case maybeValue of
    Just b -> layout a ++ (PP.Text ": " : layout t) ++ (PP.Text " = " : layout b)
    Nothing -> layout a ++ (PP.Text ": " : layout t)
  layout (Import name alias) = case alias of
    Just alias -> [PP.Text $ "import " ++ name ++ " as " ++ alias]
    Nothing -> [PP.Text $ "import " ++ name]
  layout (ImportFrom name exposed) = do
    let layoutExpose (name, Nothing) = name
        layoutExpose (name, Just alias) = name ++ " as " ++ alias
    [PP.Text $ "from " ++ name ++ " import " ++ intercalate ", " (map layoutExpose exposed)]
  layout If {test, body, orelse = []} = do
    PP.Text "if "
      : layout test
      ++ [PP.Text ":", PP.Indent (PP.Text "\n" : layout body)]
  layout If {test, body, orelse} = do
    layout If {test = test, body = body, orelse = []}
      ++ [PP.Text "\nelse:", PP.Indent (PP.Text "\n" : layout orelse)]
  layout def@FunctionDef {} = do
    let body = if null def.body then [Pass] else def.body
    PP.Text ("def " ++ def.name)
      : layoutCollection "(" "," ")" (map layout def.args)
      ++ maybe [] (\t -> PP.Text " -> " : layout t) def.returns
      ++ [PP.Text ":", PP.Indent (PP.Text "\n" : layout body)]
  layout def@ClassDef {} = do
    let body = if null def.body then [Pass] else def.body
    PP.Text ("class " ++ def.name)
      : case def.bases of
        [] -> []
        bases -> layoutCollection "(" "," ")" (map layout bases)
      ++ [PP.Text ":", PP.Indent (PP.Text "\n" : layout body)]
  layout (Return expr) =
    [ PP.Text "return ",
      PP.Or
        (layout expr)
        [ PP.Text "(",
          PP.Indent (PP.Text "\n" : layout expr),
          PP.Text "\n)"
        ]
    ]
  layout (Match arg cases) = do
    let layoutArg (Tuple [arg]) = layout arg
        layoutArg arg = layout arg
    let layoutCase' (pat, guard, body) =
          PP.Text "case "
            : layout pat
            ++ maybe [] (\e -> PP.Text " if " : layout e) guard
            ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layout body), PP.Text "\n"]
    let layoutCase (MatchSequence [pat], guard, body) = layoutCase' (pat, guard, body)
        layoutCase (pat, guard, body) = layoutCase' (pat, guard, body)
    PP.Text "match "
      : layoutArg arg
      ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutCase cases)]
  layout (Raise exc from) =
    PP.Text "raise "
      : layout exc
      ++ maybe [] (\a -> PP.Text " from " : layout a) from
  layout Pass = [PP.Text "pass"]
  layout stmt = error $ "TODO: layout: " ++ show stmt

instance Layout Pattern where
  layout :: Pattern -> PP.Layout
  layout (MatchValue expr) = layout expr
  layout (MatchSequence pats) = layoutCollection "[" "," "]" (map layout pats)
  layout (MatchStar name) = [PP.Text $ "*" ++ name]
  -- MatchMapping [(String, Pattern)] (Maybe String) -- case {p: q, [, **kvs]}
  -- MatchClass String [Pattern] [(String, Pattern)] -- ClassName(p, x=q)
  layout (MatchAs maybePattern name) = case maybePattern of
    Just pat -> layout pat ++ [PP.Text $ " as " ++ name]
    Nothing -> [PP.Text name]
  layout (MatchOr pats) = PP.join [PP.Text " | "] (map layout pats)
  layout (MatchMeta _ pat) = layout pat
  layout pat = error $ "TODO: layout: " ++ show pat

instance Layout Expr where
  layout :: Expr -> PP.Layout
  layout (Integer i) = [PP.Text $ show i]
  layout (String s) = case s of
    s | '\'' `notElem` s -> [PP.Text $ "'" ++ s ++ "'"]
    s | '"' `notElem` s -> [PP.Text $ "\"" ++ s ++ "\""]
    s -> error $ "TODO: layout String with quotes: " ++ show s
  layout (Name x) = [PP.Text x]
  layout (Tuple items) = layoutCollection "(" "," ")" (map layout items)
  layout (Dict items) = do
    let layoutField (a, b) = layout a ++ PP.Text ": " : layout b
    layoutCollection "{" "," "}" (map layoutField items)
  layout (Call func args kwargs) = do
    let kwarg (x, a) = PP.Text (x ++ "=") : layout a
    layout func ++ layoutCollection "(" "," ")" (map layout args ++ map kwarg kwargs)
  layout (Lambda [] a) = PP.Text "lambda: " : layout a
  layout (Lambda xs a) =
    PP.Text "lambda "
      : PP.join [PP.Text ", "] (map (\x -> [PP.Text x]) xs)
      ++ (PP.Text ": " : layout a)
  layout (Attribute a x) = layout a ++ [PP.Text $ '.' : x]
  layout (Subscript a b) = layout a ++ PP.Text "[" : layout b ++ [PP.Text "]"]
  -- TODO: remove redundant parentheses
  -- TODO: break long lines
  layout (BinOp a op b) = do
    let showOp Add = " + "
        showOp Sub = " - "
        showOp Mult = " * "
        showOp Div = " / "
        showOp FloorDiv = " // "
        showOp Mod = " % "
        showOp Pow = "**"
        showOp LShift = " << "
        showOp RShift = " >> "
        showOp BitOr = " | "
        showOp BitXor = " ^ "
        showOp BitAnd = " & "
        showOp MatMult = " @ "
    PP.Text "(" : layout a ++ [PP.Text $ showOp op] ++ layout b ++ [PP.Text ")"]
  layout (Compare a op b) = do
    let showOp Eq = " == "
        showOp NotEq = " != "
        showOp Lt = " < "
        showOp LtE = " <= "
        showOp Gt = " > "
        showOp GtE = " >= "
        showOp Is = " is "
        showOp IsNot = " is not "
        showOp In = " in "
        showOp NotIn = " not in "
    PP.Text "(" : layout a ++ [PP.Text $ showOp op] ++ layout b ++ [PP.Text ")"]
  layout (Meta _ a) = layout a
  layout a = error $ "TODO: layout: " ++ show a

instance Layout (String, Maybe Expr, Maybe Expr) where
  layout :: (String, Maybe Expr, Maybe Expr) -> PP.Layout
  layout (x, Nothing, Nothing) = [PP.Text x]
  layout (x, Nothing, Just value) = PP.Text (x ++ "=") : layout value
  layout (x, Just type', Nothing) = PP.Text (x ++ ": ") : layout type'
  layout (x, Just type', Just value) = PP.Text (x ++ ": ") : layout type' ++ (PP.Text " = " : layout value)

layoutCollection :: String -> String -> String -> [PP.Layout] -> PP.Layout
layoutCollection open _ close [] = [PP.Text open, PP.Text close]
layoutCollection open delim close items =
  [ PP.Text open,
    PP.Or
      (PP.join [PP.Text $ delim ++ " "] items)
      [PP.Indent (PP.Text "\n" : PP.join [PP.Text ",\n"] items), PP.Text ",\n"],
    PP.Text close
  ]
