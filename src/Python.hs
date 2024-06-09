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
import Tao

-- TODO: abstract into an `Imperative` language
-- https://en.wikipedia.org/wiki/Imperative_programming

-- https://docs.python.org/3/library/ast.html
-- https://docs.python.org/3/reference/grammar.html

-- https://docs.python.org/3/library/ast.html#ast.Module
data PyModule = PyModule
  { name :: String,
    body :: [PyStmt]
  }
  deriving (Eq, Show)

newModule :: String -> [PyStmt] -> PyModule
newModule name body =
  PyModule
    { name = name,
      body = body
    }

--- Expressions ---
-- https://docs.python.org/3/library/ast.html#expressions
data PyExpr
  = PyNone -- PyNone
  | PyBool Bool -- True
  | PyInteger Int -- 42
  | PyFloat Double -- 3.14
  | PyImaginary Double -- 3.14j
  | PyList [PyExpr] -- [x, y, z]
  | PyTuple [PyExpr] -- (x, y, z)
  | PySet [PyExpr] -- {x, y, z}
  | PyDict [(PyExpr, PyExpr)] -- {x: 1, y: 2, z: 3}
  | PyBytes String -- b'hello'
  | PyString String -- 'Hello'
  | PyFString [PyFormattedValue] -- f"hello {x}"
  | PyName String -- x
  | PyStarred PyExpr -- _, *x = _
  | PyUnaryOp PyUnaryOp PyExpr -- not x
  | PyBinOp PyExpr PyBinOp PyExpr -- x + y
  | PyBoolOp PyExpr PyBoolOp PyExpr -- x and y
  | PyCompare PyExpr PyCompare PyExpr -- x == y
  | PyLambda [String] PyExpr -- lambda x, y: z
  | PyCall PyExpr [PyExpr] [(String, PyExpr)] -- func(*args, **kwargs)
  | PyIfExp PyExpr PyExpr PyExpr -- a if b else c
  | PyAttribute PyExpr String -- x.y
  | PyNamedExpr PyExpr PyExpr -- x := y
  | PySubscript PyExpr PyExpr -- x[y]
  | PySlice PyExpr PyExpr -- x:y
  | PyListComp PyExpr PyExpr PyExpr [PyExpr] -- [x for x in xs (if y)*]
  | PySetComp PyExpr PyExpr PyExpr [PyExpr] -- {x for x in xs (if y)*}
  | PyGeneratorExp PyExpr PyExpr PyExpr [PyExpr] -- (x for x in xs (if y)*)
  | PyDictComp PyExpr PyExpr PyExpr [PyExpr] -- {x: x for x in xs (if y)*}
  | PyMeta C.Metadata PyExpr
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.FormattedValue
data PyFormattedValue
  = PyStr String
  | PyVal PyExpr
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.UnaryOp
data PyUnaryOp
  = PyUAdd -- +x
  | PyUSub -- -x
  | PyNot -- not x
  | PyInvert -- ~x
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.BinOp
data PyBinOp
  = PyAdd -- x + y
  | PySub -- x - y
  | PyMult -- x * y
  | PyDiv -- x / y
  | PyFloorDiv -- x // y
  | PyMod -- x % y
  | PyPow -- x ** y
  | PyLShift -- x << y
  | PyRShift -- x >> y
  | PyBitOr -- x | y
  | PyBitXor -- x ^ y
  | PyBitAnd -- x & y
  | PyMatMult -- x @ y
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.BoolOp
data PyBoolOp
  = PyAnd -- x and y
  | PyOr -- x or y
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.Compare
data PyCompare
  = PyEq -- x == y
  | PyNotEq -- x = y
  | PyLt -- x < y
  | PyLtE -- x <= y
  | PyGt -- x > y
  | PyGtE -- x >= y
  | PyIs -- x is y
  | PyIsNot -- x is not y
  | PyIn -- x in y
  | PyNotIn -- x not in y
  deriving (Eq, Show)

--- Statements ---
-- https://docs.python.org/3/library/ast.html#statements
data PyStmt
  = PyAssign [PyExpr] PyExpr -- x = y = z
  | PyAnnAssign PyExpr PyExpr (Maybe PyExpr) -- x: T = y
  | PyAugAssign PyExpr PyBinOp PyExpr -- x += y
  | PyRaise PyExpr (Maybe PyExpr) -- raise x [from y]
  | PyAssert PyExpr PyExpr -- assert x, y
  | PyDelete [PyExpr] -- del x, y
  | PyPass -- pass
  | PyTypeAlias String [PyTypeParam] PyExpr -- type Alias = int
  | PyImport String (Maybe String) -- import mod [as m]
  | PyImportFrom String [(String, Maybe String)] -- from mod import x, y as z
  | PyBreak -- break
  | PyContinue -- continue
  | PyMatch PyExpr [(PyPattern, Maybe PyExpr, [PyStmt])] -- match x: case p: y; ...
  | PyReturn PyExpr -- return x
  | PyYield PyExpr -- yield x
  | PyYieldFrom PyExpr -- yield from x
  | PyGlobal [String] -- global x
  | PyNonlocal [String] -- nonlocal x
  | PyAwait PyExpr -- await x
  | PyIf
      { test :: PyExpr,
        body :: [PyStmt],
        orelse :: [PyStmt]
      }
  | PyFor
      { target :: PyExpr,
        iter :: PyExpr,
        body :: [PyStmt],
        orelse :: [PyStmt],
        async :: Bool
      }
  | PyWhile
      { test :: PyExpr,
        body :: [PyStmt],
        orelse :: [PyStmt]
      }
  | PyWith
      { items :: [(PyExpr, Maybe PyExpr)],
        body :: [PyStmt],
        async :: Bool
      }
  | PyFunctionDef
      { name :: String,
        args :: [(String, Maybe PyExpr, Maybe PyExpr)],
        body :: [PyStmt],
        decorators :: [PyExpr],
        returns :: Maybe PyExpr,
        typeParams :: [PyTypeParam],
        async :: Bool
      }
  | PyClassDef
      { name :: String,
        bases :: [PyExpr],
        body :: [PyStmt],
        decorators :: [PyExpr],
        typeParams :: [PyTypeParam]
      }
  | PyTry
      { body :: [PyStmt],
        handlers :: [(Maybe PyExpr, String, PyExpr)],
        else' :: [PyStmt],
        finally :: [PyStmt]
      }
  deriving (Eq, Show)

newPyFunctionDef :: String -> [(String, Maybe PyExpr, Maybe PyExpr)] -> [PyStmt] -> PyStmt
newPyFunctionDef name args body =
  PyFunctionDef
    { name = name,
      args = args,
      body = body,
      decorators = [],
      returns = Nothing,
      typeParams = [],
      async = False
    }

newPyClassDef :: String -> [PyTypeParam] -> [PyStmt] -> PyStmt
newPyClassDef name args body =
  PyClassDef
    { name = name,
      bases = [],
      body = body,
      decorators = [],
      typeParams = args
    }

--- Pattern Matching ---
-- https://docs.python.org/3/library/ast.html#pattern-matching
data PyPattern
  = PyMatchValue PyExpr -- case 1
  | PyMatchSequence [PyPattern] -- case [p, q]
  | PyMatchStar String -- case [p, *ps]
  | PyMatchMapping [(String, PyPattern)] (Maybe String) -- case {p: q, [, **kvs]}
  | PyMatchClass String [PyPattern] [(String, PyPattern)] -- ClassName(p, x=q)
  | PyMatchAs (Maybe PyPattern) String -- case p as x
  | PyMatchOr [PyPattern] -- case p | q
  | PyMatchMeta C.Metadata PyPattern
  deriving (Eq, Show)

--- Type parameters ---
-- https://docs.python.org/3/library/ast.html#ast-type-params
data PyTypeParam
  = PyTypeVar String -- T[a]
  | PyTypeVarTuple String -- T[*ts]
  | PyParamSpec String -- T[**ts]
  deriving (Eq, Show)

data BuildOptions = BuildOptions
  { version :: (Int, Int),
    packageName :: String,
    testPath :: FilePath,
    docsPath :: FilePath,
    testingFramework :: TestingFramework,
    maxLineLength :: Int,
    indent :: String
  }
  deriving (Eq, Show)

-- Taken from help("keywords") in Python 3.12 REPL
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

pyCall :: PyExpr -> [PyExpr] -> PyExpr
pyCall f xs = PyCall f xs []

pyImport :: String -> PyStmt
pyImport name = PyImport name Nothing

pyRaise :: PyExpr -> PyStmt
pyRaise x = PyRaise x Nothing

--- Build target ---
defaultBuildOptions :: BuildOptions
defaultBuildOptions =
  BuildOptions
    { version = (3, 12),
      packageName = "",
      testingFramework = UnitTest,
      testPath = "test",
      docsPath = "docs",
      maxLineLength = 79,
      indent = "    "
    }

data TestingFramework
  = UnitTest
  | PyTest
  deriving (Eq, Show)

stmtNames :: PyStmt -> [String]
stmtNames (PyAssign [] _) = []
stmtNames (PyAssign (var : vars) value) = case var of
  PyName x -> x : stmtNames (PyAssign vars value)
  _ -> stmtNames (PyAssign vars value)
stmtNames (PyAnnAssign var _ _) = case var of
  PyName x -> [x]
  _ -> []
stmtNames (PyTypeAlias x _ _) = [x]
stmtNames (PyImport name maybeAlias) = case maybeAlias of
  Just alias -> [alias]
  Nothing -> [name]
stmtNames (PyImportFrom _ exposed) = do
  let exposedNames (_, Just alias) = [alias]
      exposedNames (name, Nothing) = [name]
  concatMap exposedNames exposed
stmtNames (PyGlobal names) = names
stmtNames (PyNonlocal names) = names
stmtNames (PyFunctionDef {name}) = [name]
stmtNames (PyClassDef {name}) = [name]
stmtNames _ = []

pyName :: [String] -> Expr -> String -> String
pyName existing a name
  | isTagDef a = nameCamelCaseUpper name
  | isTypeDef a = nameCamelCaseUpper name
  | otherwise = nameSnakeCase name

build :: BuildOptions -> FilePath -> Package -> IO FilePath
build options base pkg = do
  let pyPkg =
        refactorName pyName pkg
          & refactorModuleName (replace '/' '.' . replace '-' '_')
          & refactorModuleAlias nameSnakeCase

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

buildModule :: BuildOptions -> String -> FilePath -> Module -> IO FilePath
buildModule options pkgName base mod = do
  -- Initialize the file path recursively.
  let filename = replace '.' '/' mod.name ++ ".py"
  buildDir base (splitPath $ takeDirectory filename)

  -- Write the source file contents.
  let mod' = mod {stmts = filter (not . isTest) mod.stmts}
  let options' = options {packageName = pkgName}
  writeFile (base </> filename) $
    (emit options' mod' :: PyModule)
      & layout
      & pyPretty options'
  return filename

buildTests :: BuildOptions -> String -> FilePath -> Module -> IO FilePath
buildTests options pkgName base mod = do
  -- Initialize the file path recursively.
  let (dir, name) = splitFileName (replace '.' '/' mod.name)
  let filename = dir </> "test_" ++ name ++ ".py"
  buildDir base (splitPath $ takeDirectory filename)

  -- Write the test file contents.
  let options' = options {packageName = pkgName}
  writeFile (base </> filename) $
    buildModuleTests options' mod
      & layout
      & pyPretty options'
  return filename

buildModuleTests :: BuildOptions -> Module -> PyModule
buildModuleTests options mod = do
  let importFramework = case options.testingFramework of
        UnitTest -> PyImport "unittest" Nothing
        PyTest -> error "TODO: emitTests PyTest"
  let path = splitDirectories mod.name & filter (/= ".")
  let importPath = intercalate "." (options.packageName : path)
  let importDefs = case map fst (concatMap (stmtDefs options.packageName) mod.stmts) of
        [] -> [importFramework]
        names -> do
          let importModule = PyImportFrom importPath (map (,Nothing) names)
          [importFramework, importModule]
  let imports = emit options (filter isImport mod.stmts)
  let testClass =
        PyClassDef
          { name = "Test" ++ nameCamelCaseUpper (takeFileName mod.name),
            bases = [PyAttribute (PyName "unittest") "TestCase"],
            body = emit options (filter isTest mod.stmts),
            decorators = [],
            typeParams = []
          }
  let entrypoint =
        PyIf
          { test = PyCompare (PyName "__name__") PyEq (PyString "__main__"),
            body = [PyAssign [] (pyCall (PyAttribute (PyName "unittest") "main") [])],
            orelse = []
          }
  let stmts =
        (importFramework : importDefs ++ imports)
          ++ [testClass]
          ++ [entrypoint]
  PyModule {name = "test_" ++ mod.name, body = stmts}

isImport :: Stmt -> Bool
isImport Import {} = True
isImport _ = False

isTest :: Stmt -> Bool
isTest Test {} = True
isTest _ = False

isDefine :: Stmt -> Bool
isDefine Define {} = True
isDefine _ = False

-- TODO: rename to Emit
class Emit a b where
  emit :: BuildOptions -> a -> b

instance Emit Module PyModule where
  emit :: BuildOptions -> Module -> PyModule
  emit options mod = do
    let stmts = emit options (filter (not . isTest) mod.stmts)
    PyModule {name = mod.name, body = stmts}

instance Emit [Stmt] [PyStmt] where
  emit :: BuildOptions -> [Stmt] -> [PyStmt]
  emit _ [] = []
  emit options (stmt : stmts) = do
    emit options stmt ++ emit options stmts

instance Emit Stmt [PyStmt] where
  emit :: BuildOptions -> Stmt -> [PyStmt]
  emit options (Import pkg path alias exposed) = do
    let pkg' = if pkg == "" then options.packageName else pkg
    case exposed of
      [] -> do
        let alias' = if path == alias then Nothing else Just alias
        [PyImport (pkg' ++ "." ++ path) alias']
      exposed -> do
        let expose (name, alias) | name == alias = (name, Nothing)
            expose (name, alias) = (name, Just alias)
        let stmts = emit options (Import pkg' path alias [])
        stmts ++ [PyImportFrom (pkg' ++ "." ++ path) (map expose exposed)]
  emit options (Define def) = emit options def
  emit options (Test a p) = do
    let (stmts1, a') = emit options a
    let (stmts2, b') = emit options (toExpr p) -- TODO: do a match instead
    let def =
          PyFunctionDef
            { name = "test_" ++ nameSnakeCase (show (dropMeta a)),
              args = [("self", Nothing, Nothing)],
              body = [PyAssign [] (pyCall (PyAttribute (PyName "self") "assertEqual") [a', b'])],
              decorators = [],
              returns = Nothing,
              typeParams = [],
              async = False
            }
    stmts1 ++ stmts2 ++ [def]
  emit options stmt = error $ "TODO: emit " ++ show stmt

instance Emit Definition [PyStmt] where
  emit :: BuildOptions -> Definition -> [PyStmt]
  emit options (Def ts (PVar x) b) = case (lookup x ts, asLambda "_" b) of
    (Nothing, ([], b)) -> do
      let (stmts, b') = emit options b
      let def = PyAssign [PyName x] b'
      stmts ++ [def]
    (Just t, ([], b)) -> do
      let (stmts1, t') = emit options t
      let (stmts2, b') = emit options b
      let def = PyAnnAssign (PyName x) t' (Just b')
      stmts1 ++ stmts2 ++ [def]
    (Nothing, (xs, b)) -> do
      let (body, b') = emit options b
      let def =
            PyFunctionDef
              { name = x,
                args = map (,Nothing,Nothing) xs,
                body = body ++ [PyReturn b'],
                decorators = [],
                returns = Nothing,
                typeParams = [],
                async = False
              }
      [def]
    (Just t, (xs, b)) -> do
      let emitArg :: (String, Expr) -> ([PyStmt], [(String, Maybe PyExpr, Maybe PyExpr)]) -> ([PyStmt], [(String, Maybe PyExpr, Maybe PyExpr)])
          emitArg (x, t) (stmts, args) = do
            let (stmts', t') = emit options t
            (stmts' ++ stmts, (x, Just t', Nothing) : args)
      let (ts, ret) = asFun t
      let (stmts1, args) = foldr emitArg ([], []) (zip xs ts)
      let (stmts2, ret') = emit options ret
      let (body, b') = emit options b
      let def =
            PyFunctionDef
              { name = x,
                args = args,
                body = body ++ [PyReturn b'],
                decorators = [],
                returns = Just ret',
                typeParams = [],
                async = False
              }
      stmts1 ++ stmts2 ++ [def]
  emit options (Def ts (PMeta _ p) b) = emit options (Define (Def ts p b))
  emit options def = error $ "TODO: emit " ++ show def

instance Emit Expr ([PyStmt], PyExpr) where
  emit :: BuildOptions -> Expr -> ([PyStmt], PyExpr)
  emit _ (Int i) = ([], PyInteger i)
  emit _ (Num n) = ([], PyFloat n)
  emit _ (Var x) = ([], PyName x)
  -- Type [String]
  emit options (Tag k args) = case (k, args) of
    ("Int", []) -> ([], PyName "int")
    ("True", []) -> ([], PyName "True")
    ("False", []) -> ([], PyName "False")
    ("Nothing", []) -> ([], PyName "None")
    (k, args) -> do
      let (stmts, args') = emit options args
      (stmts, pyCall (PyName k) args')
  -- Tuple [Expr]
  -- Record [(String, Expr)]
  emit options (Trait a x) = do
    let (stmts, a') = emit options a
    (stmts, PyAttribute a' x)
  -- Fun Expr Expr
  emit options (App a b) = do
    let (f, args) = asApp (App a b)
    let (stmts1, f') = emit options f
    let (stmts2, args') = emit options args
    (stmts1 ++ stmts2, pyCall f' args')
  -- Let Definition Expr
  -- Bind (Expr, Expr) Expr
  emit options (Match [] cases) = do
    let (xs, b) = asLambda "_arg" (Match [] cases)
    let (stmts, b') = emit options b
    let expr = PyLambda xs b'
    (stmts, expr)
  emit options (Match [arg] cases) = do
    let (stmts1, arg') = emit options arg
    let (stmts2, cases') = emit options cases
    let x = C.newName (concatMap stmtNames $ stmts1 ++ stmts2) "_match"
    let stmt = PyMatch arg' (cases' x)
    let expr = PyName x
    (stmts1 ++ stmts2 ++ [stmt], expr)
  -- -- If Expr Expr Expr
  -- -- Or Expr Expr
  -- -- Ann Expr Expr
  -- -- Op1 C.UnaryOp Expr
  emit options (Op2 op a b) = do
    let (stmts1, a') = emit options a
    let (stmts2, b') = emit options b
    (stmts1 ++ stmts2, PyBinOp a' (emit options op) b')
  emit options (Meta _ a) = emit options a
  -- -- Err
  emit options expr = error $ "TODO: emit " ++ show (dropMeta expr)

instance Emit C.BinaryOp PyBinOp where
  emit :: BuildOptions -> C.BinaryOp -> PyBinOp
  emit _ C.Add = PyAdd
  emit _ C.Sub = PySub
  emit _ C.Mul = PyMult
  emit _ C.Pow = PyPow
  emit _ op = error $ "TODO: emit " ++ show op

instance Emit [Expr] ([PyStmt], [PyExpr]) where
  emit :: BuildOptions -> [Expr] -> ([PyStmt], [PyExpr])
  emit _ [] = ([], [])
  emit options (a : bs) = do
    let (stmts1, a') = emit options a
    let (stmts2, bs') = emit options bs
    (stmts1 ++ stmts2, a' : bs')

instance Emit Case ([PyStmt], String -> (PyPattern, Maybe PyExpr, [PyStmt])) where
  emit :: BuildOptions -> Case -> ([PyStmt], String -> (PyPattern, Maybe PyExpr, [PyStmt]))
  emit options (Case [p] guard b) = do
    let (stmts, p') = emit options p
    let (body, b') = emit options b
    case guard of
      Just cond -> do
        error $ "TODO: emit [p] " ++ show (Case [p] guard b)
      Nothing -> do
        let case' x = (p', Nothing, body ++ [PyAssign [PyName x] b'])
        (stmts, case')
  emit options (Case ps guard b) = error $ "TODO: emit ps " ++ show (Case ps guard b)

instance Emit [Case] ([PyStmt], String -> [(PyPattern, Maybe PyExpr, [PyStmt])]) where
  emit :: BuildOptions -> [Case] -> ([PyStmt], String -> [(PyPattern, Maybe PyExpr, [PyStmt])])
  emit _ [] = ([], const [])
  emit options (case_ : cases) = do
    let (stmts1, case') = emit options case_
    let (stmts2, cases') = emit options cases
    (stmts1 ++ stmts2, \x -> case' x : cases' x)

instance Emit Pattern ([PyStmt], PyPattern) where
  emit :: BuildOptions -> Pattern -> ([PyStmt], PyPattern)
  emit _ PAny = ([], PyMatchValue (PyName "_"))
  emit _ (PInt i) = ([], PyMatchValue (PyInteger i))
  -- -- PNum Double
  emit _ (PVar x) = ([], PyMatchValue (PyName x))
  -- -- PType [String]
  -- -- PTuple [Pattern]
  -- -- PRecord [(String, Pattern)]
  -- -- PTag String [Pattern]
  -- -- PFun Pattern Pattern
  -- -- POr [Pattern]
  -- -- PEq Expr
  emit options (PMeta _ p) = emit options p
  -- -- PErr
  emit options p = error $ "TODO: emit " ++ show p

--- Pretty printing layouts ---
pyPretty :: BuildOptions -> PP.Layout -> String
pyPretty options = PP.pretty options.maxLineLength options.indent

class Layout a where
  layout :: a -> PP.Layout

instance Layout PyModule where
  layout :: PyModule -> PP.Layout
  layout PyModule {body} = layout body

instance Layout [PyStmt] where
  layout :: [PyStmt] -> PP.Layout
  layout stmts = PP.join [PP.Text "\n"] (map layout stmts)

instance Layout PyStmt where
  layout :: PyStmt -> PP.Layout
  layout (PyAssign xs y) = case xs of
    [] -> layout y
    x : xs -> layout x ++ (PP.Text " = " : layout (PyAssign xs y))
  layout (PyAnnAssign a t maybeValue) = case maybeValue of
    Just b -> layout a ++ (PP.Text ": " : layout t) ++ (PP.Text " = " : layout b)
    Nothing -> layout a ++ (PP.Text ": " : layout t)
  layout (PyImport name alias) = case alias of
    Just alias -> [PP.Text $ "import " ++ name ++ " as " ++ alias]
    Nothing -> [PP.Text $ "import " ++ name]
  layout (PyImportFrom name exposed) = do
    let layoutExpose (name, Nothing) = name
        layoutExpose (name, Just alias) = name ++ " as " ++ alias
    [PP.Text $ "from " ++ name ++ " import " ++ intercalate ", " (map layoutExpose exposed)]
  layout PyIf {test, body, orelse = []} = do
    PP.Text "if "
      : layout test
      ++ [PP.Text ":", PP.Indent (PP.Text "\n" : layout body)]
  layout PyIf {test, body, orelse} = do
    layout PyIf {test = test, body = body, orelse = []}
      ++ [PP.Text "\nelse:", PP.Indent (PP.Text "\n" : layout orelse)]
  layout def@PyFunctionDef {} = do
    let body = if null def.body then [PyPass] else def.body
    PP.Text ("def " ++ def.name)
      : layoutCollection "(" "," ")" (map layout def.args)
      ++ maybe [] (\t -> PP.Text " -> " : layout t) def.returns
      ++ [PP.Text ":", PP.Indent (PP.Text "\n" : layout body)]
  layout def@PyClassDef {} = do
    let body = if null def.body then [PyPass] else def.body
    PP.Text ("class " ++ def.name)
      : case def.bases of
        [] -> []
        bases -> layoutCollection "(" "," ")" (map layout bases)
      ++ [PP.Text ":", PP.Indent (PP.Text "\n" : layout body)]
  layout (PyReturn expr) =
    [ PP.Text "return ",
      PP.Or
        (layout expr)
        [ PP.Text "(",
          PP.Indent (PP.Text "\n" : layout expr),
          PP.Text "\n)"
        ]
    ]
  layout (PyMatch arg cases) = do
    let layoutArg (PyTuple [arg]) = layout arg
        layoutArg arg = layout arg
    let layoutCase' (pat, guard, body) =
          PP.Text "case "
            : layout pat
            ++ maybe [] (\e -> PP.Text " if " : layout e) guard
            ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layout body), PP.Text "\n"]
    let layoutCase (PyMatchSequence [pat], guard, body) = layoutCase' (pat, guard, body)
        layoutCase (pat, guard, body) = layoutCase' (pat, guard, body)
    PP.Text "match "
      : layoutArg arg
      ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutCase cases)]
  layout (PyRaise exc from) =
    PP.Text "raise "
      : layout exc
      ++ maybe [] (\a -> PP.Text " from " : layout a) from
  layout PyPass = [PP.Text "pass"]
  layout stmt = error $ "TODO: layout: " ++ show stmt

instance Layout PyPattern where
  layout :: PyPattern -> PP.Layout
  layout (PyMatchValue expr) = layout expr
  layout (PyMatchSequence pats) = layoutCollection "[" "," "]" (map layout pats)
  layout (PyMatchStar name) = [PP.Text $ "*" ++ name]
  -- MatchMapping [(String, Pattern)] (Maybe String) -- case {p: q, [, **kvs]}
  -- MatchClass String [Pattern] [(String, Pattern)] -- ClassName(p, x=q)
  layout (PyMatchAs maybePattern name) = case maybePattern of
    Just pat -> layout pat ++ [PP.Text $ " as " ++ name]
    Nothing -> [PP.Text name]
  layout (PyMatchOr pats) = PP.join [PP.Text " | "] (map layout pats)
  layout (PyMatchMeta _ pat) = layout pat
  layout pat = error $ "TODO: layout: " ++ show pat

instance Layout PyExpr where
  layout :: PyExpr -> PP.Layout
  layout (PyInteger i) = [PP.Text $ show i]
  layout (PyString s) = case s of
    s | '\'' `notElem` s -> [PP.Text $ "'" ++ s ++ "'"]
    s | '"' `notElem` s -> [PP.Text $ "\"" ++ s ++ "\""]
    s -> error $ "TODO: layout PyString with quotes: " ++ show s
  layout (PyName x) = [PP.Text x]
  layout (PyTuple items) = layoutCollection "(" "," ")" (map layout items)
  layout (PyCall func args kwargs) = do
    let kwarg (x, a) = PP.Text (x ++ "=") : layout a
    layout func ++ layoutCollection "(" "," ")" (map layout args ++ map kwarg kwargs)
  layout (PyLambda [] a) = PP.Text "lambda: " : layout a
  layout (PyLambda xs a) =
    PP.Text "lambda "
      : PP.join [PP.Text ", "] (map (\x -> [PP.Text x]) xs)
      ++ (PP.Text ": " : layout a)
  layout (PyAttribute a x) = layout a ++ [PP.Text $ '.' : x]
  -- TODO: remove redundant parentheses
  -- TODO: break long lines
  layout (PyBinOp a op b) = do
    let showOp PyAdd = " + "
        showOp PySub = " - "
        showOp PyMult = " * "
        showOp PyDiv = " / "
        showOp PyFloorDiv = " // "
        showOp PyMod = " % "
        showOp PyPow = "**"
        showOp PyLShift = " << "
        showOp PyRShift = " >> "
        showOp PyBitOr = " | "
        showOp PyBitXor = " ^ "
        showOp PyBitAnd = " & "
        showOp PyMatMult = " @ "
    PP.Text "(" : layout a ++ [PP.Text $ showOp op] ++ layout b ++ [PP.Text ")"]
  layout (PyCompare a op b) = do
    let showOp PyEq = " == "
        showOp PyNotEq = " != "
        showOp PyLt = " < "
        showOp PyLtE = " <= "
        showOp PyGt = " > "
        showOp PyGtE = " >= "
        showOp PyIs = " is "
        showOp PyIsNot = " is not "
        showOp PyIn = " in "
        showOp PyNotIn = " not in "
    PP.Text "(" : layout a ++ [PP.Text $ showOp op] ++ layout b ++ [PP.Text ")"]
  layout (PyMeta _ a) = layout a
  layout a = error $ "TODO: layout: " ++ show a

instance Layout (String, Maybe PyExpr, Maybe PyExpr) where
  layout :: (String, Maybe PyExpr, Maybe PyExpr) -> PP.Layout
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
