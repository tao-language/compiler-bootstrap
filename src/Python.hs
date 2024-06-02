{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}
module Python where

import Control.Monad (unless, when)
import qualified Core as C
import Data.Bifunctor (Bifunctor (first))
import Data.Foldable (foldlM, foldrM)
import Data.Function ((&))
import Data.List (intercalate, union)
import Data.Maybe (fromMaybe)
import qualified Debug.Trace as Debug
import PrettyPrint (Layout)
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

data PyCtx = PyCtx
  { globals :: [PyStmt],
    locals :: [PyStmt],
    nameIndex :: Int
  }
  deriving (Eq, Show)

addGlobal :: PyStmt -> PyCtx -> PyCtx
addGlobal stmt ctx = ctx {globals = ctx.globals ++ [stmt]}

addLocal :: PyStmt -> PyCtx -> PyCtx
addLocal stmt ctx = ctx {locals = ctx.locals ++ [stmt]}

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

ctxNames :: PyCtx -> [String]
ctxNames ctx = concatMap stmtNames (ctx.globals ++ ctx.locals)

newName :: PyCtx -> String -> (PyCtx, String)
newName ctx prefix = do
  case (ctx {nameIndex = ctx.nameIndex + 1}, prefix ++ show ctx.nameIndex) of
    (ctx', name) | name `elem` ctxNames ctx -> newName ctx' prefix
    (ctx', name) -> (ctx', name)

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
  -- let layout = layoutModule (emitModule options pkgName mod)
  -- writeFile (base </> filename) (pyPretty options layout)
  let mod' = mod {stmts = filter (not . isTest) mod.stmts}
  writeFile (base </> filename) (codegen options mod')
  return filename

isTest :: Stmt -> Bool
isTest (Test _ _) = True
isTest _ = False

isDefine :: Stmt -> Bool
isDefine (Define _) = True
isDefine _ = False

-- TODO: rename to Emit
class Codegen a where
  codegen :: BuildOptions -> a -> String

instance Codegen Module where
  codegen :: BuildOptions -> Module -> String
  codegen options module' = do
    intercalate "\n" (map (codegen options) module'.stmts)

instance Codegen Stmt where
  codegen :: BuildOptions -> Stmt -> String
  codegen options (Import pkg path alias exposed) = case exposed of
    [] | path == alias -> do
      template
        "import {{module}}"
        [("module", pkg ++ "." ++ path)]
    exposed -> do
      let codegenExposed (name, alias) | name == alias = name
          codegenExposed (name, alias) = name ++ " as " ++ alias
      template
        "from {{module}} import ({{names}})"
        [ ("module", pkg ++ "." ++ path),
          ("names", intercalate ", " (map codegenExposed exposed))
        ]
  codegen options (Define def) = codegen options def
  codegen options stmt = error $ "TODO: codegen " ++ show stmt

instance Codegen Definition where
  codegen :: BuildOptions -> Definition -> String
  codegen options (Def ts (PVar x) b) = case (lookup x ts, asLambda "_" b) of
    (Nothing, ([], b)) -> do
      template
        "{{name}} = {{value}}"
        [ ("name", x),
          ("value", codegen options b)
        ]
    (Just t, ([], b)) -> do
      template
        "{{name}}: {{type}} = {{value}}"
        [ ("name", x),
          ("type", codegen options t),
          ("value", codegen options b)
        ]
    (Nothing, (xs, b)) -> do
      template
        "def {{name}}({{args}}):\n\
        \    return {{body}}"
        [ ("name", x),
          ("args", intercalate ", " xs),
          ("body", codegen options b)
        ]
    (Just t, (xs, b)) -> do
      let (ts, ret) = asFun t
      let args = zipWith (\x t -> x ++ ": " ++ codegen options t) xs ts
      template
        "def {{name}}({{args}}) -> {{ret}}:\n\
        \    return {{body}}"
        [ ("name", x),
          ("args", intercalate ", " args),
          ("ret", codegen options ret),
          ("body", codegen options b)
        ]
  codegen options (Def ts (PMeta _ p) b) = codegen options (Define (Def ts p b))
  codegen options def = do
    error $ "TODO: codegen " ++ show def

instance Codegen Expr where
  codegen :: BuildOptions -> Expr -> String
  codegen _ (Int i) = show i
  codegen _ (Var x) = x
  codegen _ (Tag k args) = case (k, args) of
    ("Int", []) -> "int"
    (k, args) -> k
  codegen options (Op2 op a b) = do
    let a' = codegen options a
    let b' = codegen options b
    case op of
      C.Add -> "(" ++ a' ++ " + " ++ b' ++ ")"
  codegen options (Meta _ a) = codegen options a
  codegen options expr = error $ "TODO: codegen " ++ show expr

template :: String -> [(String, String)] -> String
template text [] = text
template text ((x, value) : vars) =
  template (replaceString ("{{" ++ x ++ "}}") value text) vars

buildTests :: BuildOptions -> String -> FilePath -> Module -> IO FilePath
buildTests options pkg base mod = do
  -- Initialize the file path recursively.
  let (dir, name) = splitFileName (replace '.' '/' mod.name)
  let filename = dir </> "test_" ++ name ++ ".py"
  buildDir base (splitPath $ takeDirectory filename)

  -- Write the test file contents.
  let layout = layoutModule (emitModuleTests options pkg mod)
  writeFile (base </> filename) (pyPretty options layout)
  return filename

emitModule :: BuildOptions -> String -> Module -> PyModule
emitModule options pkgName mod = do
  let ctx0 = PyCtx {globals = [], locals = [], nameIndex = 0}
  let ctx = foldr (emitStmt options pkgName) ctx0 (filter (not . isTest) mod.stmts)
  PyModule {name = mod.name, body = ctx.globals ++ ctx.locals}

emitModuleTests :: BuildOptions -> String -> Module -> PyModule
emitModuleTests options pkgName mod = do
  let importFramework = case options.testingFramework of
        UnitTest -> PyImport "unittest" Nothing
        PyTest -> error "TODO: emitTests PyTest"
  let path = splitDirectories mod.name & filter (/= ".")
  let importPath = intercalate "." (pkgName : path)
  let imports = case map fst (concatMap (stmtDefs pkgName) mod.stmts) of
        [] -> [importFramework]
        names -> do
          let importModule = PyImportFrom importPath (map (,Nothing) names)
          [importFramework, importModule]
  -- TODO: include imports from the Module itself
  let ctx0 = PyCtx {globals = imports, locals = [], nameIndex = 0}
  let ctx1 = foldr (emitTest options pkgName) ctx0 mod.stmts
  let testClass =
        PyClassDef
          { name = "Test" ++ nameCamelCaseUpper (takeFileName mod.name),
            bases = [PyAttribute (PyName "unittest") "TestCase"],
            body = ctx1.locals,
            decorators = [],
            typeParams = []
          }
  let entrypoint =
        PyIf
          { test = PyCompare (PyName "__name__") PyEq (PyString "__main__"),
            body = [PyAssign [] (pyCall (PyAttribute (PyName "unittest") "main") [])],
            orelse = []
          }
  let ctx = ctx1 & addGlobal testClass & addGlobal entrypoint
  PyModule {name = "test_" ++ mod.name, body = ctx.globals}

emitStmt :: BuildOptions -> String -> Stmt -> PyCtx -> PyCtx
emitStmt options pkgName stmt ctx = case stmt of
  Import {} -> emitImport options pkgName stmt ctx
  Define {} -> emitDef options stmt ctx
  Test {} -> ctx
  MetaStmt _ stmt -> emitStmt options pkgName stmt ctx

emitImport :: BuildOptions -> String -> Stmt -> PyCtx -> PyCtx
emitImport options pkgName (Import "" name alias exposed) ctx =
  emitImport options pkgName (Import pkgName name alias exposed) ctx
emitImport options _ (Import pkg name alias exposed) ctx = case exposed of
  [] | name == alias -> addGlobal (PyImport (pkg ++ "." ++ name) Nothing) ctx
  [] -> addGlobal (PyImport (pkg ++ "." ++ name) (Just alias)) ctx
  exposed -> do
    let pyExpose (name, alias) | name == alias = (name, Nothing)
        pyExpose (name, alias) = (name, Just alias)
    ctx
      & emitStmt options pkg (Import pkg name alias [])
      & addGlobal (PyImportFrom (pkg ++ "." ++ name) (map pyExpose exposed))
emitImport _ _ _ ctx = ctx

emitArgs :: [String] -> [PyExpr] -> [(String, Maybe PyExpr, Maybe PyExpr)]
emitArgs [] _ = []
emitArgs (x : xs) [] = (x, Nothing, Nothing) : emitArgs xs []
emitArgs (x : xs) (t : ts) = (x, Just t, Nothing) : emitArgs xs ts

emitDef :: BuildOptions -> Stmt -> PyCtx -> PyCtx
emitDef options (Define def) ctx0 = case def of
  Def ts (PVar x) value -> case (fmap asFun (lookup x ts), asLambda "_" value) of
    (Just ([], t), ([], value)) -> do
      -- Typed variable definition
      let (ctx1, value') = emitExpr options ctx0 value
      let (ctx2, t') = emitExpr options ctx1 t
      let def = PyAnnAssign (PyName x) t' (Just value')
      ctx2 {locals = def : ctx2.locals}
    (Nothing, ([], value)) -> do
      -- Untyped variable definition
      let (ctx1, value') = emitExpr options ctx0 value
      let def = PyAssign [PyName x] value'
      ctx1 {locals = def : ctx1.locals}
    (Just (ts, t), (xs, value)) -> do
      -- Typed function definition
      let (ctx1, ts') = emitExprAll options ctx0 ts
      let (ctx2, t') = emitExpr options ctx1 t
      let (ctx3, value') = emitExpr options ctx2 value
      let def =
            PyFunctionDef
              { name = x,
                args = emitArgs xs ts',
                body = [PyReturn value'],
                decorators = [],
                returns = Just t',
                typeParams = [],
                async = False
              }
      ctx3 {locals = def : ctx3.locals}
    (Nothing, (xs, value)) -> do
      -- Untyped function definition
      let (ctx1, value') = emitExpr options ctx0 value
      let def =
            PyFunctionDef
              { name = x,
                args = emitArgs xs [],
                body = [PyReturn value'],
                decorators = [],
                returns = Nothing,
                typeParams = [],
                async = False
              }
      ctx1 {locals = def : ctx1.locals}
  Def ts (PMeta _ p) value -> emitDef options (Define (Def ts p value)) ctx0
  -- Def ts p a -> case p of
  --   PAny -> ctx0
  --   PInt _ -> ctx0
  --   PNum _ -> ctx0
  --   PVar x -> error "TODO: variable"
  --   PType _ -> ctx0
  --   PTag k ps -> error "TODO: unpack"
  --   PFun p q -> error "TODO: special case for Tag"
  --   POr ps -> error "TODO: multiple definitions ?"
  --   PEq a -> error "TODO: compile time error"
  --   PMeta _ p -> emitDef options (Define (Def ts p a)) ctx0
  --   PErr -> error "TODO: runtime error ?"
  Def ts p a -> error $ "TODO: emitDef " ++ show (Def ts p a)

emitTest :: BuildOptions -> String -> Stmt -> PyCtx -> PyCtx
emitTest options pkgName stmt ctx0 = case stmt of
  Import {} -> emitImport options pkgName stmt ctx0
  Test a b -> do
    let (ctx1, (a', b')) = emitExpr2 options ctx0 (a, toExpr b)
    let assertEqual x y =
          pyCall (PyAttribute (PyName "self") "assertEqual") [x, y]
    let testDef =
          PyFunctionDef
            { name = "test_" ++ nameSnakeCase (show (dropMeta a)),
              args = [("self", Nothing, Nothing)],
              body = [PyAssign [] (assertEqual a' b')],
              decorators = [],
              returns = Nothing,
              typeParams = [],
              async = False
            }
    addLocal testDef ctx1
  _ -> ctx0

emitExpr :: BuildOptions -> PyCtx -> Expr -> (PyCtx, PyExpr)
emitExpr _ ctx0 (Int i) = (ctx0, PyInteger i)
emitExpr _ ctx0 (Num n) = (ctx0, PyFloat n)
emitExpr _ ctx0 (Var x) = (ctx0, PyName x)
emitExpr _ ctx0 (Tag "Int" []) = (ctx0, PyName "int")
emitExpr _ ctx0 (Tag "Num" []) = (ctx0, PyName "float")
emitExpr options ctx0 (Tag k args) = do
  let (ctx1, args') = emitExprAll options ctx0 args
  (ctx1, pyCall (PyName k) args')
emitExpr options ctx0 (Tuple items) = do
  let (ctx1, items') = emitExprAll options ctx0 items
  (ctx1, PyTuple items')
-- emitExpr options ctx0 (Record [(String, Expr)]) = _
emitExpr options ctx0 (Trait a x) = do
  let (ctx1, a') = emitExpr options ctx0 a
  (ctx1, PyAttribute a' x)
-- emitExpr options ctx0 (Type alts) = _
emitExpr options ctx0 (Fun a b) = do
  let (ctx1, (a', b')) = emitExpr2 options ctx0 (a, b)
  error $ "TODO: emitExpr " ++ show (Fun a b)
emitExpr options ctx0 (App a b) = do
  let (fn, args) = asApp (App a b)
  let (ctx1, fn') = emitExpr options ctx0 fn
  let (ctx2, args') = emitExprAll options ctx1 args
  (ctx2, pyCall fn' args')
-- emitExpr options ctx0 (Let (Expr, Expr) Expr) = _
-- emitExpr options ctx0 (Bind (Expr, Expr) Expr) = _
-- emitExpr options ctx0 (TypeDef String [Expr] Expr) = _
emitExpr options ctx0 (Match cases) = do
  let (xs, a) = asLambda "_" (Match cases)
  let (ctx1, a') = emitExpr options ctx0 a
  (ctx1, PyLambda xs a')
-- let (x, ctx1) = newName ctx0
-- let (ctx2, arg') = emitExpr options ctx1 arg
-- let cases = []
-- let ctx3 = addLocal (PyMatch arg' cases) ctx2
-- (ctx3, PyName x)
-- emitExpr options ctx0 (Or Expr Expr) = _
-- emitExpr options ctx0 (Ann Expr Expr) = _
-- emitExpr options ctx0 (Op1 C.UnaryOp Expr) = _
emitExpr options ctx0 (Op2 op a b) = do
  let (ctx1, (a', b')) = emitExpr2 options ctx0 (a, b)
  case op of
    C.Add -> (ctx1, PyBinOp a' PyAdd b')
    C.Sub -> (ctx1, PyBinOp a' PySub b')
    C.Mul -> (ctx1, PyBinOp a' PyMult b')
    C.Pow -> (ctx1, PyBinOp a' PyPow b')
    C.Eq -> (ctx1, PyCompare a' PyEq b')
    C.Lt -> (ctx1, PyCompare a' PyLt b')
    C.Gt -> (ctx1, PyCompare a' PyGt b')
emitExpr options ctx0 (Meta m a) = do
  let (ctx1, a') = emitExpr options ctx0 a
  (ctx1, PyMeta m a')
emitExpr _ ctx0 Err = (ctx0, pyCall (PyName "RuntimeError") [])
emitExpr _ _ expr = error $ "TODO: emitExpr " ++ show expr

emitExpr2 :: BuildOptions -> PyCtx -> (Expr, Expr) -> (PyCtx, (PyExpr, PyExpr))
emitExpr2 options ctx (a, b) = do
  let (ctx1, a') = emitExpr options ctx a
  let (ctx2, b') = emitExpr options ctx1 b
  (ctx2, (a', b'))

emitExprAll :: BuildOptions -> PyCtx -> [Expr] -> (PyCtx, [PyExpr])
emitExprAll options ctx [] = (ctx, [])
emitExprAll options ctx (a : bs) = do
  let (ctx1, a') = emitExpr options ctx a
  let (ctx2, bs') = emitExprAll options ctx1 bs
  (ctx2, a' : bs')

--- Pretty printing layouts ---
pyPretty :: BuildOptions -> PP.Layout -> String
pyPretty options = PP.pretty options.maxLineLength options.indent

layoutModule :: PyModule -> PP.Layout
layoutModule PyModule {body} = layoutBlock body

layoutBlock :: [PyStmt] -> PP.Layout
layoutBlock stmts = PP.join [PP.Text "\n"] (map layoutStmt stmts)

layoutStmt :: PyStmt -> PP.Layout
layoutStmt (PyAssign xs y) = case xs of
  [] -> layoutExpr y
  x : xs -> layoutExpr x ++ (PP.Text " = " : layoutStmt (PyAssign xs y))
layoutStmt (PyAnnAssign a t maybeValue) = case maybeValue of
  Just b -> layoutExpr a ++ (PP.Text ": " : layoutExpr t) ++ (PP.Text " = " : layoutExpr b)
  Nothing -> layoutExpr a ++ (PP.Text ": " : layoutExpr t)
layoutStmt (PyImport name alias) = case alias of
  Just alias -> [PP.Text $ "import " ++ name ++ " as " ++ alias]
  Nothing -> [PP.Text $ "import " ++ name]
layoutStmt (PyImportFrom name exposed) = do
  let layoutExpose (name, Nothing) = name
      layoutExpose (name, Just alias) = name ++ " as " ++ alias
  [PP.Text $ "from " ++ name ++ " import " ++ intercalate ", " (map layoutExpose exposed)]
layoutStmt PyIf {test, body, orelse = []} = do
  PP.Text "if "
    : layoutExpr test
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : layoutBlock body)]
layoutStmt PyIf {test, body, orelse} = do
  layoutStmt PyIf {test = test, body = body, orelse = []}
    ++ [PP.Text "\nelse:", PP.Indent (PP.Text "\n" : layoutBlock orelse)]
layoutStmt def@PyFunctionDef {} = do
  let body = if null def.body then [PyPass] else def.body
  PP.Text ("def " ++ def.name)
    : layoutTuple (map layoutFunctionArg def.args)
    ++ maybe [] (\t -> PP.Text " -> " : layoutExpr t) def.returns
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : layoutBlock body)]
layoutStmt def@PyClassDef {} = do
  let body = if null def.body then [PyPass] else def.body
  PP.Text ("class " ++ def.name)
    : case def.bases of
      [] -> []
      bases -> layoutTuple (map layoutExpr bases)
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : layoutBlock body)]
layoutStmt (PyReturn expr) =
  [ PP.Text "return ",
    PP.Or
      (layoutExpr expr)
      [ PP.Text "(",
        PP.Indent (PP.Text "\n" : layoutExpr expr),
        PP.Text "\n)"
      ]
  ]
layoutStmt (PyMatch arg cases) = do
  let layoutArg (PyTuple [arg]) = layoutExpr arg
      layoutArg arg = layoutExpr arg
  let layoutCase' (pat, guard, body) =
        PP.Text "case "
          : layoutPattern pat
          ++ maybe [] (\e -> PP.Text " if " : layoutExpr e) guard
          ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutStmt body), PP.Text "\n"]
  let layoutCase (PyMatchSequence [pat], guard, body) = layoutCase' (pat, guard, body)
      layoutCase (pat, guard, body) = layoutCase' (pat, guard, body)
  PP.Text "match "
    : layoutArg arg
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutCase cases)]
layoutStmt (PyRaise exc from) =
  PP.Text "raise "
    : layoutExpr exc
    ++ maybe [] (\a -> PP.Text " from " : layoutExpr a) from
layoutStmt PyPass = [PP.Text "pass"]
layoutStmt stmt = error $ "TODO: layoutStmt: " ++ show stmt

-- layoutDocString :: DocString -> PP.Layout
-- layoutDocString docs = do
--   [PP.Text ("'''" ++ docs.description ++ "\n"), PP.Text "'''\n"]

layoutExample :: (PyExpr, PyExpr) -> PP.Layout
layoutExample (prompt, result) =
  PP.Text ">>> "
    : layoutExpr prompt
    ++ [PP.Text "\n"]
    ++ layoutExpr result
    ++ [PP.Text "\n"]

layoutPattern :: PyPattern -> PP.Layout
layoutPattern (PyMatchValue expr) = layoutExpr expr
layoutPattern (PyMatchSequence pats) = layoutList (map layoutPattern pats)
layoutPattern (PyMatchStar name) = [PP.Text $ "*" ++ name]
-- MatchMapping [(String, Pattern)] (Maybe String) -- case {p: q, [, **kvs]}
-- MatchClass String [Pattern] [(String, Pattern)] -- ClassName(p, x=q)
layoutPattern (PyMatchAs maybePattern name) = case maybePattern of
  Just pat -> layoutPattern pat ++ [PP.Text $ " as " ++ name]
  Nothing -> [PP.Text name]
layoutPattern (PyMatchOr pats) = PP.join [PP.Text " | "] (map layoutPattern pats)
layoutPattern (PyMatchMeta _ pat) = layoutPattern pat
layoutPattern pat = error $ "TODO: layoutPattern: " ++ show pat

layoutExpr :: PyExpr -> PP.Layout
layoutExpr (PyInteger i) = [PP.Text $ show i]
layoutExpr (PyString s) = case s of
  s | '\'' `notElem` s -> [PP.Text $ "'" ++ s ++ "'"]
  s | '"' `notElem` s -> [PP.Text $ "\"" ++ s ++ "\""]
  s -> error $ "TODO: layoutExpr PyString with quotes: " ++ show s
layoutExpr (PyName x) = [PP.Text x]
layoutExpr (PyTuple items) = layoutTuple (map layoutExpr items)
layoutExpr (PyCall func args kwargs) = do
  let kwarg (x, a) = PP.Text (x ++ "=") : layoutExpr a
  layoutExpr func ++ layoutTuple (map layoutExpr args ++ map kwarg kwargs)
layoutExpr (PyLambda [] a) = PP.Text "lambda: " : layoutExpr a
layoutExpr (PyLambda xs a) =
  PP.Text "lambda "
    : PP.join [PP.Text ", "] (map (\x -> [PP.Text x]) xs)
    ++ (PP.Text ": " : layoutExpr a)
layoutExpr (PyAttribute a x) = layoutExpr a ++ [PP.Text $ '.' : x]
-- TODO: remove redundant parentheses
-- TODO: break long lines
layoutExpr (PyBinOp a op b) = do
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
  PP.Text "(" : layoutExpr a ++ [PP.Text $ showOp op] ++ layoutExpr b ++ [PP.Text ")"]
layoutExpr (PyCompare a op b) = do
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
  PP.Text "(" : layoutExpr a ++ [PP.Text $ showOp op] ++ layoutExpr b ++ [PP.Text ")"]
layoutExpr (PyMeta _ a) = layoutExpr a
layoutExpr a = error $ "TODO: layoutExpr: " ++ show a

layoutFunctionArg :: (String, Maybe PyExpr, Maybe PyExpr) -> PP.Layout
layoutFunctionArg (x, Nothing, Nothing) = [PP.Text x]
layoutFunctionArg (x, Nothing, Just value) = PP.Text (x ++ "=") : layoutExpr value
layoutFunctionArg (x, Just type', Nothing) = PP.Text (x ++ ": ") : layoutExpr type'
layoutFunctionArg (x, Just type', Just value) = PP.Text (x ++ ": ") : layoutExpr type' ++ (PP.Text " = " : layoutExpr value)

layoutTuple :: [PP.Layout] -> PP.Layout
layoutTuple = layoutCollection "(" "," ")"

layoutList :: [PP.Layout] -> PP.Layout
layoutList = layoutCollection "[" "," "]"

layoutCollection :: String -> String -> String -> [PP.Layout] -> PP.Layout
layoutCollection open _ close [] = [PP.Text open, PP.Text close]
layoutCollection open delim close items =
  [ PP.Text open,
    PP.Or
      (PP.join [PP.Text $ delim ++ " "] items)
      [PP.Indent (PP.Text "\n" : PP.join [PP.Text ",\n"] items), PP.Text ",\n"],
    PP.Text close
  ]
