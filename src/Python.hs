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
import System.FilePath (joinPath, splitFileName, splitPath, takeDirectory, (</>))
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
data BuildOptions = BuildOptions
  { version :: (Int, Int),
    srcPath :: FilePath,
    testPath :: FilePath,
    docsPath :: FilePath,
    testingFramework :: TestingFramework,
    maxLineLength :: Int,
    indent :: String
  }
  deriving (Eq, Show)

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

newName :: PyCtx -> (String, PyCtx)
newName ctx = do
  case ('_' : show ctx.nameIndex, ctx {nameIndex = ctx.nameIndex + 1}) of
    (name, ctx') | name `elem` ctxNames ctx -> newName ctx'
    (name, ctx') -> (name, ctx')

build :: BuildOptions -> FilePath -> Package -> IO FilePath
build options base pkg = do
  let pkgPath = base </> "python"
  let srcPath = pkgPath </> pkg.name
  let testPath = pkgPath </> options.testPath
  let docsPath = pkgPath </> options.docsPath

  -- Initialize build path
  pkgPathExists <- doesPathExist pkgPath
  when pkgPathExists (removeDirectoryRecursive pkgPath)
  createDirectoryIfMissing True pkgPath

  -- Create source files
  files <- mapM (buildModule options srcPath) pkg.modules

  createDirectory testPath
  writeFile (testPath </> "__init__.py") ""
  files <- mapM (buildTests options pkg.name testPath) pkg.modules

  -- TODO: Create docs
  createDirectory docsPath

  -- TODO: create pyproject.toml
  -- TODO: create README.md
  -- TODO: create LICENSE

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

buildModule :: BuildOptions -> FilePath -> Module -> IO FilePath
buildModule options base mod = do
  -- Initialize the file path recursively.
  let filename = joinPath mod.path </> mod.name ++ ".py"
  buildDir base (splitPath $ takeDirectory filename)

  -- Write the source file contents.
  let layout = layoutModule (emitModule options mod)
  writeFile (base </> filename) (pyPretty options layout)
  return filename

buildTests :: BuildOptions -> String -> FilePath -> Module -> IO FilePath
buildTests options pkg base mod = do
  -- Initialize the file path recursively.
  let filename = joinPath mod.path </> "test_" ++ mod.name ++ ".py"
  buildDir base (splitPath $ takeDirectory filename)

  -- Write the test file contents.
  let layout = layoutModule (emitModuleTests options pkg mod)
  writeFile (base </> filename) (pyPretty options layout)
  return filename

emitModule :: BuildOptions -> Module -> PyModule
emitModule options mod = do
  let ctx0 = PyCtx {globals = [], locals = [], nameIndex = 0}
  let ctx = foldr (emitStmt options) ctx0 mod.stmts
  PyModule {name = mod.name, body = ctx.globals ++ ctx.locals}

emitModuleTests :: BuildOptions -> String -> Module -> PyModule
emitModuleTests options pkg mod = do
  let names = map fst (concatMap stmtDefs mod.stmts)
  let importFramework = case options.testingFramework of
        UnitTest -> [PyImport "unittest" Nothing]
        PyTest -> error "TODO: emitTests PyTest"
  let importPath = intercalate "." (pkg : mod.path ++ [mod.name])
  let importModule = [PyImportFrom importPath (map (,Nothing) names)]
  let imports = importFramework ++ importModule
  -- TODO: include imports from the Module itself
  let ctx0 = PyCtx {globals = imports, locals = [], nameIndex = 0}
  let ctx1 = foldr (emitTest options) ctx0 mod.stmts
  let testClass =
        PyClassDef
          { name = "Test" ++ mod.name,
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

emitStmt :: BuildOptions -> Stmt -> PyCtx -> PyCtx
emitStmt options stmt ctx = case stmt of
  Import {} -> emitImport options stmt ctx
  Def {} -> emitDef options stmt ctx
  Test {} -> ctx
  MetaStmt _ stmt -> emitStmt options stmt ctx

emitImport :: BuildOptions -> Stmt -> PyCtx -> PyCtx
emitImport options (Import path name alias exposed) ctx = case exposed of
  [] | name == alias -> addGlobal (PyImport name Nothing) ctx
  [] -> addGlobal (PyImport name (Just alias)) ctx
  exposed -> do
    let pyExpose (name, alias) | name == alias = (name, Nothing)
        pyExpose (name, alias) = (name, Just alias)
    ctx
      & emitStmt options (Import path name alias [])
      & addGlobal (PyImportFrom name (map pyExpose exposed))
emitImport _ _ ctx = ctx

emitDef :: BuildOptions -> Stmt -> PyCtx -> PyCtx
emitDef options (Def (DefName ts x args a)) ctx = do
  let (ctx', a') = emitExpr options ctx a
  let type' = fromMaybe Any (lookup x ts)
  case (asFun type', args) of
    (([], Any), []) -> ctx' {locals = PyAssign [PyName x] a' : ctx.locals}
-- Def (DefName String Expr)
-- Def (DefUnpack String [(String, Expr)])
-- Def (DefTrait (Expr, Expr) String)
emitDef _ _ ctx = ctx

emitTest :: BuildOptions -> Stmt -> PyCtx -> PyCtx
emitTest options (Test a b) ctx = do
  let (ctx', (a', b')) = emitExpr2 options ctx (a, b)
  let assertEqual x y =
        pyCall (PyAttribute (PyName "self") "assertEqual") [x, y]
  let testDef =
        PyFunctionDef
          { name = "test",
            args = [("self", Nothing, Nothing)],
            body = [PyAssign [] (assertEqual a' b')],
            decorators = [],
            returns = Nothing,
            typeParams = [],
            async = False
          }
  addLocal testDef ctx
emitTest _ _ ctx = ctx

emitExpr :: BuildOptions -> PyCtx -> Expr -> (PyCtx, PyExpr)
emitExpr _ ctx Any = (ctx, PyName "_")
emitExpr _ ctx IntType = (ctx, PyName "int")
emitExpr _ ctx NumType = (ctx, PyName "float")
emitExpr _ ctx (Int i) = (ctx, PyInteger i)
emitExpr _ ctx (Num n) = (ctx, PyFloat n)
emitExpr _ ctx (Var x) = (ctx, PyName x)
emitExpr options ctx (Tag k args) = do
  let (ctx', args') = emitExprAll options ctx args
  (ctx', pyCall (PyName k) args')
emitExpr options ctx (Tuple items) = do
  let (ctx', items') = emitExprAll options ctx items
  (ctx', PyTuple items')
-- emitExpr options ctx (Record [(String, Expr)]) = _
-- emitExpr options ctx (Trait Expr String) = _
-- emitExpr options ctx ListNil = _
-- emitExpr options ctx ListCons = _
-- emitExpr options ctx TextNil = _
-- emitExpr options ctx TextCons = _
-- emitExpr options ctx (Type alts) = _
-- emitExpr options ctx (Fun Expr Expr) = _
-- emitExpr options ctx (App Expr Expr) = _
-- emitExpr options ctx (Let (Expr, Expr) Expr) = _
-- emitExpr options ctx (Bind (Expr, Expr) Expr) = _
-- emitExpr options ctx (TypeDef String [Expr] Expr) = _
-- emitExpr options ctx (MatchFun [Expr]) = _
-- emitExpr options ctx (Match [Expr] [Expr]) = _
-- emitExpr options ctx (Or Expr Expr) = _
-- emitExpr options ctx (Ann Expr Expr) = _
-- emitExpr options ctx (Op1 C.UnaryOp Expr) = _
emitExpr options ctx (Op2 op a b) = do
  let (ctx', (a', b')) = emitExpr2 options ctx (a, b)
  case op of
    C.Add -> (ctx', PyBinOp a' PyAdd b')
    C.Sub -> (ctx', PyBinOp a' PySub b')
    C.Mul -> (ctx', PyBinOp a' PyMult b')
    C.Pow -> (ctx', PyBinOp a' PyPow b')
    C.Eq -> (ctx', PyCompare a' PyEq b')
    C.Lt -> (ctx', PyCompare a' PyLt b')
    C.Gt -> (ctx', PyCompare a' PyGt b')
emitExpr options ctx (Meta m a) = do
  let (ctx', a') = emitExpr options ctx a
  (ctx', PyMeta m a')
-- emitExpr ctx Err = _
emitExpr _ ctx expr = error $ "TODO: emitExpr " ++ show expr

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

-- rename :: [String] -> String -> String
-- rename existing name =

--- Pretty printing layouts ---
pyPretty :: BuildOptions -> PP.Layout -> String
pyPretty options = PP.pretty options.maxLineLength options.indent

layoutModule :: PyModule -> PP.Layout
layoutModule PyModule {body = []} = []
layoutModule PyModule {body = stmt : stmts} = layoutBlock stmt stmts

layoutBlock :: PyStmt -> [PyStmt] -> PP.Layout
layoutBlock a [] = layoutStmt a
layoutBlock a (b : stmts) | isImport a && isImport b = layoutStmt a ++ layoutBlock b stmts
layoutBlock a (b : stmts) | isImport a = layoutStmt a ++ PP.Text "\n" : layoutBlock b stmts
layoutBlock a (b : stmts) | isImport b = layoutStmt a ++ PP.Text "\n" : layoutBlock b stmts
layoutBlock a (b : stmts) = layoutStmt a ++ layoutBlock b stmts

isImport :: PyStmt -> Bool
isImport PyImport {} = True
isImport PyImportFrom {} = True
isImport _ = False

layoutStmt :: PyStmt -> PP.Layout
layoutStmt (PyAssign [] y) = layoutExpr y
layoutStmt (PyAssign (x : xs) y) = layoutExpr x ++ (PP.Text " = " : layoutStmt (PyAssign xs y))
layoutStmt (PyImport name alias) = case alias of
  Just alias -> [PP.Text $ "import " ++ name ++ " as " ++ alias ++ "\n"]
  Nothing -> [PP.Text $ "import " ++ name ++ "\n"]
layoutStmt (PyImportFrom name exposed) = do
  let layoutExpose (name, Nothing) = name
      layoutExpose (name, Just alias) = name ++ " as " ++ alias
  [PP.Text $ "from " ++ name ++ " import " ++ intercalate ", " (map layoutExpose exposed) ++ "\n"]
layoutStmt PyIf {test, body, orelse = []} = do
  PP.Text "if "
    : layoutExpr test
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutStmt body), PP.Text "\n"]
layoutStmt PyIf {test, body, orelse} = do
  layoutStmt PyIf {test = test, body = body, orelse = []}
    ++ [PP.Text "else:", PP.Indent (PP.Text "\n" : concatMap layoutStmt orelse), PP.Text "\n"]
layoutStmt def@PyFunctionDef {} = do
  let body = if null def.body then [PyPass] else def.body
  PP.Text ("def " ++ def.name)
    : layoutTuple (map layoutFunctionArg def.args)
    ++ maybe [] (\t -> PP.Text " -> " : layoutExpr t) def.returns
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutStmt body), PP.Text "\n"]
layoutStmt def@PyClassDef {} = do
  let body = if null def.body then [PyPass] else def.body
  PP.Text ("class " ++ def.name)
    : case def.bases of
      [] -> []
      bases -> layoutTuple (map layoutExpr bases)
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutStmt body), PP.Text "\n"]
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
    ++ [PP.Text "\n"]
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
