module Python where

import Control.Monad (unless, when)
import qualified Core as C
import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable (foldlM, foldrM)
import Data.Function ((&))
import Data.List (intercalate, isSuffixOf, sortBy, union)
import Data.Maybe (fromMaybe)
import qualified Debug.Trace as Debug
import qualified PrettyPrint as PP
import Stdlib (replace)
import System.Directory (copyFile, createDirectory, createDirectoryIfMissing, doesPathExist, removeDirectoryRecursive)
import System.FilePath (joinPath, splitDirectories, splitFileName, splitPath, takeDirectory, takeFileName, (</>))
import qualified Tao as T
import qualified TaoParser as P
import Text.Read (readMaybe)

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
  deriving (Eq, Show)

--- Type parameters ---
-- https://docs.python.org/3/library/ast.html#ast-type-params
data TypeParam
  = TypeVar String -- T[a]
  | TypeVarTuple String -- T[*ts]
  | ParamSpec String -- T[**ts]
  deriving (Eq, Show)

data BuildOptions = BuildOptions
  { prefix :: String,
    testPath :: FilePath,
    docsPath :: FilePath,
    maxLineLength :: Int,
    indent :: String
  }
  deriving (Eq, Show)

defaultBuildOptions :: BuildOptions
defaultBuildOptions =
  BuildOptions
    { prefix = "",
      testPath = "test",
      docsPath = "docs",
      maxLineLength = 79,
      indent = "    "
    }

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

index :: Expr -> Expr -> Expr
index = Subscript

slice :: Expr -> Expr -> Expr -> Expr
slice expr start end = Subscript expr (Slice start end)

bitOr :: Expr -> Expr -> Expr
bitOr a = BinOp a BitOr

notImplementedError :: String -> Expr
notImplementedError msg = call "NotImplementedError" [String msg]

import' :: String -> Stmt
import' name = Import name Nothing

assign :: String -> Expr -> Stmt
assign name = Assign [Name name]

raise :: Expr -> Stmt
raise x = Raise x Nothing

--- Build target ---
build :: BuildOptions -> [FilePath] -> FilePath -> FilePath -> [FilePath] -> IO FilePath
build options bases prelude path dependencies = do
  (pkg, errs) <- P.load bases prelude path dependencies
  putStr (intercalate "" (map (\e -> "❌ " ++ show e ++ "\n") errs))
  let ctx = snd pkg
  mapM_ (buildModule options ctx . fst) ctx
  error $ "TODO: build"

buildModule :: BuildOptions -> T.Context -> FilePath -> IO FilePath
buildModule options ctx path = do
  let path' = path & replace '-' '_'
  stmts <- case lookup path ctx of
    Just stmts -> return stmts
    Nothing -> do
      putStrLn ("module not found: " ++ path)
      return []
  (concatMap (emit options) stmts :: [Stmt])
    & layout
    & pretty options
    & writeFile path'
  return path'

-- build :: BuildOptions -> FilePath -> T.Package -> IO FilePath
-- build options base (name, modules) = do
--   let pkgPath = base </> "python"
--   let srcPath = pkgPath </> T.nameSnakeCase name
--   let testPath = pkgPath </> options.testPath
--   let docsPath = pkgPath </> options.docsPath

--   -- Initialize build path
--   pkgPathExists <- doesPathExist pkgPath
--   when pkgPathExists (removeDirectoryRecursive pkgPath)
--   createDirectoryIfMissing True pkgPath

--   -- Create project files.
--   writeFile (pkgPath </> "pyproject.toml") ""
--   -- TODO: create README.md
--   -- TODO: create LICENSE

--   -- Create source files
--   let options' = options {prefix = name}
--   let modules' = sortBy (\m n -> compare (fst m) (fst n)) modules
--   files <- mapM (buildModule options' name srcPath) modules'
--   copyFile "src/target/python/__tao__.py" (srcPath </> "__prelude__.py")

--   createDirectory testPath
--   writeFile (testPath </> "__init__.py") ""
--   files <- mapM (buildTests options' name testPath) modules'

--   -- TODO: Create docs
--   createDirectory docsPath

--   return pkgPath

-- buildDir :: FilePath -> [FilePath] -> IO ()
-- buildDir base dirs = do
--   exists <- doesPathExist base
--   unless exists $ do
--     createDirectoryIfMissing True base
--     writeFile (base </> "__init__.py") ""
--   case dirs of
--     [] -> return ()
--     (dir : subdirs) -> buildDir (base </> dir) subdirs

-- buildModule :: BuildOptions -> String -> FilePath -> T.Module -> IO FilePath
-- buildModule options pkgName base (path, stmts) = do
--   -- Initialize the file path recursively.
--   let filename = replace '-' '_' path ++ ".py"
--   buildDir base (splitPath $ takeDirectory filename)

--   -- Write the source file contents.
--   -- let mod' = mod {T.stmts = filter (not . T.isTest) mod.stmts}
--   let stmts' = filter (not . T.isTest) stmts
--   -- writeFile (base </> filename) $
--   --   (emit options (path, stmts') :: Module)
--   --     & layout
--   --     & pretty options
--   return filename

-- buildTests :: BuildOptions -> String -> FilePath -> T.Module -> IO FilePath
-- buildTests options pkgName base (path, stmts) = do
--   -- Initialize the file path recursively.
--   let (dir, name) = splitFileName (replace '-' '_' path)
--   let filename = dir </> "test_" ++ name ++ ".py"
--   buildDir base (splitPath $ takeDirectory filename)

--   -- Write the test file contents.
--   let options' = options {prefix = options.prefix ++ '/' : path}
--   writeFile (base </> filename) $
--     buildModuleTests options' (path, stmts)
--       & layout
--       & pretty options'
--   return filename

-- buildModuleTests :: BuildOptions -> T.Module -> Module
-- buildModuleTests options (path, stmts) = do
--   let path' = splitDirectories path & filter (/= ".")
--   -- let exposed =
--   --       T.resolveNames options.prefix mod
--   --         & map (\(_, x) -> (T.nameIdentifier x & T.nameSnakeCase, Nothing))
--   let importPath =
--         options.prefix
--           & drop 1
--           & replace '-' '_'
--           & replace '/' '.'
--   let stmts' =
--         Import "unittest" Nothing
--           : [] -- [prelude options]
--           -- : case exposed of
--           --   [] -> []
--           --   _ -> [ImportFrom importPath exposed]
--           ++ emit options (filter T.isImport stmts)
--           ++ [ ClassDef
--                  { name = "Test" ++ T.nameCamelCaseUpper (takeFileName path),
--                    bases = [Attribute (Name "unittest") "TestCase"],
--                    body = emit options (filter T.isTest stmts),
--                    decorators = [],
--                    typeParams = []
--                  },
--                If
--                  { test = Compare (Name "__name__") Eq (String "__main__"),
--                    body = [Assign [] (Call (Attribute (Name "unittest") "main") [] [])],
--                    orelse = []
--                  }
--              ]
--   Module {name = "test_" ++ path, body = stmts'}

class Emit a b where
  emit :: BuildOptions -> a -> b

instance Emit T.Expr ([Stmt], Expr) where
  emit :: BuildOptions -> T.Expr -> ([Stmt], Expr)
  emit options = \case
    T.Any -> ([], None)
    T.Unit -> ([], Tuple [])
    T.IntT -> ([], Name "int")
    T.NumT -> ([], Name "float")
    T.Int i -> ([], Integer i)
    T.Num n -> ([], Float n)
    T.Tag "Bool" -> ([], Name "bool")
    T.Tag "True" -> ([], Bool True)
    T.Tag "False" -> ([], Bool False)
    T.Tag k -> ([], Tuple [String k])
    T.Var x -> ([], Name x)
    T.Ann a _ -> emit options a
    T.And (T.Tag k) b -> do
      let (s, args) = emit options (T.andOf b)
      (s, Tuple (String k : args))
    T.And a b -> do
      let (s, items) = emit options (T.andOf (T.And a b))
      (s, Tuple items)
    T.Or a b -> do
      let (s1, a') = emit options a
      let (s2, b') = emit options b
      (s1 ++ s2, bitOr a' b')
    T.For _ a -> emit options a
    -- emit options (T.Record fields) = do
    --   let (stmts, fields') = emit options fields
    --   (stmts, record fields')
    -- emit options (T.Trait a x) = do
    --   let (stmts, a') = emit options a
    --   case readMaybe x of
    --     Just i -> (stmts, index a' (Integer $ i - 1))
    --     Nothing -> (stmts, Attribute a' x)
    -- emit options (T.TraitFun x) = do
    --   let arg = "_"
    --   let (stmts, a) = emit options (T.Trait (T.Var arg) x)
    --   (stmts, Lambda [arg] a)
    -- emit options (T.Fun a b) = do
    --   let (args, ret) = T.funOf (T.Fun a b)
    --   let (stmts1, args') = emit options args
    --   let (stmts2, ret') = emit options ret
    --   (stmts1 ++ stmts2, callable args' ret')
    -- emit options expr@(T.App _ _) = case T.appOf expr of
    --   -- (T.Match cases, args) -> do
    --   --   let x = C.newName (T.freeVars cases) "_match"
    --   --   let (stmts1, args') = emit options args
    --   --   let (stmts2, cases') = emit options cases
    --   --   let stmt = Match (Tuple args') (cases' x)
    --   --   (stmts1 ++ stmts2 ++ [stmt], Name x)
    --   (f, args) -> do
    --     let (stmts1, f') = emit options f
    --     let (stmts2, args') = emit options args
    --     (stmts1 ++ stmts2, Call f' args' [])
    -- emit options (T.Let def b) = do
    --   let stmts1 = emit options def
    --   let (stmts2, b') = emit options b
    --   (stmts1 ++ stmts2, b')
    -- emit options (T.Bind (ts, p, a) b) = do
    --   -- let stmts1 = emit options (T.Def [] p (T.Meta C.Unwrap a))
    --   -- let (stmts2, b') = emit options b
    --   -- (stmts1 ++ stmts2, b')
    --   error $ show "TODO: emit Bind " ++ show (ts, p, a, b)
    -- emit _ (T.Match _ []) = ([raise (notImplementedError "")], None)
    -- emit options (T.Match [] cases) = do
    --   -- let x = C.newName (concatMap T.freeVars cases) "_match"
    --   -- let def = T.Def [] (T.PVar x) (T.Match cases)
    --   -- let stmts = emit options def
    --   -- (stmts, Name x)
    --   error $ show "TODO: emit MatchFun " ++ show cases
    -- If Expr Expr Expr
    -- Or Expr Expr
    -- emit options (T.Ann a _) = emit options a
    -- Op1 C.UnaryOp Expr
    -- emit options (T.Call op args) = case (op, args) of
    --   ("+", [a, b]) -> emitBinOp Add a b
    --   ("-", [a, b]) -> emitBinOp Sub a b
    --   ("*", [a, b]) -> emitBinOp Mult a b
    --   ("^", [a, b]) -> emitBinOp Pow a b
    --   _ -> error $ "TODO: emit Op " ++ show (T.Call op args)
    --   where
    --     emitBinOp :: BinOp -> T.Expr -> T.Expr -> ([Stmt], Expr)
    --     emitBinOp op a b = do
    --       let (stmts1, a') = emit options a
    --       let (stmts2, b') = emit options b
    --       (stmts1 ++ stmts2, BinOp a' op b')
    -- Err
    -- emit options = \expr -> error $ "TODO: emit " ++ show expr
    expr -> error $ "TODO: emit " ++ show expr

instance Emit [T.Expr] ([Stmt], [Expr]) where
  emit :: BuildOptions -> [T.Expr] -> ([Stmt], [Expr])
  emit options = \case
    [] -> ([], [])
    a : bs -> do
      let (s1, a') = emit options a
      let (s2, bs') = emit options bs
      (s1 ++ s2, a' : bs')

instance Emit T.Stmt [Stmt] where
  emit :: BuildOptions -> T.Stmt -> [Stmt]
  emit options = \case
    T.Import path alias names -> do
      let nameAlias (x, y)
            | x == y = (x, Nothing)
            | otherwise = (x, Just y)
      let path' = path & replace '/' '.' & replace '-' '_'
      let alias' = if path == alias || ('/' : alias) `isSuffixOf` path then Nothing else Just alias
      Import path' alias' : [ImportFrom path' (map nameAlias names) | names /= []]
    T.Def def -> emit options def
    -- T.Test pos name a p -> do
    --   let (stmts1, a') = emit options a
    --   let (stmts2, b') = emit options p -- TODO: do a match instead
    --   let def =
    --         FunctionDef
    --           { name = "test_" ++ T.nameSnakeCase (show a),
    --             args = [("self", Nothing, Nothing)],
    --             body = [Assign [] (Call (Attribute (Name "self") "assertEqual") [a', b'] [])],
    --             decorators = [],
    --             returns = Nothing,
    --             typeParams = [],
    --             async = False
    --           }
    --   stmts1 ++ stmts2 ++ [def]
    stmt -> error $ "TODO: emit " ++ show stmt

instance Emit (T.Pattern, T.Expr) [Stmt] where
  emit :: BuildOptions -> (T.Pattern, T.Expr) -> [Stmt]
  emit options = \case
    (p, a) -> error $ "TODO: emit " ++ show (p, a)

-- emit options (ts, T.PVar x, b) = case (lookup x ts, T.lambdaOf "_" b) of {}
--     (Nothing, ([], b)) -> do
--       let (stmts, b') = emit options b
--       let def = Assign [Name x] b'
--       stmts ++ [def]
--     (Just t, ([], b)) -> do
--       let (stmts1, t') = emit options t
--       let (stmts2, b') = emit options b
--       let def = AnnAssign (Name x) t' (Just b')
--       stmts1 ++ stmts2 ++ [def]
--     (Nothing, (xs, b)) -> do
--       let (body, b') = emit options b
--       let def =
--             FunctionDef
--               { name = x,
--                 args = map (,Nothing,Nothing) xs,
--                 body = body ++ [Return b'],
--                 decorators = [],
--                 returns = Nothing,
--                 typeParams = [],
--                 async = False
--               }
--       [def]
--     (Just t, (xs, b)) -> do
--       let emitArg :: (String, T.Expr) -> ([Stmt], [(String, Maybe Expr, Maybe Expr)]) -> ([Stmt], [(String, Maybe Expr, Maybe Expr)])
--           emitArg (x, t) (stmts, args) = do
--             let (stmts', t') = emit options t
--             (stmts' ++ stmts, (x, Just t', Nothing) : args)
--       let (ts, ret) = T.funOf t
--       let (stmts1, args) = foldr emitArg ([], []) (zip xs ts)
--       let (stmts2, ret') = emit options ret
--       let (body, b') = emit options b
--       let def =
--             FunctionDef
--               { name = x,
--                 args = args,
--                 body = body ++ [Return b'],
--                 decorators = [],
--                 returns = Just ret',
--                 typeParams = [],
--                 async = False
--               }
--       stmts1 ++ stmts2 ++ [def]
--   emit options (ts, T.PMeta _ p, b) = emit options (ts, p, b)
--   emit options (ts, p, b) = error $ "TODO: emit Definition " ++ show p

-- instance Emit [T.Stmt] [Stmt] where
--   emit :: BuildOptions -> [T.Stmt] -> [Stmt]
--   emit _ [] = []
--   emit options (stmt : stmts) = emit options stmt ++ emit options stmts

-- instance Emit [(String, T.Expr)] ([Stmt], [(String, Expr)]) where
--   emit :: BuildOptions -> [(String, T.Expr)] -> ([Stmt], [(String, Expr)])
--   emit _ [] = ([], [])
--   emit options ((x, a) : args) = do
--     let (stmts1, a') = emit options a
--     let (stmts2, args') = emit options args
--     (stmts1 ++ stmts2, (x, a') : args')

-- instance Emit [(String, (Maybe T.Expr, Maybe T.Expr))] ([Stmt], [(String, Expr)]) where
--   emit :: BuildOptions -> [(String, (Maybe T.Expr, Maybe T.Expr))] -> ([Stmt], [(String, Expr)])
--   emit _ [] = ([], [])
--   emit options ((x, (a, _)) : args) = do
--     let (stmts1, a') = emit options (fromMaybe T.Err a)
--     let (stmts2, args') = emit options args
--     (stmts1 ++ stmts2, (x, a') : args')

-- instance Emit T.Case ([Stmt], String -> (Pattern, Maybe Expr, [Stmt])) where
--   emit :: BuildOptions -> T.Case -> ([Stmt], String -> (Pattern, Maybe Expr, [Stmt]))
--   emit options (T.Case [p] Nothing b) = do
--     let (stmts, p') = emit options p
--     let (body, b') = emit options b
--     let case' x = (p', Nothing, body ++ [Assign [Name x] b'])
--     (stmts, case')
--   emit options (T.Case ps (Just guard) b) = error $ "TODO: emit ps " ++ show (T.Case ps (Just guard) b)

-- instance Emit [T.Case] ([Stmt], String -> [(Pattern, Maybe Expr, [Stmt])]) where
--   emit :: BuildOptions -> [T.Case] -> ([Stmt], String -> [(Pattern, Maybe Expr, [Stmt])])
--   emit _ [] = ([], const [])
--   emit options (case_ : cases) = do
--     let (stmts1, case') = emit options case_
--     let (stmts2, cases') = emit options cases
--     (stmts1 ++ stmts2, \x -> case' x : cases' x)

-- instance Emit T.Pattern ([Stmt], Pattern) where
--   emit :: BuildOptions -> T.Pattern -> ([Stmt], Pattern)
--   emit _ (T.Var "_") = ([], MatchValue (Name "_"))
--   emit _ (T.Int i) = ([], MatchValue (Integer i))
--   -- -- PNum Double
--   emit _ (T.Var x) = ([], MatchValue (Name x))
--   -- -- PType [String]
--   -- -- PTuple [Pattern]
--   -- -- PRecord [(String, Pattern)]
--   -- -- PTag String [Pattern]
--   -- -- PFun Pattern Pattern
--   -- -- POr [Pattern]
--   -- -- PEq Expr
--   -- -- PErr
--   emit options p = error $ "TODO: emit " ++ show p

-- instance Emit Package Package where
--   emit :: BuildOptions -> Package -> Package
--   emit options pkg = do
--     Package
--       { name = T.nameDashCase pkg.name,
--         src = [],
--         test = []
--       }

-- instance Emit T.Module Module where
--   emit :: BuildOptions -> T.Module -> Module
--   emit options (path, stmts) = do
--     let stmts' = emit options (filter (not . T.isTest) stmts)
--     Module {name = path, body = prelude options : stmts'}

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
    let exposed' = case exposed of
          [x] -> layoutExpose x
          _ -> "(" ++ intercalate ", " (map layoutExpose exposed) ++ ")"
    [PP.Text $ "from " ++ name ++ " import " ++ exposed']
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
    let func' = case func of
          Lambda _ _ -> PP.Text "(" : layout func ++ [PP.Text ")"]
          _ -> layout func
    func' ++ layoutCollection "(" "," ")" (map layout args ++ map kwarg kwargs)
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
