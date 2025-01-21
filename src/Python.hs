module Python where

import Control.Monad (unless, when)
import qualified Core as C
import Data.Bifunctor (Bifunctor (first, second))
import Data.Foldable (foldlM, foldrM)
import Data.Function ((&))
import Data.List (intercalate, isSuffixOf, sortBy, union)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)
import qualified Debug.Trace as Debug
import Load (load)
import qualified PrettyPrint as PP
import Stdlib (filterMap, replace, replaceString)
import System.Directory (copyFile, createDirectory, createDirectoryIfMissing, doesPathExist, removeDirectoryRecursive)
import System.FilePath (joinPath, splitDirectories, splitFileName, splitPath, takeBaseName, takeDirectory, takeFileName, (</>))
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
  { buildDir :: String,
    testPath :: FilePath,
    docsPath :: FilePath,
    maxLineLength :: Int,
    indent :: String
  }
  deriving (Eq, Show)

defaultBuildOptions :: BuildOptions
defaultBuildOptions =
  BuildOptions
    { buildDir = "build",
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
build :: BuildOptions -> [FilePath] -> IO FilePath
build options paths = do
  putStrLn $ "Clearing build directory: " ++ options.buildDir
  pathExists <- doesPathExist options.buildDir
  when pathExists (removeDirectoryRecursive options.buildDir)
  createDirectoryIfMissing True options.buildDir

  putStrLn "Loading modules"
  (ctx, errs) <- load paths
  mapM_ (\e -> putStrLn ("❌ " ++ show e)) errs

  putStrLn "Creating files:"
  files <- mapM (buildModule options ctx . fst) ctx
  mapM_ (\f -> putStrLn ("- " ++ f)) files

  putStrLn "- pyproject.toml"
  writeFile (options.buildDir </> "pyproject.toml") ""

  putStrLn "Done"
  return options.buildDir

buildModule :: BuildOptions -> T.Context -> FilePath -> IO FilePath
buildModule options ctx path = do
  let path' = options.buildDir </> replace '-' '_' path
  createDirectoryIfMissing True (takeDirectory path')
  (imports, defs, tests) <- case lookup path ctx of
    Just stmts ->
      return
        ( filter T.isImport stmts,
          filterMap T.asDef stmts,
          filter T.isTest stmts
        )
    Nothing -> do
      putStrLn ("module not found: " ++ path)
      return ([], [], [])

  -- Source file
  (emit options (imports ++ map T.Def defs) :: [Stmt])
    & Module path
    & layout
    & pretty options
    & writeFile (path' ++ ".py")

  -- Test file
  let imports' =
        emit options $
          T.Import "unittest" "unittest" []
            : ( concatMap (T.bindings . fst) defs
                  & map (\x -> (x, x))
                  & T.Import path (takeBaseName path)
              )
            : imports
  let unitTest =
        ClassDef
          { name = "Test" ++ T.nameCamelCaseUpper path,
            bases = [Name "unittest" `Attribute` "TestCase"],
            body = emit options tests,
            decorators = [],
            typeParams = []
          }
  Module path (imports' ++ [unitTest])
    & layout
    & pretty options
    & writeFile (path' ++ "_test.py")

  return path'

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
    -- emit options (T.Fun a b) = do
    --   let (args, ret) = T.funOf (T.Fun a b)
    --   let (stmts1, args') = emit options args
    --   let (stmts2, ret') = emit options ret
    --   (stmts1 ++ stmts2, callable args' ret')
    T.App a b -> case T.appOf (T.App a b) of
      (T.Var "not", [a]) -> do
        let (s, a') = emit options a
        (s, UnaryOp Not a')
      (T.Var "and", [a, b]) -> do
        let (s1, a') = emit options a
        let (s2, b') = emit options b
        (s1 ++ s2, BoolOp a' And b')
      (T.Var "or", [a, b]) -> do
        let (s1, a') = emit options a
        let (s2, b') = emit options b
        (s1 ++ s2, BoolOp a' Or b')
      (f, args) -> do
        let (s1, f') = emit options f
        let (s2, args') = emit options args
        (s1 ++ s2, Call f' args' [])
    -- Call String [Expr]
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
    -- Op1 Op1 Expr
    T.Op2 op a b -> emit options op a b
    T.Match args cases -> do
      let x = C.newName (concatMap (\(xs, _, _) -> xs) cases) "_match"
      let def = T.Def (T.Var x, T.Match args cases)
      (emit options def, Name x)
    -- If Expr Expr Expr
    -- emit options (T.Let def b) = do
    --   let stmts1 = emit options def
    --   let (stmts2, b') = emit options b
    --   (stmts1 ++ stmts2, b')
    -- emit options (T.Bind (ts, p, a) b) = do
    --   -- let stmts1 = emit options (T.Def [] p (T.Meta C.Unwrap a))
    --   -- let (stmts2, b') = emit options b
    --   -- (stmts1 ++ stmts2, b')
    --   error $ show "TODO: emit Bind " ++ show (ts, p, a, b)
    -- emit options (T.Record fields) = do
    --   let (stmts, fields') = emit options fields
    --   (stmts, record fields')
    -- Select Expr [(String, Expr)]
    -- With Expr [(String, Expr)]
    T.Err -> ([], notImplementedError "error")
    expr -> error $ "TODO: emit Expr: " ++ show expr

instance Emit (Expr -> Stmt) (T.Expr -> [Stmt]) where
  emit :: BuildOptions -> (Expr -> Stmt) -> T.Expr -> [Stmt]
  emit options stmt = \case
    T.Any -> [Pass]
    T.Match [] cases -> do
      let x = C.newName (concatMap (\(xs, _, _) -> xs) cases) "_match"
      let def = T.Def (T.Var x, T.Match [] cases)
      emit options def ++ [stmt (Name x)]
    T.Match args cases -> do
      let (s, arg) = emit options (T.and' args)
      let cases' = emit options stmt cases
      s ++ [Match arg cases']
    a -> case T.letOf a of
      (defs, T.Any) -> concatMap (emit options) defs
      (defs, a) -> do
        let s1 = concatMap (emit options) defs
        let (s2, a') = emit options a
        s1 ++ s2 ++ [stmt a']

instance Emit T.Pattern Pattern where
  emit :: BuildOptions -> T.Pattern -> Pattern
  emit options = \case
    -- MatchValue Expr -- case 1
    -- MatchSequence [Pattern] -- case [p, q]
    -- MatchStar String -- case [p, *ps]
    -- MatchMapping [(String, Pattern)] (Maybe String) -- case {p: q, [, **kvs]}
    -- MatchClass String [Pattern] [(String, Pattern)] -- ClassName(p, x=q)
    -- MatchAs (Maybe Pattern) String -- case p as x
    -- MatchOr [Pattern] -- case p | q
    T.Int i -> MatchValue (Integer i)
    T.Var x -> MatchAs Nothing x
    p -> error $ "TODO emit Pattern " ++ show p

instance Emit T.Op2 (T.Expr -> T.Expr -> ([Stmt], Expr)) where
  emit :: BuildOptions -> T.Op2 -> T.Expr -> T.Expr -> ([Stmt], Expr)
  emit options op a b = do
    let (s1, a') = emit options a
    let (s2, b') = emit options b
    let c = case op of
          T.Eq -> Compare a' Eq b'
          T.Ne -> Compare a' NotEq b'
          T.Lt -> Compare a' Lt b'
          T.Le -> Compare a' LtE b'
          T.Gt -> Compare a' Gt b'
          T.Ge -> Compare a' GtE b'
          T.Add -> BinOp a' Add b'
          T.Sub -> BinOp a' Sub b'
          T.Mul -> BinOp a' Mult b'
          T.Div -> BinOp a' Div b'
          T.DivI -> BinOp a' FloorDiv b'
          -- Mod -- x % y
          T.Pow -> BinOp a' Pow b'
          -- LShift -- x << y
          -- RShift -- x >> y
          -- BitOr -- x | y
          -- BitXor -- x ^ y
          -- BitAnd -- x & y
          -- MatMult -- x @ y
          op -> error $ "TODO emit Op2 " ++ show op
    (s1 ++ s2, c)

instance Emit (Expr -> Stmt) (T.Case -> (Pattern, Maybe Expr, [Stmt])) where
  emit :: BuildOptions -> (Expr -> Stmt) -> T.Case -> (Pattern, Maybe Expr, [Stmt])
  emit options stmt (xs, ps, a) = do
    let p = emit options (T.and' ps) -- TODO: check for bound variables with xs
    let guard = Nothing -- TODO: support case guards
    (p, guard, emit options stmt a)

instance Emit (Expr -> Stmt) ([T.Case] -> [(Pattern, Maybe Expr, [Stmt])]) where
  emit :: BuildOptions -> (Expr -> Stmt) -> [T.Case] -> [(Pattern, Maybe Expr, [Stmt])]
  emit options stmt = \case
    [] -> []
    case' : cases -> do
      emit options stmt case' : emit options stmt cases

instance Emit [T.Expr] ([Stmt], [Expr]) where
  emit :: BuildOptions -> [T.Expr] -> ([Stmt], [Expr])
  emit options = \case
    [] -> ([], [])
    a : bs -> do
      let (s1, a') = emit options a
      let (s2, bs') = emit options bs
      (s1 ++ s2, a' : bs')

instance Emit (T.Pattern, T.Expr) [Stmt] where
  emit :: BuildOptions -> (T.Pattern, T.Expr) -> [Stmt]
  emit options = \case
    (T.Var x, a) -> case T.lambdaOf "_" a of
      ([], a) -> emit options (Assign [Name x]) a
      (xs, a) ->
        [ FunctionDef
            { name = x,
              args = map (,Nothing,Nothing) xs,
              body = emit options Return a,
              decorators = [],
              returns = Nothing,
              typeParams = [],
              async = False
            }
        ]
    (p, a) -> error $ "TODO: emit Def " ++ show (p, a)

instance Emit T.Stmt [Stmt] where
  emit :: BuildOptions -> T.Stmt -> [Stmt]
  emit options = \case
    T.Import path alias names -> do
      let nameAlias (x, y)
            | x == y = (x, Nothing)
            | otherwise = (x, Just y)
      let path' = path & replace '/' '.' & replace '-' '_'
      let alias' = if path == alias || ('/' : alias) `isSuffixOf` path then Nothing else Just alias
      [Import path' alias' | alias `notElem` map snd names]
        ++ [ImportFrom path' (map nameAlias names) | names /= []]
    T.Def def -> emit options def
    T.Test t -> do
      let (s1, a') = emit options t.expr
      let (s2, b') = emit options t.expect -- TODO: do a match instead
      let def =
            FunctionDef
              { name = "test_" ++ T.nameSnakeCase t.name,
                args = [("self", Nothing, Nothing)],
                body =
                  [ Assign [Name "actual"] a',
                    Assign [Name "expect"] b',
                    Assign [] (Call (Attribute (Name "self") "assertEqual") [Name "actual", Name "expect"] [])
                  ],
                decorators = [],
                returns = Nothing,
                typeParams = [],
                async = False
              }
      s1 ++ s2 ++ [def]
    stmt -> error $ "TODO: emit Stmt: " ++ show stmt

instance Emit [T.Stmt] [Stmt] where
  emit :: BuildOptions -> [T.Stmt] -> [Stmt]
  emit options = concatMap (emit options)

--- Pretty printing layouts ---
pretty :: BuildOptions -> PP.Layout -> String
pretty options = PP.pretty options.maxLineLength options.indent

class Layout a where
  layout :: a -> PP.Layout

instance Layout Module where
  layout :: Module -> PP.Layout
  layout Module {body} = layout (True, body) ++ [PP.NewLine]

instance Layout (Bool, [Stmt]) where
  layout :: (Bool, [Stmt]) -> PP.Layout
  layout (global, stmts) = case stmts of
    [] -> []
    [stmt] -> layout stmt
    (stmt1 : stmt2@FunctionDef {} : stmts) -> do
      layout stmt1
        ++ [PP.NewLine, PP.NewLine]
        ++ [PP.NewLine | global]
        ++ layout (global, stmt2 : stmts)
    (stmt1 : stmt2@ClassDef {} : stmts) -> do
      layout stmt1
        ++ [PP.NewLine, PP.NewLine]
        ++ [PP.NewLine | global]
        ++ layout (global, stmt2 : stmts)
    (stmt : stmts) ->
      layout stmt
        ++ [PP.NewLine]
        ++ layout (global, stmts)

instance Layout [Stmt] where
  layout :: [Stmt] -> PP.Layout
  layout stmts = layout (False, stmts)

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
      ++ [PP.Text ":", PP.Indent (PP.NewLine : layout body)]
  layout If {test, body, orelse} = do
    layout If {test = test, body = body, orelse = []}
      ++ [PP.NewLine, PP.Text "else:", PP.Indent (PP.NewLine : layout orelse)]
  layout def@FunctionDef {} = do
    let body = if null def.body then [Pass] else def.body
    PP.Text ("def " ++ def.name)
      : layoutCollection "(" "," ")" (map layout def.args)
      ++ maybe [] (\t -> PP.Text " -> " : layout t) def.returns
      ++ [PP.Text ":", PP.Indent (PP.NewLine : layout body)]
  layout def@ClassDef {} = do
    let body = if null def.body then [Pass] else def.body
    PP.Text ("class " ++ def.name)
      : case def.bases of
        [] -> []
        bases -> layoutCollection "(" "," ")" (map layout bases)
      ++ [PP.Text ":", PP.Indent (PP.NewLine : layout body)]
  layout (Return expr) =
    [ PP.Text "return ",
      PP.Or
        (layout expr)
        [ PP.Text "(",
          PP.Indent (PP.NewLine : layout expr),
          PP.NewLine,
          PP.Text ")"
        ]
    ]
  layout (Match arg cases) = do
    let layoutArg (Tuple [arg]) = layout arg
        layoutArg arg = layout arg
    let layoutCase' (pat, guard, body) =
          PP.Text "case "
            : layout pat
            ++ maybe [] (\e -> PP.Text " if " : layout e) guard
            ++ [PP.Text ":", PP.Indent (PP.NewLine : concatMap layout body)]
    let layoutCase (MatchSequence [pat], guard, body) = layoutCase' (pat, guard, body)
        layoutCase (pat, guard, body) = layoutCase' (pat, guard, body)
    PP.Text "match "
      : layoutArg arg
      ++ [PP.Text ":", PP.Indent (PP.NewLine : PP.join [PP.NewLine] (map layoutCase cases))]
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
  layout (Bool True) = [PP.Text "True"]
  layout (Bool False) = [PP.Text "False"]
  layout (Integer i) = [PP.Text $ show i]
  layout (Float n) = [PP.Text $ show n]
  layout (String s) = case s of
    s | '\'' `notElem` s -> [PP.Text $ "'" ++ s ++ "'"]
    s -> [PP.Text $ "\"" ++ replaceString "\"" "\\\"" s ++ "\""]
  layout (Name x) = [PP.Text x]
  layout (Tuple [a]) = [PP.Text "("] ++ layout a ++ [PP.Text ",)"]
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
  layout (UnaryOp op a) = do
    let op' = case op of
          UAdd -> "+"
          USub -> "-"
          Not -> "not "
          Invert -> "~"
    PP.Text op' : layout a
  layout (BinOp a op b) = do
    let op' = case op of
          Add -> " + "
          Sub -> " - "
          Mult -> " * "
          Div -> " / "
          FloorDiv -> " // "
          Mod -> " % "
          Pow -> "**"
          LShift -> " << "
          RShift -> " >> "
          BitOr -> " | "
          BitXor -> " ^ "
          BitAnd -> " & "
          MatMult -> " @ "
    PP.Text "(" : layout a ++ [PP.Text op'] ++ layout b ++ [PP.Text ")"]
  layout (BoolOp a op b) = do
    let op' = case op of
          And -> " and "
          Or -> " or "
    PP.Text "(" : layout a ++ [PP.Text op'] ++ layout b ++ [PP.Text ")"]
  layout (Compare a op b) = do
    let op' = case op of
          Eq -> " == "
          NotEq -> " != "
          Lt -> " < "
          LtE -> " <= "
          Gt -> " > "
          GtE -> " >= "
          Is -> " is "
          IsNot -> " is not "
          In -> " in "
          NotIn -> " not in "
    PP.Text "(" : layout a ++ [PP.Text op'] ++ layout b ++ [PP.Text ")"]
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
      [PP.Indent (PP.NewLine : PP.join [PP.Text ",", PP.NewLine] items), PP.Text ",", PP.NewLine],
    PP.Text close
  ]
