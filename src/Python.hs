{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}

module Python where

import Core
import Data.Bifunctor (Bifunctor (first))
import Data.Foldable (foldlM, foldrM)
import Data.List (intercalate, union)
import PrettyPrint (Layout)
import qualified PrettyPrint as PP
import Tao

-- TODO: abstract into an `Imperative` language
-- https://en.wikipedia.org/wiki/Imperative_programming

-- https://docs.python.org/3/library/ast.html
-- https://docs.python.org/3/reference/grammar.html

-- https://docs.python.org/3/library/ast.html#ast.Module
data PyModule = PyModule
  { name :: String,
    body :: [PyStatement]
  }
  deriving (Eq, Show)

newModule :: String -> [PyStatement] -> PyModule
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
  | PyMeta [Metadata] PyExpr
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
data PyStatement
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
  | PyMatch PyExpr [(PyPattern, Maybe PyExpr, [PyStatement])] -- match x: case p: y; ...
  | PyReturn PyExpr -- return x
  | PyYield PyExpr -- yield x
  | PyYieldFrom PyExpr -- yield from x
  | PyGlobal [String] -- global x
  | PyNonlocal [String] -- nonlocal x
  | PyAwait PyExpr -- await x
  | PyIf
      { test :: PyExpr,
        body :: [PyStatement],
        orelse :: [PyStatement]
      }
  | PyFor
      { target :: PyExpr,
        iter :: PyExpr,
        body :: [PyStatement],
        orelse :: [PyStatement],
        async :: Bool
      }
  | PyWhile
      { test :: PyExpr,
        body :: [PyStatement],
        orelse :: [PyStatement]
      }
  | PyWith
      { items :: [(PyExpr, Maybe PyExpr)],
        body :: [PyStatement],
        async :: Bool
      }
  | PyFunctionDef
      { name :: String,
        args :: [(String, Maybe PyExpr, Maybe PyExpr)],
        body :: [PyStatement],
        decorators :: [PyExpr],
        returns :: Maybe PyExpr,
        typeParams :: [PyTypeParam],
        async :: Bool
      }
  | PyClassDef
      { name :: String,
        bases :: [PyExpr],
        body :: [PyStatement],
        decorators :: [PyExpr],
        typeParams :: [PyTypeParam]
      }
  | PyTry
      { body :: [PyStatement],
        handlers :: [(Maybe PyExpr, String, PyExpr)],
        else' :: [PyStatement],
        finally :: [PyStatement]
      }
  deriving (Eq, Show)

newPyFunctionDef :: String -> [(String, Maybe PyExpr, Maybe PyExpr)] -> [PyStatement] -> PyStatement
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

newPyClassDef :: String -> [PyTypeParam] -> [PyStatement] -> PyStatement
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
  | PyMatchMeta [Metadata] PyPattern
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

pyImport :: String -> PyStatement
pyImport name = PyImport name Nothing

pyRaise :: PyExpr -> PyStatement
pyRaise x = PyRaise x Nothing

-- emitExpr :: PyTarget -> Expression -> Emit PyExpr
-- emitExpr _ IntT = return (Name "int")
-- emitExpr _ (Int i) = return (PyInteger i)
-- emitExpr target (Tag k) = emitExpr target (Var k)
-- emitExpr target (Var x) = case lookup x target.extern of
--   Just def -> do
--     addGlobals def.globals
--     addLocals def.locals
--     return def.expr -- TODO: manage globals + locals
--   Nothing -> return (Name x)
-- emitExpr target (App a b) = do
--   let (func, args) = asApp (App a b)
--   func <- emitExpr target func
--   args <- emitExprs target args
--   return (call func args)
-- emitExpr target (Op2 Sub a b) = do
--   a <- emitExpr target a
--   b <- emitExpr target b
--   return (BinOp a Sub b)
-- emitExpr target (Op2 Mul a b) = do
--   a <- emitExpr target a
--   b <- emitExpr target b
--   return (BinOp a Mult b)
-- -- emitExpr target (Tao.Meta m a) = do
-- --   a' <- emitExpr target a
-- --   return (Meta m a')
-- emitExpr _ a = error $ "TODO: expr " ++ show a

-- emitExprs :: PyTarget -> [Term] -> Emit [PyExpr]
-- emitExprs _ [] = return []
-- emitExprs target (a : bs) = do
--   a' <- emitExpr target a
--   bs' <- emitExprs target bs
--   return (a' : bs')

-- emitExample :: PyTarget -> (Term, Term) -> Emit (PyExpr, PyExpr)
-- emitExample target (prompt, result) = do
--   prompt <- emitExpr target prompt
--   result <- emitExpr target result
--   return (prompt, result)

-- emitExamples :: PyTarget -> [(Term, Term)] -> Emit [(PyExpr, PyExpr)]
-- emitExamples _ [] = return []
-- emitExamples target (example : examples) = do
--   example <- emitExample target example
--   examples <- emitExamples target examples
--   return (example : examples)

-- emitMatchCase :: PyTarget -> ([Tao.Pattern], Term) -> Emit (Pattern, Maybe PyExpr, [Statement])
-- emitMatchCase target (ps, b) = do
--   pats <- emitPatterns target ps
--   body <- emitBody target b
--   return (MatchSequence pats, Nothing, body)

-- emitMatchCases :: PyTarget -> [([Tao.Pattern], Term)] -> Emit [(Pattern, Maybe PyExpr, [Statement])]
-- emitMatchCases _ [] = return []
-- emitMatchCases target (case' : cases) = do
--   case' <- emitMatchCase target case'
--   cases <- emitMatchCases target cases
--   return (case' : cases)

-- emitPattern :: PyTarget -> Tao.Pattern -> Emit Pattern
-- -- PAny
-- -- PKnd
-- -- PIntT
-- -- PNumT
-- emitPattern _ (Tao.PInt i) = return (MatchValue (PyInteger i))
-- -- PTag String
-- emitPattern _ (Tao.PVar x) = return (MatchAs Nothing x)
-- -- PTuple [Pattern]
-- -- PRecord [(String, Pattern)]
-- -- PFun Pattern Pattern
-- -- PApp Pattern Pattern
-- emitPattern target (Tao.PMeta m p) = do
--   pat <- emitPattern target p
--   return (MatchMeta m pat)
-- emitPattern _ p = error $ "TODO: emitPattern " ++ show p

-- emitPatterns :: PyTarget -> [Tao.Pattern] -> Emit [Pattern]
-- emitPatterns _ [] = return []
-- emitPatterns target (p : ps) = do
--   p <- emitPattern target p
--   ps <- emitPatterns target ps
--   return (p : ps)

-- emitBody :: PyTarget -> Term -> Emit [PyStatement]
-- emitBody target a = Emit $
--   \ctx -> do
--     let (expr, ctx') = apply (emitExpr target a) ctx {locals = []}
--     (ctx'.locals ++ [Return expr], ctx' {locals = ctx.locals})

--- Pretty printing layouts ---

layoutModule :: PyModule -> PP.Layout
layoutModule PyModule {body} = PP.join [PP.Text "\n"] (map layoutStmt body)

layoutStmt :: PyStatement -> PP.Layout
layoutStmt (PyImport name alias) = case alias of
  Just alias -> [PP.Text $ "import " ++ name ++ " as " ++ alias]
  Nothing -> [PP.Text $ "import " ++ name]
layoutStmt def@PyFunctionDef {} = do
  PP.Text ("def " ++ def.name)
    : layoutTuple (map layoutFunctionArg def.args)
    ++ maybe [] (\t -> PP.Text " -> " : layoutExpr t) def.returns
    -- ++ [PP.Text ":", PP.Indent (PP.Text "\n" : maybe [] layoutDocString def.docs ++ concatMap layoutStmt def.body)]
    ++ [PP.Text ":\n"]
layoutStmt def@PyClassDef {} = do
  PP.Text ("class " ++ def.name)
    : case def.bases of
      [] -> []
      bases -> layoutTuple (map layoutExpr bases)
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutStmt def.body)]
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
layoutPattern (PyMatchMeta [] pat) = layoutPattern pat
layoutPattern (PyMatchMeta (m : meta) pat) = case m of
  _ -> layoutPattern (PyMatchMeta meta pat)
layoutPattern pat = error $ "TODO: layoutPattern: " ++ show pat

layoutExpr :: PyExpr -> PP.Layout
layoutExpr (PyInteger i) = [PP.Text $ show i]
layoutExpr (PyName x) = [PP.Text x]
layoutExpr (PyTuple items) = layoutTuple (map layoutExpr items)
layoutExpr (PyCall func args kwargs) = do
  let kwarg (x, a) = PP.Text (x ++ "=") : layoutExpr a
  layoutExpr func ++ layoutTuple (map layoutExpr args ++ map kwarg kwargs)
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
  -- TODO: remove redundant parentheses
  -- TODO: break long lines
  PP.Text "(" : layoutExpr a ++ [PP.Text $ showOp op] ++ layoutExpr b ++ [PP.Text ")"]
layoutExpr (PyMeta [] a) = layoutExpr a
layoutExpr (PyMeta (m : meta) a) = case m of
  _ -> layoutExpr a
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