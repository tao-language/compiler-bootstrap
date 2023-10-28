{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}

module Python where

import Core (DocString (..), Metadata (..))
import qualified Core as C
import Data.Bifunctor (Bifunctor (first))
import Data.List (intercalate, union)
import qualified PrettyPrint as PP
import qualified Tao

-- TODO: abstract into an `Imperative` language
-- https://en.wikipedia.org/wiki/Imperative_programming

-- https://docs.python.org/3/library/ast.html
-- https://docs.python.org/3/reference/grammar.html

-- https://docs.python.org/3/library/ast.html#ast.Module
data Module = Module
  { name :: String,
    docs :: Maybe DocString,
    body :: [Statement]
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
  | Meta [Metadata] Expr
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
data Statement
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
  | Match Expr [(Pattern, Maybe Expr, [Statement])]
  | Return Expr
  | Yield Expr
  | YieldFrom Expr
  | Global [String]
  | Nonlocal [String]
  | Await Expr
  | If
      { test :: Expr,
        body :: [Statement],
        orelse :: [Statement]
      }
  | For
      { target :: Expr,
        iter :: Expr,
        body :: [Statement],
        orelse :: [Statement],
        async :: Bool
      }
  | While
      { test :: Expr,
        body :: [Statement],
        orelse :: [Statement]
      }
  | With
      { items :: [(Expr, Maybe Expr)],
        body :: [Statement],
        async :: Bool
      }
  | FunctionDef
      { docs :: Maybe DocString,
        name :: String,
        args :: [(String, Maybe Expr, Maybe Expr)],
        body :: [Statement],
        decorators :: [Expr],
        returns :: Maybe Expr,
        typeParams :: [TypeParam],
        async :: Bool
      }
  | ClassDef
      { name :: String,
        bases :: [Expr],
        body :: [Statement],
        decorators :: [Expr],
        typeParams :: [TypeParam]
      }
  | Try
      { body :: [Statement],
        handlers :: [(Maybe Expr, String, Expr)],
        else' :: [Statement],
        finally :: [Statement]
      }
  deriving (Eq, Show)

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
  | MatchMeta [Metadata] Pattern
  deriving (Eq, Show)

--- Type parameters ---
-- https://docs.python.org/3/library/ast.html#ast-type-params
data TypeParam
  = TypeVar String -- T[a]
  | TypeVarTuple String -- T[*ts]
  | ParamSpec String -- T[**ts]
  deriving (Eq, Show)

newtype Emit a = Emit (Context -> (a, Context))

data Context = Context
  { imports :: [String],
    globals :: [Statement],
    locals :: [Statement],
    names :: [String]
  }
  deriving (Eq, Show)

newContext :: Context
newContext =
  Context
    { imports = [],
      globals = [],
      locals = [],
      names = []
    }

instance Functor Emit where
  fmap :: (a -> b) -> Emit a -> Emit b
  fmap f (Emit e) = Emit (first f . e)

instance Applicative Emit where
  pure :: a -> Emit a
  pure x = Emit (x,)

  (<*>) :: Emit (a -> b) -> Emit a -> Emit b
  emitF <*> emit = do
    f <- emitF
    fmap f emit

instance Monad Emit where
  (>>=) :: Emit a -> (a -> Emit b) -> Emit b
  (Emit e) >>= f =
    Emit
      ( \ctx -> do
          let (x, ctx') = e ctx
          apply (f x) ctx'
      )

apply :: Emit a -> Context -> (a, Context)
apply (Emit e) = e

addImport :: String -> Emit ()
addImport imp =
  Emit (\ctx -> ((), ctx {imports = ctx.imports `union` [imp]}))

addGlobal :: Statement -> Emit ()
addGlobal stmt =
  Emit (\ctx -> ((), ctx {globals = ctx.globals ++ [stmt]}))

addLocal :: Statement -> Emit ()
addLocal stmt =
  Emit (\ctx -> ((), ctx {locals = ctx.locals ++ [stmt]}))

--- Syntax sugar ---

call :: Expr -> [Expr] -> Expr
call f xs = Call f xs []

import' :: String -> Statement
import' name = Import name Nothing

raise :: Expr -> Statement
raise x = Raise x Nothing

--- Tao to Python ---

emit :: Tao.Module -> Module
emit mod = do
  let (body, ctx) = apply (emitStmts mod.body) newContext
  Module
    { name = mod.name,
      docs = mod.docs,
      body = map import' ctx.imports ++ ctx.globals ++ ctx.locals ++ body
    }

emitStmt :: Tao.Statement -> Emit Statement
emitStmt def@(Tao.LetDef {value = Tao.Match cases, meta}) = do
  let argNames = Tao.matchArgs "arg" cases
  (typeParams, argTypes, returns) <- case def.type' of
    Just (Tao.For xs t) -> do
      let (argsT, retT) = Tao.asFun t
      argTypes <- emitExprs argsT
      returns <- emitExpr retT
      return (map TypeVar xs, map Just argTypes, Just returns)
    Nothing -> return ([], map (const Nothing) argNames, Nothing)
  cases' <- emitMatchCases cases
  return
    FunctionDef
      { docs = def.docs,
        name = def.name,
        args = zipWith (\x t -> (x, t, Nothing)) argNames argTypes,
        body = [Match (Tuple $ map Name argNames) cases'],
        decorators = [],
        returns = returns,
        typeParams = typeParams,
        async = False
      }
emitStmt (Tao.LetDef {docs, name, type', value, meta}) = do
  error "TODO: LetDef"
emitStmt (Tao.Unpack {docs, types, pattern, value, meta}) = do
  error "TODO: Unpack"
emitStmt (Tao.TypeDef {docs, name, args, alts, meta}) = do
  error "TODO: TypeDef"
emitStmt (Tao.Import {path, name, exposing, meta}) = do
  error "TODO: TypeDef"
emitStmt (Tao.Prompt {description, expression, result, meta}) = do
  error "TODO: Prompt"

emitMatchCase :: ([Tao.Pattern], Tao.Expr) -> Emit (Pattern, Maybe Expr, [Statement])
emitMatchCase (ps, b) = do
  pats <- emitPatterns ps
  body <- emitBody b
  return (MatchSequence pats, Nothing, body)

emitMatchCases :: [([Tao.Pattern], Tao.Expr)] -> Emit [(Pattern, Maybe Expr, [Statement])]
emitMatchCases [] = return []
emitMatchCases (case' : cases) = do
  case' <- emitMatchCase case'
  cases <- emitMatchCases cases
  return (case' : cases)

emitPattern :: Tao.Pattern -> Emit Pattern
-- PAny
-- PKnd
-- PIntT
-- PNumT
emitPattern (Tao.PInt i) = return (MatchValue (Integer i))
-- PTag String
emitPattern (Tao.PVar x) = return (MatchAs Nothing x)
-- PTuple [Pattern]
-- PRecord [(String, Pattern)]
-- PFun Pattern Pattern
-- PApp Pattern Pattern
emitPattern (Tao.PMeta m p) = do
  pat <- emitPattern p
  return (MatchMeta m pat)
emitPattern p = error $ "TODO: emitPattern " ++ show p

emitPatterns :: [Tao.Pattern] -> Emit [Pattern]
emitPatterns [] = return []
emitPatterns (p : ps) = do
  p <- emitPattern p
  ps <- emitPatterns ps
  return (p : ps)

emitStmts :: [Tao.Statement] -> Emit [Statement]
emitStmts [] = return []
emitStmts (stmt : stmts) = do
  stmt' <- emitStmt stmt
  stmts' <- emitStmts stmts
  return (stmt' : stmts')

emitBody :: Tao.Expr -> Emit [Statement]
emitBody a =
  Emit
    ( \ctx -> do
        let (expr, ctx') = apply (emitExpr a) ctx {locals = []}
        (ctx'.locals ++ [Return expr], ctx' {locals = ctx.locals})
    )

emitExpr :: Tao.Expr -> Emit Expr
emitExpr Tao.IntT = return (Name "int")
emitExpr (Tao.Int i) = return (Integer i)
emitExpr (Tao.Var x) = return (Name x)
emitExpr (Tao.App a b) = do
  let (func, args) = Tao.asApp (Tao.App a b)
  func <- emitExpr func
  args <- emitExprs args
  return (call func args)
emitExpr (Tao.Sub a b) = do
  a <- emitExpr a
  b <- emitExpr b
  return (BinOp a Sub b)
emitExpr (Tao.Mul a b) = do
  a <- emitExpr a
  b <- emitExpr b
  return (BinOp a Mult b)
emitExpr (Tao.Meta m a) = do
  a' <- emitExpr a
  return (Meta m a')
emitExpr a = error $ "TODO: expr " ++ show a

emitExprs :: [Tao.Expr] -> Emit [Expr]
emitExprs [] = return []
emitExprs (a : bs) = do
  a' <- emitExpr a
  bs' <- emitExprs bs
  return (a' : bs')

--- Pretty printing layouts ---

layoutModule :: Module -> PP.Layout
layoutModule Module {body} = PP.join [PP.NewLine] (map layoutStmt body)

layoutStmt :: Statement -> PP.Layout
layoutStmt (Import name alias) = case alias of
  Just alias -> [PP.Text $ "import " ++ name ++ " as " ++ alias]
  Nothing -> [PP.Text $ "import " ++ name]
layoutStmt def@FunctionDef {} = do
  PP.Text ("def " ++ def.name)
    : layoutTuple (map layoutFunctionArg def.args)
    ++ maybe [] (\t -> PP.Text " -> " : layoutExpr t) def.returns
    ++ [PP.Text ":", PP.Indent (PP.NewLine : concatMap layoutStmt def.body)]
layoutStmt (Return expr) =
  [ PP.Text "return ",
    PP.Or
      (layoutExpr expr)
      [ PP.Text "(",
        PP.Indent (PP.NewLine : layoutExpr expr),
        PP.NewLine,
        PP.Text ")"
      ]
  ]
layoutStmt (Match arg cases) = do
  let layoutArg (Tuple [arg]) = layoutExpr arg
      layoutArg arg = layoutExpr arg
  let layoutCase' (pat, guard, body) =
        PP.Text "case "
          : layoutPattern pat
          ++ maybe [] (\e -> PP.Text " if " : layoutExpr e) guard
          ++ [PP.Text ":", PP.Indent (PP.NewLine : concatMap layoutStmt body), PP.NewLine]
  let layoutCase (MatchSequence [pat], guard, body) = layoutCase' (pat, guard, body)
      layoutCase (pat, guard, body) = layoutCase' (pat, guard, body)
  PP.Text "match "
    : layoutArg arg
    ++ [PP.Text ":", PP.Indent (PP.NewLine : concatMap layoutCase cases)]
layoutStmt (Raise exc from) =
  PP.Text "raise "
    : layoutExpr exc
    ++ maybe [] (\a -> PP.Text " from " : layoutExpr a) from
    ++ [PP.NewLine]
layoutStmt stmt = error $ "TODO: layoutStmt: " ++ show stmt

layoutPattern :: Pattern -> PP.Layout
layoutPattern (MatchValue expr) = layoutExpr expr
layoutPattern (MatchSequence pats) = layoutList (map layoutPattern pats)
layoutPattern (MatchStar name) = [PP.Text $ "*" ++ name]
-- MatchMapping [(String, Pattern)] (Maybe String) -- case {p: q, [, **kvs]}
-- MatchClass String [Pattern] [(String, Pattern)] -- ClassName(p, x=q)
layoutPattern (MatchAs maybePattern name) = case maybePattern of
  Just pat -> layoutPattern pat ++ [PP.Text $ " as " ++ name]
  Nothing -> [PP.Text name]
layoutPattern (MatchOr pats) = PP.join [PP.Text " | "] (map layoutPattern pats)
layoutPattern (MatchMeta _ pat) = layoutPattern pat
layoutPattern pat = error $ "TODO: layoutPattern: " ++ show pat

layoutExpr :: Expr -> PP.Layout
layoutExpr (Integer i) = [PP.Text $ show i]
layoutExpr (Name x) = [PP.Text x]
layoutExpr (Tuple items) = layoutTuple (map layoutExpr items)
layoutExpr (Call func args kwargs) = do
  let kwarg (x, a) = PP.Text (x ++ "=") : layoutExpr a
  layoutExpr func ++ layoutTuple (map layoutExpr args ++ map kwarg kwargs)
layoutExpr (BinOp a op b) = do
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
  -- TODO: remove redundant parentheses
  -- TODO: break long lines
  PP.Text "(" : layoutExpr a ++ [PP.Text $ showOp op] ++ layoutExpr b ++ [PP.Text ")"]
layoutExpr (Meta _ a) = layoutExpr a
layoutExpr a = error $ "TODO: layoutExpr: " ++ show a

layoutFunctionArg :: (String, Maybe Expr, Maybe Expr) -> PP.Layout
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
      [PP.Indent (PP.NewLine : PP.join [PP.Text ",", PP.NewLine] items), PP.Text ",", PP.NewLine],
    PP.Text close
  ]