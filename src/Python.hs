{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}

module Python where

import Core (Metadata (..))
import qualified Core as C
import Data.Bifunctor (Bifunctor (first))
import Data.Foldable (foldlM, foldrM)
import Data.List (intercalate, union)
import PrettyPrint (Layout)
import qualified PrettyPrint as PP
import qualified Tao

-- TODO: abstract into an `Imperative` language
-- https://en.wikipedia.org/wiki/Imperative_programming

-- https://docs.python.org/3/library/ast.html
-- https://docs.python.org/3/reference/grammar.html

-- https://docs.python.org/3/library/ast.html#ast.Module
data Module = Module
  { name :: String,
    body :: [Statement]
  }
  deriving (Eq, Show)

newModule :: String -> [Statement] -> Module
newModule name body =
  Module
    { name = name,
      body = body
    }

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
  | Match Expr [(Pattern, Maybe Expr, [Statement])] -- match x: case p: y; ...
  | Return Expr -- return x
  | Yield Expr -- yield x
  | YieldFrom Expr -- yield from x
  | Global [String] -- global x
  | Nonlocal [String] -- nonlocal x
  | Await Expr -- await x
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
      { name :: String,
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

newFunctionDef :: String -> [(String, Maybe Expr, Maybe Expr)] -> [Statement] -> Statement
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

newClassDef :: String -> [TypeParam] -> [Statement] -> Statement
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
  { globals :: [Statement],
    locals :: [Statement],
    names :: [String]
  }
  deriving (Eq, Show)

newContext :: Context
newContext =
  Context
    { globals = [],
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

addUnique :: (Eq a) => a -> [a] -> [a]
addUnique x [] = [x]
addUnique x (x' : ys) | x == x' = x : ys
addUnique x (y : ys) = y : addUnique x ys

addGlobal :: Statement -> Emit ()
addGlobal stmt = Emit (\ctx -> ((), ctx {globals = addUnique stmt ctx.globals}))

addGlobals :: [Statement] -> Emit ()
addGlobals [] = return ()
addGlobals (stmt : stmts) = do
  addGlobals stmts
  addGlobal stmt
  return ()

addLocal :: Statement -> Emit ()
addLocal stmt = Emit (\ctx -> ((), ctx {locals = addUnique stmt ctx.locals}))

addLocals :: [Statement] -> Emit ()
addLocals [] = return ()
addLocals (stmt : stmts) = do
  addLocals stmts
  addLocal stmt
  return ()

apply :: Emit a -> Context -> (a, Context)
apply (Emit e) = e

--- Syntax sugar ---

call :: Expr -> [Expr] -> Expr
call f xs = Call f xs []

import' :: String -> Statement
import' name = Import name Nothing

raise :: Expr -> Statement
raise x = Raise x Nothing

--- Tao to Python ---

-- TODO: move to Target.hs
data Target stmt expr = Target
  { requires :: [String],
    header :: String,
    footer :: String,
    extern :: [(String, TargetDef stmt expr)]
  }
  deriving (Eq, Show)

data TargetDef stmt expr = TargetDef
  { globals :: [stmt],
    locals :: [stmt],
    expr :: expr
  }
  deriving (Eq, Show)

targetDef :: expr -> TargetDef stmt expr
targetDef expr = TargetDef {globals = [], locals = [], expr = expr}

type PyTarget = Target Statement Expr

builtins :: PyTarget
builtins =
  Target
    { requires = [],
      header = "",
      footer = "",
      extern =
        [ ("True", targetDef $ Bool True),
          ("False", targetDef $ Bool False)
        ]
    }

-- emit :: Tao.Module -> Module
-- emit mod = do
--   let initialCtx = newContext -- TODO: {env = moduleToCore mod}
--   let (body, ctx) = apply (emitStmts builtins mod.stmts) initialCtx
--   Module
--     { name = mod.name,
--       docs = mod.docs,
--       body = ctx.globals ++ ctx.locals ++ body
--     }

-- emitStmt :: PyTarget -> Tao.Statement -> [Tao.Statement] -> Emit [Statement]
-- emitStmt target Tao.LetDef {docs, type', name, value = Tao.LamMatch cases} stmts = do
--   let argNames = Tao.lamMatchArgs "arg" cases
--   (typeParams, argTypes, returns) <- case type' of
--     Just (Tao.For xs t) -> do
--       let (argsT, retT) = Tao.asFun t
--       argTypes <- emitExprs target argsT
--       returns <- emitExpr target retT
--       return (map TypeVar xs, map Just argTypes, Just returns)
--     Nothing -> return ([], map (const Nothing) argNames, Nothing)
--   cases' <- emitMatchCases target cases
--   return
--     [ FunctionDef
--         { docs = docs,
--           name = name,
--           args = zipWith (\x t -> (x, t, Nothing)) argNames argTypes,
--           body = [Match (Tuple $ map Name argNames) cases'],
--           decorators = [],
--           returns = returns,
--           typeParams = typeParams,
--           async = False
--         }
--     ]
-- emitStmt target Tao.LetDef {type', name, value} stmts = do
--   value <- emitExpr target value
--   case type' of
--     -- Just type' -> do
--     --   type' <- emitType type'
--     --   return [AnnAssign (Name name) type' (Just value)]
--     Nothing -> return [Assign [Name name] value]
-- emitStmt target Tao.LetPat {docs, types, pattern, value} stmts = do
--   error "TODO: LetPat"
-- emitStmt target Tao.LetType {docs, name, args, alts} stmts = do
--   addGlobal (ImportFrom "dataclasses" [("dataclass", Nothing)])
--   typeParams <- return [] -- TODO: args
--   -- let asdf = Tao.findTraits
--   body <- emitClassDefs target name stmts
--   return
--     [ ClassDef
--         { name = name,
--           bases = [],
--           body = body,
--           decorators = [Name "dataclass"],
--           typeParams = typeParams
--         }
--     ]
-- emitStmt target Tao.LetTrait {} stmts = return []
-- emitStmt target Tao.Unbox {} stmts = do
--   error "TODO: Unbox"
-- emitStmt target Tao.Import {path, alias, exposing} stmts = case alias of
--   Just name -> return [Import path (Just name)]
--   Nothing -> return [Import path Nothing]
-- emitStmt target Tao.Prompt {} stmts = return []

-- selfPattern :: String -> [Expr] -> Tao.Pattern
-- selfPattern k args = Tao.pApp (Tao.PTag k) args

-- emitClassDef :: PyTarget -> String -> Tao.Statement -> Emit [Statement]
-- emitClassDef target name trait@Tao.LetTrait {} = do
--   -- self :: Pattern,
--   -- returns :: Maybe Expr,
--   value <- emitExpr target trait.value
--   return
--     [ FunctionDef
--         { docs = trait.docs,
--           name = trait.name,
--           args = [],
--           body = [Return value],
--           decorators = [],
--           returns = Nothing,
--           typeParams = map TypeVar trait.typeVars,
--           async = False
--         }
--     ]
-- emitClassDef _ _ _ = return []

-- emitClassDefs :: PyTarget -> String -> [Tao.Statement] -> Emit [Statement]
-- emitClassDefs _ _ [] = return []
-- emitClassDefs target name (stmt : stmts) = do
--   stmts1 <- emitClassDef target name stmt
--   stmts2 <- emitClassDefs target name stmts
--   return (stmts1 ++ stmts2)

-- emitStmts :: PyTarget -> [Tao.Statement] -> Emit [Statement]
-- emitStmts _ [] = return []
-- emitStmts target (stmt : stmts) = do
--   stmts1 <- emitStmt target stmt stmts
--   stmts2 <- emitStmts target stmts
--   return (stmts1 ++ stmts2)

emitExpr :: PyTarget -> Tao.Expr -> Emit Python.Expr
emitExpr _ Tao.IntT = return (Name "int")
emitExpr _ (Tao.Int i) = return (Integer i)
emitExpr target (Tao.Tag k) = emitExpr target (Tao.Var k)
emitExpr target (Tao.Var x) = case lookup x target.extern of
  Just def -> do
    addGlobals def.globals
    addLocals def.locals
    return def.expr -- TODO: manage globals + locals
  Nothing -> return (Name x)
emitExpr target (Tao.App a b) = do
  let (func, args) = Tao.asApp (Tao.App a b)
  func <- emitExpr target func
  args <- emitExprs target args
  return (call func args)
emitExpr target (Tao.Op2 C.Sub a b) = do
  a <- emitExpr target a
  b <- emitExpr target b
  return (BinOp a Sub b)
emitExpr target (Tao.Op2 C.Mul a b) = do
  a <- emitExpr target a
  b <- emitExpr target b
  return (BinOp a Mult b)
-- emitExpr target (Tao.Meta m a) = do
--   a' <- emitExpr target a
--   return (Meta m a')
emitExpr _ a = error $ "TODO: expr " ++ show a

emitExprs :: PyTarget -> [Tao.Expr] -> Emit [Expr]
emitExprs _ [] = return []
emitExprs target (a : bs) = do
  a' <- emitExpr target a
  bs' <- emitExprs target bs
  return (a' : bs')

emitExample :: PyTarget -> (Tao.Expr, Tao.Expr) -> Emit (Expr, Expr)
emitExample target (prompt, result) = do
  prompt <- emitExpr target prompt
  result <- emitExpr target result
  return (prompt, result)

emitExamples :: PyTarget -> [(Tao.Expr, Tao.Expr)] -> Emit [(Expr, Expr)]
emitExamples _ [] = return []
emitExamples target (example : examples) = do
  example <- emitExample target example
  examples <- emitExamples target examples
  return (example : examples)

-- emitMatchCase :: PyTarget -> ([Tao.Pattern], Tao.Expr) -> Emit (Pattern, Maybe Expr, [Statement])
-- emitMatchCase target (ps, b) = do
--   pats <- emitPatterns target ps
--   body <- emitBody target b
--   return (MatchSequence pats, Nothing, body)

-- emitMatchCases :: PyTarget -> [([Tao.Pattern], Tao.Expr)] -> Emit [(Pattern, Maybe Expr, [Statement])]
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
-- emitPattern _ (Tao.PInt i) = return (MatchValue (Integer i))
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

emitBody :: PyTarget -> Tao.Expr -> Emit [Statement]
emitBody target a = Emit $
  \ctx -> do
    let (expr, ctx') = apply (emitExpr target a) ctx {locals = []}
    (ctx'.locals ++ [Return expr], ctx' {locals = ctx.locals})

--- Pretty printing layouts ---

layoutModule :: Module -> PP.Layout
layoutModule Module {body} = PP.join [PP.Text "\n"] (map layoutStmt body)

layoutStmt :: Statement -> PP.Layout
layoutStmt (Import name alias) = case alias of
  Just alias -> [PP.Text $ "import " ++ name ++ " as " ++ alias]
  Nothing -> [PP.Text $ "import " ++ name]
layoutStmt def@FunctionDef {} = do
  PP.Text ("def " ++ def.name)
    : layoutTuple (map layoutFunctionArg def.args)
    ++ maybe [] (\t -> PP.Text " -> " : layoutExpr t) def.returns
    -- ++ [PP.Text ":", PP.Indent (PP.Text "\n" : maybe [] layoutDocString def.docs ++ concatMap layoutStmt def.body)]
    ++ [PP.Text ":\n"]
layoutStmt def@ClassDef {} = do
  PP.Text ("class " ++ def.name)
    : case def.bases of
      [] -> []
      bases -> layoutTuple (map layoutExpr bases)
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutStmt def.body)]
layoutStmt (Return expr) =
  [ PP.Text "return ",
    PP.Or
      (layoutExpr expr)
      [ PP.Text "(",
        PP.Indent (PP.Text "\n" : layoutExpr expr),
        PP.Text "\n)"
      ]
  ]
layoutStmt (Match arg cases) = do
  let layoutArg (Tuple [arg]) = layoutExpr arg
      layoutArg arg = layoutExpr arg
  let layoutCase' (pat, guard, body) =
        PP.Text "case "
          : layoutPattern pat
          ++ maybe [] (\e -> PP.Text " if " : layoutExpr e) guard
          ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutStmt body), PP.Text "\n"]
  let layoutCase (MatchSequence [pat], guard, body) = layoutCase' (pat, guard, body)
      layoutCase (pat, guard, body) = layoutCase' (pat, guard, body)
  PP.Text "match "
    : layoutArg arg
    ++ [PP.Text ":", PP.Indent (PP.Text "\n" : concatMap layoutCase cases)]
layoutStmt (Raise exc from) =
  PP.Text "raise "
    : layoutExpr exc
    ++ maybe [] (\a -> PP.Text " from " : layoutExpr a) from
    ++ [PP.Text "\n"]
layoutStmt stmt = error $ "TODO: layoutStmt: " ++ show stmt

-- layoutDocString :: DocString -> PP.Layout
-- layoutDocString docs = do
--   [PP.Text ("'''" ++ docs.description ++ "\n"), PP.Text "'''\n"]

layoutExample :: (Expr, Expr) -> PP.Layout
layoutExample (prompt, result) =
  PP.Text ">>> "
    : layoutExpr prompt
    ++ [PP.Text "\n"]
    ++ layoutExpr result
    ++ [PP.Text "\n"]

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
layoutPattern (MatchMeta [] pat) = layoutPattern pat
layoutPattern (MatchMeta (m : meta) pat) = case m of
  _ -> layoutPattern (MatchMeta meta pat)
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
layoutExpr (Meta [] a) = layoutExpr a
layoutExpr (Meta (m : meta) a) = case m of
  _ -> layoutExpr a
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
      [PP.Indent (PP.Text "\n" : PP.join [PP.Text ",\n"] items), PP.Text ",\n"],
    PP.Text close
  ]