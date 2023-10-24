{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Python where

import Core (Metadata (..))
import Tao (DocString (..))
import qualified Tao

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
  | True -- True
  | False -- True
  | Integer !Int -- 42
  | Float !Double -- 3.14
  | Imaginary !Double -- 3.14j
  | List ![Expr] -- [x, y, z]
  | Tuple ![Expr] -- (x, y, z)
  | Set ![Expr] -- {x, y, z}
  | Dict ![(Expr, Expr)] -- {x: 1, y: 2, z: 3}
  | Bytes !String -- b'hello'
  | String !String -- 'Hello'
  | FString ![FormattedValue] -- f"hello {x}"
  | UnaryOp !UnaryOp !Expr -- not x
  | BinOp !Expr !BinOp !Expr -- x + y
  | BoolOp !Expr !BoolOp !Expr -- x and y
  | Compare !Expr !Compare !Expr -- x == y
  | Lambda ![String] !Expr -- lambda x, y: z
  | Call !Expr ![Expr] ![(String, Expr)] -- func(*args, **kwargs)
  | IfExp !Expr !Expr !Expr -- a if b else c
  | Attribute !Expr !String -- x.y
  | NamedExpr !Expr !Expr -- x := y
  | Subscript !Expr !Expr -- x[y]
  | Slice !Expr !Expr -- x:y
  | ListComp !Expr !Expr !Expr ![Expr] -- [x for x in xs (if y)*]
  | SetComp !Expr !Expr !Expr ![Expr] -- {x for x in xs (if y)*}
  | GeneratorExp !Expr !Expr !Expr ![Expr] -- (x for x in xs (if y)*)
  | DictComp !Expr !Expr !Expr ![Expr] -- {x: x for x in xs (if y)*}
  deriving (Eq, Show)

-- https://docs.python.org/3/library/ast.html#ast.FormattedValue
data FormattedValue
  = Str !String
  | Val !Expr
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
  | NotEq -- x != y
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
  = Assign ![Expr] !Expr -- x = y = z
  | AnnAssign !Expr !Expr !(Maybe Expr) -- x: T = y
  | AugAssign !Expr !BinOp !Expr -- x += y
  | Raise !Expr !(Maybe Expr) -- raise x [from y]
  | Assert !Expr !Expr -- assert x, y
  | Delete ![Expr] -- del x, y
  | Pass -- pass
  | TypeAlias !String ![TypeParam] !Expr -- type Alias = int
  | Import !String !(Maybe String) -- import mod [as m]
  | ImportFrom !String ![(String, Maybe String)] -- from mod import x, y as z
  | Break -- break
  | Continue -- continue
  | Match !Expr ![(Pattern, Maybe Expr, [Statement])]
  | Return !Expr
  | Yield !Expr
  | YieldFrom !Expr
  | Global ![String]
  | Nonlocal ![String]
  | Await !Expr
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
        args :: [(String, Maybe Expr, Maybe Expr)], -- arg: Type = default
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
  = MatchValue !Expr -- case 1
  | MatchSequence ![Pattern] -- case [p, q]
  | MatchStar !String -- case [p, *ps]
  | MatchMapping ![(String, Pattern)] !(Maybe String) -- case {p: q, [, **kvs]}
  | MatchClass !String ![Pattern] ![(String, Pattern)] -- ClassName(p, x=q)
  | MatchAs !(Maybe Pattern) !String -- case p as x
  | MatchOr ![Pattern] -- case p | q
  deriving (Eq, Show)

--- Type parameters ---
-- https://docs.python.org/3/library/ast.html#ast-type-params
data TypeParam
  = TypeVar !String -- T[a]
  | TypeVarTuple !String -- T[*ts]
  | ParamSpec !String -- T[**ts]
  deriving (Eq, Show)

module' :: Tao.Module -> Python.Module
module' mod = do
  Module
    { name = mod.name,
      docs = mod.docs,
      body = map statement mod.body
    }

statement :: Tao.Statement -> Python.Statement
statement (Tao.LetDef {docs, name, type', rules, meta}) =
  error "TODO: LetDef"
statement (Tao.Unpack {docs, types, pattern, value, meta}) =
  error "TODO: Unpack"
statement (Tao.TypeDef {docs, name, args, alts, meta}) =
  error "TODO: TypeDef"
statement (Tao.Import {path, name, exposing, meta}) =
  error "TODO: TypeDef"
statement (Tao.Prompt {description, expression, result, meta}) =
  error "TODO: Prompt"
