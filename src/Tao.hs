{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Tao where

import qualified Core as C

{- TODO: syntax sugar
- Match
- Let
- Do
- Char
- Maybe
- Tuple
- Record
- Text
- List
- Set
- Dict
- From
- Until
- Range
- IfElse
- Vector
- Matrix
- Tensor
- List comprehension
- Set comprehension
- Dict comprehension
-}

data Pattern
  = PAny
  | PKnd
  | PIntT
  | PNumT
  | PInt !Int
  | PTag !String
  | PVar !String
  | PTuple ![Pattern]
  | PRecord ![(String, Pattern)]
  | PFun !Pattern !Pattern
  | PApp !Pattern !Pattern
  | PMeta ![C.Metadata] !Pattern
  deriving (Eq, Show)

data Expression
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Tag !String
  | Var !String
  | Lambda ![Pattern] !Expression
  | Tuple ![Expression]
  | Record ![(String, Expression)]
  | Block ![Definition] !Expression
  | App !Expression !Expression
  | Fun !Expression !Expression
  | Or !Expression !Expression
  | Eq !Expression !Expression
  | Lt !Expression !Expression
  | Add !Expression !Expression
  | Sub !Expression !Expression
  | Mul !Expression !Expression
  | Pow !Expression !Expression
  | Ann !Expression !Type
  | Meta ![C.Metadata] !Expression
  deriving (Eq, Show)

data Type
  = For ![String] !Expression
  deriving (Eq, Show)

data DocString = DocString
  { public :: !Bool,
    description :: !String
  }
  deriving (Eq, Show)

newDocString :: DocString
newDocString = DocString {public = False, description = ""}

data Definition
  = LetDef
      { docs :: !(Maybe DocString),
        name :: !String,
        type' :: !(Maybe Type),
        rules :: ![([Pattern], Expression)]
      }
  | Unpack
      { docs :: !(Maybe DocString),
        types :: ![(String, Type)],
        pattern :: !Pattern,
        value :: !Expression
      }
  | TypeDef
      { docs :: !(Maybe DocString),
        name :: !String,
        args :: ![Expression],
        alts :: !(String, Type)
      }
  | Run
      { description :: !String,
        value :: !Expression,
        expected :: !(Maybe Expression)
      }
  deriving (Eq, Show)

data Import = Import
  { path :: !String,
    name :: !String,
    exposing :: ![String]
  }
  deriving (Eq, Show)

data SourceFile = SourceFile
  { docs :: !(Maybe DocString),
    imports :: ![Import],
    definitions :: ![Definition]
  }
  deriving (Eq, Show)

data Module = Module
  { name :: !String,
    files :: ![(String, SourceFile)]
  }
  deriving (Eq, Show)

data ParserContext
  = CDefinition
  deriving (Eq, Show)

ann :: Expression -> Expression -> Expression
ann a t = Ann a (For [] t)

-- toCore :: Expression -> C.Expr
-- toCore (Knd tok) = C.Src (tok.path, tok.row, tok.col) C.Knd
