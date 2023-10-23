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

data Expr
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Tag !String
  | Var !String
  | Lam !Pattern !Expr
  | Tuple ![Expr]
  | Record ![(String, Expr)]
  | Block ![Definition] !Expr
  | App !Expr !Expr
  | Fun !Expr !Expr
  | Or !Expr !Expr
  | Eq !Expr !Expr
  | Lt !Expr !Expr
  | Add !Expr !Expr
  | Sub !Expr !Expr
  | Mul !Expr !Expr
  | Pow !Expr !Expr
  | Ann !Expr !Type
  | Meta ![C.Metadata] !Expr
  deriving (Eq, Show)

data Type
  = For ![String] !Expr
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
        rules :: ![([Pattern], Expr)],
        meta :: [C.Metadata]
      }
  | Unpack
      { docs :: !(Maybe DocString),
        types :: ![(String, Type)],
        pattern :: !Pattern,
        value :: !Expr,
        meta :: [C.Metadata]
      }
  | TypeDef
      { docs :: !(Maybe DocString),
        name :: !String,
        args :: ![Expr],
        alts :: !(String, Type),
        meta :: [C.Metadata]
      }
  | Prompt
      { description :: !String,
        expression :: !Expr,
        result :: !(Maybe Expr),
        meta :: [C.Metadata]
      }
  deriving (Eq, Show)

data Import = Import
  { path :: !String,
    name :: !String,
    exposing :: ![String]
  }
  deriving (Eq, Show)

data Source = Source
  { docs :: !(Maybe DocString),
    imports :: ![Import],
    definitions :: ![Definition]
  }
  deriving (Eq, Show)

data Module = Module
  { name :: !String,
    files :: ![(String, Source)]
  }
  deriving (Eq, Show)

data ParserContext
  = CDefinition
  deriving (Eq, Show)

fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

ann :: Expr -> Expr -> Expr
ann a t = Ann a (For [] t)

-- toCore :: Expr -> C.Expr
-- toCore (Knd tok) = C.Src (tok.path, tok.row, tok.col) C.Knd
