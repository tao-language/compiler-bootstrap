{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Tao where

import Parser (Span (..))

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

data Expression
  = Int !Int
  | Num !Double
  | Tag !String
  | Var !String
  | Ann !(Token Expression) !Type
  | Fun !(Token Expression) !(Token Expression)
  | Match ![([Pattern], Token Expression)]
  | Let ![Definition] !(Token Expression)
  | App !(Token Expression) !(Token Expression)
  | Or !(Token Expression) !(Token Expression)
  | If !(Token Expression) !(Token Expression)
  | Eq !(Token Expression) !(Token Expression)
  | Lt !(Token Expression) !(Token Expression)
  | Add !(Token Expression) !(Token Expression)
  | Sub !(Token Expression) !(Token Expression)
  | Mul !(Token Expression) !(Token Expression)
  | Pow !(Token Expression) !(Token Expression)
  deriving (Eq, Show)

data Pattern
  = PAny
  | PInt !Int
  | PVar !String
  deriving (Eq, Show)

data Type
  = For ![String] !(Token Expression)
  deriving (Eq, Show)

data Definition
  = Def
      { type' :: Maybe Type,
        name :: String,
        expr :: Token Expression
      }
  | Unpack
      { types :: [(String, Type)],
        pattern :: Pattern,
        expr :: Token Expression
      }
  deriving (Eq, Show)

data Token a = Token
  { span :: Span,
    docs :: DocString,
    comments :: [String],
    commentsTrailing :: String,
    value :: a
  }
  deriving (Eq, Show)

data DocString = DocString
  { public :: Bool,
    description :: String
  }
  deriving (Eq, Show)

data SourceFile = SourceFile
  { imports :: [String],
    definitions :: [Definition],
    expressions :: [Token Expression]
  }
  deriving (Eq, Show)

data Module = Module
  {
  }
  deriving (Eq, Show)

-- app :: Token Expression -> [Token Expression] -> Token Expression
-- app = foldl App