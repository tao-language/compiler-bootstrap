{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Tao where

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

data Token a = Token
  { start :: !Pos,
    end :: !Pos,
    docs :: !DocString,
    comments :: ![String],
    commentsTrailing :: !String,
    value :: a
  }
  deriving (Eq, Show)

data Pos = Pos
  { row :: !Int,
    col :: !Int
  }
  deriving (Eq, Show)

-- newToken :: a -> Token a
-- newToken x = Token {
--   span = Span {name = "", }
-- }

data DocString = DocString
  { public :: !Bool,
    description :: !String
  }
  deriving (Eq, Show)

data Expression
  = Int !(Token Int)
  | Num !(Token Double)
  | Tag !(Token String)
  | Var !(Token String)
  | Ann !(Token Expression) !(Token Type)
  | Fun !(Token Expression) !(Token Expression)
  | Match ![([Token Pattern], Token Expression)]
  | Let ![Token Definition] !(Token Expression)
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
  = PAny !(Token ())
  | PInt !(Token Int)
  | PVar !(Token String)
  deriving (Eq, Show)

data Type
  = For ![Token String] !(Token Expression)
  deriving (Eq, Show)

data Definition
  = Def
      { type' :: !(Maybe (Token Type)),
        name :: !(Token String),
        expr :: !(Token Expression)
      }
  | Unpack
      { types :: ![(Token String, Token Type)],
        pattern :: !(Token Pattern),
        expr :: !(Token Expression)
      }
  deriving (Eq, Show)

data SourceFile = SourceFile
  { imports :: ![String],
    definitions :: ![Definition],
    expressions :: ![Token Expression]
  }
  deriving (Eq, Show)

data Module = Module
  {
  }
  deriving (Eq, Show)

-- app :: Token Expression -> [Token Expression] -> Token Expression
-- app = foldl App