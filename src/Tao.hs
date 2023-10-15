{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
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
  { value :: a,
    row :: !Int,
    col :: !Int,
    comments :: ![String],
    trailingComments :: ![String]
  }
  deriving (Eq, Show)

type Token' = Token ()

type TokenStr = Token String

type TokenInt = Token Int

newToken :: a -> Token a
newToken x =
  Token
    { value = x,
      row = 1,
      col = 1,
      comments = [],
      trailingComments = []
    }

instance Functor Token where
  fmap :: (a -> b) -> Token a -> Token b
  -- fmap f x = x {value = VarP x.value}
  -- But GHC complains it's ambiguous! So the verbose way it is
  fmap f x =
    Token
      { value = f x.value,
        row = x.row,
        col = x.col,
        comments = x.comments,
        trailingComments = x.trailingComments
      }

data Pattern
  = AnyP !Token'
  | KndP !Token'
  | IntTP !Token'
  | NumTP !Token'
  | IntP !TokenInt
  | TagP !TokenStr
  | VarP !TokenStr
  | TupleP !Token' ![Pattern] !Token'
  | RecordP !Token' ![(TokenStr, Pattern)] !Token'
  | FunP !Pattern !Token' !Pattern
  | AppP !Pattern !Token' !Pattern
  deriving (Eq, Show)

-- type Expression = Token ExpressionAtom

-- data ExpressionAtom
--   = Knd
--   | IntT
--   | NumT
--   | Int !Int
--   | Num !Double
--   | Tag !String
--   | Var !String
--   | Ann !Expression !Type
--   | Lam ![Pattern] !Expression
--   | Let ![Definition] !Expression
--   | Fun !Expression !Expression
--   | Or !Expression !Expression
--   | App !Expression !Expression
--   | Rec ![(Name, Expression)]
--   | Typ !Name ![Expression] ![(Name, Type)]
--   | Eq !Expression !Expression
--   | Lt !Expression !Expression
--   | Add !Expression !Expression
--   | Sub !Expression !Expression
--   | Mul !Expression !Expression
--   | Pow !Expression !Expression
--   deriving (Eq, Show)

-- data Type
--   = For ![Name] !Expression
--   deriving (Eq, Show)

-- ann :: Expression -> Expression -> ExpressionAtom
-- ann a t = Ann a (For [] t)

data DocString = DocString
  { public :: !Bool,
    description :: !String
  }
  deriving (Eq, Show)

newDocString :: DocString
newDocString = DocString {public = False, description = ""}

-- data Definition
--   = Def
--       { docs :: DocString,
--         type' :: !(Maybe (Token Type)),
--         name :: !(Token String),
--         value :: !(Token Expression)
--       }
--   | Unpack
--       { docs :: DocString,
--         types :: ![(Token String, Token Type)],
--         pattern :: !(Token Pattern),
--         value :: !(Token Expression)
--       }
--   deriving (Eq, Show)

data SourceFile = SourceFile
  { imports :: ![String]
  -- , definitions :: ![Definition]
  -- , expressions :: ![Token Expression]
  }
  deriving (Eq, Show)

data Module = Module
  {
  }
  deriving (Eq, Show)

type Name = Token String
