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
  | IntP !(Token Int)
  | TagP !(Token String)
  | VarP !(Token String)
  | TupleP !Token' ![Pattern] !Token'
  | RecordP !Token' ![(Token String, Pattern)] !Token'
  | FunP !Pattern !Token' !Pattern
  | AppP !Pattern !Token' !Pattern
  deriving (Eq, Show)

data Expression
  = Knd !Token'
  | IntT !Token'
  | NumT !Token'
  | Int !(Token Int)
  | Num !(Token Double)
  | Tag !(Token String)
  | Var !(Token String)
  | Ann !Expression !Type
  | Lam ![Pattern] !Expression
  | Rec ![(Token String, Expression)]
  | Typ !(Token String) ![Expression] ![(Token String, Type)]
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
  deriving (Eq, Show)

data Type
  = For ![Token String] !Expression
  deriving (Eq, Show)

data DocString = DocString
  { public :: !Bool,
    description :: !String
  }
  deriving (Eq, Show)

newDocString :: DocString
newDocString = DocString {public = False, description = ""}

data Definition
  = -- = Def
    --     { docs :: DocString,
    --       type' :: !(Maybe (Token Type)),
    --       name :: !(Token String),
    --       value :: !(Token Expression)
    --     }

    -- | Unpack
    --     { docs :: DocString,
    --       types :: ![(Token String, Token Type)],
    --       pattern :: !(Token Pattern),
    --       value :: !(Token Expression)
    --     }
    TODODef
  deriving (Eq, Show)

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
