{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

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
    path :: !String,
    row :: !Int,
    col :: !Int,
    len :: !Int,
    comments :: ![String],
    trailingComments :: ![String]
  }
  deriving (Eq, Show)

type Token' = Token ()

newToken :: a -> Token a
newToken x =
  Token
    { value = x,
      path = "",
      row = 1,
      col = 1,
      len = 0,
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
        path = x.path,
        row = x.row,
        col = x.col,
        len = x.len,
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
  | FunP !Token' !Pattern !Pattern
  | AppP !Token' !Pattern !Pattern
  | SyntaxErrorP !SyntaxErrorP
  deriving (Eq, Show)

data SyntaxErrorP
  = TuplePError !(Token String)
  | RecordPError !(Token String)
  deriving (Eq, Show)

data Expression
  = Knd !Token'
  | IntT !Token'
  | NumT !Token'
  | Int !(Token Int)
  | Num !(Token Double)
  | Tag !(Token String)
  | Var !(Token String)
  | Lambda ![Pattern] !Expression
  | Tuple !Token' ![Expression] !Token'
  | Record !Token' ![(Token String, Expression)] !Token'
  | Block ![Definition] !Expression
  | App !Token' !Expression !Expression
  | Fun !Token' !Expression !Expression
  | Or !Token' !Expression !Expression
  | Eq !Token' !Expression !Expression
  | Lt !Token' !Expression !Expression
  | Add !Token' !Expression !Expression
  | Sub !Token' !Expression !Expression
  | Mul !Token' !Expression !Expression
  | Pow !Token' !Expression !Expression
  | Ann !Expression !Type
  | SyntaxError !SyntaxErrorToken !(Token String)
  deriving (Eq, Show)

data SyntaxErrorToken
  = RecordError
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
  = LetDef
      { docs :: !(Maybe DocString),
        name :: !(Token String),
        type' :: !(Maybe Type),
        rules :: ![([Pattern], Expression)]
      }
  | Unpack
      { docs :: !(Maybe DocString),
        types :: ![(Token String, Type)],
        pattern :: !Pattern,
        value :: !Expression
      }
  | TypeDef
      { docs :: !(Maybe DocString),
        name :: !(Token String),
        args :: ![Expression],
        alts :: !(Token String, Type)
      }
  | Run
      { description :: !String,
        value :: !Expression,
        expected :: !(Maybe Expression)
      }
  deriving (Eq, Show)

data Import = Import
  { path :: !(Token String),
    name :: !(Token String),
    exposing :: ![Token String]
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
