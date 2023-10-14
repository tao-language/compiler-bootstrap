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
    start :: !(Int, Int),
    end :: !(Int, Int),
    docs :: !DocString,
    comments :: ![String],
    commentsTrailing :: !String
  }
  deriving (Eq, Show)

tok :: a -> Token a
tok x =
  Token
    { value = x,
      start = (1, 1),
      end = (1, 1),
      docs = newDocString,
      comments = [],
      commentsTrailing = ""
    }

instance Functor Token where
  fmap :: (a -> b) -> Token a -> Token b
  -- fmap f x = x {value = VarP x.value}
  -- But GHC complains it's ambiguous! So the verbose way it is
  fmap f x =
    Token
      { value = f x.value,
        start = x.start,
        end = x.end,
        docs = x.docs,
        comments = x.comments,
        commentsTrailing = x.commentsTrailing
      }

data DocString = DocString
  { public :: !Bool,
    description :: !String
  }
  deriving (Eq, Show)

newDocString :: DocString
newDocString = DocString {public = False, description = ""}

data Definition
  = Def
      { type' :: !(Maybe (Token Type)),
        name :: !(Token String),
        value :: !(Token Expression)
      }
  | Unpack
      { types :: ![(Token String, Token Type)],
        pattern :: !(Token Pattern),
        value :: !(Token Expression)
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

type Name = Token String

type Pattern = Token PatternAtom

data PatternAtom
  = AnyP
  | KndP
  | IntTP
  | NumTP
  | IntP !Int
  | TagP !String
  | VarP !String
  | FunP !Pattern !Pattern
  | AppP !Pattern !Pattern
  | RecP ![(Name, Pattern)]
  deriving (Eq, Show)

type Expression = Token ExpressionAtom

data ExpressionAtom
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Tag !String
  | Var !String
  | Ann !Expression !Type
  | Match ![([Pattern], Expression)]
  | Let ![Definition] !Expression
  | Fun !Expression !Expression
  | Or !Expression !Expression
  | App !Expression !Expression
  | Rec ![(Name, Expression)]
  | Typ !Name ![Expression] ![(Name, Type)]
  | Eq !Expression !Expression
  | Lt !Expression !Expression
  | Add !Expression !Expression
  | Sub !Expression !Expression
  | Mul !Expression !Expression
  | Pow !Expression !Expression
  deriving (Eq, Show)

data Type
  = For ![Name] !Expression
  deriving (Eq, Show)
