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

data Expression
  = Int !Int
  | Num !Double
  | Tag !String
  | Var !String
  | Ann !Expression !Type
  | Fun !Expression !Expression
  | Match ![([Pattern], Expression)]
  | Let ![Definition] !Expression
  | App !Expression !Expression
  | Or !Expression !Expression
  | If !Expression !Expression
  | Eq !Expression !Expression
  | Lt !Expression !Expression
  | Add !Expression !Expression
  | Sub !Expression !Expression
  | Mul !Expression !Expression
  | Pow !Expression !Expression
  deriving (Eq, Show)

data Pattern
  = PAny
  | PInt !Int
  | PVar !String
  deriving (Eq, Show)

data Type
  = For ![String] !Expression
  deriving (Eq, Show)

data Definition
  = Def
      { docs :: Maybe DocString,
        type' :: Maybe Type,
        name :: String,
        value :: Expression
      }
  | Unpack
      { docs :: Maybe DocString,
        types :: [(String, Type)],
        pattern :: Pattern,
        value :: Expression
      }
  deriving (Eq, Show)

data DocString = DocString
  { description :: String,
    args :: [(String, String)],
    returns :: String,
    public :: Bool
  }
  deriving (Eq, Show)

data Module = Module
  { imports :: [String],
    definitions :: [Definition],
    expressions :: [Expression]
  }
  deriving (Eq, Show)

app :: Expression -> [Expression] -> Expression
app = foldl App