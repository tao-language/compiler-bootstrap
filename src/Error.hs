{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Error where

import Data.List (intercalate)
import Parser (State (..))

-- https://package.elm-lang.org/packages/elm-in-elm/compiler/latest/Elm.Compiler.Error
-- https://github.com/elm-in-elm/compiler/blob/master/src/Elm/Compiler/Error.elm
data Error
  = ParserError ![SyntaxError]
  | DesugarError !DesugarError
  | TypeError !TypeError
  | EmitError !EmitError
  deriving (Eq)

data SyntaxError = SyntaxError
  { expected :: !SyntaxErrorToken,
    name :: !String,
    row :: !Int,
    col :: !Int
  }
  deriving (Eq, Show)

data SyntaxErrorToken
  = DefinitionError
  | NameError
  | PatternError
  deriving (Eq, Show)

data DesugarError
  = TODO3
  deriving (Eq, Show)

data TypeError
  = TODO4
  deriving (Eq, Show)

data EmitError
  = TODO5
  deriving (Eq, Show)

instance Show Error where
  show :: Error -> String
  show (ParserError stack) =
    (show . intercalate "\n")
      [ "Syntax error",
        show stack
      ]
  show (DesugarError err) = show err
  show (TypeError err) = show err
  show (EmitError err) = show err

-- instance Show SyntaxError where
--   show
