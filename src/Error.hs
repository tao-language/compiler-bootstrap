{-# LANGUAGE NamedFieldPuns #-}

module Error where

import Data.List (intercalate)
import Parser (State (..))

-- https://package.elm-lang.org/packages/elm-in-elm/compiler/latest/Elm.Compiler.Error
-- https://github.com/elm-in-elm/compiler/blob/master/src/Elm/Compiler/Error.elm
data Error
  = SyntaxError !SyntaxError
  | ParseError !ParseError
  | DesugarError !DesugarError
  | TypeError !TypeError
  | CompileError !CompileError
  deriving (Eq)

data SyntaxError
  = TODO1
  deriving (Eq, Show)

data ParseError
  = TODO2
  deriving (Eq, Show)

data DesugarError
  = TODO3
  deriving (Eq, Show)

data TypeError
  = TODO4
  deriving (Eq, Show)

data CompileError
  = TODO5
  deriving (Eq, Show)

instance Show Error where
  show (SyntaxError err) = show err
  show (DesugarError err) = show err
  show (TypeError err) = show err
  show (CompileError err) = show err

-- instance Show SyntaxError where
--   show

location :: State -> String
location (State {name, row, col}) = intercalate ":" [name, show row, show col]
