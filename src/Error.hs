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
  = DesugarError !DesugarError
  | TypeError !TypeError
  | EmitError !EmitError
  deriving (Eq)

data DesugarError
  = DesugarErrorTODO
  deriving (Eq, Show)

data TypeError
  = TypeErrorTODO
  deriving (Eq, Show)

data EmitError
  = EmitErrorTODO
  deriving (Eq, Show)

instance Show Error where
  show :: Error -> String
  -- show (ParserError stack) =
  --   (show . intercalate "\n")
  --     [ "Syntax error",
  --       show stack
  --     ]
  show (DesugarError err) = show err
  show (TypeError err) = show err
  show (EmitError err) = show err

-- instance Show SyntaxError where
--   show
