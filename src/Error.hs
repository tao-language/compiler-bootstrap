module Error where

import Data.Function ((&))
import Data.List (intercalate)
import Location (Location (..), Position (..))
import Stdlib (pad, slice)

-- https://package.elm-lang.org/packages/elm-in-elm/compiler/latest/Elm.Compiler.Error
-- https://github.com/elm-in-elm/compiler/blob/master/src/Elm/Compiler/Error.elm
-- https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/error.rs

data Error a
  = SyntaxError SyntaxError
  | TypeError (TypeError a)
  | CaseError (CaseError a)
  deriving (Eq, Show)

newtype SyntaxError
  = UnexpectedChar Location
  deriving (Eq, Show)

data TypeError a
  = OccursError (Maybe Location) String a
  | TypeMismatch (Maybe Location) a a
  | NotAFunction (Maybe Location) a a
  | UndefinedVar (Maybe Location) String
  -- MissingArgs
  -- ExtraArgs
  -- ArgsMismatch
  deriving (Eq, Show)

data CaseError a
  = MissingCases Location [a]
  | RedundantCases Location [a]
  deriving (Eq, Show)

instance Show Location where
  show :: Location -> String
  show (Location filename start _) =
    filename ++ ":" ++ show start.row ++ ":" ++ show start.col

summary :: Error a -> String
summary = \case
  SyntaxError _ -> "Syntax Error"
  _ -> ""

description :: Error a -> String
description = \case
  _ -> ""

suggestion :: Error a -> String
suggestion = \case
  _ -> ""

docsUrl :: Error a -> String
docsUrl = \case
  _ -> ""

class LocationOf a where
  locationOf :: a -> Maybe Location

instance LocationOf (Error a) where
  locationOf :: Error a -> Maybe Location
  locationOf = \case
    SyntaxError e -> locationOf e
    TypeError e -> locationOf e

instance LocationOf SyntaxError where
  locationOf :: SyntaxError -> Maybe Location
  locationOf = \case
    UnexpectedChar loc -> Just loc

instance LocationOf (TypeError a) where
  locationOf :: TypeError a -> Maybe Location
  locationOf = \case
    OccursError loc _ _ -> loc
    TypeMismatch loc _ _ -> loc
    NotAFunction loc _ _ -> loc
    UndefinedVar loc _ -> loc

-- MissingArgs
-- ExtraArgs
-- ArgsMismatch

instance LocationOf (CaseError a) where
  locationOf :: CaseError a -> Maybe Location
  locationOf = \case
    MissingCases loc _ -> Just loc
    RedundantCases loc _ -> Just loc

snippet :: Location -> String -> String
snippet loc src = do
  let (before, after) = (3, 3)
  let divider = "| "
  let rowMark = "* "
  let colMark = "^"
  let start = max 1 (loc.start.row - before)
  let padding = length (rowMark ++ show (loc.end.row + after))
  let showLine x line = pad padding x ++ divider ++ line
  let linesBefore =
        lines src
          & slice start loc.start.row
          & zipWith (showLine . show) [start ..]
  let highlight =
        lines src
          & slice loc.start.row (loc.start.row + 1)
          & map (showLine (rowMark ++ show loc.start.row))
          & (++ [replicate (loc.start.col + padding + length divider - 1) ' ' ++ colMark])
  let linesAfter =
        lines src
          & slice (loc.start.row + 1) (loc.start.row + after + 1)
          & zipWith (showLine . show) [loc.start.row + 1 ..]
  intercalate
    "\n"
    ( (loc.filename ++ ":" ++ show loc.start.row ++ ":" ++ show loc.start.col)
        : linesBefore
        ++ highlight
        ++ linesAfter
    )

display :: Error a -> IO ()
display e = do
  putStrLn (replicate 60 '-')
  putStrLn ("🛑 " ++ summary e)
  case description e of
    "" -> return ()
    description -> do
      putStrLn ""
      putStrLn description
  case locationOf e of
    Nothing -> return ()
    Just loc -> do
      src <- readFile loc.filename
      putStrLn ""
      putStrLn (snippet loc src)
  case suggestion e of
    "" -> return ()
    suggestion -> do
      putStrLn ""
      putStrLn suggestion
  case docsUrl e of
    "" -> return ()
    url -> do
      putStrLn ""
      putStrLn "For more information about this error, see:"
      putStrLn ("  " ++ url)
  putStrLn ""
