module Error where

import Data.Function ((&))
import Data.List (intercalate)
import Stdlib (pad, slice)

-- https://package.elm-lang.org/packages/elm-in-elm/compiler/latest/Elm.Compiler.Error
-- https://github.com/elm-in-elm/compiler/blob/master/src/Elm/Compiler/Error.elm
-- https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/error.rs

data Position = Pos
  { row :: Int,
    col :: Int
  }
  deriving (Eq, Show)

data Location = Location
  { filename :: FilePath,
    start :: Position,
    end :: Position
  }
  deriving (Eq)

data Error a
  = Error Location (ErrorType a)
  deriving (Eq, Show)

data ErrorType a
  = SyntaxError
  | TypeError (TypeError a)
  | CaseError (CaseError a)
  deriving (Eq, Show)

data TypeError a
  = OccursError String a
  | TypeMismatch a a
  | NotAFunction a a
  | UndefinedVar String
  -- MissingArgs
  -- ExtraArgs
  -- ArgsMismatch
  deriving (Eq, Show)

data CaseError a
  = MissingCases [a]
  | RedundantCases [a]
  deriving (Eq, Show)

instance Show Location where
  show :: Location -> String
  show (Location filename start _) =
    filename ++ ":" ++ show start.row ++ ":" ++ show start.col

summary :: ErrorType a -> String
summary = \case
  SyntaxError -> "Syntax Error"
  _ -> ""

description :: ErrorType a -> String
description = \case
  _ -> ""

suggestion :: ErrorType a -> String
suggestion = \case
  _ -> ""

docsUrl :: ErrorType a -> String
docsUrl = \case
  _ -> ""

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
display (Error loc e) = do
  src <- readFile loc.filename
  putStrLn (replicate 60 '-')
  putStrLn ("🛑 " ++ summary e)
  case description e of
    "" -> return ()
    description -> do
      putStrLn ""
      putStrLn description
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
