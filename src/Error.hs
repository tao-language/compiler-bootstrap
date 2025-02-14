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
  | NameError (NameError a)
  | TypeError (TypeError a)
  | CaseError (CaseError a)
  deriving (Eq, Show)

data NameError a
  = NameNotFound String
  | NameMismatch String [a]
  deriving (Eq, Show)

data TypeError a
  = OccursError String a
  | TypeMismatch a a
  | NotAFunction a a
  | UndefinedVar String
  deriving (Eq, Show)

data CaseError a
  = MissingCases [a]
  | RedundantCases [a]
  deriving (Eq, Show)

data ErrorDetails = ErrorDetails
  { summary :: String,
    description :: String,
    suggestion :: String
  }
  deriving (Eq, Show)

instance Show Location where
  show :: Location -> String
  show (Location filename start _) =
    filename ++ ":" ++ show start.row ++ ":" ++ show start.col

details :: ErrorType a -> ErrorDetails
details = \case
  SyntaxError ->
    ErrorDetails
      { summary = "Syntax error",
        description = "Description",
        suggestion = "Suggestion"
      }

display :: Error a -> IO ()
display (Error loc e) = do
  let ErrorDetails {summary, description, suggestion} = details e
  src <- readFile loc.filename
  putStrLn (replicate 60 '-')
  putStrLn ("🛑 " ++ summary)
  putStrLn ""
  putStrLn description
  putStrLn ""
  putStrLn (snippet loc src)
  putStrLn ""
  putStrLn suggestion

-- intercalate
-- "\n"
-- [ "🛑 " ++ show e,
--   "",
--   snippet loc 3 3 src,
--   ""
-- ]

snippet :: Location -> String -> String
snippet loc src = do
  let (before, after) = (3, 3)
  let divider = "| "
  let rowMark = "* "
  let colMark = "^"
  let start = max 1 (loc.start.row - before)
  let padding = length (rowMark ++ show (loc.start.row + after))
  let showLine x line = pad padding x ++ divider ++ line
  let linesBefore =
        lines src
          & slice start loc.start.row
          & zipWith (showLine . show) [start ..]
  let highlight =
        lines src
          & slice loc.start.row (loc.start.row + 1)
          & map (showLine (rowMark ++ show loc.start.row))
          & (++ [replicate (loc.start.col + padding + length divider + 1) ' ' ++ colMark])
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
