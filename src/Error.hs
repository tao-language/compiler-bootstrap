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
  = MissingCases (Maybe Location) [a]
  | RedundantCases (Maybe Location) [a]
  deriving (Eq, Show)

summary :: Error a -> String
summary = \case
  SyntaxError _ -> "Syntax Error"
  TypeError _ -> "Type Error"
  CaseError _ -> "Case Error"

description :: Error a -> String
description = \case
  _ -> ""

suggestion :: Error a -> String
suggestion = \case
  _ -> ""

docsUrl :: Error a -> String
docsUrl = \case
  _ -> ""

location :: Error a -> Maybe Location
location = \case
  SyntaxError e -> case e of
    UnexpectedChar loc -> Just loc
  TypeError e -> case e of
    OccursError loc _ _ -> loc
    TypeMismatch loc _ _ -> loc
    NotAFunction loc _ _ -> loc
    UndefinedVar loc _ -> loc
  -- MissingArgs
  -- ExtraArgs
  -- ArgsMismatch
  CaseError e -> case e of
    MissingCases loc _ -> loc
    RedundantCases loc _ -> loc

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
  case location e of
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
