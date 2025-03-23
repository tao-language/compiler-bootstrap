module Error where

import Data.Function ((&))
import Data.List (intercalate)
import Location (Location (..), Position (..), Range (..))
import Stdlib (pad, slice)

-- https://package.elm-lang.org/packages/elm-in-elm/compiler/latest/Elm.Compiler.Error
-- https://github.com/elm-in-elm/compiler/blob/master/src/Elm/Compiler/Error.elm
-- https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/error.rs

data Error a
  = SyntaxError SyntaxError
  | TypeError (TypeError a)
  | CaseError (CaseError a)
  | RuntimeError (RuntimeError a)
  deriving (Eq, Show)

newtype SyntaxError
  = UnexpectedChar Location
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

data RuntimeError a
  = UnhandledCase a a
  | CannotApply a a
  | CustomError a
  deriving (Eq, Show)

instance Functor Error where
  fmap :: (a -> b) -> Error a -> Error b
  fmap f = \case
    RuntimeError e -> case e of
      UnhandledCase a b -> unhandledCase (f a) (f b)
      CannotApply a b -> cannotApply (f a) (f b)
      CustomError a -> customError (f a)
    SyntaxError e -> case e of
      UnexpectedChar loc -> unexpectedChar loc
    TypeError e -> case e of
      OccursError x a -> occursError x (f a)
      TypeMismatch a b -> typeMismatch (f a) (f b)
      NotAFunction a t -> notAFunction (f a) (f t)
      UndefinedVar x -> undefinedVar x
    CaseError e -> case e of
      MissingCases cases -> missingCases (map f cases)
      RedundantCases cases -> redundantCases (map f cases)

unexpectedChar :: Location -> Error a
unexpectedChar loc = SyntaxError (UnexpectedChar loc)

occursError :: String -> a -> Error a
occursError x a = TypeError (OccursError x a)

typeMismatch :: a -> a -> Error a
typeMismatch a b = TypeError (TypeMismatch a b)

notAFunction :: a -> a -> Error a
notAFunction a t = TypeError (NotAFunction a t)

undefinedVar :: String -> Error a
undefinedVar x = TypeError (UndefinedVar x)

missingCases :: [a] -> Error a
missingCases cases = CaseError (MissingCases cases)

redundantCases :: [a] -> Error a
redundantCases cases = CaseError (RedundantCases cases)

unhandledCase :: a -> a -> Error a
unhandledCase a b = RuntimeError (UnhandledCase a b)

cannotApply :: a -> a -> Error a
cannotApply a b = RuntimeError (CannotApply a b)

customError :: a -> Error a
customError a = RuntimeError (CustomError a)

summary :: (Show a) => Error a -> String
summary = \case
  SyntaxError _ -> "Syntax Error"
  TypeError e -> case e of
    OccursError {} -> "Occurs Error"
    TypeMismatch {} -> "Type Mismatch"
    NotAFunction {} -> "Not a Function"
    UndefinedVar {} -> "Undefined Variable"
  CaseError _ -> "Case Error"

description :: (Show a) => Error a -> String
description = \case
  TypeError e -> case e of
    OccursError x a -> show e
    TypeMismatch got expected ->
      "This expression is of type:\n  "
        ++ show got
        ++ "\n\nI was expecting it to be:\n  "
        ++ show expected
    NotAFunction a t -> show e
    UndefinedVar x -> show e
  _ -> "TODO: description"

suggestion :: (Show a) => Error a -> String
suggestion = \case
  _ -> ""

docsUrl :: (Show a) => Error a -> String
docsUrl = \case
  _ -> ""

snippet :: Location -> String -> String
snippet loc src = do
  let (before, after) = (3, 3)
  let divider = "| "
  let rowMark = "* "
  let colMark = "^"
  let start = max 1 (loc.range.start.row - before)
  let padding = length (rowMark ++ show (loc.range.start.row + after))
  let showLine x line = pad padding x ++ divider ++ line
  let linesBefore =
        lines src
          & slice start loc.range.start.row
          & zipWith (showLine . show) [start ..]
  let highlight =
        lines src
          & slice loc.range.start.row (loc.range.start.row + 1)
          & map (showLine (rowMark ++ show loc.range.start.row))
          & (++ [replicate (loc.range.start.col + padding + length divider - 1) ' ' ++ colMark])
  let linesAfter =
        lines src
          & slice (loc.range.start.row + 1) (loc.range.start.row + after + 1)
          & zipWith (showLine . show) [loc.range.start.row + 1 ..]
  intercalate
    "\n"
    ( (loc.filename ++ ":" ++ show loc.range.start.row ++ ":" ++ show loc.range.start.col)
        : linesBefore
        ++ highlight
        ++ linesAfter
    )

display :: (Show a) => Error a -> IO ()
display e = do
  putStrLn (replicate 60 '-')
  putStrLn ("🛑 " ++ summary e)
  case Nothing of
    Nothing -> return ()
    Just loc -> do
      src <- readFile loc.filename
      putStrLn ""
      putStrLn (snippet loc src)
  case description e of
    "" -> return ()
    description -> do
      putStrLn ""
      putStrLn description
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
