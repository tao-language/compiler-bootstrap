module Error where

import Data.Function ((&))
import Data.List (intercalate)
import Location (Location (..), Position (..), Range (..))
import Stdlib (pad, slice)

-- https://package.elm-lang.org/packages/elm-in-elm/compiler/latest/Elm.Compiler.Error
-- https://github.com/elm-in-elm/compiler/blob/master/src/Elm/Compiler/Error.elm
-- https://github.com/gleam-lang/gleam/blob/main/compiler-core/src/error.rs

data Error a
  = SyntaxError (Location, String, String, String) -- (loc, committed, expected, got)
  | TypeError (Location, TypeError a)
  | CaseError (Location, CaseError a)
  | RuntimeError (Location, RuntimeError a)
  deriving (Eq, Show)

-- instance (Show a) => Show (Error a) where
--   show :: Error a -> String
--   show (SyntaxError (loc, expected, got)) = "[syntax error]" ++ loc.filename ++ ":" ++ show loc.range ++ ": expected " ++ expected ++ ", got " ++ show got
--   show (TypeError e) = "[type error]" ++ show e
--   show (CaseError e) = "[case error]" ++ show e
--   show (RuntimeError e) = "[runtime error]" ++ show e

data TypeError a
  = OccursError String a
  | TypeMismatch a a
  | TypeInferError a
  | TypeCheckError a a
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
    SyntaxError e -> SyntaxError e
    TypeError (loc, e) -> case e of
      OccursError x a -> occursError loc x (f a)
      TypeMismatch a b -> typeMismatch loc (f a) (f b)
      NotAFunction a t -> notAFunction loc (f a) (f t)
      UndefinedVar x -> undefinedVar loc x
    CaseError (loc, e) -> case e of
      MissingCases cases -> missingCases loc (map f cases)
      RedundantCases cases -> redundantCases loc (map f cases)
    RuntimeError (loc, e) -> case e of
      UnhandledCase a b -> unhandledCase loc (f a) (f b)
      CannotApply a b -> cannotApply loc (f a) (f b)
      CustomError a -> customError loc (f a)

mainExpr :: Error a -> Maybe a
mainExpr = \case
  SyntaxError e -> Nothing
  TypeError (loc, e) -> case e of
    OccursError x a -> Just a
    TypeMismatch a b -> Just b
    NotAFunction a t -> Just a
    UndefinedVar x -> Nothing
  CaseError (loc, e) -> case e of
    MissingCases cases -> Nothing
    RedundantCases cases -> Nothing
  RuntimeError (loc, e) -> case e of
    UnhandledCase a b -> Just a
    CannotApply a b -> Just a
    CustomError a -> Just a

occursError :: Location -> String -> a -> Error a
occursError loc x a = TypeError (loc, OccursError x a)

typeMismatch :: Location -> a -> a -> Error a
typeMismatch loc a b = TypeError (loc, TypeMismatch a b)

typeInferError :: Location -> a -> Error a
typeInferError loc a = TypeError (loc, TypeInferError a)

typeCheckError :: Location -> a -> a -> Error a
typeCheckError loc a b = TypeError (loc, TypeCheckError a b)

notAFunction :: Location -> a -> a -> Error a
notAFunction loc a t = TypeError (loc, NotAFunction a t)

undefinedVar :: Location -> String -> Error a
undefinedVar loc x = TypeError (loc, UndefinedVar x)

missingCases :: Location -> [a] -> Error a
missingCases loc cases = CaseError (loc, MissingCases cases)

redundantCases :: Location -> [a] -> Error a
redundantCases loc cases = CaseError (loc, RedundantCases cases)

unhandledCase :: Location -> a -> a -> Error a
unhandledCase loc a b = RuntimeError (loc, UnhandledCase a b)

cannotApply :: Location -> a -> a -> Error a
cannotApply loc a b = RuntimeError (loc, CannotApply a b)

customError :: Location -> a -> Error a
customError loc a = RuntimeError (loc, CustomError a)

summary :: (Show a) => Error a -> String
summary = \case
  SyntaxError _ -> "Syntax error"
  TypeError (loc, e) -> case e of
    OccursError {} -> "Occurs error"
    TypeMismatch {} -> "Type mismatch"
    NotAFunction {} -> "Not a function"
    UndefinedVar {} -> "Undefined variable"
  CaseError _ -> "Case error"
  RuntimeError (loc, e) -> case e of
    UnhandledCase {} -> "Unhandled error"
    CannotApply {} -> "Cannot apply"
    CustomError {} -> "User defined error"

description :: (Show a) => Error a -> String
description = \case
  TypeError (loc, e) -> case e of
    OccursError x a -> show e
    TypeMismatch got expected ->
      "This expression is of type:\n  "
        ++ show got
        ++ "\n\nI was expecting it to be:\n  "
        ++ show expected
    NotAFunction a t -> show e
    UndefinedVar x -> show e
  RuntimeError e -> ""
  e -> "TODO: description"

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
display err = do
  -- putStrLn (replicate 60 '-')
  -- putStrLn ("🛑 " ++ summary err)
  -- case mloc of
  --   Nothing -> return ()
  --   Just loc -> do
  --     src <- readFile loc.filename
  --     putStrLn ""
  --     putStrLn (snippet loc src)
  -- case description err of
  --   "" -> return ()
  --   description -> do
  --     putStrLn ""
  --     putStrLn description
  -- case suggestion err of
  --   "" -> return ()
  --   suggestion -> do
  --     putStrLn ""
  --     putStrLn suggestion
  -- case docsUrl err of
  --   "" -> return ()
  --   url -> do
  --     putStrLn ""
  --     putStrLn "For more information about this error, see:"
  --     putStrLn ("  " ++ url)
  -- putStrLn ""
  print err
