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
  | RuntimeError (RuntimeError a)
  deriving (Eq)

instance (Show a) => Show (Error a) where
  show :: Error a -> String
  show (SyntaxError (loc, committed, expected, got)) = "syntax-error[" ++ show loc ++ ": [" ++ committed ++ "] expected " ++ expected ++ ", got " ++ show got ++ "]"
  show (TypeError (loc, e)) = "type-error[" ++ show loc ++ ": " ++ show e ++ "]"
  show (CaseError (loc, e)) = "case-error[" ++ show loc ++ ": " ++ show e ++ "]"
  show (RuntimeError e) = "runtime-error[" ++ show e ++ "]"

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
    RuntimeError e -> case e of
      UnhandledCase a b -> unhandledCase (f a) (f b)
      CannotApply a b -> cannotApply (f a) (f b)
      CustomError a -> customError (f a)

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
  RuntimeError e -> case e of
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

unhandledCase :: a -> a -> Error a
unhandledCase a b = RuntimeError (UnhandledCase a b)

cannotApply :: a -> a -> Error a
cannotApply a b = RuntimeError (CannotApply a b)

customError :: a -> Error a
customError a = RuntimeError (CustomError a)

location :: Error a -> Maybe Location
location = \case
  SyntaxError (loc, _, _, _) -> Just loc
  TypeError (loc, _) -> Just loc
  CaseError (loc, _) -> Just loc
  RuntimeError _ -> Nothing

title :: (Show a) => Error a -> String
title = \case
  SyntaxError _ -> "Syntax error"
  TypeError (loc, e) -> case e of
    OccursError {} -> "Occurs error"
    TypeMismatch {} -> "Type mismatch"
    NotAFunction {} -> "Not a function"
    UndefinedVar {} -> "Undefined variable"
  CaseError _ -> "Case error"
  RuntimeError e -> case e of
    UnhandledCase {} -> "Unhandled error"
    CannotApply {} -> "Cannot apply"
    CustomError {} -> "User defined error"

summary :: (Show a) => Error a -> String
summary = \case
  SyntaxError (loc, committed, expected, got) -> do
    let context = case committed of
          "" -> ""
          committed -> " while parsing " ++ show committed
    "Expected " ++ expected ++ context ++ "."
  e -> "TODO: summary"

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
    ( (show (loc {range = loc.range {end = loc.range.start}}))
        : linesBefore
        ++ highlight
        ++ linesAfter
    )

display :: (Show a) => Error a -> IO ()
display err = do
  putStrLn ("==== " ++ title err ++ " " ++ replicate (60 - length (title err)) '=')
  putStrLn ""
  putStrLn ("❌ " ++ summary err)
  putStrLn ""
  case location err of
    Nothing -> return ()
    Just loc -> do
      src <- readFile loc.filename
      putStrLn (snippet loc src)
      putStrLn ""
  case description err of
    "" -> return ()
    description -> do
      putStrLn description
      putStrLn ""
  case suggestion err of
    "" -> return ()
    suggestion -> do
      putStrLn suggestion
      putStrLn ""
  case docsUrl err of
    "" -> return ()
    url -> do
      putStrLn "For more information about this error, see:"
      putStrLn ("  " ++ url)
      putStrLn ""
