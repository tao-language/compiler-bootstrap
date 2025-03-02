module Grammar where

import Data.Bifunctor (Bifunctor (second))
import Data.Function ((&))
import Location (Location (..), Range (Range))
import qualified Parser as P
import qualified PrettyPrint as PP

data Operator ctx a
  = Atom (P.Parser ctx a -> P.Parser ctx a) ((a -> PP.Layout) -> a -> Maybe PP.Layout)
  | Prefix Int (P.Parser ctx a -> P.Parser ctx a) ((a -> PP.Layout) -> a -> Maybe PP.Layout)
  | InfixL Int (a -> P.Parser ctx a -> P.Parser ctx a) ((a -> PP.Layout) -> (a -> PP.Layout) -> a -> Maybe PP.Layout)
  | InfixR Int (a -> P.Parser ctx a -> P.Parser ctx a) ((a -> PP.Layout) -> (a -> PP.Layout) -> a -> Maybe PP.Layout)

data Grammar ctx a
  = Grammar
  { group :: (String, String),
    operators :: [Operator ctx a]
  }

atom :: (a -> b) -> P.Parser ctx a -> ((b -> PP.Layout) -> b -> Maybe PP.Layout) -> Operator ctx b
atom f = atomLoc (const f)

atomLoc :: (Location -> a -> b) -> P.Parser ctx a -> ((b -> PP.Layout) -> b -> Maybe PP.Layout) -> Operator ctx b
atomLoc f parser layout = do
  let parser' _ = do
        start <- P.getState
        x <- parser
        end <- P.getState
        _ <- P.spaces
        let loc = Location start.filename (Range start.pos end.pos)
        return (f loc x)
  Atom parser' layout

prefix :: Int -> (a -> a) -> String -> (a -> Maybe (String, a)) -> Operator ctx a
prefix p f = prefixLoc p (const f)

prefixLoc :: Int -> (Location -> a -> a) -> String -> (a -> Maybe (String, a)) -> Operator ctx a
prefixLoc p f op match = do
  let parser' expr = do
        start <- P.getState
        _ <- P.text op
        end <- P.getState
        _ <- P.spaces
        let loc = Location start.filename (Range start.pos end.pos)
        f loc <$> expr
  let layout' rhs x = do
        (space, a) <- match x
        return (PP.Text (op ++ space) : rhs a)
  Prefix p parser' layout'

suffix :: Int -> (a -> a) -> String -> (a -> Maybe a) -> Operator ctx a
suffix p f op match = do
  let parser' x _expr = do
        _ <- P.text op
        _ <- P.spaces
        return (f x)
  let layout' lhs _ x = do
        a <- match x
        return (lhs a ++ [PP.Text op])
  InfixL p parser' layout'

infixL :: Int -> (a -> a -> a) -> String -> (a -> Maybe (a, a)) -> Operator ctx a
infixL p f op match = do
  let parser' x expr = do
        _ <- P.text op
        _ <- P.spaces
        f x <$> expr
  let layout' lhs rhs x = do
        (a, b) <- match x
        return (lhs a ++ [PP.Text (" " ++ op ++ " ")] ++ rhs b)
  InfixL p parser' layout'

infixR :: Int -> (a -> a -> a) -> String -> (a -> Maybe (a, a)) -> Operator ctx a
infixR p f op match = do
  let parser' x expr = do
        _ <- P.text op
        _ <- P.spaces
        f x <$> expr
  let layout' lhs rhs x = do
        (a, b) <- match x
        return (lhs a ++ [PP.Text (" " ++ op ++ " ")] ++ rhs b)
  InfixR p parser' layout'

parse :: Grammar ctx a -> Int -> P.Parser ctx a
parse grammar prec = do
  let parserOf = \case
        Atom parser _ -> P.Atom parser
        Prefix p parser _ -> P.Prefix p parser
        InfixL p parser _ -> P.InfixL p parser
        InfixR p parser _ -> P.InfixR p parser
  let (open, close) = grammar.group
  let op x = P.paddedR P.spaces (P.text x)
  let group = P.group (op open) (op close) P.whitespaces
  P.precedence (group : map parserOf grammar.operators) prec

layout :: Grammar ctx a -> Int -> a -> PP.Layout
layout grammar p x = do
  let layout' = layout grammar
  let loop = \case
        [] -> []
        Atom _ try : ops -> case try (layout' 0) x of
          Just x' -> x'
          Nothing -> loop ops
        Prefix q _ try : ops -> case try (layout' q) x of
          Just x' -> groupIf (p > q) x'
          Nothing -> loop ops
        InfixL q _ try : ops -> case try (layout' q) (layout' (q + 1)) x of
          Just x' -> groupIf (p > q) x'
          Nothing -> loop ops
        InfixR q _ try : ops -> case try (layout' (q + 1)) (layout' q) x of
          Just x' -> groupIf (p > q) x'
          Nothing -> loop ops
        where
          groupIf cond x =
            if cond then PP.Text (fst grammar.group) : x ++ [PP.Text (snd grammar.group)] else x
  loop grammar.operators

format :: Grammar ctx a -> Int -> String -> a -> String
format grammar width indent x =
  layout grammar 0 x
    & PP.pretty width indent
