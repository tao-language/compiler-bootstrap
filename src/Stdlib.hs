module Stdlib where

import Data.Function ((&))
import Data.List (isPrefixOf, stripPrefix)
import Data.Maybe (fromMaybe)

replace :: (Eq a) => a -> a -> [a] -> [a]
replace x y (x' : xs)
  | x == x' = y : replace x y xs
  | otherwise = x' : replace x y xs
replace _ _ [] = []

replaceString :: String -> String -> String -> String
replaceString _ _ "" = ""
replaceString old new text | old `isPrefixOf` text = do
  new ++ replaceString old new (drop (length old) text)
replaceString old new (c : text) = c : replaceString old new text

filterMap :: (a -> Maybe b) -> [a] -> [b]
filterMap _ [] = []
filterMap f (x : xs) = case f x of
  Just y -> y : filterMap f xs
  Nothing -> filterMap f xs

push :: a -> [a] -> [a]
push y = \case
  [] -> [y]
  x : xs -> x : push y xs

set :: (Eq k) => k -> v -> [(k, v)] -> [(k, v)]
set key value = \case
  [] -> [(key, value)]
  (k', _) : kvs | key == k' -> (key, value) : kvs
  kv : kvs -> kv : set key value kvs

pad :: Int -> String -> String
pad = padWith ' '

padWith :: Char -> Int -> String -> String
padWith fill n text = replicate (n - length text) fill ++ text

slice :: Int -> Int -> [a] -> [a]
slice start end xs =
  xs
    & drop (start - 1)
    & take (end - start)

splitWith :: (a -> Bool) -> [a] -> [[a]]
splitWith f text = case dropWhile f text of
  [] -> []
  text -> do
    let (word, remaining) = break f text
    word : splitWith f remaining

split :: (Eq a) => a -> [a] -> [[a]]
split delim = splitWith (== delim)

split2 :: (Eq a) => a -> [a] -> ([a], [a])
split2 delim text = case text of
  [] -> ([], [])
  x : ys | x == delim -> ([], ys)
  x : y : ys | y == delim -> ([x], ys)
  x : xs -> case split2 delim xs of
    ([], ys) -> ([], x : ys)
    (xs, ys) -> (x : xs, ys)

trimPrefix :: (Eq a) => [a] -> [a] -> [a]
trimPrefix prefix xs = fromMaybe xs (stripPrefix prefix xs)

lookupValue :: (Eq v) => v -> [(k, v)] -> Maybe k
lookupValue x = \case
  [] -> Nothing
  (k, v) : _ | v == x -> Just k
  _ : kvs -> lookupValue x kvs
