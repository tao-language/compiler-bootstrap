module Stdlib where

import Data.Char (isSpace)
import Data.Function ((&))
import Data.List (dropWhileEnd, isPrefixOf, nub, stripPrefix, union)
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

unionMap :: (Eq b) => (a -> [b]) -> [a] -> [b]
unionMap f = foldr (union . f) []

push :: a -> [a] -> [a]
push y = \case
  [] -> [y]
  x : xs -> x : push y xs

pop :: (Eq k) => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop k ((k', _) : kvs) | k == k' = kvs
pop k (_ : kvs) = pop k kvs

pop' :: (Eq k) => k -> [(k, v)] -> Maybe (v, [(k, v)])
pop' _ [] = Nothing
pop' k ((k', v) : kvs) | k == k' = Just (v, kvs)
pop' k (kv : kvs) = do
  (v, kvs) <- pop' k kvs
  return (v, kv : kvs)

set :: (Eq k) => k -> v -> [(k, v)] -> [(k, v)]
set k v = \case
  [] -> [(k, v)]
  (k', _) : kvs | k == k' -> (k, v) : kvs
  kv : kvs -> kv : set k v kvs

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

trimL :: String -> String
trimL = dropWhile isSpace

trimR :: String -> String
trimR = dropWhileEnd isSpace

trim :: String -> String
trim = trimL . trimR

lookupValue :: (Eq v) => v -> [(k, v)] -> Maybe k
lookupValue x = \case
  [] -> Nothing
  (k, v) : _ | v == x -> Just k
  _ : kvs -> lookupValue x kvs

distinct :: (Eq a) => [a] -> [a]
distinct = nub
