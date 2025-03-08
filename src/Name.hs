module Name where

import Data.Char (isAlphaNum, isLower, isUpper, toLower, toUpper)
import Data.Function ((&))
import Data.List (intercalate, isPrefixOf, union)
import Data.List.Split (splitWhen)

camelCaseUpper :: String -> String
camelCaseUpper name =
  splitWords name
    & map capitalize
    & intercalate ""

camelCaseLower :: String -> String
camelCaseLower name = case splitWords name of
  [] -> ""
  (x : xs) -> intercalate "" (x : map capitalize xs)

snakeCase :: String -> String
snakeCase name = splitWords name & intercalate "_"

dashCase :: String -> String
dashCase name = splitWords name & intercalate "-"

splitWords :: String -> [String]
splitWords name =
  splitWhen (not . isAlphaNum) name
    & filter (/= "")
    & concatMap splitCamelCase
    & map (map toLower)

splitCamelCase :: String -> [String]
splitCamelCase [] = []
splitCamelCase (x : xs) = case splitCamelCase xs of
  [] -> [[x]]
  part : parts -> case part of
    (y : z : _) | isUpper x && isUpper y && isLower z -> split
    (y : _) | isUpper x || isLower y -> cat
    _ -> split
    where
      split = [x] : part : parts
      cat = (x : part) : parts

capitalize :: String -> String
capitalize "" = ""
capitalize (x : xs) = toUpper x : xs
