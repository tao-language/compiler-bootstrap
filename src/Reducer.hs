module Reducer where

import Lambda

reduce :: Term -> Term
reduce (App a b) = case reduce a of
  Lam x a -> reduce (substitute x b a)
  App (Call f) a -> case (f, reduce a, reduce b) of
    ("+", Int a, Int b) -> Int (a + b)
    ("-", Int a, Int b) -> Int (a - b)
    ("*", Int a, Int b) -> Int (a * b)
    ("==", Int a, Int b) -> Lam "T" (Lam "F" (Var (if a == b then "T" else "F")))
    (_, a, b) -> App (App (Call f) a) b
  Fix -> reduce (App b (App Fix b))
  a -> App a b
reduce a = a

evaluate :: Term -> Term
evaluate a = case reduce a of
  -- TODO: get Lambdas to a normal form for optimization.
  -- Lam x a -> Lam x (evaluate a)
  App a b -> App a (evaluate b)
  a -> a
