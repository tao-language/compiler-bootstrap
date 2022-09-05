module Reducer where

import Lambda

substitute :: String -> Term -> Term -> Term
substitute x a (Var x') | x == x' = a
substitute x a (App b1 b2) = App (substitute x a b1) (substitute x a b2)
substitute x a (Lam y b) | x /= y = Lam y (substitute x a b)
substitute _ _ b = b

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
