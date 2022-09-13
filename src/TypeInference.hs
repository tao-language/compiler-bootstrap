module TypeInference where

-- Probably remove this as a bidirectional approach is simpler and more flexible

import Data.Bifunctor (Bifunctor (second))
import Lambda

type Env = [(String, Term)]

bind :: String -> Term -> Maybe (Term -> Term)
bind x (Var x') | x == x' = Just id
bind x a | x `occurs` a = Nothing
bind x a = Just (substitute x a)

unify :: Term -> Term -> Maybe (Term -> Term)
unify (Var x) b = bind x b
unify a (Var x) = bind x a
unify (App a1 a2) (App b1 b2) = unify2 (a1, b1) (a2, b2)
unify (Ann a1 a2) (Ann b1 b2) = unify2 (a1, b1) (a2, b2)
unify (Fun a1 a2) (Fun b1 b2) = unify2 (a1, b1) (a2, b2)
unify (For x a) b = do
  let x' = newName (freeVariables b) x
  unify (substitute x (Var x') a) b
unify a (For x b) = do
  let x' = newName (freeVariables a) x
  unify a (substitute x (Var x') b)
unify a b | a == b = Just id
unify _ _ = Nothing

unify2 :: (Term, Term) -> (Term, Term) -> Maybe (Term -> Term)
unify2 (a1, b1) (a2, b2) = do
  s1 <- unify a1 b1
  s2 <- unify (s1 a2) (s1 b2)
  Just (s2 . s1)

inferType :: Env -> Term -> Maybe (Term, Term -> Term)
inferType _ Typ = Just (Typ, id)
inferType _ IntT = Just (Typ, id)
inferType _ (Int _) = Just (IntT, id)
inferType env (Var x) = do
  type' <- lookup x env
  Just (type', id)
inferType env (Lam x b) = do
  let x' = newName (map fst env) x
  (tb, s) <- inferType ((x, Var x') : env) b
  case s (Var x') of
    ta | ta == Var x' -> Just (For x' (Fun ta tb), s)
    ta -> Just (Fun ta tb, s)
inferType env (App a b) = do
  let t = Var (newName (map fst env) "%")
  (ta, s1) <- inferType env a
  (tb, s2) <- inferType (map (second s1) env) b
  s3 <- unify (Fun tb t) (s2 ta)
  Just (s3 t, s3 . s2 . s1)
inferType _ (Call _) = Just (for ["a", "b"] (Fun (Var "a") (Var "b")), id)
inferType _ Fix = Just (For "a" (Fun (Var "a") (Var "a")), id)
inferType env (Ann a t) = do
  (ta, s1) <- inferType env a
  s2 <- unify (s1 t) ta
  Just (s2 t, s2 . s1)
inferType _ (For _ _) = Just (Typ, id)
inferType _ (Fun _ _) = Just (Typ, id)
