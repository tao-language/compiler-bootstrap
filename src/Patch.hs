module Patch where

import Tao

apply :: Context -> FilePath -> [FilePath] -> IO ()
apply ctx buildDir = \case
  [] -> return ()
  patch : patches -> do
    error "TODO Patch.apply"

class Patch a where
  patch :: Context -> [Stmt] -> a -> a

instance Patch Expr where
  patch :: Context -> [Stmt] -> Expr -> Expr
  patch _ [] a = a
  patch ctx (rule : rules) expr = case rule of
    Import {} -> error "TODO: import sub-patches"
    Def (pattern', body) -> do
      let patch' = patch ctx (rule : rules)
      let expr' = case expr of
            Ann a b -> Ann (patch' a) (patch' b)
            And a b -> And (patch' a) (patch' b)
            a -> a
      case eval ctx "" (Let (pattern', expr') body) of
        Err -> expr'
        result -> result
    -- Def (p, b) -> case (p, a) of
    --   (Any, Any) -> b
    --   (Unit, Unit) -> b
    --   (IntT, IntT) -> b
    --   (NumT, NumT) -> b
    --   (Int i, Int i') -> if i == i' then b else a
    --   (Num n, Num n') -> if n == n' then b else a
    --   (Tag k, Tag k') -> if k == k' then b else a
    --   (Var x, Var x') -> if x == x' then b else a
    --   -- Ann Expr Type
    --   -- And Expr Expr
    --   -- Or Expr Expr
    --   -- Fix String Expr
    --   -- For [String] Expr
    --   -- Fun Expr Expr
    --   -- App Expr Expr
    --   -- Call String [Expr]
    --   -- Op1 Op1 Expr
    --   -- Op2 Op2 Expr Expr
    --   -- Match [Expr] [Expr]
    --   -- If Expr Expr Expr
    --   -- Let (Expr, Expr) Expr
    --   -- Bind (Expr, Expr) Expr
    --   -- Record [(String, Expr)]
    --   -- Select Expr [(String, Expr)]
    --   -- With Expr [(String, Expr)]
    --   -- Err
    --   (Err, Err) -> Err
    TypeDef {} -> expr
    Test {} -> expr
