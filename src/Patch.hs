module Patch where

import Control.Monad (foldM)
import Data.Function ((&))
import Error (SyntaxError (..))
import Load (load, loadSource)
import Stdlib (push, set, split2)
import System.FilePath (splitDirectories, splitFileName, (</>))
import Tao

type Rule = (Pattern, Expr)

type PatchStep = ([FilePath], [Rule])

class Plan a where
  plan :: [PatchStep] -> a -> IO ([PatchStep], [SyntaxError])

instance Plan [FilePath] where
  plan :: [PatchStep] -> [FilePath] -> IO ([PatchStep], [SyntaxError])
  plan steps0 = \case
    [] -> return (steps0, [])
    path : paths -> do
      (steps1, errs1) <- plan steps0 ([] :: [FilePath], path)
      (steps2, errs2) <- plan steps1 paths
      return (steps2, errs1 ++ errs2)

instance Plan ([FilePath], FilePath) where
  plan :: [PatchStep] -> ([FilePath], FilePath) -> IO ([PatchStep], [SyntaxError])
  plan steps (paths, path) = do
    let dir = fst (split2 ':' path)
    src <- loadSource path
    case src of
      Right (path, stmts) -> plan steps (dir, push path paths, stmts)
      Left errs -> return ([], errs)

instance Plan (FilePath, [FilePath], [Stmt]) where
  plan :: [PatchStep] -> (FilePath, [FilePath], [Stmt]) -> IO ([PatchStep], [SyntaxError])
  plan steps0 (dir, paths, stmts) = case stmts of
    [] -> return (steps0, [])
    stmt : stmts -> do
      (steps1, errs1) <- plan steps0 (dir, paths, stmt)
      (steps2, errs2) <- plan steps1 (dir, paths, stmts)
      return (steps2, errs1 ++ errs2)

instance Plan (FilePath, [FilePath], Stmt) where
  plan :: [PatchStep] -> (FilePath, [FilePath], Stmt) -> IO ([PatchStep], [SyntaxError])
  plan steps0 (dir, paths, stmt) = case stmt of
    Import path alias names -> plan steps0 (paths, dir ++ ":" ++ path)
    Def rule -> case lookup paths steps0 of
      Just rules -> return (set paths (push rule rules) steps0, [])
      Nothing -> return (push (paths, [rule]) steps0, [])
    stmt -> error $ "TODO plan " ++ show stmt

class Apply patch a where
  apply :: patch -> a -> a

instance Apply [Rule] Context where
  apply :: [Rule] -> Context -> Context
  apply rules ctx = map (apply (ctx, rules)) ctx

instance Apply (Context, [Rule]) Module where
  apply :: (Context, [Rule]) -> Module -> Module
  apply (ctx, rules) (path, stmts) =
    (path, map (apply (ctx, path, rules)) stmts)

instance Apply (Context, FilePath, [Rule]) Stmt where
  apply :: (Context, FilePath, [Rule]) -> Stmt -> Stmt
  apply (ctx, path, rules) = \case
    Def (p, b) -> Def (p, apply' b)
    Test t -> Test (t {expect = apply' t.expect})
    stmt -> error $ "TODO apply " ++ show stmt
    where
      apply' = apply (ctx, path, rules)

instance Apply (Context, FilePath, [Rule]) Expr where
  apply :: (Context, FilePath, [Rule]) -> Expr -> Expr
  apply (ctx, path, rules) expr = case rules of
    [] -> expr
    rule : rules ->
      apply (ctx, path, rule) expr
        & apply (ctx, path, rules)

instance Apply (Context, FilePath, Rule) Expr where
  apply :: (Context, FilePath, Rule) -> Expr -> Expr
  apply (ctx, path, (p, q)) expr = case run ctx path (Let (p, expr) q) of
    Err -> expr
    result -> result

class Patch step a where
  patch :: Context -> step -> a -> [(FilePath, [String], [Stmt])]

instance Patch [PatchStep] Context where
  patch :: Context -> [PatchStep] -> [Module] -> [(FilePath, [String], [Stmt])]
  patch ctx steps = concatMap (patch ctx steps)

instance Patch [PatchStep] Module where
  patch :: Context -> [PatchStep] -> Module -> [(FilePath, [String], [Stmt])]
  patch ctx steps mod@(path, stmts) =
    (path, [], stmts) : concatMap (\step -> patch ctx step mod) steps

instance Patch PatchStep Module where
  patch :: Context -> PatchStep -> Module -> [(FilePath, [String], [Stmt])]
  patch ctx (id, rules) (path, stmts) =
    [(path, id, map (apply (ctx, path, rules)) stmts)]
