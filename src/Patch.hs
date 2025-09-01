module Patch where

import Control.Monad (foldM)
import Data.Function ((&))
import Error
import Load (load, loadSource)
import Run (run)
import Stdlib (push, set, split2)
import System.FilePath (splitDirectories, splitFileName, (</>))
import Tao

type Rule = (Pattern, Expr)

type PatchStep = ([FilePath], [Rule])

class Plan a where
  plan :: [PatchStep] -> a -> IO [PatchStep]

instance Plan [FilePath] where
  plan :: [PatchStep] -> [FilePath] -> IO [PatchStep]
  plan steps = \case
    [] -> return steps
    path : paths -> do
      steps' <- plan steps ([] :: [FilePath], path)
      plan steps' paths

instance Plan ([FilePath], FilePath) where
  plan :: [PatchStep] -> ([FilePath], FilePath) -> IO [PatchStep]
  plan steps (paths, path) = do
    let dir = fst (split2 ':' path)
    maybeModule <- loadSource path
    case maybeModule of
      Just (path, stmts) -> plan steps (dir, push path paths, map dropMeta stmts)
      Nothing -> return []

instance Plan (FilePath, [FilePath], [Stmt]) where
  plan :: [PatchStep] -> (FilePath, [FilePath], [Stmt]) -> IO [PatchStep]
  plan steps0 (dir, paths, stmts) = case stmts of
    [] -> return steps0
    stmt : stmts -> do
      steps1 <- plan steps0 (dir, paths, stmt)
      plan steps1 (dir, paths, stmts)

instance Plan (FilePath, [FilePath], Stmt) where
  plan :: [PatchStep] -> (FilePath, [FilePath], Stmt) -> IO [PatchStep]
  plan steps0 (dir, paths, stmt) = case stmt of
    Import path alias names -> plan steps0 (paths, dir ++ ":" ++ path)
    -- LetDef (a, LetOp, b) -> case lookup paths steps0 of
    --   Just rules -> return (set paths (push (a, b) rules) steps0)
    --   Nothing -> return (push (paths, [(a, b)]) steps0)
    stmt -> error $ "TODO plan " ++ show (dir, paths) ++ " " ++ show stmt

class ApplyPatch applyStep a where
  applyPatch :: applyStep -> a -> a

instance ApplyPatch [Rule] Context where
  applyPatch :: [Rule] -> Context -> Context
  applyPatch rules ctx = map (applyPatch (ctx, rules)) ctx

instance ApplyPatch (Context, [Rule]) Module where
  applyPatch :: (Context, [Rule]) -> Module -> Module
  applyPatch (ctx, rules) (path, stmts) =
    (path, map (applyPatch (ctx, path, rules)) stmts)

instance ApplyPatch (Context, FilePath, [Rule]) Stmt where
  applyPatch :: (Context, FilePath, [Rule]) -> Stmt -> Stmt
  applyPatch (ctx, path, rules) = \case
    -- LetDef (p, op, b) -> LetDef (p, op, applyPatch' b)
    Test name expr expect -> Test name expr (applyPatch' expect)
    stmt -> error $ "TODO applyPatch " ++ show stmt
    where
      applyPatch' = applyPatch (ctx, path, rules)

instance ApplyPatch (Context, FilePath, [Rule]) Expr where
  applyPatch :: (Context, FilePath, [Rule]) -> Expr -> Expr
  applyPatch (ctx, path, rules) expr = case rules of
    [] -> expr
    rule : rules ->
      applyPatch (ctx, path, rule) expr
        & applyPatch (ctx, path, rules)

instance ApplyPatch (Context, FilePath, Rule) Expr where
  applyPatch :: (Context, FilePath, Rule) -> Expr -> Expr
  applyPatch (ctx, path, (p, q)) expr =
    -- case Run.run ctx path (Let (p, LetOp, expr) q) of
    --   Err -> expr
    --   result -> result
    error "TODO: applyPatch"

class ApplyStep step a where
  applyStep :: Context -> step -> a -> [(FilePath, [String], [Stmt])]

instance ApplyStep [PatchStep] Context where
  applyStep :: Context -> [PatchStep] -> [Module] -> [(FilePath, [String], [Stmt])]
  applyStep ctx steps = concatMap (applyStep ctx steps)

instance ApplyStep [PatchStep] Module where
  applyStep :: Context -> [PatchStep] -> Module -> [(FilePath, [String], [Stmt])]
  applyStep ctx steps mod@(path, stmts) =
    (path, [], stmts) : concatMap (\step -> applyStep ctx step mod) steps

instance ApplyStep PatchStep Module where
  applyStep :: Context -> PatchStep -> Module -> [(FilePath, [String], [Stmt])]
  applyStep ctx (id, rules) (path, stmts) =
    [(path, id, map (applyPatch (ctx, path, rules)) stmts)]
