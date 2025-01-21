module Patch where

import Control.Monad (foldM)
import Load (loadSource)
import Stdlib (push, set, split2)
import System.FilePath (splitDirectories, splitFileName, (</>))
import Tao

type PatchStep = ([FilePath], [(Pattern, Expr)])

patch :: FilePath -> FilePath -> FilePath -> IO (FilePath, [SyntaxError])
patch buildDir patchPath sourcePath = do
  -- (ctx, errs) <- load
  error "TODO"

-- patch :: FilePath -> [FilePath] -> (Context, [Module]) -> IO ([FilePath], [SyntaxError])

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
  apply :: Context -> FilePath -> patch -> a -> a

-- instance Apply PatchModule Module where
--   apply :: Context -> FilePath -> PatchModule -> Module -> Module
--   apply ctx path rule x = error $ "TODO apply " ++ show rule ++ " -- " ++ show x

-- instance Apply PatchStmt Module where
--   apply :: Context -> FilePath -> PatchStmt -> Module -> Module
--   apply ctx path rule x = error $ "TODO apply " ++ show rule ++ " -- " ++ show x

-- instance Apply PatchStmt Stmt where
--   apply :: Context -> FilePath -> PatchStmt -> Stmt -> Stmt
--   apply ctx path rule x = error $ "TODO apply " ++ show rule ++ " -- " ++ show x

instance Apply (Pattern, Expr) Stmt where
  apply :: Context -> FilePath -> (Pattern, Expr) -> Stmt -> Stmt
  apply ctx path rule = \case
    Def (a, b) -> Def (a, apply ctx path rule b)
    stmt -> error $ "TODO: apply " ++ show stmt

instance Apply (Pattern, Expr) Expr where
  apply :: Context -> FilePath -> (Pattern, Expr) -> Expr -> Expr
  apply ctx path (p, q) expr = do
    case eval ctx path (Let (p, expr) q) of
      Err -> expr
      result -> result
