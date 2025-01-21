module Load where

import Control.Monad (foldM)
import Data.List (isPrefixOf, sort)
import qualified Parser as P
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (dropExtension, splitExtension, takeBaseName, takeDirectory, (</>))
import Tao
import TaoParser (parseAtom, parseModule)

load :: FilePath -> [FilePath] -> IO (Context, [SyntaxError])
load dir = foldM (loadModule dir) ([], [])

include :: FilePath -> FilePath -> Context -> IO (Context, [SyntaxError])
include dir prelude ctx = do
  let include' (path, stmts) =
        (path, Import (dropExtension prelude) (takeBaseName prelude) [("", "")] : stmts)
  (ctx, errs) <- loadModule dir (ctx, []) prelude
  return (map include' ctx, errs)

loadModule :: FilePath -> (Context, [SyntaxError]) -> FilePath -> IO (Context, [SyntaxError])
loadModule dir (ctx, errs) path = do
  isDir <- doesDirectoryExist path
  isFile <- do
    dirFiles <- listDirectory (takeDirectory path)
    return (any ((takeBaseName path ++ ".") `isPrefixOf`) dirFiles)
  (ctx, errs) <-
    if isDir
      then loadDir dir path (ctx, errs)
      else return (ctx, errs)
  if isFile
    then loadFile dir path (ctx, errs)
    else return (ctx, errs)

loadDir :: FilePath -> FilePath -> (Context, [SyntaxError]) -> IO (Context, [SyntaxError])
loadDir dir path (ctx, errs) = do
  files <- walkDirectory "." path
  foldM (flip (loadFile dir)) (ctx, errs) files

loadFile :: FilePath -> FilePath -> (Context, [SyntaxError]) -> IO (Context, [SyntaxError])
loadFile dir path (ctx, errs) = do
  src <- loadSource dir path
  case src of
    Right mod -> return (mod : ctx, errs)
    Left errs' -> return (ctx, errs ++ errs')

loadSource :: FilePath -> FilePath -> IO (Either [SyntaxError] Module)
loadSource dir filename = case splitExtension filename of
  (_, "") -> loadSource dir (filename ++ ".tao")
  (name, ".tao") -> do
    src <- readFile (dir </> filename)
    let parser = parseModule name
    case P.parse parser (dir </> filename) src of
      Right (mod, _) -> return (Right mod)
      Left P.State {filename, pos = (row, col), context} -> do
        let err =
              SyntaxError
                { filename = filename,
                  row = row,
                  col = col,
                  sourceCode = src,
                  context = context
                }
        return (Left [err])
  _ -> error $ "file extension not supported: " ++ filename

loadAtom :: String -> String -> IO (Expr, [SyntaxError])
loadAtom filename src = case P.parse parseAtom filename src of
  Right (a, _) -> return (a, [])
  Left P.State {filename, pos = (row, col), context} -> do
    let err =
          SyntaxError
            { filename = filename,
              row = row,
              col = col,
              sourceCode = src,
              context = context
            }
    return (Err, [err])

loadAtoms :: String -> [String] -> IO ([Expr], [SyntaxError])
loadAtoms _ [] = return ([], [])
loadAtoms filename (src : srcs) = do
  (a, err1) <- loadAtom filename src
  (bs, err2) <- loadAtoms filename srcs
  return (a : bs, err1 ++ err2)

walkDirectory :: FilePath -> FilePath -> IO [FilePath]
walkDirectory base path = do
  let walk path = do
        isDir <- doesDirectoryExist (base </> path)
        if isDir
          then walkDirectory base path
          else return [path]
  paths <- listDirectory (base </> path)
  files <- mapM walk (sort paths)
  return (map (path </>) (concat files))
