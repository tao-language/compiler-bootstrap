module Load where

import Control.Monad (foldM)
import Data.List (isPrefixOf, sort)
import qualified Parser as P
import Stdlib (replace, split2)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (dropExtension, splitExtension, takeBaseName, takeDirectory, (</>))
import Tao
import TaoParser (parseAtom, parseModule)

load :: [FilePath] -> IO (Context, [SyntaxError])
load = foldM loadModule ([], [])

include :: FilePath -> Context -> IO (Context, [SyntaxError])
include preludePath ctx = do
  let include' (path, stmts) =
        (path, Import (dropExtension path) (takeBaseName path) [("", "")] : stmts)
  (ctx, errs) <- loadModule (ctx, []) preludePath
  return (map include' ctx, errs)

loadModule :: (Context, [SyntaxError]) -> FilePath -> IO (Context, [SyntaxError])
loadModule (ctx, errs) sourcePath = do
  let osPath = replace ':' '/' sourcePath
  isDir <- doesDirectoryExist osPath
  isFile <- do
    dirFiles <- listDirectory (takeDirectory osPath)
    return (any ((takeBaseName osPath ++ ".") `isPrefixOf`) dirFiles)
  (ctx, errs) <-
    if isDir
      then loadDir sourcePath (ctx, errs)
      else return (ctx, errs)
  if isFile
    then loadFile sourcePath (ctx, errs)
    else return (ctx, errs)

loadDir :: FilePath -> (Context, [SyntaxError]) -> IO (Context, [SyntaxError])
loadDir path (ctx, errs) = do
  files <- walkDirectory "." path
  foldM (flip loadFile) (ctx, errs) files

loadFile :: FilePath -> (Context, [SyntaxError]) -> IO (Context, [SyntaxError])
loadFile path (ctx, errs) = do
  src <- loadSource path
  case src of
    Right mod -> return (mod : ctx, errs)
    Left errs' -> return (ctx, errs ++ errs')

loadSource :: FilePath -> IO (Either [SyntaxError] Module)
loadSource filename = case splitExtension filename of
  (_, "") -> loadSource (filename ++ ".tao")
  (name, ".tao") -> do
    let osPath = replace ':' '/' filename
    src <- readFile osPath
    let parser = parseModule name
    case P.parse parser osPath src of
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
