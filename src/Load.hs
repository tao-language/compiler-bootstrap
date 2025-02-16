module Load where

import Control.Monad (foldM)
import Data.List (isPrefixOf, sort)
import Error (SyntaxError (..))
import Location (Location (..), Position (..))
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
  let include' (path, stmts) = do
        let path' = snd (split2 ':' preludePath)
        (path, Import (dropExtension path') (takeBaseName path') [("", "")] : stmts)
  (ctx, errs) <- loadModule (ctx, []) preludePath
  return (map include' ctx, errs)

loadModule :: (Context, [SyntaxError]) -> FilePath -> IO (Context, [SyntaxError])
loadModule (ctx, errs) sourcePath = do
  let osPath = getOSPath sourcePath
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
loadDir sourcePath (ctx, errs) = do
  let (dir, path) = split2 ':' sourcePath
  files <- walkDirectory dir path
  foldM (flip loadFile) (ctx, errs) (map ((dir ++ ":") ++) files)

loadFile :: FilePath -> (Context, [SyntaxError]) -> IO (Context, [SyntaxError])
loadFile path (ctx, errs) = do
  src <- loadSource path
  case src of
    Right mod -> return (mod : ctx, errs)
    Left errs' -> return (ctx, errs ++ errs')

getOSPath :: FilePath -> FilePath
getOSPath = \case
  (':' : path) -> path
  path -> replace ':' '/' path

loadSource :: FilePath -> IO (Either [SyntaxError] Module)
loadSource filename = case splitExtension filename of
  (_, "") -> loadSource (filename ++ ".tao")
  (name, ".tao") -> do
    let osPath = getOSPath filename
    src <- readFile osPath
    let parser = parseModule (snd (split2 ':' name))
    case P.parse parser osPath src of
      Right (mod, _) -> return (Right mod)
      Left P.State {filename, pos, context} -> do
        let loc =
              Location
                { filename = filename,
                  start = pos,
                  end = pos
                }
        return (Left [UnexpectedChar loc])
  _ -> error $ "file extension not supported: " ++ filename

loadAtom :: String -> String -> IO (Expr, [SyntaxError])
loadAtom filename src = case P.parse parseAtom filename src of
  Right (a, _) -> return (a, [])
  Left P.State {filename, pos, context} -> do
    let loc =
          Location
            { filename = filename,
              start = pos,
              end = pos
            }
    return (Err, [UnexpectedChar loc])

loadAtoms :: String -> [String] -> IO ([Expr], [SyntaxError])
loadAtoms _ [] = return ([], [])
loadAtoms filename (src : srcs) = do
  (a, err1) <- loadAtom filename src
  (bs, err2) <- loadAtoms filename srcs
  return (a : bs, err1 ++ err2)

walkDirectory :: FilePath -> FilePath -> IO [FilePath]
walkDirectory dir path = do
  let walk path = do
        isDir <- doesDirectoryExist (dir </> path)
        if isDir
          then walkDirectory dir path
          else return [path]
  paths <- listDirectory (dir </> path)
  files <- mapM walk (sort paths)
  return (map (path </>) (concat files))
