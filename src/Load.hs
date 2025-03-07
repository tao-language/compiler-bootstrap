module Load where

import Control.Monad (foldM)
import Data.List (isPrefixOf, sort)
import Error (Error (SyntaxError), SyntaxError (..))
import Location (Location (..), Position (..), Range (..))
import qualified Parser as P
import Stdlib (replace, split2)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (dropExtension, splitExtension, takeBaseName, takeDirectory, (</>))
import Tao

load :: [FilePath] -> IO Context
load = foldM loadModule []

include :: FilePath -> Context -> IO Context
include preludePath ctx = do
  let include' (path, stmts) = do
        let path' = snd (split2 ':' preludePath)
        (path, Import (dropExtension path') (takeBaseName path') [("", "")] : stmts)
  ctx <- loadModule ctx preludePath
  return (map include' ctx)

loadModule :: Context -> FilePath -> IO Context
loadModule ctx sourcePath = do
  let osPath = getOSPath sourcePath
  isDir <- doesDirectoryExist osPath
  isFile <- do
    dirFiles <- listDirectory (takeDirectory osPath)
    return (any ((takeBaseName osPath ++ ".") `isPrefixOf`) dirFiles)
  ctx <-
    if isDir
      then loadDir sourcePath ctx
      else return ctx
  if isFile
    then loadFile sourcePath ctx
    else return ctx

loadDir :: FilePath -> Context -> IO Context
loadDir sourcePath ctx = do
  let (dir, path) = split2 ':' sourcePath
  files <- walkDirectory dir path
  foldM (flip loadFile) ctx (map ((dir ++ ":") ++) files)

loadFile :: FilePath -> Context -> IO Context
loadFile path ctx = do
  src <- loadSource path
  case src of
    Just mod -> return (mod : ctx)
    Nothing -> return ctx

getOSPath :: FilePath -> FilePath
getOSPath = \case
  (':' : path) -> path
  path -> replace ':' '/' path

loadSource :: FilePath -> IO (Maybe Module)
loadSource filename = case splitExtension filename of
  (_, "") -> loadSource (filename ++ ".tao")
  (name, ".tao") -> do
    let osPath = getOSPath filename
    src <- readFile osPath
    let parser = parseModule (snd (split2 ':' name))
    case P.parse parser osPath src of
      Right (mod, _) -> return (Just mod)
      Left P.State {filename, pos, context} -> do
        -- let loc =
        --       Location
        --         { filename = filename,
        --           range = Range pos pos
        --         }
        -- return (Left [UnexpectedChar loc])
        error "TODO: loadSource handle error"
  _ -> error $ "file extension not supported: " ++ filename

-- loadAtom :: String -> String -> IO Expr
-- loadAtom filename src = case P.parse parseAtom filename src of
--   Right (a, _) -> return a
--   Left P.State {filename, pos, context} -> do
--     let loc =
--           Location
--             { filename = filename,
--               range = Range pos pos
--             }
--     return (Err $ SyntaxError $ UnexpectedChar loc)

-- loadAtoms :: String -> [String] -> IO [Expr]
-- loadAtoms _ [] = return []
-- loadAtoms filename (src : srcs) = do
--   a <- loadAtom filename src
--   bs <- loadAtoms filename srcs
--   return (a : bs)

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
