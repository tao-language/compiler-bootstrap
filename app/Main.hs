import Control.Monad (void)
import Data.List (intercalate, isSuffixOf)
import qualified Patch
import PrettyPrint (pretty)
import qualified Python as Py
import qualified System.Environment
import System.FilePath ((</>))
import System.FilePath.Windows (dropExtension, takeBaseName, takeDirectory, takeFileName)
import qualified Tao as T
import TaoParser (include, load, loadAtoms, srcPath)

main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    "run" : args -> case args of
      path : args -> run path args
      _ -> putStrLn "🛑 Please give me a path, and an expression to run."
    "test" : args -> case args of
      [path] -> test path ["*"]
      -- path : patterns -> test path patterns
      path : patterns -> error "TODO: match test names by patterns"
      _ -> putStrLn "🛑 Please give me a path to test."
    "patch" : args -> case args of
      path : patches -> patch path patches
      _ -> putStrLn "🛑 Please give me a path, and the patches to apply."
    "build" : args -> case args of
      [] -> build ["."]
      paths -> build paths
    _ -> error "TODO: repl"

run :: FilePath -> [String] -> IO ()
run filename args = do
  (ctx, errors) <- load [filename]
  mapM_ print errors
  (ctx, errors) <- include "prelude" ctx
  mapM_ print errors
  (args', errors) <- loadAtoms "<run>" args
  mapM_ print errors
  print (T.eval ctx (dropExtension filename) (T.app' args'))

test :: FilePath -> [String] -> IO ()
test path patterns = do
  (ctx, errors) <- load [path]
  mapM_ print errors
  (ctx, errors) <- include "prelude" ctx
  mapM_ print errors
  let results = T.testAll [] ctx
  mapM_ (putStr . show) results

patch :: FilePath -> [FilePath] -> IO ()
patch path patches = do
  (ctx, errors) <- load [path]
  mapM_ print errors
  (ctx, errors) <- include "prelude" ctx
  mapM_ print errors
  Patch.apply ctx ("build" </> "patch") patches

build :: [FilePath] -> IO ()
build paths = do
  let options = Py.defaultBuildOptions
  void $ Py.build options paths
