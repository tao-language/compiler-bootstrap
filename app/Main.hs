import Data.List (intercalate, isSuffixOf)
import PrettyPrint (pretty)
import qualified System.Environment
import System.FilePath.Windows (dropExtension, takeBaseName, takeDirectory, takeFileName)
import qualified Tao as T
import TaoParser (include, load, loadAtoms, srcPath)

main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    "run" : args -> case args of
      filename : args -> run filename args
      _ -> putStrLn "🛑 Please give me a filename, and an expression to run."
    "test" : args -> case args of
      [path] -> test path ["*"]
      -- path : patterns -> test path patterns
      path : patterns -> error "TODO: match test names by patterns"
      _ -> putStrLn "🛑 Please give me a directory or filename to test."
    _ -> error "TODO: repl"

run :: FilePath -> [String] -> IO ()
run filename args = do
  (ctx, errors) <- load [filename]
  mapM_ print errors
  (ctx, errors) <- include "prelude" ctx
  mapM_ print errors
  (args', errors) <- loadAtoms "<run>" args
  mapM_ print errors
  let result = T.eval ctx (dropExtension filename) (T.app' args')
  print result

test :: FilePath -> [String] -> IO ()
test path patterns = do
  (ctx, errors) <- load [path]
  mapM_ print errors
  (ctx, errors) <- include "prelude" ctx
  mapM_ print errors
  let results = T.testAll [] ctx
  mapM_ (putStr . show) results
