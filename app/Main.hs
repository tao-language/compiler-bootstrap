import Data.List (intercalate, isSuffixOf)
import PrettyPrint (pretty)
import qualified System.Environment
import System.FilePath.Windows (dropExtension, takeDirectory)
import qualified Tao as T
import TaoParser (load, loadAtoms)

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
  ((_, ctx), syntaxErrors) <- load filename []
  parsed <- loadAtoms args
  let errors = map snd parsed
  let expr = T.app' (map fst parsed)
  let result = T.eval ctx (dropExtension filename) expr
  print result

test :: String -> [String] -> IO ()
test path patterns = do
  (pkg, syntaxErrors) <- load path []
  let results = T.testAll [] pkg
  putStrLn (intercalate "\n" (map show results))
