import qualified System.Environment
import Tao (app, eval)
import TaoLang (loadExpr, loadFile)

-- TODO: Modules consist of all files in a directory
-- tao --module=examples factorial 5
-- tao factorial 5  # Default module to current directory
main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    filename : f : args -> do
      env' <- loadFile "." filename
      f' <- loadExpr f
      args' <- mapM loadExpr args
      case eval env' (app f' args') of
        Right result -> print result
        Left err -> fail ("❌ " ++ show err)
    _ -> putStrLn "🛑 Please provide me with a filename and an expression."
