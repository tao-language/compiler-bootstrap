import qualified System.Environment
import Tao (Expr (..), app, eval)
import TaoLang (readDefinitions, readExpr)

-- TODO: Modules consist of all files in a directory
-- tao --module=examples factorial 5
-- tao factorial 5  # Default module to current directory
main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    filename : f : args -> do
      env' <- readDefinitions filename
      f' <- readExpr f
      args' <- mapM readExpr args
      case eval (Let env' (app f' args')) of
        Right result -> print result
        Left err -> fail ("❌ " ++ show err)
    _ -> putStrLn "🛑 Please provide me with a filename and an expression."
