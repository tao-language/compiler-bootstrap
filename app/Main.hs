import qualified System.Environment
import Tao (app, prelude)
import TaoLang (loadExpr, loadModule, run)

main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    path : f : args -> do
      env <- loadModule path
      f' <- loadExpr f
      args' <- mapM loadExpr args
      case run (env ++ prelude) (app f' args') of
        Right (result, type') -> do
          print type'
          print result
        Left err -> fail ("❌ " ++ show err)
    _ -> putStrLn "🛑 Please provide me with a directory and an expression."
