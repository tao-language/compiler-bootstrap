import qualified System.Environment
import Tao (app, eval, infer)
import TaoLang (loadExpr, loadModule)

main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    path : f : args -> do
      env <- loadModule path
      f' <- loadExpr f
      args' <- mapM loadExpr args
      let expr = app f' args'
      case infer env expr of
        Right (t, _) -> do
          print t
          print (eval env expr)
        Left err -> fail ("❌ " ++ show err)
    _ -> putStrLn "🛑 Please provide me with a directory and an expression."
