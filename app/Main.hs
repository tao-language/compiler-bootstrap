import qualified System.Environment
import Tao (app, eval)
import TaoLang (parse)

main :: IO ()
main = do
  args <- System.Environment.getArgs
  case args of
    (filename : args) -> do
      src <- readFile filename
      case parse (src : args) of
        Right [] -> print ""
        Right (f : xs) -> case eval [] (app f xs) of
          Right expr -> print expr
          Left err -> putStrLn ("❌ " ++ show err)
        Left err -> putStrLn ("❌ " ++ show err)
    _ -> putStrLn "🛑 Please give me a file to run."
