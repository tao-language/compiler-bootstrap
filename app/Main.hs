import Core (Expr (..), compile)
import Reducer (evaluate)
import qualified System.Environment
import Tao (parse)

main :: IO ()
main = do
  args <- System.Environment.getArgs
  case args of
    (filename : args) -> do
      src <- readFile filename
      case parse (src : args) of
        Right (ctx, f : xs) -> case compile ctx (App f xs) of
          Just term -> print (evaluate term)
          Nothing -> print "❌ error: not all patterns covered"
        Right (_, []) -> print ""
        Left err -> print ("❌ " ++ show err)
    _ -> putStrLn "🛑 Please give me a file to run."
