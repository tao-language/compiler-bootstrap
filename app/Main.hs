import Core (Term(..))
import Reducer (evaluate)
import qualified System.Environment
import Tao

toTerms :: [String] -> Either Error [Term]
toTerms [] = Right []
toTerms (x : xs) = do
  y <- fromText x
  ys <- toTerms xs
  Right (y : ys)

main :: IO ()
main = do
  args <- System.Environment.getArgs
  case args of
    (filename : args) -> do
      src <- readFile filename
      case toTerms (src : args) of
        Right (f : xs) -> print (evaluate (foldl App f xs))
        Right [] -> print ""
        Left err -> print ("❌ " ++ show err)
    _ -> putStrLn "🛑 Please give me a file to run."
