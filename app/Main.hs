import qualified System.Environment
import TaoLang

main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    filename : args -> run filename args
    _ -> putStrLn "🛑 Please give me a file to run."

run :: String -> [String] -> IO ()
run filename args = do
  defs <- loadFile filename
  -- env <- loadModule path
  -- f' <- loadExpr f
  -- args' <- mapM loadExpr args
  -- case eval env (app f' args') of
  --   Right (result, type') -> do
  --     print type'
  --     print result
  --   Left err -> fail ("❌ " ++ show err)
  putStrLn ("🔴 TODO: filename=" ++ show filename ++ " args=" ++ show args)
