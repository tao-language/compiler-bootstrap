{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoFieldSelectors #-}

import Data.List (isSuffixOf)
import PrettyPrint (pretty)
import qualified Python
import qualified System.Environment
import qualified Tao
import TaoLang

main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    -- "build-py" : filename : args | ".tao" `isSuffixOf` filename -> buildPy filename args
    filename : args -> run filename args
    _ -> putStrLn "🛑 Please give me a file to run."

-- buildPy :: String -> [String] -> IO ()
-- buildPy filename args = do
--   taoMod <- loadModule filename
--   let pyMod = Python.emit taoMod
--   let pyFile = pretty 80 "    " (Python.layoutModule pyMod)
--   putStrLn pyFile

run :: String -> [String] -> IO ()
run filename args = do
  mod <- loadModule filename
  -- env <- loadModule path
  -- f' <- loadExpr f
  -- args' <- mapM loadExpr args
  -- case eval env (app f' args') of
  --   Right (result, type') -> do
  --     print type'
  --     print result
  --   Left err -> fail ("❌ " ++ show err)
  putStrLn ("🔴 TODO run: filename=" ++ show filename ++ " args=" ++ show args)
