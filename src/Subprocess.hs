module Subprocess where

import Control.Monad (void)
import Data.Char (isSpace)
import Data.List (dropWhileEnd, intercalate)
import GHC.IO.Exception (ExitCode (..))
import GHC.IO.Handle (hGetContents)
import System.Process (CreateProcess (std_err, std_out), StdStream (CreatePipe), createProcess, cwd, proc, waitForProcess)

run :: FilePath -> String -> [String] -> IO ()
run workingDirectory cmd args =
  void (getOutput workingDirectory cmd args)

getOutput :: FilePath -> String -> [String] -> IO String
getOutput workingDirectory cmd args = do
  let trim = dropWhileEnd isSpace . dropWhile isSpace
  let command = '>' : ' ' : unwords (cmd : args)
  putStr command
  (_, Just stdout, Just stderr, p) <-
    createProcess
      (proc cmd args)
        { cwd = Just workingDirectory,
          std_out = CreatePipe,
          std_err = CreatePipe
        }
  status <- waitForProcess p
  case status of
    ExitSuccess -> do
      out <- hGetContents stdout
      putStrLn (trim out)
      err <- hGetContents stderr
      putStrLn (trim err)
      return out
    ExitFailure _ -> do
      out <- hGetContents stdout
      putStrLn (trim out)
      err <- hGetContents stderr
      putStrLn (trim err)
      fail command
