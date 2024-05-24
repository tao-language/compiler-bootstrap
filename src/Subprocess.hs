module Subprocess where

import Data.Char (isSpace)
import Data.List (dropWhileEnd, intercalate)
import GHC.IO.Exception (ExitCode (..))
import GHC.IO.Handle (hGetContents)
import System.Process (CreateProcess (std_err, std_out), StdStream (CreatePipe), createProcess, cwd, proc, waitForProcess)

run :: FilePath -> String -> [String] -> IO ()
run workingDirectory cmd args = do
  let trim = dropWhileEnd isSpace . dropWhile isSpace
  let command = '>' : ' ' : unwords (cmd : args)
  putStrLn command
  (_, Just stdout, Just stderr, p) <-
    createProcess
      (proc cmd args)
        { cwd = Just workingDirectory,
          std_out = CreatePipe,
          std_err = CreatePipe
        }
  status <- waitForProcess p
  case status of
    ExitSuccess -> return ()
    ExitFailure _ -> do
      out <- hGetContents stdout
      err <- hGetContents stderr
      fail (intercalate "\n" ["", command, trim out, trim err, ""])
