import Check (checkTypes)
import Control.Monad (void)
import Data.Function ((&))
import Data.List (intercalate, isPrefixOf, isSuffixOf, partition)
import Error (Error (..), display)
import Load (include, load, loadAtoms)
import Patch (PatchStep, Plan (plan), patch)
import PrettyPrint (pretty)
import qualified Python as Py
import Stdlib (split2, splitWith, trimPrefix)
import qualified System.Environment
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.FilePath.Windows (dropExtension, takeBaseName, takeDirectory, takeFileName)
import qualified Tao as T

main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    "run" : args -> case args of
      path : args -> runCmd path args
      _ -> putStrLn "🛑 Please give me a path, and an expression to run."
    "check" : args -> case args of
      path : args -> checkCmd path args
      _ -> putStrLn "🛑 Please give me a path, and an expression to check."
    "test" : args -> case args of
      [path] -> testCmd path ["*"]
      -- path : patterns -> test path patterns
      path : patterns -> error "TODO: match test names by patterns"
      _ -> putStrLn "🛑 Please give me a path to test."
    "patch" : args -> case args of
      [patchFile, sourceFile] -> patchCmd "build" [patchFile] [sourceFile]
      _ -> putStrLn "🛑 Please give me a patch path and a source path."
    "build" : args -> case args of
      target : args -> case target of
        "python" -> case args of
          [] -> buildPythonCmd [] ["."]
          args -> do
            let (patches, paths) = partition ("-p=" `isPrefixOf`) args
            buildPythonCmd (map (trimPrefix "-p=") patches) paths
        _ -> putStrLn $ "🛑 Target not supported: " ++ target
      _ -> putStrLn "🛑 Please give me a target."
    _ -> error "TODO: repl"

runCmd :: FilePath -> [String] -> IO ()
runCmd filename args = do
  (ctx, errors) <- load [filename]
  mapM_ (display . SyntaxError) errors
  (ctx, errors) <- include "prelude" ctx
  mapM_ print errors
  (args', errors) <- loadAtoms "<run>" args
  mapM_ print errors
  let path = dropExtension (snd (split2 ':' filename))
  print (T.run ctx path (T.app' args'))

checkCmd :: FilePath -> [String] -> IO ()
checkCmd filename args = do
  (ctx, errors) <- load [filename]
  mapM_ (display . SyntaxError) errors
  (ctx, errors) <- include "prelude" ctx
  mapM_ print errors
  (args', errors) <- loadAtoms "<check>" args
  mapM_ print errors
  let path = dropExtension (snd (split2 ':' filename))
  case checkTypes ctx path (T.app' args') of
    [] -> return ()
    errors -> do
      mapM_ (display . TypeError) errors
      exitFailure

testCmd :: FilePath -> [String] -> IO ()
testCmd path patterns = do
  (ctx, errors) <- load [path]
  mapM_ print errors
  (ctx, errors) <- include "prelude" ctx
  mapM_ print errors
  let results = T.testAll [] ctx
  mapM_ (putStr . show) results

patchCmd :: FilePath -> [FilePath] -> [FilePath] -> IO ()
patchCmd buildDir patches sources = do
  (steps, errors) <- plan [] patches
  mapM_ print errors
  (ctx, errors) <- load sources
  mapM_ print errors
  let build = patch ctx steps ctx
  let writeFile (path, id, stmts) = do
        let filename = buildDir </> path ++ "@" ++ intercalate "!" id ++ ".tao"
        putStrLn filename
        error "TODO: tao patch -- writeFile"
  mapM_ writeFile build

buildPythonCmd :: [FilePath] -> [FilePath] -> IO ()
buildPythonCmd patches sources = do
  putStrLn $ "patches: " ++ show patches
  putStrLn $ "sources: " ++ show sources
  (steps, errors) <- plan [] patches
  putStrLn $ "steps: " ++ show steps
  mapM_ print errors
  (ctx, errors) <- load sources
  putStrLn $ "ctx: " ++ show (map fst ctx)
  mapM_ print errors
  let ctx' =
        patch ctx steps ctx
          & map (\(path, _, stmts) -> (path, stmts))
  putStrLn "TODO: write intermediate patch files"
  let options = Py.defaultBuildOptions
  void $ Py.build options ctx'
