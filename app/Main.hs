import Control.Monad (void)
import qualified Core as C
import Data.Either (fromRight)
import Data.Function ((&))
import Data.List (intercalate, isPrefixOf, isSuffixOf, partition)
import Data.Maybe (fromMaybe)
import Error
import Load (include, load, loadExpr)
import Patch
import PrettyPrint (pretty)
import qualified Python as Py
import Run (run)
import Stdlib (split2, splitWith, trimPrefix)
import qualified System.Environment
import System.Exit (exitFailure, exitSuccess)
import System.FilePath ((</>))
import System.FilePath.Windows (dropExtension, takeBaseName, takeDirectory, takeFileName)
import Tao
import Test (count, testAll)

main :: IO ()
main = do
  cliArgs <- System.Environment.getArgs
  case cliArgs of
    "core" : args -> case args of
      path : arg : args -> coreCmd path arg
      _ -> putStrLn "🛑 Please give me a path, and an expression to convert to Core."
    "run" : args -> case args of
      path : arg : args -> runCmd path arg
      _ -> putStrLn "🛑 Please give me a path, and an expression to run."
    "check" : args -> case args of
      path : _ -> checkCmd path
      _ -> putStrLn "🛑 Please give me a path to collectErrors."
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
    args -> error "TODO: repl"

coreCmd :: FilePath -> String -> IO ()
coreCmd filename arg = do
  pkg <- load [filename]
  ctx <- include "prelude" pkg
  case collectErrors ctx "" ctx of
    [] -> return ()
    syntaxErrors -> do
      mapM_ display syntaxErrors
      exitFailure
  expr <- loadExpr "<core>" arg
  case collectErrors ctx "" expr of
    [] -> return ()
    syntaxErrors -> do
      mapM_ (displayOn arg) syntaxErrors
      exitFailure
  -- TODO: collectErrors for errors
  let printExpr a = putStrLn ("  " ++ C.format 80 "  " a)
  let path = dropExtension (snd (split2 ':' filename))
  let (env, a) = compile ctx path expr
  putStrLn "---- env ----"
  printExpr (C.dropMeta $ C.let' env C.Any)
  putStrLn $ ">> env: " ++ show (map fst env)
  putStrLn "---- lower ----"
  printExpr (C.dropMeta $ lower expr)
  putStrLn "---- bind ----"
  printExpr (C.dropMeta $ C.bind [] $ lower expr)
  putStrLn "---- compile ----"
  printExpr (C.dropMeta a)
  putStrLn "---- eval ----"
  let b = C.eval runtimeOps $ C.let' env a
  printExpr (C.dropMeta b)
  putStrLn ("--- " ++ C.showCtr' 3 b)
  -- putStrLn "---- eval (untyped)"
  -- printExpr (C.dropTypes b)
  return ()

runCmd :: FilePath -> String -> IO ()
runCmd filename arg = do
  pkg <- load [filename]
  ctx <- include "prelude" pkg
  let path = dropExtension (snd (split2 ':' filename))
  case collectErrors ctx path ctx of
    [] -> return ()
    syntaxErrors -> do
      mapM_ display syntaxErrors
      exitFailure
  expr <- loadExpr "<run>" arg
  case collectErrors ctx "" expr of
    [] -> return ()
    syntaxErrors -> do
      mapM_ display syntaxErrors
      exitFailure
  print (dropTypes $ dropMeta $ Run.run ctx path expr)

checkCmd :: FilePath -> IO ()
checkCmd filename = do
  pkg <- load [filename]
  ctx <- include "prelude" pkg
  let path = dropExtension (snd (split2 ':' filename))
  case collectErrors ctx path ctx of
    [] -> return ()
    syntaxErrors -> do
      mapM_ display syntaxErrors
      exitFailure

-- case collectErrors ctx path ctx of
--   [] -> return ()
--   errors -> do
--     let n = length errors
--     mapM_ display errors
--     putStrLn $ "=== SUMMARY " ++ replicate 50 '='
--     putStrLn filename
--     putStrLn $ "🚨 " ++ show n ++ " error" ++ (if n == 1 then "" else "s")
--     putStrLn ""
--     exitFailure

testCmd :: FilePath -> [String] -> IO ()
testCmd path patterns = do
  pkg <- load [path]
  ctx <- include "prelude" pkg
  case collectErrors ctx "" ctx of
    [] -> return ()
    syntaxErrors -> do
      mapM_ display syntaxErrors
      exitFailure
  let results = testAll ctx pkg
  mapM_ (putStr . show) results
  let (failures, total) = count results
  putStrLn ""
  putStrLn $ "Ran " ++ show total ++ " tests"
  if failures > 0
    then do
      putStrLn $ " ✅ " ++ show (total - failures) ++ " passed"
      putStrLn $ " ❌ " ++ show failures ++ " failed"
      exitFailure
    else exitSuccess

patchCmd :: FilePath -> [FilePath] -> [FilePath] -> IO ()
patchCmd buildDir patches sources = do
  steps <- plan [] patches
  ctx <- load sources
  case collectErrors ctx "" ctx of
    [] -> return ()
    syntaxErrors -> do
      mapM_ display syntaxErrors
      exitFailure
  -- TODO: display errors
  let build = applyStep ctx steps ctx
  let writeFile (path, id, stmts) = do
        let filename = buildDir </> path ++ "@" ++ intercalate "!" id ++ ".tao"
        putStrLn filename
        error "TODO: tao patch -- writeFile"
  mapM_ writeFile build

buildPythonCmd :: [FilePath] -> [FilePath] -> IO ()
buildPythonCmd patches sources = do
  putStrLn $ "patches: " ++ show patches
  putStrLn $ "sources: " ++ show sources
  steps <- plan [] patches
  putStrLn $ "steps: " ++ show steps
  ctx <- load sources
  case collectErrors ctx "" ctx of
    [] -> return ()
    syntaxErrors -> do
      mapM_ display syntaxErrors
      exitFailure
  putStrLn $ "ctx: " ++ show (map fst ctx)
  -- TODO: display errors
  let ctx' =
        applyStep ctx steps ctx
          & map (\(path, _, stmts) -> (path, stmts))
  putStrLn "TODO: write intermediate patch files"
  let options = Py.defaultBuildOptions
  void $ Py.build options ctx'
