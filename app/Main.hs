import Check (checkTypes)
import Control.Monad (void)
import qualified Core as C
import Data.Function ((&))
import Data.List (intercalate, isPrefixOf, isSuffixOf, partition)
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
import Data.Either (fromRight)

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
      _ -> putStrLn "🛑 Please give me a path to check."
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

coreCmd :: FilePath -> String -> IO ()
coreCmd filename arg = do
  pkg <- dropMeta <$> load [filename]
  ctx <- dropMeta <$> include "prelude" pkg
  arg' <- dropMeta <$> loadExpr "<core>" arg
  -- TODO: check for errors
  let path = dropExtension (snd (split2 ':' filename))
  -- let a = lower [] arg'
  -- let env = concatMap (fst . compile ctx path) (C.freeNames (True, True, False) a)
  let a = compile ctx path arg'
  let (env, a') = C.letOf a
  putStrLn $ "core: " ++ show a'
  putStrLn $ "env: " ++ unwords (map fst env)
  mapM_ (\(x, a) -> putStrLn ("  " ++ show (C.Var x) ++ ": " ++ show (C.dropLet a))) env
  mapM_
    ( \a -> do
        putStrLn "----------"
        putStrLn $ "> " ++ show (C.dropMeta a)
        print $ C.dropMeta $ C.dropTypes $ C.eval runtimeOps (C.Let env a)
        -- putStrLn "\n# type substitutions"
        -- mapM_ (\(x, a) -> putStrLn ("  - " ++ fmt (C.Var x) ++ ": " ++ fmt a)) s
        putStrLn ""
    )
    (C.orOf a')
  putStrLn "----------"
  print $ C.dropMeta $ C.dropTypes $ C.eval runtimeOps a

runCmd :: FilePath -> String -> IO ()
runCmd filename arg = do
  ctx <- load [filename]
  ctx <- include "prelude" ctx
  arg' <- loadExpr "<run>" arg
  -- TODO: check for errors
  let path = dropExtension (snd (split2 ':' filename))
  print (dropTypes $ dropMeta $ Run.run ctx path arg')

checkCmd :: FilePath -> IO ()
checkCmd filename = do
  pkg <- load [filename]
  ctx <- include "prelude" pkg
  let path = dropExtension (snd (split2 ':' filename))
  case checkTypes ctx path pkg of
    [] -> return ()
    errors -> do
      let n = length errors
      mapM_ display errors
      putStrLn $ "=== SUMMARY " ++ replicate 50 '='
      putStrLn filename
      putStrLn $ "🚨 " ++ show n ++ " error" ++ (if n == 1 then "" else "s")
      putStrLn ""
      exitFailure

testCmd :: FilePath -> [String] -> IO ()
testCmd path patterns = do
  pkg <- load [path]
  ctx <- include "prelude" pkg
  -- TODO: display errors
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
  putStrLn $ "ctx: " ++ show (map fst ctx)
  -- TODO: display errors
  let ctx' =
        applyStep ctx steps ctx
          & map (\(path, _, stmts) -> (path, stmts))
  putStrLn "TODO: write intermediate patch files"
  let options = Py.defaultBuildOptions
  void $ Py.build options ctx'
