module Test where

import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap, second))
import Data.List (intercalate)
import Error
import Location
import Tao

data TestResult
  = TestPass String
  | TestFail UnitTest Expr
  deriving (Eq)

isFailure :: TestResult -> Bool
isFailure TestFail {} = True
isFailure _ = False

count :: [TestResult] -> (Int, Int)
count [] = (0, 0)
count (result : results) = do
  let (failures, total) = count results
  case result of
    TestPass {} -> (failures, total + 1)
    TestFail {} -> (failures + 1, total + 1)

instance Show TestResult where
  show :: TestResult -> String
  show result = case result of
    TestPass name -> "✅ " ++ name ++ "\n"
    TestFail (name, test, expect) got -> "❌ " ++ name ++ "\n  > " ++ show (dropMeta test) ++ "\n  " ++ show (dropMeta expect) ++ "\n* " ++ show (dropMeta got) ++ "\n"

type UnitTest = (String, Expr, Pattern)

class TestSome a where
  testSome :: Context -> (UnitTest -> Bool) -> a -> [TestResult]

instance TestSome Package where
  testSome :: Context -> (UnitTest -> Bool) -> Package -> [TestResult]
  testSome ctx filter = concatMap (testSome ctx filter)

instance TestSome Module where
  testSome :: Context -> (UnitTest -> Bool) -> Module -> [TestResult]
  testSome ctx filter (path, stmts) =
    concatMap (\stmt -> testSome ctx filter (path, stmt)) stmts

instance TestSome (String, Stmt) where
  testSome :: Context -> (UnitTest -> Bool) -> (String, Stmt) -> [TestResult]
  testSome ctx filter (path, stmt) = case stmt of
    Import {} -> []
    Let {} -> []
    Bind {} -> []
    TypeDef {} -> []
    Test name expr expect | filter (name, expr, expect) -> testSome ctx filter (path, (name, expr, expect))
    Test {} -> []
    Run {} -> []
    Nop {} -> []

instance TestSome (FilePath, UnitTest) where
  testSome :: Context -> (UnitTest -> Bool) -> (FilePath, UnitTest) -> [TestResult]
  testSome ctx _ (path, (name, expr, expect)) = do
    let name' = if name == "" then show (dropMeta expr) else name
    let cases =
          [ Fun expect (Tag "Pass" []),
            Fun (Var "got") (Tag "Fail" [Var "got"])
          ]
    let (env, test') = compile ctx path (Match expr cases)
    let result = C.eval runtimeOps (C.let' env test')
    -- (error . intercalate "\n")
    --   [ "testSome",
    --     "expr:  " ++ show (dropMeta expr),
    --     "expr': " ++ show (snd $ compile ctx path expr),
    --     "expect: " ++ show (dropMeta expect),
    --     "env: " ++ show (map (Var . fst) env),
    --     intercalate "\n" $ map (\(x, a) -> " - " ++ show (Var x) ++ ": " ++ show (C.dropLet a)) env,
    --     "test: " ++ show (dropMeta $ Match expr cases),
    --     "lower: " ++ show (lower (dropMeta $ Match expr cases)),
    --     "bind: " ++ show (C.bind [] $ lower (dropMeta $ Match expr cases)),
    --     "core: " ++ show test',
    --     "result: " ++ show result,
    --     ""
    --   ]
    case C.typedOf (snd $ C.forOf result) of
      (C.Tag "Pass" _, _) -> [TestPass name']
      -- TODO: Fix this, it's where type errors on tests get reported.
      --       Just check the result for any errors and mark it as failure.
      -- (_, C.Tag "Err" (C.Err e)) -> [TestFail filename pos name expr expect (lift (C.Err e))]
      (C.Tag "Fail" got, _) -> [TestFail (name', dropMeta expr, dropMeta expect) (lift got)]
      -- (got, _) -> [TestFail filename pos name expr expect (lift got)]
      (got, ty) -> error ("Unreachable " ++ name' ++ "\ntest:\n" ++ show (C.Let env test') ++ "\ngot: " ++ show got ++ "\nt: " ++ show ty)

testAll :: (TestSome a) => Context -> a -> [TestResult]
testAll ctx = testSome ctx (const True)
