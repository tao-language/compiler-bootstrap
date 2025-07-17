module Test where

import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap, second))
import Data.List (intercalate)
import Error
import Location
import Tao

data TestResult
  = TestPass
      { filename :: String,
        pos :: Position,
        name :: String
      }
  | TestFail
      { filename :: String,
        pos :: Position,
        name :: String,
        test :: Expr,
        expected :: Expr,
        got :: Expr
      }
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
    TestPass filename pos name -> "✅ " ++ filename ++ ":" ++ show pos.row ++ ":" ++ show pos.col ++ ": " ++ name ++ "\n"
    TestFail filename pos name test expect got -> "❌ " ++ filename ++ ":" ++ show pos.row ++ ":" ++ show pos.col ++ ": " ++ name ++ "\n  > " ++ show (dropMeta test) ++ "\n  " ++ show (dropMeta expect) ++ "\n* " ++ show (dropMeta got) ++ "\n"

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
    Def {} -> []
    TypeDef {} -> []
    Test t | filter t -> testSome ctx filter (path, t)
    Test {} -> []
    Run {} -> []
    Comment {} -> []

instance TestSome (FilePath, UnitTest) where
  testSome :: Context -> (UnitTest -> Bool) -> (FilePath, UnitTest) -> [TestResult]
  testSome ctx _ (path, t) = do
    let name = if t.name == "" then show (dropMeta t.expr) else t.name
    let cases =
          [ Fun t.expect (Tag "Pass" []),
            Fun (Var "got") (Tag "Fail" [Var "got"])
          ]
    let (env, test') = compile ctx path (Match t.expr cases)
    -- (error . intercalate "\n")
    --   [ "testSome",
    --     "expr:  " ++ show (dropMeta t.expr),
    --     "expr': " ++ show (snd $ compile ctx path t.expr),
    --     "expect: " ++ show (dropMeta t.expect),
    --     "env: " ++ show (map (Var . fst) env),
    --     intercalate "\n" $ map (\(x, a) -> "  " ++ show (Var x) ++ ": " ++ show (C.eval runtimeOps $ C.let' env a)) env,
    --     "test: " ++ show (dropMeta $ Match t.expr cases),
    --     "lower: " ++ show (lower (dropMeta $ Match t.expr cases)),
    --     "core: " ++ show test',
    --     "core alts:",
    --     intercalate "\n" $ map (\a -> "  | " ++ show a) (C.orOf test'),
    --     "result: " ++ show (C.eval runtimeOps $ C.let' env test'),
    --     ""
    --   ]
    let result = C.eval' runtimeOps (C.let' env test')
    case C.typedOf (snd $ C.forOf result) of
      (C.Tag "Pass" _, _) -> [TestPass t.filename t.pos name]
      -- TODO: Fix this, it's where type errors on tests get reported.
      --       Just check the result for any errors and mark it as failure.
      -- (_, C.Tag "Err" (C.Err e)) -> [TestFail t.filename t.pos name t.expr t.expect (lift (C.Err e))]
      (C.Tag "Fail" got, _) -> [TestFail t.filename t.pos name (dropMeta t.expr) (dropMeta t.expect) (lift got)]
      -- (got, _) -> [TestFail t.filename t.pos t.name t.expr t.expect (lift got)]
      (got, ty) -> error ("Unreachable " ++ t.filename ++ ":" ++ show t.pos.row ++ ":" ++ show t.pos.col ++ ": " ++ t.name ++ "\ngot: " ++ show got ++ "\nt: " ++ show ty)

testAll :: (TestSome a) => Context -> a -> [TestResult]
testAll ctx = testSome ctx (const True)
