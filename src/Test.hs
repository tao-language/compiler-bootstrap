module Test where

import qualified Core as C
import Data.List (intercalate)
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

instance Show TestResult where
  show :: TestResult -> String
  show result = case result of
    TestPass filename pos name -> "✅ " ++ filename ++ ":" ++ show pos.row ++ ":" ++ show pos.col ++ " -- " ++ name ++ "\n"
    TestFail filename pos name test expect got -> "❌ " ++ filename ++ ":" ++ show pos.row ++ ":" ++ show pos.col ++ " -- " ++ name ++ "\n  > " ++ show test ++ "\n  " ++ show expect ++ "\n* " ++ show got ++ "\n"

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

instance TestSome (FilePath, UnitTest) where
  testSome :: Context -> (UnitTest -> Bool) -> (FilePath, UnitTest) -> [TestResult]
  testSome ctx _ (path, t) = do
    let cases =
          [ For [] (Fun t.expect (Tag ":Ok" [])),
            fun [Var "$got"] (Var "$got")
          ]
    let (env, test') = compile ctx path (Match t.expr cases)
    case C.eval runtimeOps (C.Let env test') of
      C.Ann (C.Tag ":Ok") _ -> [TestPass t.filename t.pos t.name]
      C.Tag ":Ok" -> [TestPass t.filename t.pos t.name]
      got -> [TestFail t.filename t.pos t.name t.expr t.expect (dropTypes $ lift got)]

testAll :: (TestSome a) => Context -> a -> [TestResult]
testAll ctx = testSome ctx (const True)
