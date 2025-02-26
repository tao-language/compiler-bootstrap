module Test where

import Compile (compile, lift)
import qualified Core as C
import Data.List (intercalate)
import Tao

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
    let (env, expr) = compile ctx path t.expr
    let expect = let (env', a) = compile ctx path (Fun t.expect (Tag ":Ok")) in C.let' (env' ++ env) a
    let test' = expect `C.Or` C.For "got" (C.Fun (C.Var "got") (C.Var "got"))
    -- error . intercalate "\n" $
    --   [ "-- testSome",
    --     "ctx = " ++ show (map fst ctx),
    --     "env = " ++ C.format (C.Let env C.Any),
    --     "      " ++ show (map fst env),
    --     "expr = " ++ C.format expr,
    --     "expect = " ++ C.format expect,
    --     "eval expect: " ++ C.format (C.eval runtimeOps expect),
    --     "eval expr:   " ++ C.format (C.eval runtimeOps (C.let' env expr)),
    --     "eval test:   " ++ C.format (C.eval runtimeOps (C.App test' (C.let' env expr))),
    --     ""
    --   ]
    case C.eval runtimeOps (C.App test' (C.let' env expr)) of
      C.Tag ":Ok" -> [TestPass t.filename t.pos t.name]
      got -> [TestFail t.filename t.pos t.name t.expr t.expect (lift got)]

testAll :: (TestSome a) => Context -> a -> [TestResult]
testAll ctx = testSome ctx (const True)
