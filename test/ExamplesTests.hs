{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module ExamplesTests where

import Core
import Data.Bifunctor (second)
import Tao
import TaoParser
import Test.Hspec

moduleFiles :: String -> IO [TaoFile]
moduleFiles name = do
  mod <- parseModule name (TaoModule {name = name, files = []})
  return mod.files

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let comment = TaoComment []
  let (x, y) = (TaoVar "x", TaoVar "y")

  it "☯ empty" $ do
    let name = "examples/empty.tao"
    let stmts = []
    moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ comments" $ do
--   let name = "examples/comments.tao"
--   let stmts = [comment "A line starting with '#' is a comment."]
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ comments-multiline" $ do
--   let pkg = Package {name = "pkg", modules = []}
--   let name = "examples/comments-multiline.tao"
--   let stmts = []
--   package name pkg `shouldReturn` pkg {modules = [(name, stmts)]}

-- it "☯ variables" $ do
--   let name = "examples/variables.tao"
--   let stmts =
--         [ comment "Simple variable definitions.",
--           Def [] x (Int 42),
--           Def [] y (Num 3.14)
--         ]
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ variables-typed" $ do
--   let name = "examples/variables-typed.tao"
--   let stmts =
--         [ comment "A typed variable definition.",
--           Def [] (Ann x (For [] IntT)) (Int 42),
--           comment "The type annotation can also live in its own line.",
--           Def [("y", For [] NumT)] y (Num 3.14)
--         ]
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ tests" $ do
--   let name = "examples/tests.tao"
--   let stmts =
--         [ Def [] x (Int 42),
--           comment "Prompt-like example.",
--           Test x (Int 42),
--           comment "Single line prompt example.",
--           Test x (Int 42),
--           comment "Assertions, check for True if no explicit result.",
--           Test (Tag "True") (Tag "True"),
--           comment "Type assertion, just check the type.",
--           Test (Ann x (For [] IntT)) x
--         ]
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ tests-failure" $ do
--   let name = "examples/tests-failure.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ arithmetic" $ do
--   let name = "examples/arithmetic.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ arithmetic-sugar" $ do
--   let name = "examples/arithmetic-sugar.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ arithmetic-division-by-zero" $ do
--   let name = "examples/arithmetic-division-by-zero.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ comparison" $ do
--   let name = "examples/comparison.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ functions" $ do
--   let name = "examples/functions.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ functions-lambda" $ do
--   let name = "examples/functions-lambda.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ functions-application" $ do
--   let name = "examples/functions-application.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ pattern-matching" $ do
--   let name = "examples/pattern-matching.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ union-types" $ do
--   let name = "examples/union-types.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ tuples" $ do
--   let name = "examples/tuples.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ records" $ do
--   let name = "examples/records.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- it "☯ literals-numbers" $ do
--   let name = "examples/literals-numbers.tao"
--   let stmts = []
--   moduleFiles name `shouldReturn` [(name, stmts)]

-- # targets.py
-- def now():
--   return datetime.now()

-- # targets.py.yaml
-- exclude
-- rename
