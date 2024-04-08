{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module ExamplesTests where

import Core (Metadata (..))
import Data.Bifunctor (second)
import Tao
import TaoLang
import Test.Hspec

package' :: String -> IO [(String, [Statement])]
package' name = do
  pkg <- package name (Package {name = name, modules = []})
  return (dropMetadataPackage pkg).modules

run :: SpecWith ()
run = describe "--==☯ Examples ☯==--" $ do
  let comment = Comment []
  let (x, y) = (Var "x", Var "y")

  it "☯ empty" $ do
    let name = "examples/empty.tao"
    let stmts = []
    package' name `shouldReturn` [(name, stmts)]

  it "☯ comments" $ do
    let name = "examples/comments.tao"
    let stmts = [comment "A line starting with '#' is a comment."]
    package' name `shouldReturn` [(name, stmts)]

  -- it "☯ comments-multiline" $ do
  --   let pkg = Package {name = "pkg", modules = []}
  --   let name = "examples/comments-multiline.tao"
  --   let stmts = []
  --   package name pkg `shouldReturn` pkg {modules = [(name, stmts)]}

  it "☯ variables" $ do
    let name = "examples/variables.tao"
    let stmts =
          [ comment "Simple variable definitions.",
            Def [] x (Int 42),
            Def [] y (Num 3.14)
          ]
    package' name `shouldReturn` [(name, stmts)]

  it "☯ variables-typed" $ do
    let name = "examples/variables-typed.tao"
    let stmts =
          [ comment "A typed variable definition.",
            Def [] (Ann x (For [] IntT)) (Int 42),
            comment "The type annotation can also live in its own line.",
            Def [("y", For [] NumT)] y (Num 3.14)
          ]
    package' name `shouldReturn` [(name, stmts)]

  it "☯ tests" $ do
    let name = "examples/tests.tao"
    let stmts =
          [ Def [] x (Int 42),
            comment "Prompt-like example.",
            Test x (Int 42),
            comment "Single line prompt example.",
            Test x (Int 42),
            comment "Assertions.",
            Test (x `eq` Int 42) (Tag "True"),
            Test (x `gt` Int 0) (Tag "True"),
            comment "Type assertion.",
            Test (Ann x (For [] IntT)) x
          ]
    package' name `shouldReturn` [(name, stmts)]
