module LoadTests where

import qualified Core as C
import Data.Bifunctor (Bifunctor (first))
import Load
import qualified Parser as P
import System.Directory (withCurrentDirectory)
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Load ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")

  it "☯ loadModule" $ do
    let ctx = [("exists", [])]
    let loadModule' = loadModule ctx
    loadModule' "exists" `shouldReturn` [("exists", [])]
    loadModule' "examples/empty" `shouldReturn` [("examples/empty", []), ("examples/empty/empty-file", []), ("exists", [])]
    loadModule' "examples:empty" `shouldReturn` [("empty", []), ("empty/empty-file", []), ("exists", [])]

  it "☯ load" $ do
    let ctx =
          [ ("examples/empty", []),
            ("examples/empty/empty-file", []),
            ( "examples/sub/mod",
              [ Def (x, Int 1),
                Def (y, Int 2)
              ]
            )
          ]
    result <- load ["examples/sub", "examples/empty"]
    dropMeta result `shouldBe` ctx
