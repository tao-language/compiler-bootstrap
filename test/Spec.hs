module Main where

import qualified CoreTests
-- import qualified ExamplesTests
import qualified ParserTests
import qualified PrettyPrintTests
-- import qualified TaoLangTests
import qualified TaoTests
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  ParserTests.run
  PrettyPrintTests.run
  CoreTests.run
  TaoTests.run

-- TaoLangTests.run
-- ExamplesTests.run
