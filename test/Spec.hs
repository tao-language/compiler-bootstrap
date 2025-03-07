module Main where

import qualified CoreTests
import qualified ExamplesTests
import qualified GrammarTests
import qualified LoadTests
import qualified OperatorPrecedenceTests
import qualified ParserTests
import qualified PatchTests
import qualified PrettyPrintTests
import qualified PythonTests
import qualified TaoTests
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  ParserTests.run
  PrettyPrintTests.run
  GrammarTests.run
  CoreTests.run
  TaoTests.run
  LoadTests.run
  OperatorPrecedenceTests.run
  PatchTests.run
  ExamplesTests.run
  PythonTests.run
