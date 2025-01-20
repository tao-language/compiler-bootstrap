module Main where

import qualified CoreTests
import qualified ExamplesTests
import qualified OperatorPrecedenceTests
import qualified ParserTests
import qualified PatchTests
import qualified PrettyPrintTests
import qualified PythonTests
import qualified TaoParserTests
import qualified TaoTests
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  ParserTests.run
  PrettyPrintTests.run
  CoreTests.run
  TaoTests.run
  TaoParserTests.run
  OperatorPrecedenceTests.run
  PatchTests.run
  ExamplesTests.run
  PythonTests.run
