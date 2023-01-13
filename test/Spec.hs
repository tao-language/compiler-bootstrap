import Core2Tests (core2Tests)
import Core3Tests (core3Tests)
import CoreTests (coreTests)
import ExamplesTests (examplesTests)
import ParserTests (parserTests)
import Tao2Tests (tao2Tests)
import TaoLangTests (taoLangTests)
import TaoTests (taoTests)
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  parserTests
  coreTests
  taoTests
  taoLangTests
  examplesTests
  core2Tests
  tao2Tests
  core3Tests
