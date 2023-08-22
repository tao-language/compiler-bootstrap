import qualified CoreTests
-- import ExamplesTests (examplesTests)
import qualified ParserTests
-- import TaoLangTests (taoLangTests)
import qualified TaoTests
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  ParserTests.run
  CoreTests.run
  TaoTests.run

-- taoLangTests
-- examplesTests
