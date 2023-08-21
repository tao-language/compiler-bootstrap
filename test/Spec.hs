import qualified CoreTests
-- import ExamplesTests (examplesTests)
import qualified ParserTests
-- import TaoLangTests (taoLangTests)
-- import TaoTests (taoTests)
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  ParserTests.run
  CoreTests.run

-- taoTests
-- taoLangTests
-- examplesTests
