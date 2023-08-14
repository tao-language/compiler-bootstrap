-- import CoreTests (coreTests)
-- import ExamplesTests (examplesTests)
import qualified NewCoreTests as CoreTests
-- import ParserTests (parserTests)
-- import TaoLangTests (taoLangTests)
-- import TaoTests (taoTests)
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  -- parserTests
  -- coreTests
  -- taoTests
  -- taoLangTests
  -- examplesTests
  CoreTests.run
