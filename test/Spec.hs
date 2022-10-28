import CoreTests (coreTests)
import ParserTests (parserTests)
import TaoLangTests (taoLangTests)
import TaoTests (taoTests)
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  parserTests
  coreTests
  taoTests
  taoLangTests
