import CoreTests (coreTests)
import ParserTests (parserTests)
import ReducerTests (reducerTests)
import TaoTests (taoTests)
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  parserTests
  coreTests
  taoTests
  reducerTests
