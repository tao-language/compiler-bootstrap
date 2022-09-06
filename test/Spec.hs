import CoreTests (coreTests)
import LambdaTests (lambdaTests)
import ParserTests (parserTests)
import ReducerTests (reducerTests)
import TaoTests (taoTests)
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  parserTests
  lambdaTests
  coreTests
  taoTests
  reducerTests
