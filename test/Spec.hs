import CoreTests (coreTests)
import LambdaTests (lambdaTests)
import ParserTests (parserTests)
import TaoTests (taoTests)
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  parserTests
  lambdaTests
  coreTests
  taoTests
