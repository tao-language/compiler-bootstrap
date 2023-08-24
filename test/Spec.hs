import qualified CoreTests
import qualified ExamplesTests
import qualified ParserTests
import qualified TaoTests
import Test.Hspec (hspec)

main :: IO ()
main = hspec $ do
  ParserTests.run
  CoreTests.run
  TaoTests.run
  ExamplesTests.run
