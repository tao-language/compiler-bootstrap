module StdlibTests where

import Stdlib
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Stdlib ☯==--" $ do
  it "☯ split2" $ do
    split2 ':' "" `shouldBe` ("", "")
    split2 ':' "abc" `shouldBe` ("", "abc")
    split2 ':' ":abc" `shouldBe` ("", "abc")
    split2 ':' "a:bc" `shouldBe` ("a", "bc")
    split2 ':' "ab:c" `shouldBe` ("ab", "c")
    split2 ':' "abc:" `shouldBe` ("abc", "")
