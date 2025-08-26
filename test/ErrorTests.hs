module ErrorTests where

import Data.Maybe (fromMaybe)
import Error
import Location
import qualified Parser as P
import Tao
import Test.Hspec

data ParserResult a
  = Ok a [Error Expr]
  | Crash
      { location :: String,
        committed :: String,
        expected :: String,
        remaining :: String
      }
  deriving (Eq, Show)

checkExpr :: String -> String -> ParserResult String
checkExpr name txt = case P.parse (parseExpr 0) name txt of
  Right (a, s) -> Ok (show $ dropMeta a) (check a)
  Left s ->
    Crash
      { location = (s.filename ++ ":" ++ show s.pos),
        committed = s.committed,
        expected = s.expected,
        remaining = s.remaining
      }

checkModuleText :: String -> String -> ParserResult [String]
checkModuleText name txt = case P.parse (parseModule name) name txt of
  Right (a, s) -> error "TODO"
  Left s -> error "TODO"

checkModuleFile :: String -> IO (ParserResult [String])
checkModuleFile filename = do
  contents <- readFile filename
  return $ checkModuleText filename contents

run :: SpecWith ()
run = describe "--==☯ Errors ☯==--" $ do
  let loc name r1 c1 r2 c2 = Location name (Range (Pos r1 c1) (Pos r2 c2))

  it "☯ Error.expr.syntax" $ do
    checkExpr "expr" "" `shouldBe` Crash "expr:1:1" "" "" ""
    checkExpr "expr" "$" `shouldBe` Crash "expr:1:1" "" "" "$"
    checkExpr "expr" "x" `shouldBe` Ok "x" []
    checkExpr "expr" "[$]" `shouldBe` Ok "[!error]" [SyntaxError (loc "expr" 1 2 1 3, "", "list item", "$")]
    checkExpr "expr" "[$, x]" `shouldBe` Ok "[!error, x]" [SyntaxError (loc "expr" 1 2 1 3, "", "list item", "$")]
    checkExpr "expr" "[x, $]" `shouldBe` Ok "[x, !error]" [SyntaxError (loc "expr" 1 5 1 6, "", "list item", "$")]
    checkExpr "expr" "[x, $, y]" `shouldBe` Ok "[x, !error, y]" [SyntaxError (loc "expr" 1 5 1 6, "", "list item", "$")]
    checkExpr "expr" "[$, $]" `shouldBe` Ok "[!error, !error]" [SyntaxError (loc "expr" 1 2 1 3, "", "list item", "$"), SyntaxError (loc "expr" 1 5 1 6, "", "list item", "$")]
    checkExpr "expr" "[x" `shouldBe` Crash "expr:1:1" "" "" "[x"

  -- it "☯ Error.expr.type" $ do
  --   "" `shouldBe` ""
  -- it "☯ Error.expr.case" $ do
  --   "" `shouldBe` ""

  it "☯ Error.module.syntax" $ do
    "" `shouldBe` ""
