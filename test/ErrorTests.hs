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
  Right ((_, stmts), s) -> Ok (map (show . dropMeta) stmts) (check stmts)
  Left s ->
    Crash
      { location = (s.filename ++ ":" ++ show s.pos),
        committed = s.committed,
        expected = s.expected,
        remaining = s.remaining
      }

checkModuleFile :: String -> IO (ParserResult [String])
checkModuleFile filename = do
  contents <- readFile filename
  return $ checkModuleText filename contents

run :: SpecWith ()
run = describe "--==☯ Errors ☯==--" $ do
  let loc name r1 c1 r2 c2 = Location name (Range (Pos r1 c1) (Pos r2 c2))

  it "☯ Error.expr.syntax" $ do
    -- Parsing expressions is allowed to crash, this delimits when the expression stops.
    -- Expressions should attempt to recover when possible and return a valid expression with syntax errors.
    -- Notable exceptions: Do not recover on Infix parsers, they expect a failed parser to stop.
    checkExpr "expr" "" `shouldBe` Crash "expr:1:1" "" "" ""
    checkExpr "expr" "$" `shouldBe` Crash "expr:1:1" "" "" "$"
    checkExpr "expr" "x" `shouldBe` Ok "x" []
    -- Error recovery on collection.
    checkExpr "expr" "[$]" `shouldBe` Ok "[!error]" [SyntaxError (loc "expr" 1 2 1 3, "", "list item", "$")]
    checkExpr "expr" "[$, x]" `shouldBe` Ok "[!error, x]" [SyntaxError (loc "expr" 1 2 1 3, "", "list item", "$")]
    checkExpr "expr" "[x, $]" `shouldBe` Ok "[x, !error]" [SyntaxError (loc "expr" 1 5 1 6, "", "list item", "$")]
    checkExpr "expr" "[x, $, y]" `shouldBe` Ok "[x, !error, y]" [SyntaxError (loc "expr" 1 5 1 6, "", "list item", "$")]
    checkExpr "expr" "[$, $]" `shouldBe` Ok "[!error, !error]" [SyntaxError (loc "expr" 1 2 1 3, "", "list item", "$"), SyntaxError (loc "expr" 1 5 1 6, "", "list item", "$")]
  -- TODO: explicit error about not closing a collection.
  -- checkExpr "expr" "[x" `shouldBe` Ok "TODO" []

  -- it "☯ Error.expr.type" $ do
  --   "" `shouldBe` ""
  -- it "☯ Error.expr.case" $ do
  --   "" `shouldBe` ""

  it "☯ Error.module.syntax" $ do
    -- Parsing modules is NOT allowed to crash, it should always return a valid module.
    -- All parsing errors should be handled and returned as syntax errors within valid expressions.
    -- A `Crash` here is a bug that needs to be fixed, but will give useful debugging info.
    checkModuleText "module" "" `shouldBe` Ok [] []
    checkModuleText "module" " " `shouldBe` Ok [] []
    checkModuleText "module" " //  comment " `shouldBe` Ok ["// comment"] []
    checkModuleText "module" "let x = y" `shouldBe` Ok ["let x = y"] []
    checkModuleText "module" "let x = $" `shouldBe` Ok ["let x = !error"] [SyntaxError (loc "module" 1 9 1 10, "definition", "body", "$")]
    checkModuleText "module" "let x $ y" `shouldBe` Ok ["let x $ y"] [SyntaxError (loc "module" 1 7 1 9, "definition", "'=' or '<-'", "$ ")]
    checkModuleText "module" "let $ = y" `shouldBe` Ok ["let !error $ = y"] [SyntaxError (loc "module" 1 7 1 9, "definition", "'=' or '<-'", "$ ")]
