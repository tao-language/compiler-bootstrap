module GrammarTests where

import Grammar
import qualified Parser as P
import qualified PrettyPrint as PP
import Test.Hspec

data AST
  = Var String
  | Neg AST
  | Fac AST
  | At AST
  | Add AST AST
  | Sub AST AST
  | Mul AST AST
  | App AST AST
  | Pow AST AST
  | If AST AST AST
  deriving (Eq, Show)

grammar :: Grammar String AST
grammar =
  Grammar
    { group = ("(", ")"),
      operators =
        [ atom (const Var) (P.oneOrMore P.letter) $ \_ -> \case
            Var x -> Just [PP.Text x]
            _ -> Nothing,
          infixL 1 (const Add) "+" $ \case
            Add a b -> Just (a, " ", b)
            _ -> Nothing,
          infixL 1 (const Sub) "-" $ \case
            Sub a b -> Just (a, " ", b)
            _ -> Nothing,
          infixL 2 (const Mul) "*" $ \case
            Mul a b -> Just (a, " ", b)
            _ -> Nothing,
          prefix 3 (const Neg) "-" $ \case
            Neg a -> Just ("", a)
            _ -> Nothing,
          infixR 4 (const Pow) "^" $ \case
            Pow a b -> Just (a, " ", b)
            _ -> Nothing,
          suffix 5 (const Fac) "!" $ \case
            Fac a -> Just (a, "")
            _ -> Nothing,
          prefix 5 (const At) "@" $ \case
            At a -> Just ("", a)
            _ -> Nothing
        ]
    }

test :: Int -> String -> Either ([String], String) (AST, String, String)
test width text = case P.parse (parser grammar 0) "<GrammarTests>" text of
  Right (x, s) -> do
    Right (x, format grammar width ("  ", "") x, s.remaining)
  Left s -> Left (s.context, s.remaining)

run :: SpecWith ()
run = describe "--==☯ Grammar ☯==--" $ do
  let (x, y, z) = (Var "x", Var "y", Var "z")
  it "☯ parse-format" $ do
    test 80 "% " `shouldBe` Left ([], "% ")
    test 80 "x " `shouldBe` Right (x, "x", "")
    test 80 "-x " `shouldBe` Right (Neg x, "-x", "")
    test 80 "- x " `shouldBe` Right (Neg x, "-x", "")
    test 80 "x! " `shouldBe` Right (Fac x, "x!", "")
    test 80 "-x! " `shouldBe` Right (Neg (Fac x), "-x!", "")
    test 80 "@x! " `shouldBe` Right (Fac (At x), "@x!", "")
    test 80 "--x " `shouldBe` Right (Neg (Neg x), "--x", "")
    test 80 "-@x " `shouldBe` Right (Neg (At x), "-@x", "")
    test 80 "@-x " `shouldBe` Left ([], "@-x ")
    test 80 "@(-x) " `shouldBe` Right (At (Neg x), "@(-x)", "")
    test 80 "x + y " `shouldBe` Right (Add x y, "x + y", "")
    test 80 "x - y " `shouldBe` Right (Sub x y, "x - y", "")
    test 80 "x * y " `shouldBe` Right (Mul x y, "x * y", "")
    test 80 "x ^ y " `shouldBe` Right (Pow x y, "x ^ y", "")
    test 80 "-x - -y " `shouldBe` Right (Neg x `Sub` Neg y, "-x - -y", "")
    test 80 "x + y + z " `shouldBe` Right (Add x y `Add` z, "x + y + z", "")
    test 80 "x + y - z " `shouldBe` Right (Add x y `Sub` z, "x + y - z", "")
    test 80 "x - y + z " `shouldBe` Right (Sub x y `Add` z, "x - y + z", "")
    test 80 "x + y * z " `shouldBe` Right (x `Add` Mul y z, "x + y * z", "")
    test 80 "x * y + z " `shouldBe` Right (Mul x y `Add` z, "x * y + z", "")
    test 80 "x * y * z " `shouldBe` Right (Mul x y `Mul` z, "x * y * z", "")
    test 80 "x * y ^ z " `shouldBe` Right (x `Mul` Pow y z, "x * y ^ z", "")
    test 80 "x ^ y * z " `shouldBe` Right (Pow x y `Mul` z, "x ^ y * z", "")
    test 80 "x ^ y ^ z " `shouldBe` Right (x `Pow` Pow y z, "x ^ y ^ z", "")
    test 80 "(x ^ y) ^ z " `shouldBe` Right (Pow x y `Pow` z, "(x ^ y) ^ z", "")
    test 80 "x ^ (y ^ z) " `shouldBe` Right (x `Pow` Pow y z, "x ^ y ^ z", "")
