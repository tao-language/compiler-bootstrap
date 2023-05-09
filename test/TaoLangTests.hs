module TaoLangTests where

import qualified Parser as P
import Tao
import TaoLang
import Test.Hspec

taoLangTests :: SpecWith ()
taoLangTests = describe "--==☯ Tao language ☯==--" $ do
  let (a, b) = (Var "a", Var "b")
  let (a', b') = (VarP "a", VarP "b")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (x', y', z') = (VarP "x", VarP "y", VarP "z")
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)

  let eq = Op2 "=="
  let lt = Op2 "<"
  let add = Op2 "+"
  let sub = Op2 "-"
  let mul = Op2 "*"

  let parse' parser src = case parseSome parser src of
        Right (x, P.State {P.source = remaining}) ->
          Right (x, remaining)
        Left (SyntaxError (P.ParserError _ P.State {P.source = remaining})) ->
          Left remaining
        Left (CompileError err) -> Left (show err)

  it "☯ keyword" $ do
    let p = parse' (keyword True "A")
    p "A" `shouldBe` Right (True, "")
    p "ABC" `shouldBe` Left "BC"
    p "A2" `shouldBe` Left "2"
    p "A_" `shouldBe` Left "_"
    p "A'" `shouldBe` Left "'"

  it "☯ identifier" $ do
    let p = parse' (identifier P.lowercase)
    p "" `shouldBe` Left ""
    p "a" `shouldBe` Right ("a", "")
    p "a1" `shouldBe` Right ("a1", "")
    p "_a1" `shouldBe` Right ("_a1", "")

  it "☯ commentSingleLine" $ do
    let p = parse' commentSingleLine
    p "" `shouldBe` Left ""
    p "--" `shouldBe` Right ("", "")
    p "--abc" `shouldBe` Right ("abc", "")
    p "-- abc " `shouldBe` Right ("abc ", "")
    p "--  abc  " `shouldBe` Right (" abc  ", "")
    p "-- abc\ndef" `shouldBe` Right ("abc", "def")

  it "☯ commentMultiLine" $ do
    let p = parse' commentMultiLine
    p "" `shouldBe` Left ""
    p "{----}" `shouldBe` Right ("", "")
    p "{--abc--}" `shouldBe` Right ("abc", "")
    p "{-- abc --}" `shouldBe` Right ("abc", "")
    p "{--  abc  --}" `shouldBe` Right (" abc ", "")
    p "{-- abc\ndef --}" `shouldBe` Right ("abc\ndef", "")

  it "☯ comments" $ do
    let p = parse' comments
    p "" `shouldBe` Right ("", "")
    p "-- a" `shouldBe` Right ("a", "")
    p "-- a\n-- b" `shouldBe` Right ("a\nb", "")
    p "-- a\n{-- b --}" `shouldBe` Right ("a\nb", "")
    p "{-- a --}\n-- b" `shouldBe` Right ("a\nb", "")

  it "☯ token" $ do
    let p = parse' (P.zeroOrMore (token P.letter))
    p "abc.d" `shouldBe` Right ("abc", ".d")
    p "a b c . d" `shouldBe` Right ("abc", ". d")

  it "☯ pattern" $ do
    let p = parse' pattern'
    p "_" `shouldBe` Right (AnyP, "")
    p "x" `shouldBe` Right (VarP "x", "")
    p "A" `shouldBe` Right (CtrP "A" [], "")
    p "B x y" `shouldBe` Right (CtrP "B" [x', y'], "")
    p "(_)" `shouldBe` Right (AnyP, "")
    p "(x)" `shouldBe` Right (VarP "x", "")
    p "(A)" `shouldBe` Right (CtrP "A" [], "")
    p "(B x y)" `shouldBe` Right (CtrP "B" [x', y'], "")

  it "☯ expression" $ do
    let p = parse' (expression 0)
    p "Type" `shouldBe` Right (Knd, "")
    p "Int" `shouldBe` Right (IntT, "")
    p "42" `shouldBe` Right (Int 42, "")
    p "3.14" `shouldBe` Right (Num 3.14, "")
    p "x" `shouldBe` Right (Var "x", "")
    p "A" `shouldBe` Right (Var "A", "")
    p "@forall x. y" `shouldBe` Right (For "x" y, "")
    p "@forall x y. z" `shouldBe` Right (for ["x", "y"] z, "")
    p "\\x = 1" `shouldBe` Right (Match [Case [x'] i1], "")
    p "\\x y = 1" `shouldBe` Right (Match [Case [x', y'] i1], "")
    p "\\x = 1 | y = 2" `shouldBe` Right (Match [Case [x'] i1, Case [y'] i2], "")
    p "x = 1; a" `shouldBe` Right (Let [Def [] x' i1] a, "")
    p "x = 1\na" `shouldBe` Right (Let [Def [] x' i1] a, "")
    p "x = 1; y = 2; a" `shouldBe` Right (Let [Def [] x' i1, Def [] y' i2] a, "")
    p "x = 1\ny = 2\na" `shouldBe` Right (Let [Def [] x' i1, Def [] y' i2] a, "")
    p "@typeof x" `shouldBe` Right (TypeOf x, "")
    p "x -> y" `shouldBe` Right (Fun x y, "")
    p "x == y" `shouldBe` Right (eq x y, "")
    p "x < y" `shouldBe` Right (lt x y, "")
    p "x + y" `shouldBe` Right (add x y, "")
    p "x - y" `shouldBe` Right (sub x y, "")
    p "x * y" `shouldBe` Right (mul x y, "")
    p "x y" `shouldBe` Right (App x y, "")
    p "(x)" `shouldBe` Right (x, "")

  describe "☯ operator precedence" $ do
    it "☯ Let" $ do
      let p = parse' (expression 0)
      p "x = 1; y = 2; z" `shouldBe` Right (Let [Def [] x' i1, Def [] y' i2] z, "")
      p "x = 1; @forall y. z" `shouldBe` Right (Let [Def [] x' i1] (For "y" z), "")
      p "x = 1; @typeof y" `shouldBe` Right (Let [Def [] x' i1] (TypeOf y), "")
      p "x = 1; y == z" `shouldBe` Right (Let [Def [] x' i1] (eq y z), "")
      p "x = 1; y -> z" `shouldBe` Right (Let [Def [] x' i1] (Fun y z), "")
      p "x = 1; y < z" `shouldBe` Right (Let [Def [] x' i1] (lt y z), "")
      p "x = 1; y + z" `shouldBe` Right (Let [Def [] x' i1] (add y z), "")
      p "x = 1; y - z" `shouldBe` Right (Let [Def [] x' i1] (sub y z), "")
      p "x = 1; y * z" `shouldBe` Right (Let [Def [] x' i1] (mul y z), "")
      p "x = 1; y z" `shouldBe` Right (Let [Def [] x' i1] (App y z), "")

    it "☯ For" $ do
      let p = parse' (expression 0)
      p "@forall x. y = 1; z" `shouldBe` Right (For "x" (Let [Def [] y' i1] z), "")
      p "@forall x. @forall y. z" `shouldBe` Right (For "x" (For "y" z), "")
      p "@forall x. @typeof y" `shouldBe` Right (For "x" (TypeOf y), "")
      p "@forall x. y == z" `shouldBe` Right (eq (For "x" y) z, "")
      p "@forall x. y -> z" `shouldBe` Right (For "x" (Fun y z), "")
      p "@forall x. y < z" `shouldBe` Right (For "x" (lt y z), "")
      p "@forall x. y + z" `shouldBe` Right (For "x" (add y z), "")
      p "@forall x. y - z" `shouldBe` Right (For "x" (sub y z), "")
      p "@forall x. y * z" `shouldBe` Right (For "x" (mul y z), "")
      p "@forall x. y z" `shouldBe` Right (For "x" (App y z), "")

    it "☯ TypeOf" $ do
      let p = parse' (expression 0)
      p "@typeof x = 1; y" `shouldBe` Right (TypeOf (Let [Def [] x' i1] y), "")
      p "@typeof @forall x. y" `shouldBe` Right (TypeOf (For "x" y), "")
      p "@typeof @typeof x" `shouldBe` Right (TypeOf (TypeOf x), "")
      p "@typeof x == y" `shouldBe` Right (eq (TypeOf x) y, "")
      p "@typeof x -> y" `shouldBe` Right (TypeOf (Fun x y), "")
      p "@typeof x < y" `shouldBe` Right (TypeOf (lt x y), "")
      p "@typeof x + y" `shouldBe` Right (TypeOf (add x y), "")
      p "@typeof x - y" `shouldBe` Right (TypeOf (sub x y), "")
      p "@typeof x * y" `shouldBe` Right (TypeOf (mul x y), "")
      p "@typeof x y" `shouldBe` Right (TypeOf (App x y), "")

    it "☯ Eq (==)" $ do
      let p = parse' (expression 0)
      p "x == y = 1; z" `shouldBe` Right (eq x (Let [Def [] y' i1] z), "")
      p "x == @forall y. z" `shouldBe` Right (eq x (For "y" z), "")
      p "x == @typeof y" `shouldBe` Right (eq x (TypeOf y), "")
      p "x == y == z" `shouldBe` Right (eq (eq x y) z, "")
      p "x == y -> z" `shouldBe` Right (eq x (Fun y z), "")
      p "x == y < z" `shouldBe` Right (eq x (lt y z), "")
      p "x == y + z" `shouldBe` Right (eq x (add y z), "")
      p "x == y - z" `shouldBe` Right (eq x (sub y z), "")
      p "x == y * z" `shouldBe` Right (eq x (mul y z), "")
      p "x == y z" `shouldBe` Right (eq x (App y z), "")

    it "☯ Fun (->)" $ do
      let p = parse' (expression 0)
      p "x -> y = 1; z" `shouldBe` Right (Fun x (Let [Def [] y' i1] z), "")
      p "x -> @forall y. z" `shouldBe` Right (Fun x (For "y" z), "")
      p "x -> @typeof y" `shouldBe` Right (Fun x (TypeOf y), "")
      p "x -> y == z" `shouldBe` Right (eq (Fun x y) z, "")
      p "x -> y -> z" `shouldBe` Right (Fun x (Fun y z), "")
      p "x -> y < z" `shouldBe` Right (Fun x (lt y z), "")
      p "x -> y + z" `shouldBe` Right (Fun x (add y z), "")
      p "x -> y - z" `shouldBe` Right (Fun x (sub y z), "")
      p "x -> y * z" `shouldBe` Right (Fun x (mul y z), "")
      p "x -> y z" `shouldBe` Right (Fun x (App y z), "")

    it "☯ Lt (<)" $ do
      let p = parse' (expression 0)
      p "x < y = 1; z" `shouldBe` Right (lt x (Let [Def [] y' i1] z), "")
      p "x < @forall y. z" `shouldBe` Right (lt x (For "y" z), "")
      p "x < @typeof y" `shouldBe` Right (lt x (TypeOf y), "")
      p "x < y == z" `shouldBe` Right (eq (lt x y) z, "")
      p "x < y -> z" `shouldBe` Right (Fun (lt x y) z, "")
      p "x < y < z" `shouldBe` Right (lt (lt x y) z, "")
      p "x < y + z" `shouldBe` Right (lt x (add y z), "")
      p "x < y - z" `shouldBe` Right (lt x (sub y z), "")
      p "x < y * z" `shouldBe` Right (lt x (mul y z), "")
      p "x < y z" `shouldBe` Right (lt x (App y z), "")

    it "☯ Add (+)" $ do
      let p = parse' (expression 0)
      p "x + y = 1; z" `shouldBe` Right (add x (Let [Def [] y' i1] z), "")
      p "x + @forall y. z" `shouldBe` Right (add x (For "y" z), "")
      p "x + @typeof y" `shouldBe` Right (add x (TypeOf y), "")
      p "x + y == z" `shouldBe` Right (eq (add x y) z, "")
      p "x + y -> z" `shouldBe` Right (Fun (add x y) z, "")
      p "x + y < z" `shouldBe` Right (lt (add x y) z, "")
      p "x + y + z" `shouldBe` Right (add (add x y) z, "")
      p "x + y - z" `shouldBe` Right (sub (add x y) z, "")
      p "x + y * z" `shouldBe` Right (add x (mul y z), "")
      p "x + y z" `shouldBe` Right (add x (App y z), "")

    it "☯ Sub (-)" $ do
      let p = parse' (expression 0)
      p "x - y = 1; z" `shouldBe` Right (sub x (Let [Def [] y' i1] z), "")
      p "x - @forall y. z" `shouldBe` Right (sub x (For "y" z), "")
      p "x - @typeof y" `shouldBe` Right (sub x (TypeOf y), "")
      p "x - y == z" `shouldBe` Right (eq (sub x y) z, "")
      p "x - y -> z" `shouldBe` Right (Fun (sub x y) z, "")
      p "x - y < z" `shouldBe` Right (lt (sub x y) z, "")
      p "x - y + z" `shouldBe` Right (add (sub x y) z, "")
      p "x - y - z" `shouldBe` Right (sub (sub x y) z, "")
      p "x - y * z" `shouldBe` Right (sub x (mul y z), "")
      p "x - y z" `shouldBe` Right (sub x (App y z), "")

    it "☯ Mul (*)" $ do
      let p = parse' (expression 0)
      p "x * y = 1; z" `shouldBe` Right (mul x (Let [Def [] y' i1] z), "")
      p "x * @forall y. z" `shouldBe` Right (mul x (For "y" z), "")
      p "x * @typeof y" `shouldBe` Right (mul x (TypeOf y), "")
      p "x * y == z" `shouldBe` Right (eq (mul x y) z, "")
      p "x * y -> z" `shouldBe` Right (Fun (mul x y) z, "")
      p "x * y < z" `shouldBe` Right (lt (mul x y) z, "")
      p "x * y + z" `shouldBe` Right (add (mul x y) z, "")
      p "x * y - z" `shouldBe` Right (sub (mul x y) z, "")
      p "x * y * z" `shouldBe` Right (mul (mul x y) z, "")
      p "x * y z" `shouldBe` Right (mul x (App y z), "")

    it "☯ App" $ do
      let p = parse' (expression 0)
      p "x @forall y. z" `shouldBe` Right (App x (For "y" z), "")
      p "x @typeof y" `shouldBe` Right (App x (TypeOf y), "")
      p "x y == z" `shouldBe` Right (eq (App x y) z, "")
      p "x y -> z" `shouldBe` Right (Fun (App x y) z, "")
      p "x y < z" `shouldBe` Right (lt (App x y) z, "")
      p "x y + z" `shouldBe` Right (add (App x y) z, "")
      p "x y - z" `shouldBe` Right (sub (App x y) z, "")
      p "x y * z" `shouldBe` Right (mul (App x y) z, "")
      p "x y z" `shouldBe` Right (App (App x y) z, "")

  it "☯ defineRules" $ do
    let types = [("x", a)]
    let p = parse' (defineRules types)
    p "x = 1" `shouldBe` Right (Def types x' i1, "")
    p "x y = 1" `shouldBe` Right (Def types x' (Lam y' i1), "")
    p "x y z = 1" `shouldBe` Right (Def types x' (lam [y', z'] i1), "")
    p "x y = 1; x z = 2" `shouldBe` Right (Def types x' (Match [Case [y'] i1, Case [z'] i2]), "")
    p "x y = 1\nx z = 2" `shouldBe` Right (Def types x' (Match [Case [y'] i1, Case [z'] i2]), "")

  it "☯ definePattern" $ do
    let types = [("x", a)]
    let p = parse' (definePattern types)
    p "A x y = z" `shouldBe` Right (Def types (CtrP "A" [x', y']) z, "")

  it "☯ defineType" $ do
    let (a, n) = (Var "a", Var "n")
    let boolT = Var "Bool"
    let maybeT a = App (Var "Maybe") a
    let vecT n a = app (Var "Vec") [n, a]
    let p = parse' defineType
    p "Bool = True : Bool | False : Bool" `shouldBe` Right (DefT "Bool" [] [("True", boolT), ("False", boolT)], "")
    p "Bool = True | False" `shouldBe` Right (DefT "Bool" [] [("True", boolT), ("False", boolT)], "")
    p "Maybe (a : Type) = Just : a -> Maybe a | Nothing : Maybe a" `shouldBe` Right (DefT "Maybe" [("a", Knd)] [("Just", Fun a (maybeT a)), ("Nothing", maybeT a)], "")
    p "Maybe a = Just a | Nothing" `shouldBe` Right (DefT "Maybe" [("a", Knd)] [("Just", Fun a (maybeT a)), ("Nothing", maybeT a)], "")
    p "Vec (n : Int) (a : Type) = Cons : a -> Vec n a -> Vec (n + 1) a | Nil : Vec 0 a" `shouldBe` Right (DefT "Vec" [("n", IntT), ("a", Knd)] [("Cons", fun [a, vecT n a] (vecT (add n (Int 1)) a)), ("Nil", vecT (Int 0) a)], "")
    p "Vec (n : Int) a = Cons : a -> Vec n a -> Vec (n + 1) a | Nil : Vec 0 a" `shouldBe` Right (DefT "Vec" [("n", IntT), ("a", Knd)] [("Cons", fun [a, vecT n a] (vecT (add n (Int 1)) a)), ("Nil", vecT (Int 0) a)], "")

  it "☯ define" $ do
    let p = parse' define
    p "x : a = 1" `shouldBe` Right (Def [("x", a)] x' i1, "")
    p "x = 1" `shouldBe` Right (Def [] x' i1, "")
    p "x y = 1" `shouldBe` Right (Def [] x' (Lam y' i1), "")
    p "A x y = 1" `shouldBe` Right (Def [] (CtrP "A" [x', y']) i1, "")
    p "x : a; x = 1" `shouldBe` Right (Def [("x", a)] x' i1, "")
    p "x : a\nx = 1" `shouldBe` Right (Def [("x", a)] x' i1, "")
    p "x : a; y : b; A x y = 1" `shouldBe` Right (Def [("x", a), ("y", b)] (CtrP "A" [x', y']) i1, "")
    p "x : a\ny : b\nA x y = 1" `shouldBe` Right (Def [("x", a), ("y", b)] (CtrP "A" [x', y']) i1, "")
    p "Bool = True | False" `shouldBe` Right (DefT "Bool" [] [("True", Var "Bool"), ("False", Var "Bool")], "")
