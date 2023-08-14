module NewCoreTests where

import Data.List (delete, union)
import Test.Hspec

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
data Expr
  = Knd
  | IntT
  | Int !Int
  | Var !String
  | Ctr !String ![Expr]
  | Typ !String ![Expr]
  | Fun !Expr !Expr
  | Lam !Pattern !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Or !Expr !Expr
  | Fix !String !Expr
  | Op2 !BinaryOp !Expr !Expr
  | Err
  deriving (Eq, Show)

data Pattern
  = AnyP
  | KndP
  | IntTP
  | IntP !Int
  | VarP !String
  | CtrP !String ![Pattern]
  | TypP !String ![Pattern]
  | FunP !Pattern !Pattern
  | ErrP
  deriving (Eq, Show)

data Type
  = For ![String] !Expr
  deriving (Eq, Show)

data BinaryOp
  = Add
  | Sub
  | Mul
  | Gt
  deriving (Eq, Show)

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

data TypeError
  = UndefinedVar !String
  deriving (Eq, Show)

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

gt :: Expr -> Expr -> Expr
gt = Op2 Gt

let' :: [(Pattern, Expr)] -> Expr -> Expr
let' [] b = b
-- let' ((x, a) : defs) b = eval [(x, a)] (let' defs b)
let' ((p, a) : defs) b = App (Lam p (let' defs b)) a

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

app :: Expr -> [Expr] -> Expr
app = foldl App

-- Helper functions
freeVars :: Expr -> [String]
freeVars Knd = []
freeVars IntT = []
freeVars (Int _) = []
freeVars (Var x) = [x]
freeVars (Ctr _ args) = foldr (union . freeVars) [] args
freeVars (Typ _ args) = foldr (union . freeVars) [] args
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (Lam p a) = filter (`notElem` freeVarsP p) (freeVars a)
freeVars (Ann a _) = freeVars a
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars Err = []

freeVarsP :: Pattern -> [String]
freeVarsP AnyP = []
freeVarsP KndP = []
freeVarsP IntTP = []
freeVarsP (IntP _) = []
freeVarsP (VarP x) = [x]
freeVarsP (CtrP _ ps) = foldr (union . freeVarsP) [] ps
freeVarsP (TypP _ ps) = foldr (union . freeVarsP) [] ps
freeVarsP (FunP p q) = freeVarsP p `union` freeVarsP q
freeVarsP ErrP = []

freshName :: [String] -> String -> String
freshName existing x = do
  head
    [ name
      | i <- [(0 :: Int) ..],
        let name = if i == 0 then x else x ++ show i,
        name `notElem` existing
    ]

isClosed :: Expr -> Bool
isClosed = null . freeVars

isOpen :: Expr -> Bool
isOpen = not . isClosed

-- Evaluation
eval :: Env -> Expr -> Expr
eval _ Knd = Knd
eval _ IntT = IntT
eval _ (Int i) = Int i
eval env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Ann (Var x') _) | x == x' -> Var x
  Just a -> eval env a
  Nothing -> Var x
eval env (Ctr k args) = Ctr k (eval env <$> args)
eval env (Typ t args) = Typ t (eval env <$> args)
eval env (Fun a b) = Fun (eval env a) (eval env b)
eval env (Lam p b) = do
  let vars = map (\x -> (x, Var x)) (freeVarsP p)
  Lam p (eval (vars ++ env) b)
eval env (App a b) = case (eval env a, eval env b) of
  (Var x, b) -> App (Var x) b
  (Lam AnyP a, _) -> a
  (a, b) | isOpen b -> App a b
  (Lam KndP a, Knd) -> a
  (Lam IntTP a, IntT) -> a
  (Lam (IntP i) a, Int i') | i == i' -> a
  (Lam (VarP x) a, b) -> eval [(x, b)] a
  (Lam (CtrP k ps) a, Ctr k' args) | k == k' -> eval [] (app (lam ps a) args)
  (Lam (TypP t ps) a, Typ t' args) | t == t' -> eval [] (app (lam ps a) args)
  (Lam (FunP p q) a, Fun b1 b2) -> app (lam [p, q] a) [b1, b2]
  (Lam ErrP a, Err) -> a
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err -> eval [] (App a2 b)
    c -> c
  (Fix x a, b) -> eval [(x, Fix x a)] (App a b)
  _patternMismatch -> Err
eval env (Ann a _) = eval env a
eval env (Or a b) = case (eval env a, eval env b) of
  (a, Err) -> a
  (Err, b) -> b
  (Or a1 a2, b) -> Or a1 (Or a2 b)
  (a, b) -> Or a b
eval env (Fix x a) = Fix x (eval ((x, Var x) : env) a)
eval env (Op2 op a b) = case (op, eval env a, eval env b) of
  (Add, Int a, Int b) -> Int (a + b)
  (Sub, Int a, Int b) -> Int (a - b)
  (Mul, Int a, Int b) -> Int (a * b)
  (op, a, b) -> Op2 op a b
eval _ Err = Err

-- Type inference
infer :: Expr -> Either TypeError (Expr, Substitution)
infer a = error "TODO"

run :: SpecWith ()
run = describe "--==☯️ Core language ☯️==--" $ do
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (f, g, h) = (Var "f", Var "g", Var "h")

  let factorial f = Fix "f" (Lam (IntP 0) i1 `Or` Lam (VarP "x") (x `mul` App (Var f) (x `sub` i1)))

  it "☯ syntax sugar" $ do
    let ty = For ["a"] (Var "b")

    let' [] x `shouldBe` x
    let' [(VarP "y", z)] x `shouldBe` App (Lam (VarP "y") x) z
    -- letT [] x `shouldBe` x
    -- letT [("y", ty, z)] x `shouldBe` App (LamT "y" ty x) z

    or' [] `shouldBe` Err
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

    lam [] x `shouldBe` x
    lam [VarP "y"] x `shouldBe` Lam (VarP "y") x
    -- lamT [] x `shouldBe` x
    -- lamT [("y", ty)] x `shouldBe` LamT "y" ty x

    app x [] `shouldBe` x
    app x [y, z] `shouldBe` App (App x y) z

  describe "☯ eval core" $ do
    it "☯ eval const" $ do
      let env = []
      eval env Knd `shouldBe` Knd
      eval env IntT `shouldBe` IntT
      eval env (Int 1) `shouldBe` Int 1

    it "☯ eval Var" $ do
      let env = [("x", Int 1), ("b", Int 2), ("a", Var "b"), ("c", Ann (Var "c") (For [] (Var "t")))]
      eval env (Var "x") `shouldBe` Int 1
      eval env (Var "y") `shouldBe` Var "y"
      eval env (Var "z") `shouldBe` Var "z"
      eval env (Var "a") `shouldBe` Int 2
      eval env (Var "c") `shouldBe` Var "c"

    it "☯ eval Ctr" $ do
      let env = [("x", Int 1)]
      eval env (Ctr "A" []) `shouldBe` Ctr "A" []
      eval env (Ctr "B" [x]) `shouldBe` Ctr "B" [Int 1]

    it "☯ eval Typ" $ do
      let env = [("x", Int 1)]
      eval env (Typ "T" []) `shouldBe` Typ "T" []
      eval env (Typ "U" [x]) `shouldBe` Typ "U" [Int 1]

    it "☯ eval Fun" $ do
      let env = [("x", Int 1), ("y", IntT)]
      eval env (fun [x] y) `shouldBe` fun [Int 1] IntT

    it "☯ eval Lam" $ do
      let env = [("x", Int 1)]
      eval env (Lam (VarP "x") x) `shouldBe` Lam (VarP "x") x
      eval env (Lam (VarP "y") x) `shouldBe` Lam (VarP "y") (Int 1)

    it "☯ eval Or" $ do
      let env = [("x", i1), ("y", i2), ("z", i3)]
      eval env (Or x Err) `shouldBe` i1
      eval env (Or Err y) `shouldBe` i2
      eval env (Or x y) `shouldBe` Or i1 i2
      eval env (Or x (Or y z)) `shouldBe` Or i1 (Or i2 i3)
      eval env (Or (Or x y) z) `shouldBe` Or i1 (Or i2 i3)

    it "☯ eval App" $ do
      let env = [("x", Int 1), ("f", g), ("g", g), ("h", h)]
      eval env (App (Var "f") Knd) `shouldBe` App g Knd
      eval env (App (Lam AnyP x) y) `shouldBe` Int 1
      eval env (App (Lam KndP x) y) `shouldBe` App (Lam KndP (Int 1)) y
      eval env (App (Lam KndP x) Knd) `shouldBe` Int 1
      eval env (App (Lam KndP x) IntT) `shouldBe` Err
      eval env (App (Lam IntTP x) IntT) `shouldBe` Int 1
      eval env (App (Lam (IntP 1) x) (Int 1)) `shouldBe` Int 1
      eval env (App (Lam (IntP 1) x) (Int 2)) `shouldBe` Err
      eval env (App (Lam (VarP "x") x) Knd) `shouldBe` Knd
      eval env (App (Lam (VarP "y") x) Knd) `shouldBe` Int 1
      eval env (App (Lam (CtrP "A" []) x) (Ctr "A" [])) `shouldBe` Int 1
      eval env (App (Lam (CtrP "A" []) x) (Ctr "B" [])) `shouldBe` Err
      eval env (App (Lam (CtrP "B" [VarP "x"]) x) (Ctr "B" [Knd])) `shouldBe` Knd
      eval env (App (Lam (TypP "T" []) x) (Typ "T" [])) `shouldBe` Int 1
      eval env (App (Lam (TypP "T" []) x) (Typ "U" [])) `shouldBe` Err
      eval env (App (Lam (TypP "U" [VarP "x"]) x) (Typ "U" [Knd])) `shouldBe` Knd
      eval env (App (Lam ErrP x) Knd) `shouldBe` Err
      eval env (App (Lam ErrP x) Err) `shouldBe` Int 1
      eval env (App (Or Err Err) Knd) `shouldBe` Err
      eval env (App (Or Err f) Knd) `shouldBe` App g Knd
      eval env (App (Or f Err) Knd) `shouldBe` App g Knd
      eval env (App (Or f h) Knd) `shouldBe` App g Knd
      eval env (App (Fix "f" (Lam (VarP "x") (App h f))) Knd) `shouldBe` App h (Fix "f" (Lam (VarP "x") (App h f)))
      eval env (App Err Knd) `shouldBe` Err
      eval env (App Err Knd) `shouldBe` Err

    it "☯ eval Ann" $ do
      let env = [("x", Int 1)]
      eval env (Ann x (For [] IntT)) `shouldBe` Int 1

    it "☯ eval Op2" $ do
      let env = []
      eval env (add x y) `shouldBe` add x y
      eval env (add x i2) `shouldBe` add x i2
      eval env (add i1 y) `shouldBe` add i1 y

      eval env (add i1 i2) `shouldBe` Int 3
      eval env (sub i1 i2) `shouldBe` Int (-1)
      eval env (mul i1 i2) `shouldBe` Int 2

    it "☯ eval Err" $ do
      eval [] Err `shouldBe` Err

  it "☯ eval factorial" $ do
    let env = [("f", factorial "f")]
    eval env (Var "f") `shouldBe` factorial "f"
    eval env (App f x) `shouldBe` App (factorial "f") x
    eval env (App f (Int 0)) `shouldBe` Int 1
    eval env (App f (Int 1)) `shouldBe` Int 1
    eval env (App f (Int 2)) `shouldBe` Int 2
    eval env (App f (Int 3)) `shouldBe` Int 6
    eval env (App f (Int 4)) `shouldBe` Int 24
    eval env (App f (Int 5)) `shouldBe` Int 120

  it "☯ infer core" $ do
    True `shouldBe` True

  it "☯ infer sugar" $ do
    True `shouldBe` True

  it "☯ Bool" $ do
    True `shouldBe` True

  it "☯ Maybe" $ do
    True `shouldBe` True

  it "☯ Nat" $ do
    True `shouldBe` True

  it "☯ Vec" $ do
    True `shouldBe` True
