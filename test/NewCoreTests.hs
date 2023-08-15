module NewCoreTests where

import Data.List (delete, union)
import Test.Hspec

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
data Expr
  = Knd
  | IntT
  | Int !Int
  | Ctr !String
  | Typ !String
  | Var !String
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
  | CtrP !String
  | TypP !String
  | VarP !String
  | FunP !Pattern !Pattern
  | AppP !Pattern !Pattern
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
  | UndefinedCtr !String
  | UndefinedTyp !String
  | InconsistentCtr !String !String
  | InconsistentTyp !String !String
  | MissingType !String
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
let' ((p, a) : defs) b = App (Lam p (let' defs b)) a

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

app :: Expr -> [Expr] -> Expr
app = foldl App

-- Helper functions
pop :: Eq k => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

pushAll :: [(String, Expr)] -> Env -> Env
pushAll vars env = foldr (:) env vars

popAll :: [String] -> Env -> Env
popAll xs env = foldl (flip pop) env xs

pushVars :: [String] -> Env -> Env
pushVars xs = pushAll (map (\x -> (x, Var x)) xs)

freeVars :: Expr -> [String]
freeVars Knd = []
freeVars IntT = []
freeVars (Int _) = []
freeVars (Var x) = [x]
freeVars (Ctr _) = []
freeVars (Typ _) = []
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
freeVarsP (CtrP _) = []
freeVarsP (TypP _) = []
freeVarsP (AppP p q) = freeVarsP p `union` freeVarsP q
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

instantiate :: [String] -> Type -> (Expr, Substitution)
instantiate _ (For [] a) = (a, [])
instantiate existing (For (x : xs) a) = do
  let y = freshName existing x
  let (b, s) = instantiate (y : existing) (For xs a)
  (eval [(x, Var y)] b, (y, Var y) : s)

apply :: Substitution -> Env -> Env
apply _ [] = []
apply s ((x, Ann a (For xs b)) : env) = (x, Ann a (For xs (eval s b))) : apply s env
apply s (def : env) = def : apply s env

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = apply s1 s2 `union` s1

-- Evaluation
eval :: Env -> Expr -> Expr
eval _ Knd = Knd
eval _ IntT = IntT
eval _ (Int i) = Int i
eval _ (Ctr k) = Ctr k
eval _ (Typ t) = Typ t
eval env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Ann (Var x') _) | x == x' -> Var x
  Just a -> eval env a
  Nothing -> Var x
eval env (Fun a b) = Fun (eval env a) (eval env b)
eval env (Lam p b) = Lam p (eval (pushVars (freeVarsP p) env) b)
eval env (App a b) = case (eval env a, eval env b) of
  (Lam AnyP a, _) -> a
  (Lam KndP a, Knd) -> a
  (Lam IntTP a, IntT) -> a
  (Lam (IntP i) a, Int i') | i == i' -> a
  (Lam (VarP x) a, b) -> eval [(x, b)] a
  (Lam (CtrP k) a, Ctr k') | k == k' -> a
  (Lam (TypP t) a, Typ t') | t == t' -> a
  (Lam (AppP p q) a, App b1 b2) -> eval [] (let' [(p, b1), (q, b2)] a)
  (Lam (FunP p q) a, Fun b1 b2) -> eval [] (let' [(p, b1), (q, b2)] a)
  (Lam ErrP a, Err) -> a
  (Or a1 a2, b) -> case eval [] (App a1 b) of
    Err -> eval [] (App a2 b)
    c -> c
  (a@Ctr {}, b) -> App a b
  (a@Typ {}, b) -> App a b
  (a@Var {}, b) -> App a b
  (a@App {}, b) -> App a b
  (a, b) | isOpen b -> App a b
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
infer :: Env -> Expr -> Either TypeError (Expr, Substitution)
infer _ Knd = Right (Knd, [])
infer _ IntT = Right (Knd, [])
infer _ (Int _) = Right (IntT, [])
infer env (Ctr k) = case lookup k env of
  Just (Ann (Ctr k') ty) | k == k' -> do
    let (t, s) = instantiate (map fst env) ty
    Right (eval (apply s env) t, s)
  Just (Ann (Ctr k') _) -> Left (InconsistentCtr k k')
  Just _ -> Left (MissingType k)
  Nothing -> Left (UndefinedCtr k)
infer env (Typ t) = case lookup t env of
  Just (Ann (Typ t') ty) | t == t' -> do
    let (t, s) = instantiate (map fst env) ty
    Right (eval (apply s env) t, s)
  Just (Ann (Typ t') _) -> Left (InconsistentTyp t t')
  Just _ -> Left (MissingType t)
  Nothing -> Left (UndefinedTyp t)
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let xT = freshName (map fst env) (x ++ "T")
    Right (Var xT, [(xT, Var xT), (x, Ann (Var x) (For [] (Var xT)))])
  Just (Ann (Var x') ty) | x == x' -> do
    let (t, s) = instantiate (map fst env) ty
    Right (eval (apply s env) t, s)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Fun a b) = do
  (_, s) <- infer2 env a b
  Right (Knd, s)
-- Lam !Pattern !Expr
-- App !Expr !Expr
-- Ann !Expr !Type
-- Or !Expr !Expr
-- Fix !String !Expr
-- Op2 !BinaryOp !Expr !Expr
infer _ Err = Right (Err, [])
infer _ _ = error "TODO"

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (apply s1 env) b
  Right ((eval s2 ta, tb), s2 `compose` s1)

-- inferApp :: Env -> (String, Type) -> [Expr] -> Either TypeError (Expr, Substitution)
-- inferApp env (x, ty) args = do
--   let y = freshName (map fst env) x
--   let env' = (y, Ann (Var y) ty) : env
--   infer env' (app (Var y) args)

run :: SpecWith ()
run = describe "--==☯️ Core language ☯️==--" $ do
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (f, g, h) = (Var "f", Var "g", Var "h")

  let factorial f = Fix "f" (Lam (IntP 0) i1 `Or` Lam (VarP "x") (x `mul` App (Var f) (x `sub` i1)))

  it "☯ syntax sugar" $ do
    let' [] x `shouldBe` x
    let' [(VarP "y", z)] x `shouldBe` App (Lam (VarP "y") x) z

    or' [] `shouldBe` Err
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

    lam [] x `shouldBe` x
    lam [VarP "y"] x `shouldBe` Lam (VarP "y") x

    app x [] `shouldBe` x
    app x [y, z] `shouldBe` App (App x y) z

  describe "☯ eval core" $ do
    it "☯ eval const" $ do
      eval [] Knd `shouldBe` Knd
      eval [] IntT `shouldBe` IntT
      eval [] (Int 1) `shouldBe` Int 1
      eval [] Err `shouldBe` Err

    it "☯ eval Ctr" $ do
      let env = [("x", Int 1)]
      eval env (Ctr "A") `shouldBe` Ctr "A"
      eval env (App (Ctr "B") x) `shouldBe` App (Ctr "B") (Int 1)

    it "☯ eval Typ" $ do
      let env = [("x", Int 1)]
      eval env (Typ "T") `shouldBe` Typ "T"
      eval env (App (Typ "U") x) `shouldBe` App (Typ "U") (Int 1)

    it "☯ eval Var" $ do
      let env = [("x", i1), ("y", y), ("b", i2), ("a", b), ("c", Ann c (For ["a"] a))]
      eval env (Var "x") `shouldBe` Int 1
      eval env (Var "y") `shouldBe` Var "y"
      eval env (Var "z") `shouldBe` Var "z"
      eval env (Var "a") `shouldBe` Int 2
      eval env (Var "c") `shouldBe` Var "c"

    it "☯ eval Fun" $ do
      let env = [("x", Int 1), ("y", IntT)]
      eval env (Fun x y) `shouldBe` Fun (Int 1) IntT

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
      eval env (App (Lam (CtrP "A") x) (Ctr "A")) `shouldBe` Int 1
      eval env (App (Lam (CtrP "A") x) (Ctr "B")) `shouldBe` Err
      eval env (App (Lam (TypP "T") x) (Typ "T")) `shouldBe` Int 1
      eval env (App (Lam (TypP "T") x) (Typ "U")) `shouldBe` Err
      eval env (App (Lam (AppP (CtrP "B") (VarP "x")) x) (App (Ctr "B") Knd)) `shouldBe` Knd
      eval env (App (Lam (AppP (TypP "U") (VarP "x")) x) (App (Typ "U") Knd)) `shouldBe` Knd
      eval env (App (Lam (FunP KndP (VarP "x")) x) (Fun IntT Knd)) `shouldBe` Err
      eval env (App (Lam (FunP IntTP (VarP "x")) x) (Fun IntT Knd)) `shouldBe` Knd
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

  describe "☯ infer core" $ do
    it "☯ infer const" $ do
      infer [] Knd `shouldBe` Right (Knd, [])
      infer [] IntT `shouldBe` Right (Knd, [])
      infer [] (Int 1) `shouldBe` Right (IntT, [])
      infer [] Err `shouldBe` Right (Err, [])

    it "☯ infer Ctr" $ do
      let env =
            [ ("C1", Ann (Ctr "C1") (For [] a)),
              ("C2", Ann (Ctr "C2") (For ["a"] a)),
              ("C3", Ann (Ctr "C3") (For ["b"] b)),
              ("C4", Ann (Ctr "C5") (For [] a)),
              ("C5", Ctr "C5"),
              ("b", b)
            ]
      infer env (Ctr "X") `shouldBe` Left (UndefinedCtr "X")
      infer env (Ctr "C1") `shouldBe` Right (a, [])
      infer env (Ctr "C2") `shouldBe` Right (a, [("a", a)])
      infer env (Ctr "C3") `shouldBe` Right (Var "b1", [("b1", Var "b1")])
      infer env (Ctr "C4") `shouldBe` Left (InconsistentCtr "C4" "C5")
      infer env (Ctr "C5") `shouldBe` Left (MissingType "C5")

    it "☯ infer Typ" $ do
      let env =
            [ ("T1", Ann (Typ "T1") (For [] a)),
              ("T2", Ann (Typ "T2") (For ["a"] a)),
              ("T3", Ann (Typ "T3") (For ["b"] b)),
              ("T4", Ann (Typ "T5") (For [] a)),
              ("T5", Typ "T5"),
              ("b", b)
            ]
      infer env (Typ "X") `shouldBe` Left (UndefinedTyp "X")
      infer env (Typ "T1") `shouldBe` Right (a, [])
      infer env (Typ "T2") `shouldBe` Right (a, [("a", a)])
      infer env (Typ "T3") `shouldBe` Right (Var "b1", [("b1", Var "b1")])
      infer env (Typ "T4") `shouldBe` Left (InconsistentTyp "T4" "T5")
      infer env (Typ "T5") `shouldBe` Left (MissingType "T5")

    it "☯ infer Var" $ do
      let (a1, yT) = (Var "a1", Var "yT")
      let env = [("x", Int 1), ("y", y), ("b", Int 2), ("a", b), ("c", Ann c (For ["a"] a))]
      infer env (Var "x") `shouldBe` Right (IntT, [])
      infer env (Var "y") `shouldBe` Right (yT, [("yT", yT), ("y", Ann y (For [] yT))])
      infer env (Var "z") `shouldBe` Left (UndefinedVar "z")
      infer env (Var "a") `shouldBe` Right (IntT, [])
      infer env (Var "c") `shouldBe` Right (a1, [("a1", a1)])

    it "☯ infer Fun" $ do
      let aT = Var "aT"
      let env = [("a", a), ("b", IntT)]
      infer env (Fun x y) `shouldBe` Left (UndefinedVar "x")
      infer env (Fun a y) `shouldBe` Left (UndefinedVar "y")
      infer env (Fun a b) `shouldBe` Right (Knd, [("aT", aT), ("a", Ann a (For [] aT))])

    it "☯ infer Lam" $ do
      True `shouldBe` True

    it "☯ infer App" $ do
      True `shouldBe` True

    it "☯ infer Ann" $ do
      True `shouldBe` True

    it "☯ infer Or" $ do
      True `shouldBe` True

    it "☯ infer Fix" $ do
      True `shouldBe` True

    it "☯ infer Op2" $ do
      True `shouldBe` True

  it "☯ Bool" $ do
    True `shouldBe` True

  it "☯ Maybe" $ do
    True `shouldBe` True

  it "☯ Nat" $ do
    True `shouldBe` True

  it "☯ Vec" $ do
    True `shouldBe` True
