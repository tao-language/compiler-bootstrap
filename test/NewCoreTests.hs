module NewCoreTests where

import Data.List (delete, intercalate, union)
import Test.Hspec

{- TODO:
- Literal types -- (1 : 1), (x : Int), (x + 1 : Int)
- Type aliases

Vec n a
  = Cons : a -> Vec n a -> Vec (n + 1) a
  | Nil : Vec 0 a

Vec = Vec : Int -> Type -> Type

Vec = \n a. @alias Vec (Cons a () | Nothing) : Int -> Type -> Type
Cons = #Cons : @for n a. a -> Vec n a -> Vec (n + 1) a
Nil = #Nil : @for a. Vec 0 a
-}

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
-- https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- https://www.youtube.com/live/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf
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
  deriving (Eq)

instance Show Expr where
  show Knd = "@Type"
  show IntT = "@Int"
  show (Int i) = show i
  show (Ctr k) = "#" ++ k
  show (Typ t) = "%" ++ t
  show (Var x) = x
  show (Fun a b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (Lam p b) = "(\\" ++ show p ++ ". " ++ show b ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (Ann a ty) = "(" ++ show a ++ " : " ++ show ty ++ ")"
  show (Or a b) = "(" ++ show a ++ " | " ++ show b ++ ")"
  show (Fix x a) = "(@fix " ++ x ++ " " ++ show a ++ ")"
  show (Op2 op a b) = "(" ++ show op ++ " " ++ show a ++ " " ++ show b ++ ")"
  show Err = "@err"

data Pattern
  = KndP
  | IntTP
  | IntP !Int
  | CtrP !String
  | TypP !String
  | VarP !String
  | FunP !Pattern !Pattern
  | AppP !Pattern !Pattern
  | ErrP
  deriving (Eq)

instance Show Pattern where
  show p = show (patternValue p)

data Type
  = For ![String] !Expr
  deriving (Eq)

instance Show Type where
  show (For [] t) = show t
  show (For xs t) = "@for " ++ unwords xs ++ ". " ++ show t

data BinaryOp
  = AddI
  | SubI
  | MulI
  deriving (Eq)

instance Show BinaryOp where
  show AddI = "@addI"
  show SubI = "@subI"
  show MulI = "@mulI"

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

data TypeError
  = UndefinedVar !String
  | UndefinedCtr !String
  | UndefinedTyp !String
  | InconsistentCtr !String !String
  | InconsistentTyp !String !String
  | InfiniteType !String !Expr
  | MissingType !String
  | NotAFunction !Expr !Expr
  | TypeMismatch !Expr !Expr
  deriving (Eq, Show)

-- Syntax sugar
fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

addI :: Expr -> Expr -> Expr
addI = Op2 AddI

subI :: Expr -> Expr -> Expr
subI = Op2 SubI

mulI :: Expr -> Expr -> Expr
mulI = Op2 MulI

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

patternValue :: Pattern -> Expr
patternValue KndP = Knd
patternValue IntTP = IntT
patternValue (IntP i) = Int i
patternValue (CtrP k) = Ctr k
patternValue (TypP t) = Typ t
patternValue (VarP x) = Var x
patternValue (FunP p q) = Fun (patternValue p) (patternValue q)
patternValue (AppP p q) = App (patternValue p) (patternValue q)
patternValue ErrP = Err

freeVars :: Expr -> [String]
freeVars Knd = []
freeVars IntT = []
freeVars (Int _) = []
freeVars (Var x) = [x]
freeVars (Ctr _) = []
freeVars (Typ _) = []
freeVars (Fun a b) = freeVars a `union` freeVars b
freeVars (Lam p a) = filter (`notElem` freeVars (patternValue p)) (freeVars a)
freeVars (Ann a _) = freeVars a
freeVars (App a b) = freeVars a `union` freeVars b
freeVars (Or a b) = freeVars a `union` freeVars b
freeVars (Fix x a) = delete x (freeVars a)
freeVars (Op2 _ a b) = freeVars a `union` freeVars b
freeVars Err = []

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

newName :: [String] -> String -> String
newName existing x = do
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
eval _ (Ctr k) = Ctr k
eval _ (Typ t) = Typ t
eval env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> Var x
  Just (Ann (Var x') _) | x == x' -> Var x
  Just a -> eval env a
  Nothing -> Var x
eval env (Fun a b) = case (eval env a, eval env b) of
  (Or a1 a2, b) -> Or (Fun a1 b) (Fun a2 b)
  (a, Or b1 b2) -> Or (Fun a b1) (Fun a b2)
  (a, b) -> Fun a b
eval env (Lam p b) = do
  let xs = freeVars (patternValue p)
  case eval (pushVars xs env) b of
    Or b1 b2 -> Or (Lam p b1) (Lam p b2)
    b -> Lam p b
eval env (App a b) = case (eval env a, eval env b) of
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
  (op, Or a1 a2, b) -> eval [] (Or (Op2 op a1 b) (Op2 op a2 b))
  (op, a, Or b1 b2) -> eval [] (Or (Op2 op a b1) (Op2 op a b2))
  (AddI, Int a, Int b) -> Int (a + b)
  (SubI, Int a, Int b) -> Int (a - b)
  (MulI, Int a, Int b) -> Int (a * b)
  (op, a, b) -> Op2 op a b
eval _ Err = Err

-- Type inference
apply :: Substitution -> Env -> Env
apply _ [] = []
apply s ((x, Ann a (For xs t)) : env) = do
  let t' = eval (pushVars xs s) t
  (x, Ann (eval s a) (For xs t')) : apply s env
apply s ((x, a) : env) = (x, eval s a) : apply s env

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = apply s1 s2 `union` s1

intOps :: [BinaryOp]
intOps = [AddI, SubI, MulI]

instantiate :: [String] -> Type -> (Expr, Substitution)
instantiate _ (For [] a) = (a, [])
instantiate existing (For (x : xs) a) = do
  let y = newName existing x
  let (b, s) = instantiate (y : existing) (For xs a)
  (eval [(x, Var y)] b, [(y, Var y)] `union` s)

unify :: Expr -> Expr -> Either TypeError (Expr, Substitution)
unify Knd Knd = Right (Knd, [])
unify IntT IntT = Right (IntT, [])
unify (Typ t) (Typ t') | t == t' = Right (Typ t, [])
unify (Var x) (Var x') | x == x' = Right (Var x, [])
unify (Var x) b | x `occurs` b = Left (InfiniteType x b)
unify (Var x) b = Right (b, [(x, b)])
unify a (Var x) = unify (Var x) a
unify (Fun a1 b1) (Fun a2 b2) = do
  ((a, b), s) <- unify2 (a1, a2) (b1, b2)
  Right (Fun a b, s)
unify (App a1 b1) (App a2 b2) = do
  ((a, b), s) <- unify2 (a1, a2) (b1, b2)
  Right (App a b, s)
-- Or !Expr !Expr
unify Err Err = Right (Err, [])
unify a b = Left (TypeMismatch a b)

unify2 :: (Expr, Expr) -> (Expr, Expr) -> Either TypeError ((Expr, Expr), Substitution)
unify2 (a1, a2) (b1, b2) = do
  (a, s1) <- unify a1 a2
  (b, s2) <- unify (eval s1 b1) (eval s1 b2)
  Right ((a, b), s2 `compose` s1)

infer :: Env -> Expr -> Either TypeError (Expr, Substitution)
infer _ Knd = Right (Knd, [])
infer _ IntT = Right (Knd, [])
infer _ (Int _) = Right (IntT, [])
infer env (Ctr k) = case lookup k env of
  Just (Ann (Ctr k') ty) | k == k' -> do
    let (t, s) = instantiate (map fst env) ty
    Right (eval (s ++ apply s env) t, s)
  Just (Ann (Ctr k') _) -> Left (InconsistentCtr k k')
  Just _ -> Left (MissingType k)
  Nothing -> Left (UndefinedCtr k)
infer env (Typ t) = case lookup t env of
  Just (Ann (Typ t') ty) | t == t' -> do
    let (t, s) = instantiate (map fst env) ty
    Right (eval (s ++ apply s env) t, s)
  Just (Ann (Typ t') _) -> Left (InconsistentTyp t t')
  Just _ -> Left (MissingType t)
  Nothing -> Left (UndefinedTyp t)
infer env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let xT = newName (map fst env) (x ++ "T")
    Right (Var xT, [(xT, Var xT), (x, Ann (Var x) (For [] (Var xT)))])
  Just (Ann (Var x') ty) | x == x' -> do
    let (t, s) = instantiate (map fst env) ty
    Right (eval (s ++ apply s env) t, s)
  Just a -> infer env a
  Nothing -> Left (UndefinedVar x)
infer env (Fun a b) = do
  (_, s) <- infer2 env a b
  Right (Knd, s)
infer env (Lam p b) = do
  let a = patternValue p
  ((t1, t2), s) <- infer2 (pushVars (freeVars a) env) a b
  Right (Fun t1 t2, s)
infer env (App a b) = do
  ((ta, tb), s1) <- infer2 env a b
  let x = newName (map fst (s1 ++ env)) "t"
  (_, s2) <- unify (Fun tb (Var x)) ta
  let s = s2 `compose` s1
  case eval s (Var x) of
    Var x' | x == x' -> Right (Var x, [(x, Var x)] `compose` s)
    t -> Right (t, s)
infer env (Ann a ty) = do
  (ta, s1) <- infer env a
  let (t, s2) = instantiate (map fst (s1 ++ apply s1 env)) ty
  (t, s3) <- unify (eval s2 ta) t
  Right (t, s3 `compose` s2 `compose` s1)
infer env (Or a b) = do
  ((ta, tb), s1) <- infer2 env a b
  case unify ta tb of
    Right (t, s2) -> Right (t, s2 `compose` s1)
    Left _ -> Right (Or ta tb, s1)
infer env (Fix x a) = infer ((x, Var x) : env) a
infer env (Op2 AddI a b) = do
  (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
  Right (IntT, s)
infer env (Op2 SubI a b) = do
  (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
  Right (IntT, s)
infer env (Op2 MulI a b) = do
  (_, s) <- infer2 env (Ann a (For [] IntT)) (Ann b (For [] IntT))
  Right (IntT, s)
infer _ Err = Right (Err, [])

infer2 :: Env -> Expr -> Expr -> Either TypeError ((Expr, Expr), Substitution)
infer2 env a b = do
  (ta, s1) <- infer env a
  (tb, s2) <- infer (s1 ++ apply s1 env) b
  Right ((eval s2 ta, tb), s2 `compose` s1)

run :: SpecWith ()
run = describe "--==☯️ Core language ☯️==--" $ do
  let (i1, i2, i3) = (Int 1, Int 2, Int 3)
  let (a, b, c) = (Var "a", Var "b", Var "c")
  let (x, y, z) = (Var "x", Var "y", Var "z")
  let (f, g, h) = (Var "f", Var "g", Var "h")

  let (x', y') = (VarP "x", VarP "y")

  let factorial f = Fix "f" (Lam (IntP 0) i1 `Or` Lam x' (x `mulI` App (Var f) (x `subI` i1)))

  it "☯ syntax sugar" $ do
    let' [] x `shouldBe` x
    let' [(y', z)] x `shouldBe` App (Lam y' x) z

    or' [] `shouldBe` Err
    or' [x] `shouldBe` x
    or' [x, y] `shouldBe` Or x y
    or' [x, y, z] `shouldBe` Or x (Or y z)

    lam [] x `shouldBe` x
    lam [y'] x `shouldBe` Lam y' x

    app x [] `shouldBe` x
    app x [y, z] `shouldBe` App (App x y) z

  describe "☯ eval core" $ do
    it "☯ eval const" $ do
      eval [] Knd `shouldBe` Knd
      eval [] IntT `shouldBe` IntT
      eval [] (Int 1) `shouldBe` Int 1
      eval [] Err `shouldBe` Err

    it "☯ eval Ctr" $ do
      let env = [("x", i1)]
      eval env (Ctr "A") `shouldBe` Ctr "A"
      eval env (App (Ctr "B") x) `shouldBe` App (Ctr "B") i1

    it "☯ eval Typ" $ do
      let env = [("x", i1)]
      eval env (Typ "T") `shouldBe` Typ "T"
      eval env (App (Typ "U") x) `shouldBe` App (Typ "U") i1

    it "☯ eval Var" $ do
      let env = [("x", i1), ("y", y), ("b", Ann b (For [] IntT)), ("a", b), ("c", Ann c (For ["a"] a))]
      eval env (Var "x") `shouldBe` Int 1
      eval env (Var "y") `shouldBe` Var "y"
      eval env (Var "z") `shouldBe` Var "z"
      eval env (Var "a") `shouldBe` Var "b"
      eval env (Var "c") `shouldBe` Var "c"

    it "☯ eval Fun" $ do
      let env = [("x", i1), ("y", IntT)]
      eval env (Fun x y) `shouldBe` Fun i1 IntT
      eval env (Fun (Or x y) z) `shouldBe` Or (Fun i1 z) (Fun IntT z)
      eval env (Fun x (Or y z)) `shouldBe` Or (Fun i1 IntT) (Fun i1 z)

    it "☯ eval Lam" $ do
      let env = [("x", i1)]
      eval env (Lam x' x) `shouldBe` Lam x' x
      eval env (Lam y' x) `shouldBe` Lam y' i1
      eval env (Lam x' (Or x y)) `shouldBe` Or (Lam x' x) (Lam x' y)

    it "☯ eval Or" $ do
      let env = [("x", i1), ("y", i2), ("z", i3)]
      eval env (Or x Err) `shouldBe` i1
      eval env (Or Err y) `shouldBe` i2
      eval env (Or x y) `shouldBe` Or i1 i2
      eval env (Or x (Or y z)) `shouldBe` Or i1 (Or i2 i3)
      eval env (Or (Or x y) z) `shouldBe` Or i1 (Or i2 i3)

    it "☯ eval App" $ do
      let env = [("x", i1), ("f", g), ("g", g), ("h", h)]
      eval env (App (Var "f") Knd) `shouldBe` App g Knd
      eval env (App (Lam KndP x) y) `shouldBe` App (Lam KndP i1) y
      eval env (App (Lam KndP x) Knd) `shouldBe` i1
      eval env (App (Lam KndP x) IntT) `shouldBe` Err
      eval env (App (Lam IntTP x) IntT) `shouldBe` i1
      eval env (App (Lam (IntP 1) x) i1) `shouldBe` i1
      eval env (App (Lam (IntP 1) x) i2) `shouldBe` Err
      eval env (App (Lam (VarP "x") x) Knd) `shouldBe` Knd
      eval env (App (Lam (VarP "y") x) Knd) `shouldBe` i1
      eval env (App (Lam (CtrP "A") x) (Ctr "A")) `shouldBe` i1
      eval env (App (Lam (CtrP "A") x) (Ctr "B")) `shouldBe` Err
      eval env (App (Lam (TypP "T") x) (Typ "T")) `shouldBe` i1
      eval env (App (Lam (TypP "T") x) (Typ "U")) `shouldBe` Err
      eval env (App (Lam (AppP (CtrP "B") x') x) (App (Ctr "B") Knd)) `shouldBe` Knd
      eval env (App (Lam (AppP (TypP "U") x') x) (App (Typ "U") Knd)) `shouldBe` Knd
      eval env (App (Lam (FunP KndP x') x) (Fun IntT Knd)) `shouldBe` Err
      eval env (App (Lam (FunP IntTP x') x) (Fun IntT Knd)) `shouldBe` Knd
      eval env (App (Lam ErrP x) Knd) `shouldBe` Err
      eval env (App (Lam ErrP x) Err) `shouldBe` i1
      eval env (App (Or Err Err) Knd) `shouldBe` Err
      eval env (App (Or Err f) Knd) `shouldBe` App g Knd
      eval env (App (Or f Err) Knd) `shouldBe` App g Knd
      eval env (App (Or f h) Knd) `shouldBe` App g Knd
      eval env (App (Fix "f" (Lam x' (App h f))) Knd) `shouldBe` App h (Fix "f" (Lam x' (App h f)))
      eval env (App Err Knd) `shouldBe` Err
      eval env (App Err Knd) `shouldBe` Err

    it "☯ eval Ann" $ do
      let env = [("x", i1)]
      eval env (Ann x (For [] IntT)) `shouldBe` i1

    it "☯ eval Op2" $ do
      let env = []
      eval env (addI x y) `shouldBe` addI x y
      eval env (addI x i2) `shouldBe` addI x i2
      eval env (addI i1 y) `shouldBe` addI i1 y

      eval env (addI i1 i2) `shouldBe` Int 3
      eval env (subI i1 i2) `shouldBe` Int (-1)
      eval env (mulI i1 i2) `shouldBe` Int 2

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
      let env = [("x", i1), ("y", y), ("b", Ann b (For [] IntT)), ("a", b), ("c", Ann c (For ["a"] a))]
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

    it "☯ infer Ann" $ do
      infer [] (Ann i1 (For [] IntT)) `shouldBe` Right (IntT, [])
      infer [] (Ann i1 (For [] Knd)) `shouldBe` Left (TypeMismatch IntT Knd)
      infer [] (Ann i1 (For ["a"] a)) `shouldBe` Right (IntT, [("a", IntT)])

    it "☯ infer Lam" $ do
      let (t, xT) = (Var "t", Var "xT")
      let env =
            [ ("A", Ann (Ctr "A") (For ["a"] a)),
              ("T", Ann (Typ "T") (For ["b"] b)),
              ("x", Ann x (For [] IntT))
            ]
      infer env (Lam KndP x) `shouldBe` Right (Fun Knd IntT, [])
      infer env (Lam IntTP x) `shouldBe` Right (Fun Knd IntT, [])
      infer env (Lam IntTP x) `shouldBe` Right (Fun Knd IntT, [])
      infer env (Lam (CtrP "A") x) `shouldBe` Right (Fun a IntT, [("a", a)])
      infer env (Lam (TypP "T") x) `shouldBe` Right (Fun b IntT, [("b", b)])
      infer env (Lam (VarP "x") x) `shouldBe` Right (Fun xT xT, [("xT", xT), ("x", Ann x (For [] xT))])
      infer env (Lam (FunP x' IntTP) x) `shouldBe` Right (Fun Knd xT, [("xT", xT), ("x", Ann x (For [] xT))])
      infer env (Lam (AppP x' IntTP) x) `shouldBe` Right (Fun t (Fun Knd t), [("xT", Fun Knd t), ("x", Ann x (For [] (Fun Knd t))), ("t", t)])

    it "☯ infer App" $ do
      let t = Var "t"
      let env = [("x", i1), ("y", y), ("f", Ann (Var "f") (For [] $ Fun IntT Knd))]
      infer env (App (Var "f") x) `shouldBe` Right (Knd, [("t", Knd)])
      infer env (App (Lam y' y) x) `shouldBe` Right (IntT, [("yT", IntT), ("y", Ann y (For [] IntT)), ("t", IntT)])
      infer env (App y x) `shouldBe` Right (t, [("yT", Fun IntT t), ("y", Ann y (For [] (Fun IntT t))), ("t", t)])

    it "☯ infer Or" $ do
      let env = [("x", i1), ("y", IntT)]
      infer env (Or x x) `shouldBe` Right (IntT, [])
      infer env (Or x y) `shouldBe` Right (Or IntT Knd, [])

    it "☯ infer Fix" $ do
      True `shouldBe` True

    it "☯ infer Op2" $ do
      True `shouldBe` True

  it "☯ infer factorial" $ do
    let env = [("f", factorial "f")]
    infer env (Var "f") `shouldBe` Right (Fun IntT IntT, [("xT", IntT), ("x", Ann x (For [] IntT)), ("fT", Fun IntT IntT), ("f", Ann f (For [] (Fun IntT IntT))), ("t", IntT)])

  it "☯ infer Bool" $ do
    let i0 = Int 0
    let n = Var "n"
    let nat n = App (Typ "Nat") n
    let env =
          [ ("Nat", Ann (Typ "Nat") (For [] (Fun IntT Knd))),
            ("Zero", Ann (Ctr "Zero") (For [] (nat i0))),
            ("Succ", Ann (Ctr "Succ") (For ["n"] (Fun (nat n) (nat (addI n i1)))))
          ]

    let num :: Int -> Expr
        num 0 = Ctr "Zero"
        num n = App (Ctr "Succ") (num (n - 1))
    let infer' = fmap fst . infer env
    infer' (num 0) `shouldBe` Right (nat i0)
    infer' (num 1) `shouldBe` Right (nat i1)
    infer' (num 2) `shouldBe` Right (nat i2)

  it "☯ infer Vec" $ do
    let i0 = Int 0
    let (n, a) = (Var "n", Var "a")
    let vec n a = app (Typ "Vec") [n, a]
    let env =
          [ ("Vec", Ann (Typ "Vec") (For [] (fun [IntT, Knd] Knd))),
            ("Nil", Ann (Ctr "Nil") (For ["a"] (vec i0 a))),
            ("Cons", Ann (Ctr "Cons") (For ["n", "a"] (fun [a, vec n a] (vec (addI n i1) a))))
          ]

    let list [] = Ctr "Nil"
        list (x : xs) = app (Ctr "Cons") [x, list xs]
    let infer' = fmap fst . infer env
    infer' (list []) `shouldBe` Right (vec i0 a)
    infer' (list [Int 42]) `shouldBe` Right (vec i1 IntT)
    infer' (list [Int 42, Int 9]) `shouldBe` Right (vec i2 IntT)
    infer' (list [Int 42, Knd]) `shouldBe` Left (TypeMismatch Knd IntT)
