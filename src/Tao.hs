module Tao where

import Control.Monad (void)
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap, second))
import Data.Char (chr, isSpace, ord)
import Data.Function ((&))
import Data.List (delete, dropWhileEnd, intercalate, intersect, isPrefixOf, sort, union, unionBy, (\\))
import Error
import Grammar as G
import Location (Location (Location), Position (Pos), Range (Range))
import qualified Parser as P
import qualified PrettyPrint as PP
import Stdlib (lookupValue, split)
import System.FilePath (takeBaseName)

type Parser a = P.Parser String a

data Expr
  = Any
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Char Char
  | Var String
  | Tag String [Expr]
  | Ann Expr Type
  | Tuple [Expr]
  | List [Expr]
  | String [Segment]
  | Or Expr Expr
  | For [String] Expr
  | Fun Pattern Expr
  | App Expr Expr
  | Call String [Expr]
  | Op1 Op1 Expr
  | Op2 Op2 Expr Expr
  | Dot Expr String (Maybe [Expr])
  | Match Expr [Expr]
  | MatchFun [Expr]
  | Let (Pattern, Expr) Expr
  | Bind (Pattern, Expr) Expr
  | Record [(String, Expr)]
  | Select Expr [(String, Expr)]
  | With Expr [(String, Expr)]
  | If Expr Expr Expr
  | Meta (C.Metadata Expr) Expr
  | Err
  deriving (Eq)

instance Show Expr where
  show :: Expr -> String
  show = Tao.format 80

type Type = Expr

type Pattern = Expr

type Case = ([String], Pattern, Expr)

data Segment
  = Str String
  | Val Expr
  deriving (Eq, Show)

data Op1
  = Neg
  deriving (Eq)

op1s :: [(String, Op1)]
op1s =
  [ ("-", Neg)
  ]

showOp1 :: Op1 -> String
showOp1 op = case lookupValue op op1s of
  Just x -> x
  Nothing -> error "TODO: showOp1"

instance Show Op1 where
  show :: Op1 -> String
  show = showOp1

data Op2
  = Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge
  | Cons
  | AndOp
  | OrOp
  | XorOp
  | Add
  | Sub
  | Mul
  | Div
  | DivI
  | Pow
  | ShiftL
  | ShiftR
  | PipeL
  | PipeR
  deriving (Eq)

op2s :: [(String, Op2)]
op2s =
  [ ("and", AndOp),
    ("or", OrOp),
    ("xor", XorOp),
    (">>", ShiftR),
    ("<<", ShiftL),
    ("|>", PipeL),
    ("<|", PipeR),
    ("::", Cons),
    ("==", Eq),
    ("!=", Ne),
    ("<", Lt),
    ("<=", Le),
    (">", Gt),
    (">=", Ge),
    ("+", Add),
    ("-", Sub),
    ("*", Mul),
    ("/", Div),
    ("//", DivI),
    ("^", Pow)
  ]

showOp2 :: Op2 -> String
showOp2 op = case lookupValue op op2s of
  Just x -> x
  Nothing -> error "TODO: showOp2"

instance Show Op2 where
  show :: Op2 -> String
  show = showOp2

data Stmt
  = Import String String [(String, String)]
  | Def (Pattern, Expr)
  | TypeDef (String, [Expr], [(Expr, Maybe Type)])
  | Test UnitTest
  | Run Expr
  | Comment String
  deriving (Eq, Show)

data UnitTest = UnitTest
  { filename :: FilePath,
    pos :: Position,
    name :: String,
    expr :: Expr,
    expect :: Pattern
  }
  deriving (Eq, Show)

type Module = (FilePath, [Stmt])

type Package = [Module]

type Context = [Module]

keywords :: [String]
keywords =
  [ "not",
    "and",
    "or",
    "xor",
    "let",
    "if",
    "then",
    "else",
    "match",
    "type",
    "with"
  ]

tupleOf :: Expr -> [Expr]
tupleOf (Tuple items) = items
tupleOf a = [a]

isTuple :: Expr -> Bool
isTuple = \case
  Tuple _ -> True
  Meta _ a -> isTuple a
  _ -> False

isOr :: Expr -> Bool
isOr = \case
  Or _ _ -> True
  Meta _ a -> isOr a
  _ -> False

isFor :: Expr -> Bool
isFor = \case
  For _ _ -> True
  Meta _ a -> isFor a
  _ -> False

isFun :: Expr -> Bool
isFun = \case
  Fun _ _ -> True
  Meta _ a -> isFun a
  _ -> False

lets :: [(Pattern, Expr)] -> Expr -> Expr
lets [] a = a
lets (def : defs) a = Let def (lets defs a)

isErr :: Expr -> Bool
isErr = \case
  Err -> True
  Meta _ a -> isErr a
  _ -> False

errOf :: Expr -> Maybe (Error Expr)
errOf (Meta (C.Error e) _) = Just e
errOf _ = Nothing

isImport :: Stmt -> Bool
isImport Import {} = True
isImport _ = False

isTest :: Stmt -> Bool
isTest Test {} = True
isTest _ = False

def :: (Expr, Expr) -> Stmt
def (a, b) = Def (a, b)

asDef :: Stmt -> Maybe (Pattern, Expr)
asDef (Def def) = Just def
asDef _ = Nothing

-- Syntax sugar
asInt :: Expr -> Maybe Int
asInt (Int i) = Just i
asInt (Ann a _) = asInt a
asInt (Meta _ a) = asInt a
asInt _ = Nothing

asNum :: Expr -> Maybe Double
asNum (Num n) = Just n
asNum (Ann a _) = asNum a
asNum (Meta _ a) = asNum a
asNum _ = Nothing

asVar :: Expr -> Maybe String
asVar (Var x) = Just x
asVar (Meta _ a) = asVar a
asVar _ = Nothing

bool :: Expr
bool = tag "Bool"

true :: Expr
true = tag "True"

false :: Expr
false = tag "False"

tag :: String -> Expr
tag k = Tag k []

fun :: [Expr] -> Expr -> Expr
fun ps = Fun (Tuple ps)

asFun :: Expr -> Maybe (Expr, Expr)
asFun = \case
  Fun a b -> Just (a, b)
  Meta _ a -> asFun a
  _ -> Nothing

asFor :: Expr -> Maybe ([String], Expr)
asFor = \case
  For xs a -> case asFor a of
    Just (ys, a') -> Just (xs ++ ys, a')
    Nothing -> Just (xs, a)
  Meta m a -> do
    (xs, a') <- asFor a
    Just (xs, Meta m a')
  _ -> Nothing

or' :: [Expr] -> Expr
or' [] = Err
or' [a] = a
or' (a : bs) = Or a (or' bs)

orOf :: Expr -> [Expr]
orOf = \case
  Err -> []
  Or a b -> a : orOf b
  a -> [a]

lambda :: [Expr] -> Expr -> Expr
lambda args = Fun (Tuple args)

isAnn :: Expr -> Bool
isAnn (Ann _ _) = True
isAnn (Meta _ a) = isAnn a
isAnn _ = False

app :: Expr -> [Expr] -> Expr
app fun args = App fun (Tuple args)

app1 :: Expr -> Expr -> Expr
app1 a b = app a [b]

app2 :: Expr -> Expr -> Expr -> Expr
app2 a b c = app a [b, c]

string :: String -> Expr
string str = String [Str str]

neg :: Expr -> Expr
neg = Op1 Neg

andOp :: Expr -> Expr -> Expr
andOp = Op2 AndOp

orOp :: Expr -> Expr -> Expr
orOp = Op2 OrOp

xorOp :: Expr -> Expr -> Expr
xorOp = Op2 XorOp

eq :: Expr -> Expr -> Expr
eq = Op2 Eq

ne :: Expr -> Expr -> Expr
ne = Op2 Ne

lt :: Expr -> Expr -> Expr
lt = Op2 Lt

le :: Expr -> Expr -> Expr
le = Op2 Le

gt :: Expr -> Expr -> Expr
gt = Op2 Gt

ge :: Expr -> Expr -> Expr
ge = Op2 Ge

cons :: Expr -> Expr -> Expr
cons = Op2 Cons

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

div' :: Expr -> Expr -> Expr
div' = Op2 Div

divI :: Expr -> Expr -> Expr
divI = Op2 DivI

pow :: Expr -> Expr -> Expr
pow = Op2 Pow

typed :: Expr -> (Expr, Type)
typed (Ann a t) = (a, t)
typed (Meta _ a) | isAnn a = typed a
typed a = (a, Any)

bound :: Expr -> Expr
bound = \case
  Fun a b -> For [] (Fun (bound a) (bound b))
  a -> apply bound a

-- Helper functions
class Apply a where
  apply :: (Expr -> Expr) -> a -> a

instance Apply Expr where
  apply :: (Expr -> Expr) -> Expr -> Expr
  apply f = \case
    Any -> Any
    IntT -> IntT
    NumT -> NumT
    Int i -> Int i
    Num n -> Num n
    Char c -> Char c
    Var x -> Var x
    Tag k args -> Tag k (map f args)
    Ann a b -> Ann (f a) (f b)
    Tuple items -> Tuple (map f items)
    List items -> List (map f items)
    String segments -> do
      let applySegment = \case
            Str s -> Str s
            Val a -> Val (f a)
      String (map applySegment segments)
    Or a b -> Or (f a) (f b)
    For xs a -> For xs (f a)
    Fun a b -> Fun (f a) (f b)
    App a b -> App (f a) (f b)
    Call x args -> Call x (map f args)
    Op1 op a -> Op1 op (f a)
    Op2 op a b -> Op2 op (f a) (f b)
    Dot a x Nothing -> Dot (f a) x Nothing
    Dot a x (Just args) -> Dot (f a) x (Just (map f args))
    Match arg cases -> Match (f arg) (map f cases)
    MatchFun cases -> MatchFun (map f cases)
    Let (a, b) c -> Let (f a, f b) (f c)
    Bind (a, b) c -> Bind (f a, f b) (f c)
    Record fields -> Record (second f <$> fields)
    Select a fields -> Select (f a) (second f <$> fields)
    With a fields -> With (f a) (second f <$> fields)
    If a b c -> If (f a) (f b) (f c)
    Meta m a -> Meta m (f a)
    Err -> Err

instance Apply Stmt where
  apply :: (Expr -> Expr) -> Stmt -> Stmt
  apply f = \case
    Import path alias names -> Import path alias names
    Def (a, b) -> Def (f a, f b)
    TypeDef (name, args, alts) -> TypeDef (name, map f args, map (bimap f (fmap f)) alts)
    Test t -> Test (apply f t)
    Run a -> Run (f a)
    Comment x -> Comment x

instance Apply UnitTest where
  apply :: (Expr -> Expr) -> UnitTest -> UnitTest
  apply f t = t {expr = f t.expr, expect = f t.expect}

class DropMeta a where
  dropMeta :: a -> a

instance DropMeta Expr where
  dropMeta :: Expr -> Expr
  dropMeta = \case
    Meta (C.Error e) a -> Meta (C.Error e) (dropMeta a)
    Meta _ a -> dropMeta a
    -- Err e -> Err (fmap dropMeta e)
    a -> apply dropMeta a

instance DropMeta Stmt where
  dropMeta :: Stmt -> Stmt
  dropMeta = apply dropMeta

instance DropMeta Module where
  dropMeta :: Module -> Module
  dropMeta (path, stmts) = (path, map dropMeta stmts)

instance DropMeta Context where
  dropMeta :: Context -> Context
  dropMeta = map dropMeta

class DropLocations a where
  dropLocations :: a -> a

instance DropLocations Expr where
  dropLocations :: Expr -> Expr
  dropLocations = \case
    Meta (C.Loc _) a -> dropLocations a
    a -> apply dropLocations a

instance DropLocations Stmt where
  dropLocations :: Stmt -> Stmt
  dropLocations = error "TODO: dropLocations Stmt"

class DropTypes a where
  dropTypes :: a -> a

instance DropTypes Expr where
  dropTypes :: Expr -> Expr
  dropTypes = \case
    Ann a _ -> dropTypes a
    Fun (Ann a t) b -> Fun (Ann (dropTypes a) (dropTypes t)) (dropTypes b)
    App a (Ann b t) -> do
      App (dropTypes a) (Ann (dropTypes b) (dropTypes t))
    -- Err e -> Err (fmap dropTypes e)
    a -> apply dropTypes a

instance DropTypes Stmt where
  dropTypes :: Stmt -> Stmt
  dropTypes = error "TODO: dropTypes Stmt"

collect :: (Eq a) => (Expr -> [a]) -> Expr -> [a]
collect f = \case
  Any -> []
  IntT -> []
  NumT -> []
  Int _ -> []
  Num _ -> []
  Char _ -> []
  Var _ -> []
  Tag _ args -> unionMap f args
  Ann a b -> f a `union` f b
  Tuple items -> unionMap f items
  List items -> unionMap f items
  String segments -> do
    let collectSegment = \case
          Str _ -> []
          Val a -> f a
    unionMap collectSegment segments
  Or a b -> f a `union` f b
  For _ a -> f a
  Fun a b -> f a `union` f b
  App a b -> f a `union` f b
  Call _ args -> unionMap f args
  Op1 op a -> f (Var (show op)) `union` f a
  Op2 op a b -> f (Var (show op)) `union` f a `union` f b
  Dot a _ Nothing -> f a
  Dot a _ (Just args) -> f a `union` unionMap f args
  Match arg cases -> f arg `union` unionMap f cases
  MatchFun cases -> unionMap f cases
  Let (a, b) c -> f a `union` f b `union` f c
  Bind (a, b) c -> f a `union` f b `union` f c
  Record fields -> unionMap (f . snd) fields
  Select a fields -> f a `union` unionMap (f . snd) fields
  With a fields -> f a `union` unionMap (f . snd) fields
  If a b c -> f a `union` f b `union` f c
  Meta m a -> f a
  Err -> []
  where
    unionMap f = foldr (union . f) []

-- freeVars :: Expr -> [String]
-- freeVars = \case
--   Var x -> [x]
--   For xs a -> filter (`notElem` xs) (freeVars a)
--   Dot a x Nothing -> [x] `union` freeVars a
--   Dot a x (Just args) -> freeVars a `union` [x] `union` concatMap freeVars args
--   Let (a, b) c -> (freeVars a \\ bindings a) `union` freeVars b `union` freeVars c
--   Bind (a, b) c -> ["<-"] `union` (freeVars a \\ bindings a) `union` freeVars b `union` freeVars c
--   a -> collect freeVars a

-- freeTags :: Expr -> [String]
-- freeTags = \case
--   Tag k [] -> [k]
--   Tag k (a : args) -> freeTags a `union` freeTags (Tag k args)
--   a -> collect freeTags a

-- freeNames :: Expr -> [String]
-- freeNames a = freeVars a `union` freeTags a

parse :: FilePath -> String -> Either (P.State String) (Expr, P.State String)
parse = P.parse (parseExpr 0)

format :: Int -> Expr -> String
format width = G.format grammar width "  "

grammar :: G.Grammar String Expr
grammar = do
  let withLoc start end = Meta (C.Loc (Location start.filename (Range start.pos end.pos)))
  let loc0 f location _ = Meta (C.Loc location) f
  let loc1 f location x = Meta (C.Loc location) (f x)
  let loc2 f location x y = Meta (C.Loc location) (f x y)
  let locOp1 op location x = Meta (C.Loc location) (Op1 op x)
  let locOp2 op location x y = Meta (C.Loc location) (Op2 op x y)
  G.Grammar
    { group = ("(", ")"),
      operators =
        [ -- Grammar.Any
          G.atom (loc0 Any) (P.word "_") $ \_ -> \case
            Any -> Just [PP.Text "_"]
            _ -> Nothing,
          -- Grammar.IntT
          G.atom (loc0 IntT) (P.word "Int") $ \_ -> \case
            IntT -> Just [PP.Text "Int"]
            _ -> Nothing,
          -- Grammar.NumT
          G.atom (loc0 NumT) (P.word "Num") $ \_ -> \case
            NumT -> Just [PP.Text "Num"]
            _ -> Nothing,
          -- Grammar.Int
          G.atom (loc1 Int) P.integer $ \_ -> \case
            Int i -> Just [PP.Text $ show i]
            _ -> Nothing,
          -- Grammar.Num
          G.atom (loc1 Num) P.number $ \_ -> \case
            Num n -> Just [PP.Text $ show n]
            _ -> Nothing,
          -- Grammar.Char
          let parser _ = do
                start <- P.getState
                _ <- P.char 'c'
                quote <- P.oneOf [P.char '\'', P.char '"']
                _ <- P.commit "char"
                ch <- P.anyChar
                _ <- P.char quote
                end <- P.getState
                _ <- P.spaces
                return (withLoc start end $ Char ch)
           in G.Atom parser $ \_ -> \case
                Char ch -> Just [PP.Text $ "c" ++ show ch]
                _ -> Nothing,
          -- Grammar.Var
          G.atom (loc1 Var) parseNameVar $ \_ -> \case
            Var x -> Just [PP.Text x]
            _ -> Nothing,
          -- Grammar.Tag
          let parser expr = do
                start <- P.getState
                k <- parseNameTag
                end <- P.getState
                _ <- P.spaces
                args <- P.oneOf [parseCollection "(" "," ")" expr, return []]
                _ <- P.spaces
                return (withLoc start end $ Tag k args)
           in G.Atom parser $ \layout -> \case
                Tag k [] -> Just [PP.Text k]
                Tag k args -> do
                  Just (PP.Text k : PP.Text "(" : collectionLayout layout args ++ [PP.Text ")"])
                _ -> Nothing,
          -- Grammar.Tuple.empty
          let parser expr = do
                start <- P.getState
                items <- parseCollection "(" "," ")" expr
                end <- P.getState
                _ <- P.spaces
                return (withLoc start end $ Tuple items)
           in G.Atom parser $ \layout -> \case
                Tuple items -> do
                  Just (PP.Text "(" : collectionLayout layout items ++ [PP.Text ")"])
                _ -> Nothing,
          -- Grammar.List
          let parser expr = do
                start <- P.getState
                items <- parseCollection "[" "," "]" expr
                end <- P.getState
                _ <- P.spaces
                return (withLoc start end $ List items)
           in G.Atom parser $ \layout -> \case
                List items -> do
                  Just (PP.Text "[" : collectionLayout layout items ++ [PP.Text "]"])
                _ -> Nothing,
          -- Grammar.String
          -- TODO: support string interpolation
          let parser expr = do
                start <- P.getState
                quote <- P.oneOf [P.char '\'', P.char '"']
                _ <- P.commit "string"
                txt <- P.skipTo (P.char quote)
                _ <- P.char quote
                end <- P.getState
                _ <- P.spaces
                let segments = [Str txt | txt /= ""]
                return (withLoc start end $ String segments)
           in G.Atom parser $ \layout -> \case
                String segments -> do
                  let layoutSegment = \case
                        Str s -> [PP.Text s]
                        Val a -> error "TODO: layout string interpolation"
                  Just ([PP.Text "'"] ++ concatMap layoutSegment segments ++ [PP.Text "'"])
                _ -> Nothing,
          -- Grammar.Let
          -- Grammar.Bind
          let parser expr = do
                start <- P.getState
                _ <- P.word "let"
                _ <- P.commit "let"
                end <- P.getState
                _ <- P.whitespaces
                a <- parseExprUntil "let lhs" 0 ["=", "<-", ";", "\n", "~>"]
                _ <- P.whitespaces
                bind <-
                  P.oneOf
                    [ do _ <- P.char '='; return Let,
                      do _ <- P.text "<-"; return Bind
                    ]
                _ <- P.whitespaces
                b <- parseExprUntil "let rhs" 0 [";", "\n", "~>"]
                _ <- parseLineBreak
                withLoc start end . bind (a, b) <$> expr
           in G.Atom parser $ \layout -> \case
                Let (a, b) c -> Just (PP.Text "let " : layout a ++ PP.Text " = " : layout b ++ PP.NewLine : layout c)
                Bind (a, b) c -> Just (PP.Text "let " : layout a ++ PP.Text " <- " : layout b ++ PP.NewLine : layout c)
                _ -> Nothing,
          -- Grammar.Or
          G.infixR 2 (loc2 Or) "|" $ \case
            Or a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.OrOp
          G.infixL 3 (locOp2 OrOp) "or" $ \case
            Op2 OrOp a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.XorOp
          G.infixL 3 (locOp2 XorOp) "xor" $ \case
            Op2 XorOp a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.AndOp
          G.infixL 4 (locOp2 AndOp) "and" $ \case
            Op2 AndOp a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.ShiftL
          G.infixL 4 (locOp2 ShiftL) "<<" $ \case
            Op2 ShiftL a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.ShiftR
          G.infixL 4 (locOp2 ShiftR) ">>" $ \case
            Op2 ShiftR a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.PipeL
          G.infixL 4 (locOp2 PipeL) "<|" $ \case
            Op2 PipeL a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.PipeR
          G.infixL 4 (locOp2 PipeR) "|>" $ \case
            Op2 PipeR a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Eq
          G.infixL 5 (locOp2 Eq) "==" $ \case
            Op2 Eq a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Ne
          G.infixL 5 (locOp2 Ne) "!=" $ \case
            Op2 Ne a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Lt
          let parser a expr = do
                start <- P.getState
                _ <- P.char '<'
                end <- P.getState
                _ <- P.lookaheadNot (P.char '-')
                _ <- P.spaces
                withLoc start end . Op2 Lt a <$> expr
           in G.InfixL 6 parser $ \lhs rhs -> \case
                Op2 Lt a b -> Just (lhs a ++ PP.Text " < " : rhs b)
                _ -> Nothing,
          -- Grammar.Op2.Le
          G.infixL 6 (locOp2 Le) "<=" $ \case
            Op2 Le a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Gt
          G.infixL 6 (locOp2 Gt) ">" $ \case
            Op2 Gt a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Ge
          G.infixL 6 (locOp2 Ge) ">=" $ \case
            Op2 Ge a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Cons
          G.infixR 7 (locOp2 Cons) "::" $ \case
            Op2 Cons a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Ann
          G.infixR 8 (loc2 Ann) ":" $ \case
            Ann a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.For
          let parser expr = do
                start <- P.getState
                _ <- P.char '@'
                _ <- P.commit "for"
                xs <-
                  P.oneOf
                    [ do
                        x <- parseNameVar
                        _ <- P.spaces
                        xs <- P.zeroOrMore $ do
                          y <- parseNameVar
                          _ <- P.spaces
                          return y
                        return (x : xs),
                      return []
                    ]
                end <- P.getState
                _ <- P.oneOf [P.char '.', P.char '\n']
                _ <- P.whitespaces
                a <- expr
                _ <- P.spaces
                return (withLoc start end $ For xs a)
           in G.Prefix 9 parser $ \layout -> \case
                For xs a ->
                  Just (PP.Text ('@' : unwords xs ++ ". ") : layout a)
                _ -> Nothing,
          -- Grammar.Fun
          G.infixR 9 (loc2 Fun) "->" $ \case
            Fun a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Add
          G.infixL 10 (locOp2 Add) "+" $ \case
            Op2 Add a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Sub
          G.infixL 10 (locOp2 Sub) "-" $ \case
            Op2 Sub a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Mul
          G.infixL 11 (locOp2 Mul) "*" $ \case
            Op2 Mul a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.DivI must go before Div '/'
          G.infixL 11 (locOp2 DivI) "//" $ \case
            Op2 DivI a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Div must go after DivI '//'
          G.infixL 11 (locOp2 Div) "/" $ \case
            Op2 Div a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Pow
          G.infixR 12 (locOp2 Pow) "^" $ \case
            Op2 Pow a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op1.Neg
          G.prefix 13 (locOp1 Neg) "-" $ \case
            Op1 Neg a -> Just ("", a)
            _ -> Nothing,
          -- Grammar.not
          G.prefix 13 (loc1 (App (Var "not"))) "not" $ \case
            App (Var "not") a -> Just (" ", a)
            _ -> Nothing,
          -- Grammar.App
          let parser a expr = do
                start <- P.getState
                args <- parseCollection "(" "," ")" $ do
                  -- name <-
                  --   P.oneOf
                  --     [ do
                  --         name <- parseNameVar
                  --         _ <- P.spaces
                  --         _ <- P.char ':'
                  --         _ <- P.whitespaces
                  --         return name,
                  --       return ""
                  --     ]
                  parseExprUntil "app arg" 0 [",", ")", "\n"]
                end <- P.getState
                _ <- P.spaces
                return (withLoc start end $ app a args)
           in G.InfixL 13 parser $ \lhs rhs -> \case
                App a b -> do
                  let args = tupleOf b
                  Just (lhs a ++ PP.Text "(" : collectionLayout (G.layout grammar 0) args ++ [PP.Text ")"])
                _ -> Nothing,
          -- Grammar.Dot
          let parser a expr = do
                start <- P.getState
                _ <- P.char '.'
                end <- P.getState
                _ <- P.whitespaces
                x <- parseNameVar
                _ <- P.spaces
                args <-
                  P.maybe' $ do
                    args <- parseCollection "(" "," ")" (parseExpr 0)
                    _ <- P.spaces
                    return args
                _ <- P.spaces
                return (withLoc start end $ Dot a x args)
           in G.InfixL 13 parser $ \lhs rhs -> \case
                Dot a x Nothing -> Just (lhs a ++ [PP.Text ("." ++ x)])
                Dot a x (Just args) -> Just (lhs a ++ [PP.Text ("." ++ x ++ "(")] ++ collectionLayout (G.layout grammar 0) args ++ [PP.Text ")"])
                _ -> Nothing,
          -- Grammar.Call
          let parser expr = do
                start <- P.getState
                _ <- P.char '%'
                _ <- P.commit "call"
                f <- parseName
                end <- P.getState
                _ <- P.spaces
                args <-
                  P.oneOf
                    [ do
                        args <- parseCollection "(" "," ")" expr
                        _ <- P.spaces
                        return args,
                      return []
                    ]
                return (withLoc start end $ Call f args)
           in G.Atom parser $ \layout -> \case
                Call f [] -> Just [PP.Text $ "%" ++ f]
                Call f args -> Just (PP.Text ("%" ++ f ++ "(") : collectionLayout layout args ++ [PP.Text ")"])
                _ -> Nothing,
          -- Grammar.Match / Grammar.MatchFun
          let parser expr = do
                start <- P.getState
                _ <- P.word "match"
                _ <- P.commit "match"
                end <- P.getState
                _ <- P.whitespaces
                maybeArg <- P.maybe' $ do
                  arg <- expr
                  _ <- P.whitespaces
                  return arg
                _ <- P.char '{'
                _ <- P.whitespaces
                cases <- P.zeroOrMore $ do
                  _ <- P.char '|'
                  _ <- P.spaces
                  case' <- parseExprUntil "match alt" 1 ["|", "}", "\n"]
                  _ <- P.whitespaces
                  return case'
                _ <- P.char '}'
                _ <- P.spaces
                case maybeArg of
                  Just arg -> return (withLoc start end $ Match arg cases)
                  Nothing -> return (withLoc start end $ MatchFun cases)
              layoutCases layout = \case
                [] -> []
                cases -> PP.NewLine : concatMap (\c -> PP.Text "| " : layout c ++ [PP.NewLine]) cases
           in G.Atom parser $ \layout -> \case
                Match arg cases -> do
                  Just (PP.Text "match " : layout arg ++ PP.Text " {" : layoutCases layout cases ++ [PP.Text "}"])
                MatchFun cases -> do
                  Just (PP.Text "match {" : layoutCases layout cases ++ [PP.Text "}"])
                _ -> Nothing,
          -- Grammar.Record [(String, Expr)]
          -- Grammar.Select Expr [(String, Expr)]
          -- Grammar.With Expr [(String, Expr)]
          -- Grammar.If
          let parser expr = do
                start <- P.getState
                _ <- P.word "if"
                _ <- P.commit "if"
                end <- P.getState
                _ <- P.spaces
                a <- expr
                _ <- P.whitespaces
                _ <- P.word "then"
                _ <- P.spaces
                b <- expr
                _ <- P.whitespaces
                _ <- P.word "else"
                _ <- P.spaces
                c <- expr
                _ <- P.spaces
                return (withLoc start end $ If a b c)
           in G.Atom parser $ \layout -> \case
                If a b c -> Just (PP.Text "if " : layout a ++ PP.Text " then " : layout b ++ PP.Text " else " : layout c)
                _ -> Nothing,
          -- Grammar.Metadata.Comments
          let parser expr = do
                comments <- P.oneOrMore $ do
                  _ <- P.char '#'
                  _ <- P.spaces
                  comment <- P.zeroOrMore (P.charIf (/= '\n'))
                  _ <- P.whitespaces
                  return comment
                Meta (C.Comments comments) <$> expr
           in G.Atom parser $ \rhs -> \case
                Meta (C.Comments comments) a -> do
                  let comments' = concatMap (\c -> [PP.Text ("# " ++ c), PP.NewLine]) comments
                  Just (comments' ++ rhs a)
                _ -> Nothing,
          -- Grammar.Metadata.TrailingComment
          let parser a _expr = do
                _ <- P.char '#'
                _ <- P.spaces
                comment <- P.zeroOrMore (P.charIf (/= '\n'))
                _ <- P.whitespaces
                return (Meta (C.TrailingComment comment) a)
           in G.InfixL 1 parser $ \lhs _ -> \case
                Meta (C.TrailingComment comment) a ->
                  Just (lhs a ++ [PP.Text ("  # " ++ comment), PP.NewLine])
                _ -> Nothing,
          -- Grammar.Metadata.Location
          let parser expr = do
                _ <- P.text "^loc["
                P.commit "Metadata location"
                filename <- P.oneOrMore $ P.charIf (/= ':')
                _ <- P.char ':'
                row1 <- P.integer
                _ <- P.char ':'
                col1 <- P.integer
                _ <- P.char ','
                row2 <- P.integer
                _ <- P.char ':'
                col2 <- P.integer
                _ <- P.char ']'
                _ <- P.spaces
                _ <- P.char '('
                a <- expr
                _ <- P.char ')'
                let loc = Location filename (Range (Pos row1 col1) (Pos row2 col2))
                return (Meta (C.Loc loc) a)
           in G.Atom parser $ \layout -> \case
                Meta (C.Loc loc) a -> Just (PP.Text ("^loc[" ++ show loc ++ "](") : layout a ++ [PP.Text ")"])
                _ -> Nothing,
          -- Grammar.Metadata.SyntaxError
          G.Atom (const P.fail') $ \layout -> \case
            Meta (C.Error e) a -> Just (PP.Text ("![" ++ show e ++ "](") : layout a ++ [PP.Text ")"])
            Meta m a -> error $ "Grammar.layout " ++ show m
            _ -> Nothing,
          -- Grammar.Err
          let parser expr = do
                start <- P.getState
                _ <- P.word "!error"
                end <- P.getState
                _ <- P.spaces
                a <-
                  P.oneOf
                    [ do
                        _ <- P.char '('
                        _ <- P.whitespaces
                        a <- expr
                        _ <- P.whitespaces
                        _ <- P.char ')'
                        return a,
                      return (withLoc start end Any)
                    ]
                _ <- P.spaces
                return (Meta (C.Error $ customError a) Err)
           in G.Atom parser $ \layout -> \case
                Err -> Just [PP.Text "!Err"]
                Meta (C.Error e) c -> case e of
                  SyntaxError (loc, ctx, txt) -> Just [PP.Text $ "!syntax-error[" ++ show loc ++ "|" ++ show ctx ++ "|" ++ show txt ++ "]"]
                  TypeError e -> case e of
                    UndefinedVar x -> Just [PP.Text $ "!undefined-var(" ++ x ++ ")"]
                    TypeMismatch a b -> Just (PP.Text "!type-mismatch(" : layout a ++ PP.Text ", " : layout b ++ [PP.Text ")"])
                    NotAFunction a b -> Just (PP.Text "!not-a-function(" : layout a ++ PP.Text ", " : layout b ++ [PP.Text ")"])
                    e -> Just [PP.Text $ "!error(" ++ show e ++ ")"]
                  RuntimeError e -> case e of
                    UnhandledCase a b -> Just (PP.Text "!unhandled-case(" : layout a ++ PP.Text ", " : layout b ++ [PP.Text ")"])
                    CannotApply a b -> Just (PP.Text "!cannot-apply(" : layout a ++ PP.Text ", " : layout b ++ [PP.Text ")"])
                    CustomError a -> Just (PP.Text "!error(" : layout a ++ [PP.Text ")"])
                  e -> Just [PP.Text $ "!error(" ++ show e ++ ")"]
                _ -> Nothing
        ]
    }
  where
    collectionLayout layout = \case
      [] -> []
      [a] -> layout a
      a : bs -> layout a ++ [PP.Text ", "] ++ collectionLayout layout bs

lower :: [String] -> Expr -> C.Expr
lower xs = \case
  Any -> C.Any
  IntT -> C.IntT
  NumT -> C.NumT
  Int i -> C.Int i
  Num n -> C.Num n
  Char c -> C.tag "Char" [C.Int (ord c)]
  Var x -> C.Var x
  Tag k args -> C.tag k (map (lower xs) args)
  Ann a b -> C.Ann (lower xs a) (lower xs b)
  Tuple items -> C.and' (map (lower xs) items)
  List [] -> C.tag' "[]"
  List (a : bs) -> lower xs (Tag "::" [a, List bs])
  String [] -> C.tag' "''"
  String [Str txt] -> lower xs (List (map Char txt))
  String segments -> error "TODO: lower String interpolation"
  Or a b -> C.Or (lower xs a) (lower xs b)
  For ys a | Just (a, b) <- asFun a -> do
    C.for ys (C.Fun (lower (xs ++ ys) a) (lower (xs ++ ys) b))
  For ys a -> C.for xs (lower (xs ++ ys) a)
  Fun a b -> do
    let ys = filter (`notElem` xs) (C.freeVars (lower xs a))
    let (a', b') = (lower (xs ++ ys) a, lower (xs ++ ys) b)
    C.for' ys (C.Fun a' b')
  App a b -> C.App (lower xs a) (lower xs b)
  Call op args -> C.Call op (map (lower xs) args)
  Op1 op a -> C.app (C.Var $ show op) [lower xs a]
  Op2 Cons a b -> lower xs (Tag "::" [a, b])
  Op2 op a b -> C.app (C.Var $ show op) [lower xs a, lower xs b]
  Dot a x Nothing -> C.App (C.Var x) (lower xs a)
  Dot a x (Just args) -> C.App (C.Var x) (lower xs $ Tuple (a : args))
  Match arg cases -> lower xs (App (or' cases) arg)
  MatchFun cases -> lower xs (or' cases)
  Let (a, b) c -> case a of
    Var x | c == Var x -> lower xs b
    Ann (Var x) t | c == Var x -> lower xs (Ann b t)
    Ann (Or a1 a2) t -> lower xs (lets [(Ann a1 t, b), (Ann a2 t, b)] c)
    Ann (App a1 a2) t -> lower xs (Let (Ann a1 t, Fun a2 b) c)
    Ann (Op1 op a) t -> lower xs (Let (Ann (Var (show op)) t, Fun a b) c)
    Ann (Op2 op a1 a2) t -> lower xs (Let (Ann (Var (show op)) t, fun [a1, a2] b) c)
    Ann (Meta m a) t -> case lower xs (Let (Ann a t, b) c) of
      C.App a b -> C.App (C.Meta (fmap (lower xs) m) a) b
      a -> a
    Ann a t -> lower xs (Let (a, Ann b t) c)
    Or a1 a2 -> lower xs (lets [(a1, b), (a2, b)] c)
    App a1 a2 -> lower xs (Let (a1, Fun a2 b) c)
    Op1 op a -> lower xs (Let (Var (show op), Fun a b) c)
    Op2 op a1 a2 -> lower xs (Let (Var (show op), fun [a1, a2] b) c)
    For xs a -> lower xs (App (For xs (Fun a c)) b)
    Meta m a -> case lower xs (Let (a, b) c) of
      C.App a b -> C.App (C.Meta (fmap (lower xs) m) a) b
      a -> a
    -- a -> lower xs (App (For (freeVars a) (Fun a c)) b)
    a -> C.App (lower xs $ Fun a c) (lower xs b)
  Bind (a, b) c -> lower xs (app (Var "<-") [b, Fun a c])
  -- Record fields -> do
  --   let k = '~' : intercalate "," (map fst fields)
  --   lower (tag k (map snd fields))
  -- Select a kvs -> do
  --   let sub = case a of
  --         Record fields -> map (second lower) fields
  --         a -> do
  --           let xs = freeVars (and' (map snd kvs))
  --           map (\x -> (x, C.App (C.Var x) (lower a))) xs
  --   let k = '~' : intercalate "," (map fst kvs)
  --   let args = map ((C.substitute sub . lower) . snd) kvs
  --   C.tag k args
  If a b c -> lower xs (Match a [Fun (Ann true bool) b, Fun (Ann false bool) c])
  Meta m a -> C.Meta (fmap (lower xs) m) (lower xs a)
  Err -> C.Err
  a -> error $ "TODO: lower " ++ show a

lift :: C.Expr -> Expr
lift = \case
  C.Any -> Any
  C.Unit -> Tuple []
  C.IntT -> IntT
  C.NumT -> NumT
  C.Int i -> Int i
  C.Num n -> Num n
  C.Var x -> Var x
  C.Tag "Char" (C.Int i) -> Char (chr i)
  C.Tag ('~' : names) a -> do
    let keys = split ',' names
    let values = map lift (C.andOf a)
    Record (zip keys values)
  C.Tag "[]" C.Unit -> List []
  C.Tag "''" C.Unit -> String []
  C.Tag "::" a -> case map lift (C.andOf a) of
    [a, List bs] -> List (a : bs)
    [a, String segments] -> error "TODO: lift String"
    args -> Tag "::" args
  C.Tag k a -> Tag k (map lift (C.andOf a))
  C.Ann a b -> Ann (lift a) (lift b)
  C.And a bs -> Tuple (map lift (a : C.andOf bs))
  C.Or a b -> Or (lift a) (lift b)
  C.For x a -> case C.forOf (C.For x a) of
    (xs, C.Fun a b) | sort xs == sort (C.freeVars a) -> Fun (lift a) (lift b)
    (xs, C.Fun a b) -> For xs (Fun (lift a) (lift b))
    (xs, a) -> For xs (lift a)
  C.Fun a b | null (C.freeVars a) -> Fun (lift a) (lift b)
  C.Fun a b -> For [] (Fun (lift a) (lift b))
  C.Fix x a
    | x `C.occurs` a -> Let (Var x, lift a) (lift a)
    | otherwise -> lift a
  C.App a b -> case (lift a, lift b) of
    (Err, arg) -> Match arg []
    (Var x, a) | Just op <- lookup x op1s -> do
      Op1 op a
    (Var x, Ann (Tuple [a, b]) (Tuple [ta, tb])) | Just op <- lookup x op2s -> do
      Op2 op (Ann a ta) (Ann b tb)
    (Fun a c, b) -> Let (a, b) c
    (cases, arg) | isFun cases || isFor cases || isOr cases -> do
      Match arg (orOf cases)
    (a, Ann (Tuple bs) (Tuple ts)) -> do
      app a (zipWith Ann bs ts)
    (a, b) -> App a b
  C.Call op args -> Call op (map lift args)
  -- C.Let [] b -> lift b
  -- C.Let ((x, b) : env) c -> Let (Var x, lift b) (lift (C.Let env c))
  C.Meta (C.Loc _) (C.Meta (C.Loc loc) a) -> Meta (C.Loc loc) (lift a)
  C.Meta m a -> Meta (fmap lift m) (lift a)
  C.Err -> Err
  a -> error $ "TODO: lift " ++ show a

parseExpr :: Int -> Parser Expr
parseExpr = G.parser grammar

parseExprUntil :: String -> Int -> [String] -> Parser Expr
parseExprUntil msg prec delims = do
  a <- parseExpr prec
  start <- P.getState
  txt <- P.chooseShortest (map (P.skipTo . P.text) delims)
  case txt of
    "" -> return a
    txt -> do
      end <- P.getState
      let loc = Location start.filename (Range start.pos end.pos)
      return (Meta (C.Error (SyntaxError (loc, msg, txt))) a)

parseCollection :: String -> String -> String -> P.Parser ctx a -> P.Parser ctx [a]
parseCollection open delim close parser = do
  _ <- P.text open
  _ <- P.whitespaces
  args <-
    P.oneOf
      [ do
          a <- parser
          _ <- P.whitespaces
          bs <- P.zeroOrMore $ do
            _ <- P.text delim
            _ <- P.whitespaces
            parser
          _trailingDelim <- P.maybe' $ do
            _ <- P.text delim
            P.whitespaces
          return (a : bs),
        return []
      ]
  _ <- P.whitespaces
  _ <- P.text close
  return args

parseLineBreak :: Parser ()
parseLineBreak = do
  _ <- P.oneOf [P.char '\n', P.char ';', '$' <$ P.endOfFile]
  _ <- P.whitespaces
  return ()

parseNameBase :: Parser Char -> Parser String
parseNameBase firstChar = do
  let validChars =
        [ P.letter,
          P.digit,
          P.char '_',
          P.paddedR (P.lookaheadNot $ P.char '>') (P.char '-')
        ]
  c <- firstChar
  cs <- P.zeroOrMore (P.oneOf validChars)
  case c : cs of
    name | name `elem` keywords -> P.fail'
    name -> return name

parseNameVar :: Parser String
parseNameVar =
  P.oneOf
    [ parseNameBase P.lowercase,
      parseNameEscaped,
      parseNameOp
    ]

parseNameEscaped :: Parser String
parseNameEscaped = do
  _ <- P.char '`'
  name <- P.zeroOrMore $ do
    P.oneOf
      [ fmap (const '`') (P.text "\\`"),
        P.charIf (/= '`')
      ]
  _ <- P.char '`'
  return name

parseNameOp :: Parser String
parseNameOp = do
  _ <- P.char '('
  _ <- P.whitespaces
  op <-
    P.oneOf
      [ P.word "not",
        P.word "and",
        P.word "or",
        P.word "xor",
        P.text "<<",
        P.text ">>",
        P.text "<|",
        P.text "|>",
        P.text "<-",
        P.text "==",
        P.text "!=",
        P.text "<=",
        P.text "<",
        P.text ">=",
        P.text ">",
        P.text "+",
        P.text "-",
        P.text "*",
        P.text "//",
        P.text "/",
        P.text "^"
      ]
  _ <- P.whitespaces
  _ <- P.char ')'
  return op

parseNameTag :: Parser String
parseNameTag =
  P.oneOf
    [ parseNameBase P.uppercase,
      P.paddedL (P.char '^') parseNameEscaped,
      parseNameOpTag
    ]

parseNameOpTag :: Parser String
parseNameOpTag = do
  _ <- P.char '('
  _ <- P.whitespaces
  op <-
    P.oneOf
      [ P.text "::"
      ]
  _ <- P.whitespaces
  _ <- P.char ')'
  return op

parseName :: Parser String
parseName = P.oneOf [parseNameVar, parseNameTag]

parseModule :: String -> Parser Module
parseModule name = do
  _ <- P.whitespaces
  stmts <- P.zeroOrMore parseStmt
  _ <- P.endOfFile
  return (name, stmts)

parseStmt :: Parser Stmt
parseStmt = do
  stmt <-
    P.oneOf
      [ parseImport,
        Def <$> parseDef "=",
        TypeDef <$> parseTypeDef,
        parseTest,
        Comment <$> parseComment,
        Run <$> parseExprUntil "run stmt" 1 [";", "\n"],
        -- TODO: consider a trailing comment on a syntax error like this
        Run . (\e -> Meta (C.Error e) Err) . SyntaxError <$> recoverSyntaxError "statement" (P.text "\n")
      ]
  _ <- parseLineBreak
  return stmt

parseModulePath :: Parser (String, String)
parseModulePath = do
  pkg <- parseNameVar
  path <- P.zeroOrMore $ do
    _ <- P.char '/'
    name <- parseNameVar
    return ('/' : name)
  let modulePath = concat (pkg : path)
  return (modulePath, takeBaseName modulePath)

parseImport :: Parser Stmt
parseImport = do
  _ <- P.word "import"
  P.commit "import"
  _ <- P.spaces
  (path, alias) <- parseModulePath
  _ <- P.spaces
  exposing <-
    P.oneOf
      [ do
          parseCollection "(" "," ")" $ do
            name <- parseName
            _ <- P.spaces
            P.oneOf
              [ do
                  _ <- P.word "as"
                  _ <- P.spaces
                  alias <- parseName
                  return (name, alias),
                return (name, name)
              ],
        return []
      ]
  return (Import path alias exposing)

parseDef :: String -> Parser (Expr, Expr)
parseDef "" = error "parseDef delimiter must not be empty"
parseDef op = do
  typeAnnotation <- P.maybe' $ do
    _ <- P.char ':'
    P.commit "def type"
    _ <- P.spaces
    t <- parseExprUntil "def type" 0 [";", "\n"]
    _ <- parseLineBreak
    return t
  _ <- P.word "let"
  _ <- P.commit "def"
  _ <- P.whitespaces
  a <- parseExprUntil "def lhs" 0 [op, "\n"]
  _ <- P.word op
  _ <- P.whitespaces
  b <- parseExprUntil "def rhs" 0 [";", "\n"]
  case typeAnnotation of
    Just t -> return (Ann a t, b)
    Nothing -> return (a, b)

parseTypeDef :: Parser (String, [Expr], [(Expr, Maybe Type)])
parseTypeDef = do
  _ <- P.word "type"
  _ <- P.commit "type"
  _ <- P.whitespaces
  name <- parseNameTag
  _ <- P.whitespaces
  args <-
    P.oneOf
      [ parseCollection "(" "," ")" $ do
          parseExprUntil "typedef arg" 0 [",", ")", "=", "\n"],
        return []
      ]
  _ <- P.whitespaces
  _ <- P.char '='
  _ <- P.whitespaces
  let parseAlt = do
        a <- parseExprUntil "type alt" 3 ["=>", "|", "\n"]
        _ <- P.spaces
        mb <- P.maybe' $ do
          _ <- P.whitespaces
          _ <- P.text "=>"
          _ <- P.whitespaces
          parseExprUntil "type alt-type" 3 ["|", "\n"]
        return (a, mb)
  _ <- P.maybe' (P.char '|')
  _ <- P.whitespaces
  alt <- parseAlt
  _ <- P.whitespaces
  alts <- P.zeroOrMore $ do
    _ <- P.char '|'
    _ <- P.whitespaces
    parseAlt
  return (name, args, alt : alts)

parseTest :: Parser Stmt
parseTest = do
  name <-
    P.oneOf
      [ do
          _ <- P.text "--"
          _ <- P.spaces
          name <- P.skipTo P.endOfLine
          _ <- P.whitespaces
          return name,
        return ""
      ]
  s <- P.getState
  _ <- P.char '>'
  _ <- P.oneOrMore P.space
  P.commit "test"
  expr <- parseExprUntil "test expr" 0 ["~>", "\n"]
  result <-
    P.oneOf
      [ do
          _ <- parseLineBreak
          parseExprUntil "test expect newline" 0 ["\n"],
        do
          _ <- P.text "~>"
          _ <- P.whitespaces
          parseExprUntil "test expect =>" 0 ["\n"],
        return (Tag "True" [])
      ]
  return (Test (UnitTest s.filename s.pos name expr result))

parseComment :: Parser String
parseComment = parseCommentSingleLine

parseCommentSingleLine :: Parser String
parseCommentSingleLine = do
  _ <- P.char '#'
  P.commit "comment-singleline"
  _ <- P.spaces
  -- line <- P.skipTo P.endOfLine
  line <- P.zeroOrMore (P.charIf (/= '\n'))
  -- _ <- P.whitespaces
  return (dropWhileEnd isSpace line)

-- parseCommentMultiLine :: Parser String
-- parseCommentMultiLine = do
--   -- #{ multi-line comment }#
--   delim <- P.chain [P.text "#--", P.zeroOrMore (P.char '-')]
--   P.commit "comment-multiline"
--   _ <- P.spaces
--   line <- P.skipTo parseLineBreak
--   _ <- P.whitespaces
--   error "TODO: parseCommentMultiLine"
--   return (dropWhileEnd isSpace line)

recoverSyntaxError :: msg -> Parser delim -> Parser (Location, msg, String)
recoverSyntaxError msg delim = do
  start <- P.getState
  txt <- P.skipTo delim
  end <- P.getState
  let loc = Location start.filename (Range start.pos end.pos)
  return (loc, msg, txt)

locOf :: Expr -> Maybe Location
locOf (Meta (C.Loc loc) _) = Just loc
locOf (Meta _ a) = locOf a
locOf (Ann a _) = locOf a
locOf _ = Nothing

class Check a where
  check :: a -> [(Maybe Location, Error Expr)]

instance Check Expr where
  check :: Expr -> [(Maybe Location, Error Expr)]
  check = \case
    Ann a b -> case errOf b of
      Just e -> (locOf a, e) : check a
      Nothing -> check a
    Meta (C.Error (SyntaxError (loc, ctx, txt))) a ->
      (Just loc, SyntaxError (loc, ctx, txt)) : check a
    Meta (C.Error e) Err | Just a <- Error.mainExpr e -> case locOf a of
      Just loc -> [(Just loc, e)]
      Nothing -> [(Nothing, e)]
    Meta (C.Loc loc) a | Just e <- errOf a -> do
      [(Just loc, e)]
    Meta _ a -> check a
    a -> collect check a

instance Check (Expr, Maybe Type) where
  check :: (Expr, Maybe Type) -> [(Maybe Location, Error Expr)]
  check (a, Just t) = check a ++ check t
  check (a, Nothing) = check a

instance Check Stmt where
  check :: Stmt -> [(Maybe Location, Error Expr)]
  check = \case
    Import {} -> []
    Def (a, b) -> check a ++ check b
    TypeDef (_, args, alts) -> concatMap check args ++ concatMap check alts
    Test t -> concatMap check [t.expr, t.expect]
    Run a -> check a
    Comment _ -> []

instance (Check a) => Check [a] where
  check :: [a] -> [(Maybe Location, Error Expr)]
  check = concatMap check

instance Check Module where
  check :: Module -> [(Maybe Location, Error Expr)]
  check (_, stmts) = concatMap check stmts

run :: Context -> FilePath -> Expr -> (Expr, Type)
run ctx path expr = do
  let (env, a) = compile ctx path expr
  eval [] (C.let' env a)

eval :: C.Env -> C.Expr -> (Expr, Type)
eval env expr =
  C.eval runtimeOps (C.let' env expr)
    & lift
    & typed

buildOps :: C.Ops
buildOps = do
  let call op f =
        (op, \eval args -> f (map eval args))
  let intOp1 op f = call op $ \case
        [a] | Just x <- C.asInt a -> Just (f x)
        _ -> Nothing
  let numOp1 op f = call op $ \case
        [a] | Just x <- C.asNum a -> Just (f x)
        _ -> Nothing
  let intOp2 op f = call op $ \case
        [a, b] | Just x <- C.asInt a, Just y <- C.asInt b -> Just (f x y)
        _ -> Nothing
  let numOp2 op f = call op $ \case
        [a, b] | Just x <- C.asNum a, Just y <- C.asNum b -> Just (f x y)
        _ -> Nothing
  [ intOp1 "int_neg" (\x -> C.Int (-x)),
    intOp2 "int_lt" (\x y -> C.tag' (if x < y then "True" else "False")),
    intOp2 "int_add" (\x y -> C.Int (x + y)),
    intOp2 "int_sub" (\x y -> C.Int (x - y)),
    intOp2 "int_mul" (\x y -> C.Int (x * y)),
    intOp2 "int_div" (\x y -> C.Num (fromIntegral x / fromIntegral y)),
    intOp2 "int_divi" (\x y -> C.Int (Prelude.div x y)),
    intOp2 "int_pow" (\x y -> C.Int (x ^ y)),
    numOp1 "num_neg" (\x -> C.Num (-x)),
    numOp2 "num_lt" (\x y -> C.tag' (if x < y then "True" else "False")),
    numOp2 "num_add" (\x y -> C.Num (x + y)),
    numOp2 "num_sub" (\x y -> C.Num (x - y)),
    numOp2 "num_mul" (\x y -> C.Num (x * y)),
    numOp2 "num_div" (\x y -> C.Num (x / y)),
    numOp2 "num_divi" (\x y -> C.Num (fromIntegral (floor (x / y)))),
    numOp2 "num_pow" (\x y -> C.Num (x ** y))
    ]

runtimeOps :: C.Ops
runtimeOps = buildOps

class Resolve a where
  resolve :: Context -> FilePath -> a -> [(FilePath, Expr)]

instance Resolve String where
  resolve :: Context -> FilePath -> String -> [(FilePath, Expr)]
  resolve ctx path name = resolve ctx path (name, ctx)

instance Resolve (String, [Module]) where
  resolve :: Context -> FilePath -> (String, [Module]) -> [(FilePath, Expr)]
  resolve ctx path (name, modules) = do
    let matchStmts (path', stmts) =
          if path == path' || (path ++ "/@") `isPrefixOf` path'
            then stmts
            else []
    resolve ctx path (name, concatMap matchStmts modules)

instance Resolve (String, [Stmt]) where
  resolve :: Context -> FilePath -> (String, [Stmt]) -> [(FilePath, Expr)]
  resolve ctx path (name, stmts) =
    concatMap (\stmt -> resolve ctx path (name, stmt)) stmts

instance Resolve (String, Stmt) where
  resolve :: Context -> FilePath -> (String, Stmt) -> [(FilePath, Expr)]
  resolve ctx path (name, stmt) = case stmt of
    Import path' alias names -> case names of
      _ | path == path' -> []
      ("", _) : _ -> do
        resolve ctx path (name, Import path' alias [(name, name)])
      (x, y) : names -> do
        let defs = if y == name then resolve ctx path' x else []
        defs ++ resolve ctx path (name, Import path' alias names)
      [] | alias == name -> [(path, Tag path' [])]
      [] -> []
    Def (p, b) | name `elem` bindings p -> do
      [(path, Let (p, b) (Var name))]
    TypeDef (name', args, alts) | name == name' -> do
      let resolveAlt (a, Just b) = Fun a b
          resolveAlt (a, Nothing) = Fun a (Tag name' args)
      [(path, fun args (or' $ map resolveAlt alts))]
    _ -> []

bindings :: Expr -> [String]
bindings p = do
  let (a, _) = C.appOf (lower [] $ Let (p, Any) Any)
  fst (C.forOf a)

class Compile a where
  compile :: Context -> FilePath -> a -> (C.Env, C.Expr)

instance Compile Expr where
  compile :: Context -> FilePath -> Expr -> (C.Env, C.Expr)
  compile ctx path expr = compile ctx path ("", expr)

instance Compile (String, Expr) where
  compile :: Context -> FilePath -> (String, Expr) -> (C.Env, C.Expr)
  compile ctx path (name, expr) = do
    let a = C.dropMeta $ lower [] expr
    let xs = delete name (C.freeVars a `union` C.freeTags a)
    let env = compileDefs ctx path xs
    case C.infer buildOps ((name, C.Var name) : env) a of
      Right [] ->
        (error . intercalate "\n")
          [ "compile: infer was empty",
            "name: " ++ name,
            "xs: " ++ show xs,
            "env: " ++ show (map fst env),
            "expr: " ++ show (dropMeta expr),
            "core: " ++ show (C.dropMeta a),
            ""
          ]
      Right alts -> do
        case C.collapse buildOps env (map (snd . fst) alts) of
          Right [(t, s)] -> (env, C.Ann (C.or' $ map (fst . fst) alts) t)
          _ -> (env, C.or' $ map (C.ann . fst) alts)
      Left err -> error $ show (name, xs, map fst env, err)

compileDefs :: Context -> FilePath -> [String] -> C.Env
compileDefs _ _ [] = []
compileDefs ctx path (x : xs) = do
  let compileDef (path, a) = compile ctx path (x, a)
  let defs = map compileDef (resolve ctx path x)
  let env1 = foldr (unionBy (\a b -> fst a == fst b)) [] (map fst defs)
  let env2 = compileDefs ctx path xs
  let env = unionBy (\a b -> fst a == fst b) env1 env2
  case defs of
    [] -> env
    defs -> do
      let a = C.let' env1 $ C.or' $ map snd defs
      (x, C.fix' [x] a) : env
