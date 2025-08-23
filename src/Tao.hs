module Tao where

import Control.Monad (void)
import qualified Core as C
import Data.Bifunctor (Bifunctor (bimap, second))
import Data.Char (chr, isAlphaNum, isSpace, ord)
import Data.Either (fromRight)
import Data.Function ((&))
import Data.List (delete, dropWhileEnd, intercalate, intersect, isPrefixOf, sort, union, unionBy, (\\))
import Data.Maybe (fromMaybe)
import Data.Sort (uniqueSort)
import Debug.Trace (trace)
import Error
import qualified Grammar as G
import Location (Location (Location), Position (Pos), Range (Range))
import Parser (Parser)
import qualified Parser as P
import qualified PrettyPrint as PP
import Stdlib (distinct, lookupValue, split)
import System.FilePath (dropTrailingPathSeparator, splitFileName, takeBaseName)

data Expr
  = Any
  | Int Int
  | Num Double
  | Char Char
  | Var String
  | Tag String [Expr]
  | Tuple [Expr]
  | List [Expr]
  | String [Segment]
  | For [String] Expr
  | Ann Expr Type
  | Or Expr Expr
  | Fun Pattern Expr
  | App Expr Expr
  | Call String [Expr]
  | Op1 Op1 Expr
  | Op2 Op2 Expr Expr
  | Dot Expr String (Maybe [Expr])
  | Spread Expr
  | Get Expr Expr
  | Slice Expr (Expr, Expr)
  | Match Expr [Expr]
  | MatchFun [Expr]
  | Let (Pattern, Expr) Expr
  | Bind (Pattern, Expr) Expr
  | Record [(String, Expr)]
  | Select Expr [(String, Expr)]
  | With Expr [(String, Expr)]
  | If Expr Expr
  | IfElse Expr Expr Expr
  | Meta (C.Metadata Expr) Expr
  | Err
  deriving (Eq)

instance Show Expr where
  show :: Expr -> String
  show = Tao.format 80 ""

type Type = Expr

type Pattern = Expr

type Case = ([String], Pattern, Expr)

data Segment
  = Str String
  | Val Expr
  deriving (Eq, Show)

data Op1
  = Not
  | Neg
  deriving (Eq)

op1s :: [(String, Op1)]
op1s =
  [ ("not", Not),
    ("-", Neg)
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
  | As
  | In
  | Is
  | Add
  | Add2
  | Sub
  | Sub2
  | Mul
  | Mul2
  | Div
  | Div2
  | Pow
  | Pow2
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
    ("as", As),
    ("in", In),
    ("is", Is),
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
    ("++", Add2),
    ("-", Sub),
    ("--", Sub2),
    ("*", Mul),
    ("**", Mul2),
    ("/", Div),
    ("//", Div2),
    ("^", Pow),
    ("^^", Pow2)
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
  | Nop (C.Metadata Expr)
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
    "as",
    "in",
    "is",
    "xor",
    "let",
    "if",
    "then",
    "else",
    "match",
    "type",
    "with"
  ]

varOf :: Expr -> Maybe String
varOf (Var x) = Just x
varOf (Meta _ a) = varOf a
varOf _ = Nothing

tupleOf :: Expr -> [Expr]
tupleOf (Tuple items) = items
tupleOf a = [a]

isTuple :: Expr -> Bool
isTuple = \case
  Tuple _ -> True
  Meta _ a -> isTuple a
  _ -> False

listOf :: Expr -> Maybe [Expr]
listOf (List items) = Just items
listOf (Meta _ a) = listOf a
listOf _ = Nothing

isOr :: Expr -> Bool
isOr = \case
  Or _ _ -> True
  Meta _ a -> isOr a
  _ -> False

forOf :: Expr -> ([String], Expr)
forOf = \case
  For xs a -> case forOf a of
    (ys, a') -> (xs ++ ys, a')
  Ann a _ -> forOf a
  Meta _ a -> forOf a
  a -> ([], a)

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

isSpread :: Expr -> Bool
isSpread = \case
  Spread _ -> True
  Ann a _ -> isSpread a
  Meta _ a -> isSpread a
  _ -> False

spreadOf :: Expr -> Maybe Expr
spreadOf = \case
  Spread a -> Just a
  Ann a _ -> spreadOf a
  Meta _ a -> spreadOf a
  _ -> Nothing

list' :: [Expr] -> Expr
list' [] = tag "[]"
list' [a] | Just a' <- spreadOf a = a'
list' (a : bs) = Tag "::" [a, list' bs]

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

tagOf :: Expr -> Maybe (String, [Expr])
tagOf (Tag k args) = Just (k, args)
tagOf (Meta _ a) = tagOf a
tagOf _ = Nothing

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
or' [] = Tuple []
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

not' :: Expr -> Expr
not' = Op1 Not

neg :: Expr -> Expr
neg = Op1 Neg

andOp :: Expr -> Expr -> Expr
andOp = Op2 AndOp

orOp :: Expr -> Expr -> Expr
orOp = Op2 OrOp

xorOp :: Expr -> Expr -> Expr
xorOp = Op2 XorOp

as :: Expr -> Expr -> Expr
as = Op2 As

asAs :: Expr -> Maybe (Expr, Expr)
asAs = \case
  Op2 As a b -> Just (a, b)
  Meta _ a -> asAs a
  _ -> Nothing

notAs :: Expr -> Expr -> Expr
notAs a b = not' (as a b)

in' :: Expr -> Expr -> Expr
in' = Op2 In

asIn :: Expr -> Maybe (Expr, Expr)
asIn = \case
  Op2 In a b -> Just (a, b)
  Meta _ a -> asIn a
  _ -> Nothing

notIn :: Expr -> Expr -> Expr
notIn a b = not' (in' a b)

is :: Expr -> Expr -> Expr
is = Op2 Is

asIs :: Expr -> Maybe (Expr, Expr)
asIs = \case
  Op2 Is a b -> Just (a, b)
  Meta _ a -> asIs a
  _ -> Nothing

isNot :: Expr -> Expr -> Expr
isNot a b = not' (is a b)

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

shiftL :: Expr -> Expr -> Expr
shiftL = Op2 ShiftL

shiftR :: Expr -> Expr -> Expr
shiftR = Op2 ShiftR

pipeL :: Expr -> Expr -> Expr
pipeL = Op2 PipeL

pipeR :: Expr -> Expr -> Expr
pipeR = Op2 PipeR

cons :: Expr -> Expr -> Expr
cons = Op2 Cons

consOf :: Expr -> Maybe (Expr, Expr)
consOf (Op2 Cons a b) = Just (a, b)
consOf (Meta _ a) = consOf a
consOf _ = Nothing

add :: Expr -> Expr -> Expr
add = Op2 Add

sub :: Expr -> Expr -> Expr
sub = Op2 Sub

mul :: Expr -> Expr -> Expr
mul = Op2 Mul

div' :: Expr -> Expr -> Expr
div' = Op2 Div

div2 :: Expr -> Expr -> Expr
div2 = Op2 Div2

pow :: Expr -> Expr -> Expr
pow = Op2 Pow

ifOf :: Expr -> Maybe (Expr, Expr)
ifOf (If a b) = Just (a, b)
ifOf (Ann a _) = ifOf a
ifOf (Meta _ a) = ifOf a
ifOf _ = Nothing

typed :: Expr -> (Expr, Type)
typed (Ann a t) = (a, t)
typed (Meta _ a) | isAnn a = typed a
typed a = (a, Any)

bound :: Expr -> Expr
bound = \case
  Fun a b -> For [] (Fun (bound a) (bound b))
  a -> apply bound a

isSimpleExpr :: Expr -> Bool
isSimpleExpr = \case
  For _ _ -> False
  Or _ _ -> False
  Fun _ _ -> False
  Match _ _ -> False
  MatchFun _ -> False
  Let _ _ -> False
  Bind _ _ -> False
  Meta _ a -> isSimpleExpr a
  _ -> True

-- Helper functions
class Apply a where
  apply :: (Expr -> Expr) -> a -> a

instance Apply Expr where
  apply :: (Expr -> Expr) -> Expr -> Expr
  apply f = \case
    Any -> Any
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
    Spread a -> Spread (f a)
    Get a b -> Get (f a) (f b)
    Slice a (b, c) -> Slice (f a) (f b, f c)
    Match arg cases -> Match (f arg) (map f cases)
    MatchFun cases -> MatchFun (map f cases)
    Let (a, b) c -> Let (f a, f b) (f c)
    Bind (a, b) c -> Bind (f a, f b) (f c)
    Record fields -> Record (second f <$> fields)
    Select a fields -> Select (f a) (second f <$> fields)
    With a fields -> With (f a) (second f <$> fields)
    If a b -> If (f a) (f b)
    IfElse a b c -> IfElse (f a) (f b) (f c)
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
    Nop m -> Nop (fmap f m)

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
  Spread a -> f a
  Get a b -> f a `union` f b
  Slice a (b, c) -> f a `union` f b `union` f c
  Match arg cases -> f arg `union` unionMap f cases
  MatchFun cases -> unionMap f cases
  Let (a, b) c -> f a `union` f b `union` f c
  Bind (a, b) c -> f a `union` f b `union` f c
  Record fields -> unionMap (f . snd) fields
  Select a fields -> f a `union` unionMap (f . snd) fields
  With a fields -> f a `union` unionMap (f . snd) fields
  If a b -> f a `union` f b
  IfElse a b c -> f a `union` f b `union` f c
  Meta m a -> f a
  Err -> []
  where
    unionMap f = foldr (union . f) []

locSpan :: P.State -> P.State -> Location
locSpan start end = Location start.filename (Range start.pos end.pos)

withLoc :: P.State -> P.State -> Expr -> Expr
withLoc start end = Meta (C.Loc (locSpan start end))

parse :: Int -> FilePath -> String -> Either P.State (Expr, P.State)
parse prec = P.parse (G.parser grammar prec)

layout :: Int -> Expr -> PP.Layout
layout prec = G.layout grammar prec

format :: Int -> String -> Expr -> String
format width indent = G.format grammar width ("  ", indent)

syntaxError :: Location -> String -> String -> Expr
syntaxError loc expected got = do
  Meta (C.Error $ SyntaxError (loc, expected, got)) Err

syntaxErrorStmt :: Location -> String -> String -> Stmt
syntaxErrorStmt loc expected got = do
  Nop (C.Error $ SyntaxError (loc, expected, got))

parseCollection :: String -> String -> String -> String -> (Location -> String -> String -> a) -> Parser a -> Parser [a]
parseCollection msg open delim close catch parser = do
  _ <- P.text open
  _ <- P.whitespaces
  xs <- P.zeroOrMore $ do
    x <- P.expect msg parser & P.recover [P.text delim] catch
    _ <- P.whitespaces
    _ <- P.text delim
    _ <- P.whitespaces
    return x
  x <- P.zeroOrOne $ do
    x <- P.expect msg parser & P.recover [P.text close] catch
    _ <- P.whitespaces
    return x
  _ <- P.text close
  return (xs ++ x)

layoutCollection :: String -> String -> String -> [PP.Layout] -> PP.Layout
layoutCollection open _ close [] = [PP.Text (open ++ close)]
layoutCollection open delim close xs = do
  let alt1 = [PP.Indent (PP.join [PP.Text (delim ++ " ")] xs)]
  let alt2 = [PP.Indent (PP.Text " " : PP.join [PP.Text delim, PP.NewLine] xs), PP.Text delim, PP.NewLine]
  [PP.Text open, PP.Or alt1 alt2, PP.Text close]

parserDecorator :: String -> ([String] -> Expr -> Expr) -> Parser Expr -> Parser Expr
parserDecorator op f rhs = do
  start <- P.state
  _ <- P.text op
  _ <- P.spaces
  x <- parseNameVar
  xs <- P.zeroOrMore $ do
    _ <- P.spaces
    parseNameVar
  end <- P.state
  _ <- P.spaces
  _ <- P.oneOf [P.char '.', P.char '\n']
  _ <- P.whitespaces
  a <- rhs
  _ <- P.spaces
  return (withLoc start end $ f (x : xs) a)

layoutDecorator :: String -> (a -> Maybe ([String], a)) -> (a -> PP.Layout) -> a -> Maybe PP.Layout
layoutDecorator op match rhs a = do
  (xs, a) <- match a
  let names = unwords xs
  let decorator = PP.Text (op ++ names)
  let alt1 = PP.Text ". " : rhs a
  let alt2 = PP.NewLine : rhs a
  if length names > 3
    then Just (decorator : alt2)
    else Just [decorator, PP.Or alt1 alt2]

layoutLeading :: (String, String) -> (Expr -> Maybe (Expr, Expr)) -> (Expr -> PP.Layout) -> (Expr -> PP.Layout) -> Expr -> Maybe PP.Layout
layoutLeading (op1, op2) match lhs rhs a = do
  (x, y) <- match a
  let alt1 = lhs x ++ [PP.Text " | "] ++ rhs y
  let alt2 = lhs x ++ [PP.NewLine, PP.Text "| ", PP.Indent (rhs y)]
  return $
    if isSimpleExpr x
      then [PP.Or alt1 alt2]
      else alt2

grammar :: G.Grammar Expr
grammar = do
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
                start <- P.state
                _ <- P.char 'c'
                quote <- P.oneOf [P.char '\'', P.char '"']
                -- _ <- P.commit "char"
                ch <- P.anyChar
                _ <- P.char quote
                end <- P.state
                _ <- P.spaces
                return (withLoc start end $ Char ch)
           in G.Atom parser $ \_ -> \case
                Char ch -> Just [PP.Text $ "c" ++ show ch]
                _ -> Nothing,
          -- Grammar.Var
          G.atom (loc1 Var) parseNameVar $ \_ -> \case
            Var x -> do
              let showVar = \case
                    x | all (\c -> isAlphaNum c || c `elem` "_-$") x -> x
                    x -> "(" ++ x ++ ")"
              Just [PP.Text (showVar x)]
            _ -> Nothing,
          -- Grammar.Tag
          let parser expr = do
                start <- P.state
                k <- parseNameTag
                end <- P.state
                _ <- P.spaces
                args <- P.oneOf [parseCollection "tag argument" "<" "," ">" syntaxError expr, return []]
                _ <- P.spaces
                return (withLoc start end $ Tag k args)
           in G.Atom parser $ \rhs -> \case
                Tag k args -> do
                  let showTag = \case
                        "[]" -> "[]"
                        k | all (\c -> isAlphaNum c || c `elem` "_-$") k -> k
                        k -> "t'" ++ k ++ "'"
                  let showArgs = \case
                        [] -> []
                        args -> layoutCollection "<" "," ">" (map rhs args)
                  Just (PP.Text (showTag k) : showArgs args)
                _ -> Nothing,
          -- Grammar.Tuple
          let parser expr = do
                start <- P.state
                items <- parseCollection "tuple item" "(" "," ")" syntaxError expr
                end <- P.state
                _ <- P.spaces
                return (withLoc start end $ Tuple items)
           in G.Atom parser $ \layout -> \case
                Tuple items -> Just (layoutCollection "(" "," ")" (map layout items))
                _ -> Nothing,
          -- Grammar.List
          let parser expr = do
                start <- P.state
                items <- parseCollection "list item" "[" "," "]" syntaxError expr
                end <- P.state
                _ <- P.spaces
                return (withLoc start end $ List items)
           in G.Atom parser $ \layout -> \case
                List items -> Just (layoutCollection "[" "," "]" (map layout items))
                _ -> Nothing,
          -- Grammar.String
          let parser expr = do
                start <- P.state
                quote <- P.oneOf [P.char '\'', P.char '"']
                -- _ <- P.commit "string"
                txt <- P.skipTo (P.char quote)
                _ <- P.char quote
                end <- P.state
                _ <- P.spaces
                let segments = [Str txt]
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
                start <- P.state
                _ <- P.word "let"
                -- _ <- P.commit "let"
                end <- P.state
                _ <- P.whitespaces
                a <- expr
                _ <- P.whitespaces
                bind <-
                  P.oneOf
                    [ do _ <- P.char '='; return Let,
                      do _ <- P.text "<-"; return Bind
                    ]
                _ <- P.whitespaces
                b <- expr
                _ <- parseLineBreak
                withLoc start end . bind (a, b) <$> expr
           in G.Atom parser $ \layout -> \case
                Let (a, b) c -> Just (PP.Text "let " : layout a ++ PP.Text " = " : layout b ++ PP.NewLine : layout c)
                Bind (a, b) c -> Just (PP.Text "let " : layout a ++ PP.Text " <- " : layout b ++ PP.NewLine : layout c)
                _ -> Nothing,
          -- Grammar.Ann
          G.InfixR 1 (G.parserLeading ":" (loc2 Ann)) $ layoutLeading (" : ", ": ") $ \case
            Ann a b -> Just (a, b)
            _ -> Nothing,
          G.infixR 1 (loc2 Ann) ":" $ \case
            Ann a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.PipeL
          G.infixR 4 (locOp2 PipeL) "<|" $ \case
            Op2 PipeL a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.PipeR
          G.infixL 5 (locOp2 PipeR) "|>" $ \case
            Op2 PipeR a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Or
          G.InfixR 3 (G.parserLeading "|" (loc2 Or)) $ layoutLeading (" | ", "| ") $ \case
            Or a b -> Just (a, b)
            _ -> Nothing,
          -- Grammar.Op2.ShiftL
          G.infixR 6 (locOp2 ShiftL) "<<" $ \case
            Op2 ShiftL a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.ShiftR
          G.infixL 7 (locOp2 ShiftR) ">>" $ \case
            Op2 ShiftR a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Fun
          G.InfixR 8 (G.parserLeading "->" (loc2 Fun)) $ layoutLeading (" -> ", "->") $ \case
            Fun a b -> Just (a, b)
            _ -> Nothing,
          -- Grammar.If
          let parser a expr = do
                start <- P.state
                _ <- P.word "if"
                -- _ <- P.commit "if"
                end <- P.state
                _ <- P.spaces
                b <- expr
                return (withLoc start end $ If a b)
           in G.InfixR 9 parser $ \lhs rhs -> \case
                If a b -> Just (lhs a ++ PP.Text " if " : rhs b)
                _ -> Nothing,
          -- Grammar.Op2.OrOp
          G.infixL 10 (locOp2 OrOp) "or" $ \case
            Op2 OrOp a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.XorOp
          G.infixL 10 (locOp2 XorOp) "xor" $ \case
            Op2 XorOp a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.AndOp
          G.infixL 11 (locOp2 AndOp) "and" $ \case
            Op2 AndOp a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Eq
          G.infixL 12 (locOp2 Eq) "==" $ \case
            Op2 Eq a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Ne
          G.infixL 12 (locOp2 Ne) "!=" $ \case
            Op2 Ne a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Lt
          let parser a expr = do
                start <- P.state
                _ <- P.char '<'
                end <- P.state
                _ <- P.lookaheadNot (P.char '-')
                _ <- P.spaces
                withLoc start end . Op2 Lt a <$> expr
           in G.InfixL 13 parser $ \lhs rhs -> \case
                Op2 Lt a b -> Just (lhs a ++ PP.Text " < " : rhs b)
                _ -> Nothing,
          -- Grammar.Op2.Le
          G.infixL 13 (locOp2 Le) "<=" $ \case
            Op2 Le a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Gt
          G.infixL 13 (locOp2 Gt) ">" $ \case
            Op2 Gt a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Ge
          G.infixL 13 (locOp2 Ge) ">=" $ \case
            Op2 Ge a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.For
          G.Prefix 14 (parserDecorator "@" For) $ layoutDecorator "@" $ \case
            For xs a -> Just (xs, a)
            _ -> Nothing,
          -- Grammar.Op2.As
          G.infixL 14 (locOp2 As) "as" $ \case
            Op2 As a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.In
          G.infixL 14 (locOp2 In) "in" $ \case
            Op2 In a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Not.As | Grammar.Op2.Not.In
          let parser a expr = do
                start <- P.state
                _ <- P.word "not"
                _ <- P.spaces
                op <-
                  P.oneOf
                    [ as <$ P.word "as",
                      in' <$ P.word "in"
                    ]
                end <- P.state
                _ <- P.spaces
                b <- expr
                return (withLoc start end $ not' (op a b))
           in G.InfixL 14 parser $ \lhs rhs -> \case
                Op1 Not expr
                  | Just (a, b) <- asAs expr -> Just (lhs a ++ PP.Text " not as " : rhs b)
                  | Just (a, b) <- asIn expr -> Just (lhs a ++ PP.Text " not in " : rhs b)
                _ -> Nothing,
          -- Grammar.Op2.Is | Grammar.Op2.Not.Is
          let parser a expr = do
                start <- P.state
                _ <- P.word "is"
                f <- P.oneOf [do _ <- P.spaces; not' <$ P.word "not", return id]
                end <- P.state
                _ <- P.spaces
                b <- expr
                return (withLoc start end $ f (is a b))
           in G.InfixL 14 parser $ \lhs rhs -> \case
                Op2 Is a b -> Just (lhs a ++ PP.Text " is " : rhs b)
                Op1 Not expr | Just (a, b) <- asIs expr -> Just (lhs a ++ PP.Text " is not " : rhs b)
                _ -> Nothing,
          -- Grammar.Op2.Cons
          G.infixR 15 (locOp2 Cons) "::" $ \case
            Op2 Cons a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Add2
          G.infixL 16 (locOp2 Add2) "++" $ \case
            Op2 Add2 a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Add
          G.infixL 16 (locOp2 Add) "+" $ \case
            Op2 Add a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Sub
          G.infixL 16 (locOp2 Sub2) "--" $ \case
            Op2 Sub2 a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Sub
          G.infixL 16 (locOp2 Sub) "-" $ \case
            Op2 Sub a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Mul2
          G.infixL 17 (locOp2 Mul2) "**" $ \case
            Op2 Mul2 a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Mul
          G.infixL 17 (locOp2 Mul) "*" $ \case
            Op2 Mul a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Div2
          G.infixL 17 (locOp2 Div2) "//" $ \case
            Op2 Div2 a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Div
          G.infixL 17 (locOp2 Div) "/" $ \case
            Op2 Div a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Pow2
          G.infixR 18 (locOp2 Pow2) "^^" $ \case
            Op2 Pow2 a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op2.Pow
          G.infixR 18 (locOp2 Pow) "^" $ \case
            Op2 Pow a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Op1.Neg
          G.prefix 19 (locOp1 Neg) "-" $ \case
            Op1 Neg a -> Just ("", a)
            _ -> Nothing,
          -- Grammar.not
          G.prefix 19 (loc1 not') "not" $ \case
            Op1 Not a -> Just (" ", a)
            _ -> Nothing,
          -- Grammar.App
          let parser a expr = do
                start <- P.state
                args <- parseCollection "function argument" "(" "," ")" syntaxError (parseExpr 0)
                end <- P.state
                _ <- P.spaces
                return (withLoc start end $ app a args)
           in G.InfixL 19 parser $ \lhs rhs -> \case
                App a b -> do
                  let args = map (layout 0) (tupleOf b)
                  Just (lhs a ++ layoutCollection "(" "," ")" args)
                _ -> Nothing,
          -- Grammar.Get | Grammar.Slice
          let parser a expr = do
                start <- P.state
                _ <- P.char '['
                _ <- P.whitespaces
                b <- parseExpr 2
                op <-
                  P.oneOf
                    [ do
                        _ <- P.char ':'
                        _ <- P.whitespaces
                        c <- parseExpr 2
                        return (`Slice` (b, c)),
                      return (`Get` b)
                    ]
                _ <- P.whitespaces
                _ <- P.char ']'
                end <- P.state
                _ <- P.spaces
                return (withLoc start end $ op a)
           in G.InfixL 19 parser $ \lhs rhs -> \case
                Get a b -> do
                  Just (lhs a ++ PP.Text "[" : G.layout grammar 2 b ++ [PP.Text "]"])
                Slice a (b, c) -> do
                  Just (lhs a ++ PP.Text "[" : G.layout grammar 2 b ++ PP.Text ":" : G.layout grammar 2 c ++ [PP.Text "]"])
                _ -> Nothing,
          -- Grammar.Dot
          let parser a expr = do
                start <- P.state
                _ <- P.char '.'
                end <- P.state
                _ <- P.whitespaces
                x <- parseNameVar
                _ <- P.spaces
                args <-
                  P.maybe' $ do
                    args <- parseCollection "method argument" "(" "," ")" syntaxError (parseExpr 0)
                    _ <- P.spaces
                    return args
                _ <- P.spaces
                return (withLoc start end $ Dot a x args)
           in G.InfixL 19 parser $ \lhs rhs -> \case
                Dot a x Nothing -> Just (lhs a ++ [PP.Text ("." ++ x)])
                Dot a x (Just args) -> Just (lhs a ++ [PP.Text ("." ++ x)] ++ layoutCollection "(" "," ")" (map (layout 0) args))
                _ -> Nothing,
          -- Grammar.Spread
          let parser expr = do
                _ <- P.text ".."
                a <- P.oneOf [do _ <- P.spaces; expr, return Any]
                return (Spread a)
           in G.Atom parser $ \layout -> \case
                Spread Any -> Just [PP.Text ".."]
                Spread a -> Just (PP.Text ".." : layout a)
                _ -> Nothing,
          -- Grammar.Call
          let parser expr = do
                start <- P.state
                _ <- P.char '%'
                -- _ <- P.commit "call"
                f <- parseName
                end <- P.state
                _ <- P.spaces
                args <-
                  P.oneOf
                    [ do
                        args <- parseCollection "builtin call argument" "(" "," ")" syntaxError expr
                        _ <- P.spaces
                        return args,
                      return []
                    ]
                return (withLoc start end $ Call f args)
           in G.Atom parser $ \rhs -> \case
                Call f [] -> Just [PP.Text $ "%" ++ f]
                Call f args -> Just (PP.Text ("%" ++ f) : layoutCollection "(" "," ")" (map rhs args))
                _ -> Nothing,
          -- Grammar.Match / Grammar.MatchFun
          let parser expr = do
                start <- P.state
                _ <- P.word "match"
                -- _ <- P.commit "match"
                end <- P.state
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
                  case' <- parseExpr 1
                  _ <- P.whitespaces
                  return case'
                _ <- P.char '}'
                _ <- P.spaces
                case maybeArg of
                  Just arg -> return (withLoc start end $ Match arg cases)
                  Nothing -> return (withLoc start end $ MatchFun cases)
              layoutCases layout = \case
                [] -> []
                cases -> PP.NewLine : concatMap (\c -> [PP.Text "| ", PP.Indent (layout c), PP.NewLine]) cases
           in G.Atom parser $ \layout -> \case
                Match arg cases -> do
                  let arg' = case layout arg of
                        arg | PP.isMultiLine arg -> do
                          [PP.Text "(", PP.Indent (PP.NewLine : arg), PP.NewLine, PP.Text ")"]
                        arg -> arg
                  Just (PP.Text "match " : arg' ++ PP.Text " {" : layoutCases layout cases ++ [PP.Text "}"])
                MatchFun cases -> do
                  Just (PP.Text "match {" : layoutCases layout cases ++ [PP.Text "}"])
                _ -> Nothing,
          -- Grammar.Record [(String, Expr)]
          -- Grammar.Select Expr [(String, Expr)]
          -- Grammar.With Expr [(String, Expr)]
          -- Grammar.IfElse
          let parser expr = do
                start <- P.state
                _ <- P.word "if"
                -- _ <- P.commit "if"
                end <- P.state
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
                return (withLoc start end $ IfElse a b c)
           in G.Atom parser $ \layout -> \case
                IfElse a b c -> Just (PP.Text "if " : layout a ++ PP.Text " then " : layout b ++ PP.Text " else " : layout c)
                _ -> Nothing,
          -- Grammar.Metadata.Comments
          let parser expr = do
                comments <- P.oneOrMore $ do
                  _ <- P.oneOf [P.text "//", P.text "#"]
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
                -- P.commit "Metadata location"
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
                start <- P.state
                _ <- P.word "!error"
                end <- P.state
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
                Err -> Just [PP.Text "!error"]
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

lower :: Expr -> C.Expr
lower = \case
  Any -> C.Any
  Int i -> C.Int i
  Num n -> C.Num n
  Char c -> C.tag "Char" [C.Int (ord c)]
  Var x -> C.Var x
  Tag "Int" [] -> C.IntT
  Tag "Num" [] -> C.NumT
  Tag k args -> C.tag k (map lower args)
  Ann a b -> C.Ann (lower a) (lower b)
  Tuple items -> C.and' (map lower items)
  List items -> lower (list' items)
  String [] -> C.tag' "''"
  String [Str txt] -> lower (List (map Char txt))
  String segments -> error "TODO: lower String interpolation"
  Or a b -> C.Or (lower a) (lower b)
  For ys a -> C.for ys (lower a)
  Fun a b
    | Just (a, cond) <- ifOf a -> lower (Fun a (If b cond))
    | otherwise -> C.Fun (lower a) (lower b)
  App a b -> C.App (lower a) (lower b)
  Call op args -> C.Call op (lower (Tuple args))
  Op1 Neg a -> lower (sub (Int 0) a)
  Op1 op a -> C.app (C.Var $ show op) [lower a]
  Op2 Cons a b -> lower (Tag "::" [a, b])
  Op2 op a b -> C.app (C.Var $ show op) [lower a, lower b]
  Dot a x Nothing -> C.App (C.Var x) (lower a)
  Dot a x (Just args) -> C.App (C.Var x) (lower $ Tuple (a : args))
  Spread a -> error $ "TODO: lower Spread " ++ show a
  Get a b -> lower (app (Var ".[]") [a, b])
  Slice a (b, c) -> lower (app (Var ".[:]") [a, b, c])
  Match arg cases -> lower (App (or' cases) arg)
  MatchFun cases -> lower (or' cases)
  Let (a, b) c | Just x <- varOf c, Just d <- lookup x (C.unpack (lower a, lower b)) -> d
  Let (a, b) c -> lower (App (Fun a c) b)
  Bind (a, b) c -> lower (app (Var "<-") [b, Fun a c])
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
  If a b -> lower (Let (Ann true bool, b) a)
  IfElse a b c -> lower (Match a [Fun (Ann true bool) b, Fun (Ann false bool) c])
  Meta m a -> C.Meta (fmap lower m) (lower a)
  Err -> C.Err
  a -> error $ "TODO: lower " ++ show (dropMeta a)

lift :: C.Expr -> Expr
lift = \case
  C.Any -> Any
  C.Unit -> Tuple []
  C.IntT -> tag "Int"
  C.NumT -> tag "Num"
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
  C.Call op a -> Call op (tupleOf (lift a))
  -- C.Let [] b -> lift b
  -- C.Let ((x, b) : env) c -> Let (Var x, lift b) (lift (C.Let env c))
  C.Meta (C.Loc _) (C.Meta (C.Loc loc) a) -> Meta (C.Loc loc) (lift a)
  C.Meta m a -> Meta (fmap lift m) (lift a)
  C.Err -> Err
  a -> error $ "TODO: lift " ++ show a

parseExpr :: Int -> Parser Expr
parseExpr = G.parser grammar

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
        P.word "as",
        P.word "in",
        P.word "is",
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
        P.text "++",
        P.text "+",
        P.text "--",
        P.text "-",
        P.text "**",
        P.text "*",
        P.text "//",
        P.text "/",
        P.text "^^",
        P.text "^",
        P.text ".[]",
        P.text ".[:]"
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
  let parsers =
        [ parseImport,
          Def <$> parseDef "=",
          TypeDef <$> parseTypeDef,
          parseTest,
          -- Nop <$> parseComment,
          Run <$> parseExpr 1
          -- TODO: consider a trailing comment on a syntax error like this
          -- , Run . (\e -> Meta (C.Error e) Err) . SyntaxError <$> recoverSyntaxError "statement" (P.text "\n")
        ]
  stmt <-
    P.oneOf parsers
      & P.recover [parseLineBreak] syntaxErrorStmt
  _ <- parseLineBreak
  return stmt

parseModulePath :: Parser String
parseModulePath = do
  pkg <- parseNameVar
  path <- P.zeroOrMore $ do
    _ <- P.char '/'
    name <- parseNameVar
    return ('/' : name)
  return $ concat (pkg : path)

parseImport :: Parser Stmt
parseImport = do
  _ <- P.commit "import statement" $ P.word "import"
  _ <- P.spaces
  path <-
    -- TODO: Import strings should support a list of Metadata for errors, comments, locations, etc
    -- type Name = ([Meta], String)
    -- Import Name Name [(Name, Name)] [Meta]
    P.expect "import module path" parseModulePath
      & P.recover [P.word "as", P.text "(", "" <$ parseLineBreak] (\loc exp got -> '!' : show (SyntaxError (loc, exp, got) :: Error Expr))
  _ <- P.spaces
  alias <-
    P.oneOf
      [ do
          _ <- P.commit "import module alias" $ P.word "as"
          _ <- P.spaces
          alias <- parseName
          _ <- P.spaces
          return alias,
        return $ case path of
          '!' : syntaxError -> ""
          path -> takeBaseName path
      ]
  names <-
    P.oneOf
      [ do
          parseCollection "imported name" "(" "," ")" (\loc got expected -> error "TODO: parseImport error handling") $ do
            name <- parseName
            _ <- P.spaces
            alias <-
              P.oneOf
                [ do
                    _ <- P.commit "import name alias" $ P.word "as"
                    _ <- P.spaces
                    alias <- parseName
                    _ <- P.spaces
                    return alias,
                  return name
                ]
            return (name, alias),
        return []
      ]
  _ <- P.spaces
  return (Import path alias names)

parseDef :: String -> Parser (Expr, Expr)
parseDef "" = error "parseDef delimiter must not be empty"
parseDef op = do
  typeAnnotation <- P.maybe' $ do
    _ <- P.char ':'
    -- P.commit "def type"
    _ <- P.spaces
    t <- parseExpr 0
    _ <- parseLineBreak
    return t
  _ <- P.word "let"
  -- _ <- P.commit "def"
  _ <- P.whitespaces
  a <- parseExpr 0
  _ <- P.word op
  _ <- P.whitespaces
  b <- parseExpr 0
  case typeAnnotation of
    Just t -> return (Ann a t, b)
    Nothing -> return (a, b)

parseTypeDef :: Parser (String, [Expr], [(Expr, Maybe Type)])
parseTypeDef = do
  _ <- P.commit "type definition" $ P.word "type"
  _ <- P.whitespaces
  name <- P.expect "type name" $ parseNameTag
  _ <- P.whitespaces
  args <-
    P.oneOf
      [ parseCollection "type argument" "<" "," ">" syntaxError (parseExpr 0)
          & P.recover [P.char '='] (\loc expected got -> error ("TODO: " ++ show (loc, expected, got))),
        -- return []
        error $ "TODO: could not parse type args: " ++ name
      ]
  _ <- P.whitespaces
  _ <- P.char '='
  _ <- P.whitespaces
  let parseAlt = do
        a <- parseExpr 4
        _ <- P.spaces
        mb <- P.maybe' $ do
          _ <- P.whitespaces
          _ <- P.text "=>"
          _ <- P.whitespaces
          parseExpr 4
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
  s <- P.state
  _ <- P.char '>'
  _ <- P.oneOrMore P.space
  -- P.commit "test"
  expr <- parseExpr 0
  result <-
    P.oneOf
      [ do
          _ <- parseLineBreak
          parseExpr 0,
        do
          _ <- P.text "~>"
          _ <- P.whitespaces
          parseExpr 0,
        return (Tag "True" [])
      ]
  return (Test (UnitTest s.filename s.pos name expr result))

parseComment :: Parser String
parseComment = parseCommentSingleLine

parseCommentSingleLine :: Parser String
parseCommentSingleLine = do
  _ <- P.char '#'
  -- P.commit "comment-singleline"
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
    -- TODO: check should parse import (path, alias, names) in look for syntax errors (names starting with '!')
    -- TODO check should verify the import path exists
    -- TODO check should verify the imported names exist
    Import {} -> []
    Def (a, b) -> check a ++ check b
    TypeDef (_, args, alts) -> concatMap check args ++ concatMap check alts
    Test t -> concatMap check [t.expr, t.expect]
    Run a -> check a
    Nop m -> check (Meta m Err)

instance (Check a) => Check [a] where
  check :: [a] -> [(Maybe Location, Error Expr)]
  check = concatMap check

instance Check Module where
  check :: Module -> [(Maybe Location, Error Expr)]
  check (_, stmts) = concatMap check stmts

run :: Context -> FilePath -> Expr -> Expr
run ctx path expr = do
  let (env, a) = compile ctx path expr
  eval [] (C.let' env a)

eval :: C.Env -> C.Expr -> Expr
eval env expr =
  lift $ C.eval runtimeOps (C.let' env expr)

buildOps :: C.Ops
buildOps = do
  let call op f =
        (op, \eval a -> f (C.dropTypes $ eval a))
  let intOp1 op f = call op $ \case
        C.Int x -> Just (f x)
        _ -> Nothing
  let numOp1 op f = call op $ \case
        C.Num x -> Just (f x)
        _ -> Nothing
  let intOp2 op f = call op $ \case
        C.And (C.Int x) (C.Int y) -> Just (f x y)
        _ -> Nothing
  let numOp2 op f = call op $ \case
        C.And (C.Num x) (C.Num y) -> Just (f x y)
        _ -> Nothing
  [ intOp2 "int_lt" (\x y -> C.tag' (if x < y then "True" else "False")),
    intOp2 "int_add" (\x y -> C.Int (x + y)),
    intOp2 "int_sub" (\x y -> C.Int (x - y)),
    intOp2 "int_mul" (\x y -> C.Int (x * y)),
    intOp2 "int_div" (\x y -> C.Num (fromIntegral x / fromIntegral y)),
    intOp2 "int_divi" (\x y -> C.Int (Prelude.div x y)),
    intOp2 "int_pow" (\x y -> C.Int (x ^ y)),
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
    concatMap (\mod -> resolve ctx path (name, mod)) modules

instance Resolve (String, Module) where
  resolve :: Context -> FilePath -> (String, Module) -> [(FilePath, Expr)]
  resolve ctx path (name, (path', stmts)) = case splitFileName path of
    (dir, '@' : _) -> resolve ctx (dropTrailingPathSeparator dir) (name, (path', stmts))
    _ | path == path' -> resolve ctx path (name, stmts)
    _ | (path ++ "/@") `isPrefixOf` path' -> resolve ctx path (name, stmts)
    _ -> []

instance Resolve (String, [Stmt]) where
  resolve :: Context -> FilePath -> (String, [Stmt]) -> [(FilePath, Expr)]
  resolve ctx path (name, stmts) =
    concatMap (\stmt -> resolve ctx path (name, stmt)) stmts

instance Resolve (String, Stmt) where
  resolve :: Context -> FilePath -> (String, Stmt) -> [(FilePath, Expr)]
  resolve ctx path (name, stmt) = case stmt of
    Import path' alias names -> case names of
      _ | path == path' -> []
      _ | (path' ++ "/@") `isPrefixOf` path -> []
      -- _ | (path' ++ "/@") `isPrefixOf` path -> do
      --   let ctx' = filter ((/= path) . fst) ctx
      --   let paths = filter (\p -> p /= path && (path' ++ "/@") `isPrefixOf` p) (map fst ctx)
      --   resolve ctx' path (name, map (\p -> Import p alias names) paths)
      -- resolve ctx path (name, map ())
      -- _ | (path ++ "/@") `isPrefixOf` path' -> []
      -- TODO: support imported name wildcards, e.g. parse-*
      ("*", _) : _ -> do
        resolve ctx path (name, Import path' alias [(name, name)])
      (x, y) : names -> do
        -- let ctx' = filter ((`notElem` [path]) . fst) ctx
        let ctx' = ctx
        let defs = if y == name then resolve ctx' path' x else []
        defs ++ resolve ctx path (name, Import path' alias names)
      -- [] | alias == name -> [(path, Tag path' [])]
      [] -> []
    Def (p, b)
      | Just x <- varOf p, name == x -> [(path, b)]
      | name `elem` bindings p -> do
          [(path, Let (p, b) (Var name))]
      | otherwise -> []
      where
        bindings :: Pattern -> [String]
        bindings p = map fst (C.unpack (lower p, C.Any))
    TypeDef (tname, args, alts) | name == tname -> do
      let resolveAlt (a, Just b) = Fun a b
          resolveAlt (a, Nothing) = Fun a (Tag tname args)
      [(path, fun args (or' $ map resolveAlt alts))]
    _ -> []

class Compile a where
  compile :: Context -> FilePath -> a -> (C.Env, C.Expr)

instance Compile Expr where
  compile :: Context -> FilePath -> Expr -> (C.Env, C.Expr)
  compile ctx path expr = compile ctx path ("", expr)

instance Compile (String, Expr) where
  compile :: Context -> FilePath -> (String, Expr) -> (C.Env, C.Expr)
  -- compile ctx path (name@"map", expr) = do
  --   let a = C.dropMeta $ C.bind [] $ lower expr
  --   let dependencies = delete name (C.freeVars a `union` C.freeTags a)
  --   let env = compileDefs ctx path dependencies
  --   -- case C.infer buildOps ((name, C.Var name) : env) a of
  --   --   C.Ok ats -> do
  --   --     let alt ((a, t), s) = C.Ann a t
  --   --     (env, C.or' (map alt ats))
  --   --   C.Fail err -> error $ show (name, dependencies, map fst env, err)
  --   (error . intercalate "\n")
  --     [ "\n\ncompile " ++ name,
  --       "expr: " ++ show expr,
  --       "lower: " ++ show (C.dropMeta $ lower expr),
  --       "bind: " ++ show (C.dropMeta $ C.bind [] $ lower expr),
  --       "infer:",
  --       case C.infer buildOps ((name, C.Var name) : env) a of
  --         C.Ok ats -> intercalate "\n" (map (\x -> "- " ++ show (fst x)) ats)
  --         C.Fail err -> show err,
  --       ""
  --     ]
  compile ctx path (name, expr) = do
    let a = C.dropMeta $ C.bind [] $ lower expr
    let dependencies = delete name (C.freeVars a `union` C.freeTags a)
    let env = compileDefs ctx path dependencies
    case C.infer buildOps ((name, C.Var name) : env) a of
      C.Ok ats -> do
        -- let alt ((a, t), s) = C.for' (map fst s) (C.Ann a t)
        -- let alt ((a, _), s) = C.for' (map fst s) a
        -- let alt ((a, t), _) = C.Ann a t
        let alt ((a, _), _) = a
        (env, C.or' (distinct $ map alt ats))
      C.Fail errors ->
        (error . intercalate "\n")
          [ "\n\ncompile " ++ show name,
            "--- env:",
            intercalate "\n" (map (\(x, a) -> "- " ++ x ++ " =\n    " ++ C.format 80 "    " a) env),
            "--- expr:",
            show (dropMeta expr),
            "--- lower:",
            show (C.dropMeta $ lower expr),
            "--- bind:",
            show (C.dropMeta $ C.bind [] $ lower expr),
            "--- errors:",
            intercalate "\n" (map (\e -> "- " ++ show e) errors),
            ""
          ]

compileDefs :: Context -> FilePath -> [String] -> C.Env
compileDefs _ _ [] = []
compileDefs ctx path (x : xs) = do
  let defs = map (\(path, a) -> compile ctx path (x, a)) (resolve ctx path x)
  let env = compileDefs ctx path xs
  case defs of
    [] -> env
    defs -> do
      let def (env, a) = C.let' env a
      let a = C.or' (map def defs)
      (x, C.fix' [x] a) : env
