module Core where

import Data.Bifunctor (Bifunctor (bimap, first, second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.Either (fromRight, partitionEithers)
import Data.Function ((&))
import Data.List (delete, intercalate, intersect, nub, nubBy, sort, union, unionBy)
import Data.Maybe (fromMaybe, maybeToList)
import Debug.Trace (trace)
import Error
import qualified Grammar as G
import Location (Location (..), Position (..), Range (..))
import qualified Parser as P
import qualified PrettyPrint as PP
import Stdlib

-- Lambda calculus: https://mroman42.github.io/mikrokosmos/tutorial.html
-- Closure calculus: https://blog.chewxy.com/wp-content/uploads/personal/dissertation31482.pdf
-- Type inference from scratch: https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- Bidirectional type checking: https://www.youtube.com/live/utyBNDj7s2w -- https://www.cl.cam.ac.uk/~nk480/bidir.pdf
-- Verse calculus: https://simon.peytonjones.org/verse-calculus

type Parser a = P.Parser String a

data Expr
  = Any
  | Unit
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Var String
  | Tag String Expr
  | For String Expr
  | Fix String Expr
  | Ann Expr Type
  | And Expr Expr
  | Or Expr Expr
  | Fun Expr Expr
  | App Expr Expr
  | Call String Expr
  | Let [(String, Expr)] Expr
  | Meta (Metadata Expr) Expr
  | Err
  -- deriving (Eq, Show)
  deriving (Eq)

instance Show Expr where
  show :: Expr -> String
  show = Core.format 80 ""

showCtr :: Expr -> String
showCtr = \case
  Any -> "Any"
  Unit -> "Unit"
  IntT -> "IntT"
  NumT -> "NumT"
  Int _ -> "Int"
  Num _ -> "Num"
  Tag _ a -> "Tag"
  Var _ -> "Var"
  And a b -> "And"
  Or a b -> "Or"
  Ann a b -> "Ann"
  For _ a -> "For"
  Fix _ a -> "Fix"
  Fun a b -> "Fun"
  App a b -> "App"
  Call _ _ -> "Call"
  Let _ a -> "Let"
  Meta _ a -> "Meta"
  Err -> "Err"

showCtr' :: Int -> Expr -> String
showCtr' 0 = showCtr
showCtr' i = \case
  Any -> "Any"
  Unit -> "Unit"
  IntT -> "IntT"
  NumT -> "NumT"
  Int _ -> "Int"
  Num _ -> "Num"
  Tag _ a -> "Tag(" ++ self a ++ ")"
  Var _ -> "Var"
  And a b -> "And(" ++ self a ++ ", " ++ self b ++ ")"
  Or a b -> "Or(" ++ self a ++ ", " ++ self b ++ ")"
  Ann a b -> "Ann(" ++ self a ++ ", " ++ self b ++ ")"
  For _ a -> "For(" ++ self a ++ ")"
  Fix _ a -> "Fix(" ++ self a ++ ")"
  Fun a b -> "Fun(" ++ self a ++ ", " ++ self b ++ ")"
  App a b -> "App(" ++ self a ++ ", " ++ self b ++ ")"
  Call _ _ -> "Call"
  Let _ a -> "Let(" ++ self a ++ ")"
  Meta _ a -> "Meta(" ++ self a ++ ")"
  Err -> "Err"
  where
    self = showCtr' (i - 1)

type Type = Expr

type Ops = [(String, (Expr -> Expr) -> Expr -> Maybe Expr)]

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

data Metadata a
  = Loc Location
  | Comments [String]
  | TrailingComment String
  | Error (Error a)
  deriving (Eq, Show)

data MatchResult a
  = Matched a
  | MaybeMatched Expr Expr
  | NotMatched Expr Expr
  deriving (Eq, Show)

instance Functor Metadata where
  fmap :: (a -> b) -> Metadata a -> Metadata b
  fmap _ (Loc loc) = Loc loc
  fmap _ (Comments cs) = Comments cs
  fmap _ (TrailingComment c) = TrailingComment c
  fmap f (Error e) = Error (fmap f e)

instance Functor MatchResult where
  fmap :: (a -> b) -> MatchResult a -> MatchResult b
  fmap f (Matched env) = Matched (f env)
  fmap _ (MaybeMatched a b) = MaybeMatched a b
  fmap _ (NotMatched a b) = NotMatched a b

instance Applicative MatchResult where
  pure :: a -> MatchResult a
  pure = Matched

  (<*>) :: MatchResult (a -> b) -> MatchResult a -> MatchResult b
  (<*>) (Matched f) m = fmap f m
  (<*>) (MaybeMatched a b) _ = MaybeMatched a b
  (<*>) (NotMatched a b) _ = NotMatched a b

instance Monad MatchResult where
  (>>=) :: MatchResult a -> (a -> MatchResult b) -> MatchResult b
  (>>=) (Matched env) f = f env
  (>>=) (MaybeMatched a b) _ = MaybeMatched a b
  (>>=) (NotMatched a b) _ = NotMatched a b

parse :: Int -> FilePath -> String -> Either (P.State String) (Expr, P.State String)
parse prec = P.parse (G.parser grammar prec)

layout :: Int -> Expr -> PP.Layout
layout prec = G.layout grammar prec

format :: Int -> String -> Expr -> String
format width indent = G.format grammar width ("  ", indent)

showVar :: String -> String
showVar = \case
  "-" -> "(-)"
  x | all (\c -> isAlphaNum c || c `elem` "_-$") x -> x
  x -> "(" ++ x ++ ")"

showTag :: String -> String
showTag = \case
  "[]" -> "[]"
  k | all (\c -> isAlphaNum c || c `elem` "_-$") k -> k
  k -> "(" ++ k ++ ")"

parseTuple :: Parser [Expr]
parseTuple = do
  _ <- P.char '('
  _ <- P.whitespaces
  xs <- P.zeroOrMore $ do
    x <- parseExpr 0
    _ <- P.whitespaces
    _ <- P.char ','
    _ <- P.whitespaces
    return x
  x <- P.zeroOrOne $ do
    x <- parseExpr 0
    _ <- P.whitespaces
    return x
  _ <- P.char ')'
  _ <- P.spaces
  return (xs ++ x)

layoutTuple :: [PP.Layout] -> PP.Layout
layoutTuple [] = [PP.Text "()"]
layoutTuple xs = do
  let alt1 = [PP.Indent (PP.join [PP.Text ", "] xs)]
  let alt2 = [PP.Indent (PP.Text " " : PP.join [PP.Text ",", PP.NewLine] xs), PP.Text ",", PP.NewLine]
  [PP.Text "(", PP.Or alt1 alt2, PP.Text ")"]

layoutArgs :: [PP.Layout] -> PP.Layout
layoutArgs [] = [PP.Text "()"]
layoutArgs xs = do
  let alt1 = [PP.Indent (PP.join [PP.Text ", "] xs)]
  let alt2 = [PP.Indent (PP.NewLine : PP.join [PP.Text ",", PP.NewLine] xs), PP.Text ",", PP.NewLine]
  [PP.Text "(", PP.Or alt1 alt2, PP.Text ")"]

maybeLayoutArgs :: [PP.Layout] -> PP.Layout
maybeLayoutArgs [] = []
maybeLayoutArgs args = layoutArgs args

parserDecorator :: String -> ([String] -> Expr -> Expr) -> Parser Expr -> Parser Expr
parserDecorator op f rhs = do
  _ <- P.text op
  _ <- P.spaces
  xs <- P.oneOrMore $ do
    x <- parseNameVar
    _ <- P.spaces
    return x
  _ <- P.oneOf [P.char '.', P.char '\n']
  _ <- P.whitespaces
  a <- rhs
  _ <- P.spaces
  return (f xs a)

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

grammar :: G.Grammar String Expr
grammar = do
  G.Grammar
    { group = ("(", ")"),
      operators =
        [ -- Grammar.Any
          G.atom (\_ _ -> Any) (P.word "_") $ \_ -> \case
            Any -> Just [PP.Text "_"]
            _ -> Nothing,
          -- Grammar.Unit
          let parser = do _ <- P.char '('; _ <- P.whitespaces; P.char ')'
           in G.atom (\_ _ -> Unit) parser $ \_ -> \case
                Unit -> Just [PP.Text "()"]
                _ -> Nothing,
          -- Grammar.IntT
          G.atom (\_ _ -> IntT) (P.word "!Int") $ \_ -> \case
            IntT -> Just [PP.Text "!Int"]
            _ -> Nothing,
          -- Grammar.NumT
          G.atom (\_ _ -> NumT) (P.word "!Num") $ \_ -> \case
            NumT -> Just [PP.Text "!Num"]
            _ -> Nothing,
          -- Grammar.Int
          G.atom (const Int) P.integer $ \_ -> \case
            Int i -> Just [PP.Text $ show i]
            _ -> Nothing,
          -- Grammar.Num
          G.atom (const Num) P.number $ \_ -> \case
            Num n -> Just [PP.Text $ show n]
            _ -> Nothing,
          -- Grammar.Var
          G.atom (const Var) parseNameVar $ \_ -> \case
            Var x -> Just [PP.Text (showVar x)]
            _ -> Nothing,
          -- Grammar.Tag
          let parser expr = do
                k <- parseNameTag
                _ <- P.spaces
                args <- P.oneOf [parseTuple, return []]
                return (tag k args)
           in G.Atom parser $ \rhs -> \case
                Tag k a -> do
                  let args = map rhs (andOf a)
                  Just (PP.Text (showTag k) : maybeLayoutArgs args)
                _ -> Nothing,
          -- Grammar.And
          let parser expr = do
                items <- parseTuple
                return (and' items)
           in G.Atom parser $ \layout -> \case
                And a b -> do
                  let items = map layout (andOf (And a b))
                  Just (layoutTuple items)
                _ -> Nothing,
          -- Grammar.sugar.def
          let parser expr = do
                _ <- P.word "^let"
                _ <- P.spaces
                bindings <-
                  P.oneOf
                    [ do
                        _ <- P.char '<'
                        _ <- P.spaces
                        xs <- P.zeroOrMore $ do
                          x <- parseNameVar
                          _ <- P.spaces
                          return x
                        _ <- P.char '>'
                        _ <- P.spaces
                        return (const xs),
                      return freeVars
                    ]
                a <- expr
                _ <- P.char '='
                _ <- P.whitespaces
                b <- expr
                _ <- P.oneOf [P.char ';', P.char '\n']
                _ <- P.whitespaces
                def' (bindings a, a, b) <$> expr
           in G.Atom parser $ \layout -> \case
                -- App a b -> case forOf a of
                --   (xs, Fun a c) -> do
                --     Just (PP.Text ("^let<" ++ unwords xs ++ "> ") : layout a ++ PP.Text " = " : layout b ++ PP.Text "; " : layout c)
                --   _ -> Nothing
                _ -> Nothing,
          -- Grammar.Or
          G.InfixR 1 (G.parserLeading "|" (const Or)) $ \lhs rhs -> \case
            Or a b -> do
              let alt1 = lhs a ++ [PP.Text " | "] ++ rhs b
              let alt2 = [PP.Text "| ", PP.Indent (lhs a), PP.NewLine, PP.Text "| ", PP.Indent (rhs b)]
              return $
                if isFun a
                  then alt2
                  else [PP.Or alt1 alt2]
            _ -> Nothing,
          -- Grammar.Fix
          G.Atom (parserDecorator "&" fix) $ layoutDecorator "&" $ \case
            Fix x a -> Just (fixOf (Fix x a))
            _ -> Nothing,
          -- Grammar.Ann
          G.InfixR 3 (G.parserLeading ":" (const Ann)) $ \lhs rhs -> \case
            Ann a b -> do
              let alt1 = lhs a ++ [PP.Text " : "] ++ rhs b
              let alt2 = lhs a ++ [PP.NewLine, PP.Text ": ", PP.Indent (rhs b)]
              return $
                if isFun a || isApp a || isOr a
                  then alt2
                  else [PP.Or alt1 alt2]
            _ -> Nothing,
          -- Grammar.For
          G.Prefix 4 (parserDecorator "@" for) $ layoutDecorator "@" $ \case
            For x a -> Just (forOf (For x a))
            _ -> Nothing,
          -- Grammar.Fun
          G.InfixR 4 (G.parserLeading "->" (const Fun)) $ \lhs rhs -> \case
            Fun a b -> do
              let alt1 = PP.Text " " : rhs b
              let alt2 = [PP.Indent (PP.NewLine : rhs b)]
              if isFun b || isApp b || isOr b
                then Just (lhs a ++ (PP.Text " ->" : alt2))
                else Just (lhs a ++ [PP.Text " ->", PP.Or alt1 alt2])
            _ -> Nothing,
          -- Grammar.App
          let parser a _ = do
                args <- parseTuple
                return (app a args)
           in G.InfixL 5 parser $ \lhs rhs -> \case
                App a b -> do
                  let args = map (layout 0) (andOf b)
                  Just (lhs a ++ layoutArgs args)
                _ -> Nothing,
          -- Grammar.Call
          let parser expr = do
                _ <- P.char '%'
                x <- parseNameVar
                _ <- P.spaces
                args <- P.oneOf [parseTuple, return []]
                return (call x args)
           in G.Atom parser $ \rhs -> \case
                Call f a -> do
                  let args = map rhs (andOf a)
                  Just (PP.Text ("%" ++ f) : maybeLayoutArgs args)
                _ -> Nothing,
          -- Grammar.Let
          let parser expr = do
                env <-
                  P.oneOf
                    [ P.oneOrMore $ do
                        _ <- P.char '^'
                        _ <- P.whitespaces
                        x <- parseNameVar
                        _ <- P.whitespaces
                        _ <- P.char '='
                        _ <- P.whitespaces
                        a <- parseExpr 0
                        _ <- P.oneOf [P.char ';', P.char '\n']
                        _ <- P.whitespaces
                        return (x, a),
                      do
                        _ <- P.char '^'
                        _ <- P.whitespaces
                        _ <- P.char '{'
                        _ <- P.whitespaces
                        _ <- P.char '}'
                        _ <- P.whitespaces
                        return []
                    ]
                a <- expr
                return (Let env a)
           in G.Prefix 1 parser $ \rhs -> \case
                Let [] a -> do
                  Just (PP.Text "^{}" : PP.NewLine : rhs a)
                Let env a -> do
                  let layoutDef (x, a) = do
                        let def = PP.Text ("^" ++ show (Var x) ++ " =")
                        let alt1 = PP.Text " " : layout 0 a
                        let alt2 = PP.NewLine : layout 0 a
                        -- let alt2 = [PP.Text " ..."]
                        if isValue a || isVar a
                          then [def, PP.Indent [PP.Or alt1 alt2], PP.NewLine]
                          else [def, PP.Indent alt2, PP.NewLine]
                  Just (concatMap layoutDef env ++ rhs a)
                _ -> Nothing,
          -- Grammar.Metadata.Comments
          let parser expr = do
                comments <- P.oneOrMore $ do
                  _ <- P.char '#'
                  _ <- P.spaces
                  comment <- P.zeroOrMore (P.charIf (/= '\n'))
                  _ <- P.whitespaces
                  return comment
                Meta (Comments comments) <$> expr
           in G.Atom parser $ \rhs -> \case
                Meta (Comments comments) a -> do
                  let comments' = concatMap (\c -> [PP.Text ("# " ++ c), PP.NewLine]) comments
                  Just (comments' ++ rhs a)
                _ -> Nothing,
          -- Grammar.Metadata.TrailingComment
          let parser x _expr = do
                _ <- P.char '#'
                _ <- P.spaces
                comment <- P.zeroOrMore (P.charIf (/= '\n'))
                _ <- P.whitespaces
                return (Meta (TrailingComment comment) x)
           in G.InfixL 1 parser $ \lhs _ -> \case
                Meta (TrailingComment comment) a ->
                  Just (lhs a ++ [PP.Text ("  # " ++ comment), PP.NewLine])
                _ -> Nothing,
          -- Grammar.Metadata.Location
          let parser expr = do
                _ <- P.text "^["
                _ <- P.spaces
                filename <- P.oneOrMore $ P.charIf (/= ':')
                _ <- P.char ':'
                _ <- P.spaces
                row1 <- P.integer
                _ <- P.spaces
                _ <- P.char ':'
                _ <- P.spaces
                col1 <- P.integer
                _ <- P.spaces
                _ <- P.char ','
                _ <- P.spaces
                row2 <- P.integer
                _ <- P.spaces
                _ <- P.char ':'
                _ <- P.spaces
                col2 <- P.integer
                _ <- P.spaces
                _ <- P.char ']'
                _ <- P.spaces
                _ <- P.char '('
                _ <- P.whitespaces
                a <- expr
                _ <- P.whitespaces
                _ <- P.char ')'
                _ <- P.spaces
                return (Meta (Loc (Location filename (Range (Pos row1 col1) (Pos row2 col2)))) a)
           in G.Atom parser $ \layout -> \case
                Meta (Loc loc) a -> Just (PP.Text ("^[" ++ show loc ++ "](") : layout a ++ [PP.Text ")"])
                _ -> Nothing,
          -- Grammar.Err.CustomError
          let parser expr = do
                _ <- P.word "!error"
                _ <- P.spaces
                _ <- P.char '('
                _ <- P.whitespaces
                a <- expr
                _ <- P.whitespaces
                _ <- P.char ')'
                _ <- P.spaces
                return (err $ customError a)
           in G.Atom parser $ \layout -> \case
                Err -> Just [PP.Text "!error"]
                Meta (Error e) c -> case e of
                  TypeError e -> case e of
                    UndefinedVar x -> Just (PP.Text ("!undefined-var<" ++ x ++ ">(") : layout c ++ [PP.Text ")"])
                    TypeMismatch a b -> Just (PP.Text "!type-mismatch<" : layout a ++ PP.Text ", " : layout b ++ PP.Text ">(" : layout c ++ [PP.Text ")"])
                    NotAFunction a b -> Just (PP.Text "!not-a-function<" : layout a ++ PP.Text ", " : layout b ++ PP.Text ">(" : layout c ++ [PP.Text ")"])
                    e -> Just [PP.Text $ "!error(" ++ show e ++ ")"]
                  RuntimeError e -> case e of
                    UnhandledCase a b -> Just (PP.Text "!unhandled-case<" : layout a ++ PP.Text ", " : layout b ++ PP.Text ">(" : layout c ++ [PP.Text ")"])
                    CannotApply a b -> Just (PP.Text "!cannot-apply<" : layout a ++ PP.Text ", " : layout b ++ PP.Text ">(" : layout c ++ [PP.Text ")"])
                    CustomError a -> Just (PP.Text "!error(" : layout a ++ [PP.Text ")"])
                  e -> Just [PP.Text $ "!error(" ++ show e ++ ")"]
                _ -> Nothing
        ]
    }

parseExpr :: Int -> Parser Expr
parseExpr = G.parser grammar

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
  return (c : cs)

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

parseNameVar :: Parser String
parseNameVar =
  P.oneOf
    [ parseNameBase P.lowercase,
      parseNameEscaped
    ]

parseNameTag :: Parser String
parseNameTag =
  P.oneOf
    [ parseNameBase P.uppercase,
      P.paddedL (P.char ':') parseNameEscaped
    ]

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

isVar :: Expr -> Bool
isVar (Var _) = True
isVar (Ann a _) = isVar a
isVar (Meta _ a) = isVar a
isVar _ = False

varOf :: Expr -> Maybe String
varOf (Var x) = Just x
varOf (Meta _ a) = varOf a
varOf _ = Nothing

tag :: String -> [Expr] -> Expr
tag k = Tag k . and'

tag' :: String -> Expr
tag' k = Tag k Unit

isTag :: Expr -> Bool
isTag (Tag _ _) = True
isTag (Ann a _) = isTag a
isTag (Meta _ a) = isTag a
isTag _ = False

and' :: [Expr] -> Expr
and' [] = Unit
and' [a] = a
and' (a : bs) = And a (and' bs)

isAnd :: Expr -> Bool
isAnd (And _ _) = True
isAnd (Ann a _) = isAnd a
isAnd (Meta _ a) = isAnd a
isAnd _ = False

andOf :: Expr -> [Expr]
andOf Unit = []
andOf (And a b) = a : andOf b
andOf a = [a]

isOr :: Expr -> Bool
isOr (Or _ _) = True
isOr (Meta _ a) = isOr a
isOr _ = False

or' :: [Expr] -> Expr
or' [] = Unit
or' [a] = a
or' (a : bs) = Or a (or' bs)

orOf :: Expr -> [Expr]
orOf (Or a b) = a : orOf b
orOf a = [a]

asOr :: Expr -> Maybe (Expr, Expr)
asOr (Or a b) = Just (a, b)
asOr (Meta _ a) = asOr a
asOr _ = Nothing

ann :: Expr -> Type -> Expr
ann a _ | Just (a', t') <- asAnn a = ann a' t'
ann a t | Just (t', _) <- asAnn t = ann a t'
ann a t = Ann a t

isAnn :: Expr -> Bool
isAnn (Ann _ _) = True
isAnn (Meta _ a) = isAnn a
isAnn _ = False

asAnn :: Expr -> Maybe (Expr, Expr)
asAnn (Ann a b) = Just (a, b)
asAnn (Meta _ a) = asAnn a
asAnn _ = Nothing

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

for' :: [String] -> Expr -> Expr
for' [] a = a
for' (x : xs) a | x `occurs` a = For x (for' xs a)
for' (_ : xs) a = for' xs a

forOf :: Expr -> ([String], Expr)
forOf = \case
  For x a -> do
    let (ys, a') = forOf a
    (x : ys, a')
  Meta m a -> do
    let (xs, a') = forOf a
    (xs, Meta m a')
  a -> ([], a)

forOf' :: Expr -> Maybe (String, Expr)
forOf' = \case
  For x a -> Just (x, a)
  Meta _ a -> forOf' a
  a -> Nothing

asFor :: Expr -> Maybe ([String], Expr)
asFor = \case
  For x a -> case asFor a of
    Just (ys, a') -> Just (x : ys, a')
    Nothing -> Just ([x], a)
  Meta m a -> do
    (xs, a') <- asFor a
    Just (xs, Meta m a')
  _ -> Nothing

isFor :: Expr -> Bool
isFor (For _ _) = True
isFor (Meta _ a) = isFor a
isFor _ = False

fix :: [String] -> Expr -> Expr
fix xs a = foldr Fix a xs

fix' :: [String] -> Expr -> Expr
fix' [] a = a
fix' (x : xs) a | x `occurs` a = Fix x (fix' xs a)
fix' (_ : xs) a = fix' xs a

fixOf :: Expr -> ([String], Expr)
fixOf (Fix x a) = let (xs, b) = fixOf a in (x : xs, b)
fixOf a = ([], a)

fun :: [Expr] -> Expr -> Expr
fun ps = Fun (and' ps)

funOf :: Expr -> ([Expr], Expr)
funOf (Fun arg ret) = (andOf arg, ret)
funOf a = ([], a)

isFun :: Expr -> Bool
isFun (Fun _ _) = True
isFun (For _ a) = isFun a
isFun (Ann a _) = isFun a
isFun (Meta _ a) = isFun a
isFun _ = False

asFun :: Expr -> Maybe (Expr, Expr)
asFun (Fun a b) = Just (a, b)
asFun (Ann a _) = asFun a
asFun (Meta _ a) = asFun a
asFun _ = Nothing

lam :: [Expr] -> Expr -> Expr
lam ps b = for' (freeVars (and' ps)) (fun ps b)

app :: Expr -> [Expr] -> Expr
app fun args = App fun (and' args)

appT :: Expr -> [Expr] -> [Type] -> Expr
appT fun args types = App fun (Ann (and' args) (and' types))

isApp :: Expr -> Bool
isApp (App _ _) = True
isApp (Ann a _) = isApp a
isApp (Meta _ a) = isApp a
isApp _ = False

appOf :: Expr -> (Expr, [Expr])
appOf (App a b) = let (a', bs) = appOf a in (a', bs ++ [b])
appOf a = (a, [])

curry' :: Expr -> [Expr] -> Expr
curry' = foldl App

call :: String -> [Expr] -> Expr
call f args = Call f (and' args)

isCall :: Expr -> Bool
isCall (Call _ _) = True
isCall (Ann a _) = isCall a
isCall (Meta _ a) = isCall a
isCall _ = False

let' :: Env -> Expr -> Expr
let' [] a = a
let' env (Let env' a) = let' (env ++ env') a
let' env a = Let env a

letOf :: Expr -> Maybe (Env, Expr)
letOf (Let env a) = Just (env, a)
letOf (Ann a _) = letOf a
letOf (Meta _ a) = letOf a
letOf _ = Nothing

isLet :: Expr -> Bool
isLet (Let _ _) = True
isLet (Meta _ a) = isLet a
isLet (Ann a _) = isLet a
isLet _ = False

letP :: (Expr, Expr) -> Expr -> Expr
letP (a, b) c = App (Fun a c) b

letPs :: [(Expr, Expr)] -> Expr -> Expr
letPs [] c = c
letPs (def : defs) c = letP def (letPs defs c)

def :: (Expr, Expr) -> Expr -> Expr
def (a, b) = def' (freeVars a, a, b)

def' :: ([String], Expr, Expr) -> Expr -> Expr
def' (xs, a, b) c = App (for xs (Fun a c)) b

list :: Expr -> Expr -> [Expr] -> Expr
list _ nil [] = nil
list cons nil (a : bs) = app cons [a, list cons nil bs]

match' :: [Expr] -> [([Expr], Expr)] -> Expr
match' args cases = app (matchFun cases) args

matchFun :: [([Expr], Expr)] -> Expr
matchFun [] = Unit
matchFun [(ps, b)] = fun ps b
matchFun ((ps, b) : cases) = fun ps b `Or` matchFun cases

err :: Error Expr -> Expr
err e = Meta (Error e) Err

-- TODO: centralize into a single kind of errors
isErr :: Expr -> Bool
isErr Err = True
isErr (Ann a b) = isErr a || isErr b
isErr (Meta _ a) = isErr a
isErr _ = False

hasErr :: Expr -> Bool
hasErr = \case
  Tag _ a -> hasErr a
  And a b -> hasErr a || hasErr b
  Or a b -> hasErr a || hasErr b
  Ann a b -> hasErr a || hasErr b
  For _ a -> hasErr a
  Fix _ a -> hasErr a
  Fun a b -> hasErr a || hasErr b
  App a b -> hasErr a || hasErr b
  Call _ a -> hasErr a
  Let _ a -> hasErr a
  Meta (Error _) _ -> True
  Meta _ a -> hasErr a
  Err -> True
  _ -> False

typed :: Expr -> Type -> Expr
typed a _ | isAnn a = a
typed a t = Ann a t

typedOf :: Expr -> (Expr, Type)
typedOf (Ann a t) = case typedOf a of
  (a, Any) -> (a, t)
  (a, t) -> typedOf (Ann a t)
typedOf (Meta _ a) | isAnn a = typedOf a
typedOf a = (a, Any)

-- Helper functions
class Apply a where
  apply :: (Expr -> Expr) -> a -> a

instance Apply Expr where
  apply :: (Expr -> Expr) -> Expr -> Expr
  apply f = \case
    Any -> Any
    Unit -> Unit
    IntT -> IntT
    NumT -> NumT
    Int i -> Int i
    Num n -> Num n
    Var x -> Var x
    Tag k a -> Tag k (f a)
    Ann a b -> Ann (f a) (f b)
    And a b -> And (f a) (f b)
    Or a b -> Or (f a) (f b)
    For x a -> For x (f a)
    Fix x a -> Fix x (f a)
    Fun a b -> Fun (f a) (f b)
    App a b -> App (f a) (f b)
    Call x a -> Call x (f a)
    Let env a -> Let (second f <$> env) (f a)
    Meta m a -> Meta m (f a)
    Err -> Err

collect :: (Eq a, Show a) => (Expr -> [a]) -> Expr -> [a]
collect f = \case
  Any -> []
  Unit -> []
  IntT -> []
  NumT -> []
  Int _ -> []
  Num _ -> []
  Var _ -> []
  Tag _ a -> f a
  Ann a b -> f a `union` f b
  And a b -> f a `union` f b
  Or a b -> f a `union` f b
  For _ a -> f a
  Fix _ a -> f a
  Fun a b -> f a `union` f b
  App a b -> f a `union` f b
  Call _ a -> f a
  Let env a -> concatMap f (map snd env) `union` f a
  Meta _ a -> f a
  Err -> []
  where
    unionMap f = foldr (union . f) []

freeVars :: Expr -> [String]
freeVars = \case
  Var x -> [x]
  For x a -> delete x (freeVars a)
  Fix x a -> delete x (freeVars a)
  Let env a -> do
    let collectDef x = case lookup x env of
          Just b -> freeVars (let' (filter (\(x', _) -> x /= x') env) b)
          Nothing -> [x]
    foldr (union . collectDef) [] (freeVars a)
  a -> collect freeVars a

freeTags :: Expr -> [String]
freeTags = \case
  Tag k a -> [k] `union` freeTags a
  For x a -> delete x (freeTags a)
  Fix x a -> delete x (freeTags a)
  Let env a -> do
    let collectDef x = case lookup x env of
          Just b -> freeTags (let' (filter (\(x', _) -> x /= x') env) b)
          Nothing | x `elem` freeTags a -> [x]
          Nothing -> []
    foldr (union . collectDef) [] (freeVars a `union` freeTags a)
  a -> collect freeTags a

pushAll :: [(String, Expr)] -> Env -> Env
pushAll vars env = foldr (:) env vars

popAll :: [String] -> Env -> Env
popAll xs env = foldl (flip pop) env xs

pushVars :: [String] -> Env -> Env
pushVars xs = pushAll (map (\x -> (x, Var x)) xs)

unpack :: (Expr, Expr) -> Env
unpack (a, b) = case unpackDef (a, b) of
  (Just xs, a, b) -> do
    map (unpackVar xs (a, b)) xs
  (Nothing, a, b) -> do
    let xs = freeVars a
    map (unpackVar xs (a, b)) xs

unpackDef :: (Expr, Expr) -> (Maybe [String], Expr, Expr)
unpackDef (a, b) = case a of
  Ann a t -> case unpackDef (a, b) of
    (Just xs, a', b') -> (Just xs, a', b')
    (Nothing, a', b') -> (Nothing, a', Ann b' t)
  App a1 a2 -> unpackDef (a1, Fun a2 b)
  For x a -> case unpackDef (a, b) of
    (Just xs, a', b') -> (Just (x : xs), a', b')
    (Nothing, a', b') -> (Just [x], a', b')
  Fix x a -> case unpackDef (a, b) of
    (Just xs, a', b') -> (Just (x : xs), Fix x a', b')
    (Nothing, a', b') -> (Just [x], Fix x a', b')
  Meta _ a -> unpackDef (a, b)
  _ -> (Nothing, a, b)

unpackVar :: [String] -> (Expr, Expr) -> String -> (String, Expr)
unpackVar xs (a, b) x | Just x' <- varOf a, x == x', x `elem` xs = (x, b)
unpackVar xs (a, b) x = (x, letP (for' xs a, b) (Var x))

bind :: [String] -> Expr -> Expr
bind xs = \case
  Ann a b | Just (xs, b) <- asFor b -> do
    bind xs (for xs (Ann a b))
  Ann a b -> do
    let ys = filter (`notElem` xs) (freeVars b)
    for ys (Ann (bind xs a) (bind (xs ++ ys) b))
  For x a -> for' [x] (bind (x : xs ++ freeVars a) a)
  Fun a b | Just (xs, a) <- asFor a -> do
    bind xs (for xs (Fun a b))
  Fun a b -> do
    let ys = filter (`notElem` xs) (freeVars a)
    for ys (Fun (bind (xs ++ ys) a) (bind xs b))
  a -> apply (bind xs) a

occurs :: String -> Expr -> Bool
occurs x a = x `elem` freeVars a

newName :: [String] -> String -> String
newName existing x = head (newNamesStream existing x)

newNames :: [String] -> [String] -> [String]
newNames _ [] = []
newNames existing (x : xs) = do
  let y = newName existing x
  let ys = newNames (y : existing) xs
  y : ys

newNamesStream :: [String] -> String -> [String]
newNamesStream existing x =
  [ name
  | i <- [(0 :: Int) ..],
    let name = if i == 0 then x else x ++ show i,
    name `notElem` existing
  ]

isClosed :: Expr -> Bool
isClosed = null . freeVars

isOpen :: Expr -> Bool
isOpen = not . isClosed

isValue :: Expr -> Bool
isValue = \case
  Any -> True
  Unit -> True
  IntT -> True
  NumT -> True
  Int _ -> True
  Num _ -> True
  Tag _ _ -> True
  Ann a _ -> isValue a
  And _ _ -> True
  Let _ a -> isValue a
  Meta _ a -> isValue a
  _ -> False

-- Evaluation
reduce :: Ops -> Expr -> Expr
reduce ops (App a (Or b1 b2)) = case reduce ops (App a b1) of
  c | isErr c -> reduce ops (App a b2)
  c | isValue c -> c
  c -> Or c (App a b2)
reduce ops (App a b) = case reduce ops a of
  Any -> Any
  a@Var {} -> App a b
  a@App {} -> App a b
  a@Call {} -> App a b
  For x a -> do
    let y = newName (freeVars b) x
    case reduce ops $ App (substitute [(x, Var y)] a) b of
      App a b -> App (for' [y] a) b
      c -> c
  Fix x a -> reduce ops $ App (Let [(x, Fix x a)] a) b
  Ann a _ -> reduce ops $ App a b
  Or a1 a2 -> case reduce ops (App a1 b) of
    c | isErr c -> reduce ops (App a2 b)
    c | isValue c -> c
    c -> Or c (App a2 b)
  Fun a c -> case (a, b) of
    (Let env a, b) -> reduce ops $ letP (reduce ops $ Let env a, b) c
    (Meta _ a, b) -> reduce ops $ letP (reduce ops a, b) c
    (_, Any) -> reduce ops c
    (Any, _) -> reduce ops c
    (For x a, b) -> reduce ops $ App (For x (Fun a c)) b
    (Or a1 a2, b) -> reduce ops $ App (Or (Fun a1 c) (Fun a2 c)) b
    (Var x, b) -> reduce ops $ Let [(x, b)] c
    (a, Var x) -> reduce ops $ Let [(x, a)] c
    (Unit, Unit) -> reduce ops c
    (IntT, IntT) -> reduce ops c
    (NumT, NumT) -> reduce ops c
    (Int i, Int i') | i == i' -> reduce ops c
    (Num n, Num n') | n == n' -> reduce ops c
    (Tag k a, Tag k' b) | k == k' -> reduce ops $ letP (a, b) c
    (Fix x a, Fix y b) -> do
      let x' = newName (freeVars (Fix y b)) x
      let a' = substitute [(x, Var x')] a
      reduce ops $ letP (a', b) c
    (Ann a ta, Ann b tb) -> reduce ops $ letPs [(ta, tb), (a, b)] c
    (And a1 a2, And b1 b2) -> reduce ops $ letPs [(a1, b1), (a2, b2)] c
    (Fun a1 a2, Fun b1 b2) -> reduce ops $ letPs [(a1, b1), (a2, b2)] c
    (App a1 a2, App b1 b2) -> reduce ops $ letPs [(a1, b1), (a2, b2)] c
    (Call f a, Call f' b) | f == f' -> reduce ops $ letP (a, b) c
    (Err, Err) -> reduce ops c
    (a, App {}) -> case reduce ops b of
      b@App {} -> letP (a, b) c
      b@Call {} -> letP (a, b) c
      b -> reduce ops (letP (a, b) c)
    (a, Call {}) -> case reduce ops b of
      b@App {} -> letP (a, b) c
      b@Call {} -> letP (a, b) c
      b -> reduce ops (letP (a, b) c)
    (a, Let env b) -> reduce ops $ letP (a, reduce ops $ Let env b) c
    (a, Meta _ b) -> reduce ops $ letP (a, reduce ops b) c
    (Ann a _, b) -> reduce ops $ letP (a, b) c
    (a, Ann b _) -> reduce ops $ letP (a, b) c
    (a, b) -> err $ unhandledCase a b
  a -> err $ cannotApply a b
-- reduce ops (Or a b) = Or (reduce ops a) b
reduce ops (Call f a) = case lookup f ops of
  Just f | Just result <- f (eval ops) a -> result
  _ -> Call f a
reduce ops (Let env a) = case a of
  Var x -> case lookup x env of
    Just (Var x') | x == x' -> Var x
    Just (Ann (Var x') t) | x == x' -> Ann (Var x) t
    Just a -> reduce ops a
    Nothing -> Var x
  Tag k a -> Tag k (Let env a)
  For x a -> For x (Let env a)
  Fix x a -> Fix x (Let env a)
  Ann a b -> reduce ops $ Ann (Let env a) (Let env b)
  And a b -> And (Let env a) (Let env b)
  Or a b -> reduce ops $ Or (Let env a) (Let env b)
  Fun a b -> Fun (Let env a) (Let env b)
  App a b -> reduce ops $ App (Let env a) (Let env b)
  Call f a -> reduce ops $ Call f (Let env a)
  Let env' a -> reduce ops $ Let (env' ++ env) a
  Meta m a -> reduce ops $ Let env a
  a -> a
reduce ops (Meta _ a) = reduce ops a
reduce ops a = a

eval :: Ops -> Expr -> Expr
eval ops a = case reduce ops a of
  Tag k a -> Tag k (eval ops a)
  For x a -> for' [x] (eval ops a)
  Fix x a -> fix' [x] (eval ops a)
  Ann a b -> case eval ops a of
    Ann a b -> reduce ops (Ann a b)
    a -> Ann a (eval ops b)
  And a b -> And (eval ops a) (eval ops b)
  Or a b -> case eval ops a of
    a | isErr a -> eval ops b
    a | isValue a -> a
    a -> case eval ops b of
      b | isErr b -> a
      b -> Or a b
  Fun a b -> Fun (eval ops a) (eval ops b)
  App a b -> App (eval ops a) (eval ops b)
  Call f a -> Call f (eval ops a)
  Meta (Error e) a -> Meta (Error $ fmap (eval ops) e) (eval ops a)
  a -> a

class Substitute a where
  substitute :: Substitution -> a -> a

instance Substitute Expr where
  substitute :: Substitution -> Expr -> Expr
  substitute _ Any = Any
  substitute _ Unit = Unit
  substitute _ IntT = IntT
  substitute _ NumT = NumT
  substitute _ (Int i) = Int i
  substitute _ (Num n) = Num n
  substitute s (Var x) = case lookup x s of
    Just a | not (x `occurs` a) -> a
    _ -> Var x
  substitute s (Tag k a) = Tag k (substitute s a)
  substitute s (Ann a b) = Ann (substitute s a) (dropTypes $ substitute s b)
  substitute s (And a b) = And (substitute s a) (substitute s b)
  substitute s (Or a b) = Or (substitute s a) (substitute s b)
  substitute s (For x a) = For x (substitute (filter ((/= x) . fst) s) a)
  substitute s (Fix x a) = Fix x (substitute (filter ((/= x) . fst) s) a)
  substitute s (Fun a b) = Fun (substitute s a) (substitute s b)
  substitute s (App a b) = App (substitute s a) (substitute s b)
  substitute s (Call op a) = Call op (substitute s a)
  substitute s (Let env b) = do
    let sub (x, a) = (x, substitute s a)
    let s' = filter ((`notElem` map fst env) . fst) s
    Let (map sub env) (substitute s' b)
  substitute s (Meta m a) = Meta m (substitute s a)
  substitute _ Err = Err

instance Substitute (Expr, Expr) where
  substitute :: Substitution -> (Expr, Expr) -> (Expr, Expr)
  substitute s (a, b) = (substitute s a, substitute s b)

instance Substitute (Error Expr) where
  substitute :: Substitution -> Error Expr -> Error Expr
  substitute s = fmap (substitute s)

instance (Substitute a) => Substitute [a] where
  substitute s = map (substitute s)

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = do
  let key (x, _) (y, _) = x == y
  let -- sub s (x, For x' a) | x == x' = (x, For x (substitute s a))
      sub s (x, a) = case lookup x s of
        Just b -> (x, b)
        Nothing -> (x, substitute s a)
  -- let generic kv = fst kv `elem` map fst (generics s2)
  -- unionBy key (filter (not . generic) s1) (map (sub s1) s2)
  unionBy key s1 (map (sub s1) s2)

-- generics :: Env -> Env
-- generics = filterMap (forOf' . snd)

dropTypes :: Expr -> Expr
dropTypes (Tag k a) = Tag k (dropTypes a)
-- dropTypes (Ann a@Call {} t) = Ann (dropTypes a) (dropTypes t)
dropTypes (Ann a _) = dropTypes a
dropTypes (And a b) = And (dropTypes a) (dropTypes b)
dropTypes (Or a b) = Or (dropTypes a) (dropTypes b)
dropTypes (For x a) = For x (dropTypes a)
dropTypes (Fix x a) = Fix x (dropTypes a)
-- dropTypes (Fun (Ann a ta) b) = case andOf ta of
--   [Ann ta _] -> Fun (Ann (dropTypes a) (dropTypes ta)) (dropTypes b)
--   _ -> Fun (Ann (dropTypes a) (dropTypes ta)) (dropTypes b)
dropTypes (Fun a b) = Fun (dropTypes a) (dropTypes b)
-- dropTypes (App a (Ann b tb)) = case andOf tb of
--   [Ann tb _] -> App (dropTypes a) (Ann (dropTypes b) (dropTypes tb))
--   _ -> App (dropTypes a) (Ann (dropTypes b) (dropTypes tb))
dropTypes (App a b) = App (dropTypes a) (dropTypes b)
dropTypes (Call op a) = Call op (dropTypes a)
dropTypes (Let defs b) = Let (map (second dropTypes) defs) (dropTypes b)
dropTypes (Meta m a) = Meta m (dropTypes a)
dropTypes a = a

dropMeta :: Expr -> Expr
dropMeta (Tag k a) = Tag k (dropMeta a)
dropMeta (Ann a b) = Ann (dropMeta a) (dropMeta b)
dropMeta (And a b) = And (dropMeta a) (dropMeta b)
dropMeta (Or a b) = Or (dropMeta a) (dropMeta b)
dropMeta (For x a) = For x (dropMeta a)
dropMeta (Fix x a) = Fix x (dropMeta a)
dropMeta (Fun a b) = Fun (dropMeta a) (dropMeta b)
dropMeta (App a b) = App (dropMeta a) (dropMeta b)
dropMeta (Call op a) = Call op (dropMeta a)
dropMeta (Let defs b) = Let (map (second dropMeta) defs) (dropMeta b)
dropMeta (Meta (Error e) a) = Meta (Error e) (dropMeta a)
dropMeta (Meta _ a) = dropMeta a
dropMeta Err = Err
dropMeta a = a

dropLet :: Expr -> Expr
dropLet (Tag k a) = Tag k (dropLet a)
dropLet (Ann a b) = Ann (dropLet a) (dropLet b)
dropLet (And a b) = And (dropLet a) (dropLet b)
dropLet (Or a b) = Or (dropLet a) (dropLet b)
dropLet (For x a) = For x (dropLet a)
dropLet (Fix x a) = Fix x (dropLet a)
dropLet (Fun a b) = Fun (dropLet a) (dropLet b)
dropLet (App a b) = App (dropLet a) (dropLet b)
dropLet (Call op a) = Call op (dropLet a)
dropLet (Let _ b) = dropLet b
dropLet (Meta m a) = Meta (fmap dropLet m) (dropLet a)
dropLet a = a

findLocation :: Expr -> Maybe Location
findLocation = \case
  Meta (Loc loc) _ -> Just loc
  Meta _ a -> findLocation a
  _ -> Nothing

instantiate :: [String] -> Expr -> (Expr, Substitution)
instantiate vars (For x a) | x `occurs` a = do
  let y = newName vars x
  let (b, s) = instantiate (y : vars) (substitute [(x, Var y)] a)
  (b, (y, Var y) : s)
instantiate vars (For _ a) = instantiate vars a
instantiate vars (Meta _ a) = instantiate vars a
instantiate _ a = (a, [])

collapse :: [String] -> Expr -> Expr
collapse vars = \case
  Any -> Var (newName ("_" : vars) "_")
  Ann a b -> collapse2 vars Ann a b
  And a b -> collapse2 vars And a b
  Or a b -> collapse2 vars Or a b
  Fun a b -> collapse2 vars Fun a b
  App a b -> collapse2 vars App a b
  Call f a -> Call f (collapse vars a)
  Let env a -> Let env (collapse vars a)
  a -> apply (collapse vars) a

collapse2 :: [String] -> (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
collapse2 vars f a b = do
  let a' = collapse vars a
  f a' (collapse (freeVars a' `union` vars) b)

trace1 :: (Show a) => [Char] -> [(String, Expr)] -> Expr -> a -> Bool
trace1 name env a x = do
  let xs = filterMap (\(x, a) -> if a == Var x then Just (show $ Var x) else Nothing) env
  let env' = filterMap (\(x, a) -> if a /= Var x then Just (x, a) else Nothing) env
  let lines =
        [ ">> " ++ name ++ "[" ++ showCtr a ++ "]",
          "   @" ++ unwords xs ++ " @{" ++ intercalate ", " (map show env') ++ "}",
          "     a: "
            ++ show (dropLet a),
          "   " ++ show x
        ]
  -- False
  trace (intercalate "\n" lines) False

trace2 :: (Show a) => [Char] -> [(String, Expr)] -> Expr -> Expr -> a -> Bool
trace2 name env a b x = do
  let xs = filterMap (\(x, a) -> if a == Var x then Just (show $ Var x) else Nothing) env
  let env' = filterMap (\(x, a) -> if a /= Var x then Just (x, a) else Nothing) env
  let lines =
        [ ">> " ++ name ++ "[" ++ showCtr a ++ ":" ++ showCtr b ++ "]",
          "   @" ++ unwords xs ++ " @{" ++ intercalate ", " (map show env') ++ "}",
          "     a: "
            ++ show (dropLet a),
          "     b: " ++ show (dropLet b),
          "   " ++ show x
        ]
  -- False
  trace (intercalate "\n" lines) False

class (Show a, Show b) => Inspect a b where
  inspect :: String -> Env -> a -> b -> b

instance (Show a) => Inspect Expr a where
  inspect :: String -> Env -> Expr -> a -> a
  inspect name env a x
    | trace1 name env a x = undefined
    | otherwise = x

instance (Show a) => Inspect Expr [a] where
  inspect :: String -> Env -> Expr -> [a] -> [a]
  inspect name env a xs
    | trace1 name env a $
        (intercalate "\n")
          ( ("--- " ++ show (length xs))
              : map (\x -> "   - " ++ show x) xs
          ) =
        undefined
    | otherwise = xs

instance (Show a) => Inspect (Expr, Expr) a where
  inspect :: String -> Env -> (Expr, Expr) -> a -> a
  inspect name env (a, b) x
    | trace2 name env a b x = undefined
    | otherwise = x

instance (Show a) => Inspect (Expr, Expr) [a] where
  inspect :: String -> Env -> (Expr, Expr) -> [a] -> [a]
  inspect name env (a, b) xs
    | trace2 name env a b $
        (intercalate "\n")
          ( ("--- " ++ show (length xs))
              : map (\x -> "   - " ++ show x) xs
          ) =
        undefined
    | otherwise = xs

class Merge a where
  merge :: Ops -> Env -> a -> a -> a

instance Merge Expr where
  merge :: Ops -> Env -> Expr -> Expr -> Expr
  merge ops env a a' | a == a' = a
  -- merge ops env a b = case unify ops env a b of
  --   Right (c, []) -> c
  --   _ -> Or a b
  merge ops env a b = error $ show "TODO: merge"

instance Merge Substitution where
  merge :: Ops -> Env -> Substitution -> Substitution -> Substitution
  merge ops env [] s2 = s2
  merge ops env ((x, a) : s1) s2 = case pop' x s2 of
    Just (b, s2) -> (x, Var x) : merge ops env s1 s2
    Nothing -> (x, a) : merge ops env s1 s2

splitFun :: Ops -> Env -> Expr -> Maybe (Expr, Expr)
splitFun ops env = \case
  Or a b -> do
    (a1, a2) <- splitFun ops env a
    (b1, b2) <- splitFun ops env b
    Just (merge ops env a1 b1, merge ops env a2 b2)
  Fun a b -> Just (a, b)
  Meta _ a -> splitFun ops env a
  t -> Nothing

data Typed a
  = Ok [a]
  | Fail [Error Expr]
  deriving (Eq, Show)

instance Functor Typed where
  fmap :: (a -> b) -> Typed a -> Typed b
  fmap f mx = do
    x <- mx
    return (f x)

instance Applicative Typed where
  pure :: a -> Typed a
  pure x = Ok [x]

  (<*>) :: Typed (a -> b) -> Typed a -> Typed b
  (<*>) mf mx = do
    f <- mf
    fmap f mx

instance Monad Typed where
  (>>=) :: Typed a -> (a -> Typed b) -> Typed b
  (>>=) (Ok xs) f = do
    let partition (xs, e1) (Ok ys) = (xs ++ ys, e1)
        partition (xs, e1) (Fail e2) = (xs, e1 ++ e2)
    case foldl' partition ([], []) (map f xs) of
      ([], e) -> Fail e
      (ys, _) -> Ok ys
  (>>=) (Fail e) _ = Fail e

unify :: Ops -> Env -> (Expr, Expr) -> Typed (Expr, Substitution)
unify ops env (Meta _ a, b) = unify ops env (a, b)
unify ops env (a, Meta _ b) = unify ops env (a, b)
unify ops env (Or a1 a2, b) = case (unify ops env (a1, b), unify ops env (a2, b)) of
  (Ok xs, Ok ys) -> Ok (xs `union` ys)
  (Ok xs, Fail _) -> Ok xs
  (Fail _, Ok ys) -> Ok ys
  (Fail e1, Fail e2) -> Fail (e1 ++ e2)
unify ops env (a, Or b1 b2) = case (unify ops env (a, b1), unify ops env (a, b2)) of
  (Ok xs, Ok ys) -> Ok (xs `union` ys)
  (Ok xs, Fail _) -> Ok xs
  (Fail _, Ok ys) -> Ok ys
  (Fail e1, Fail e2) -> Fail (e1 ++ e2)
unify _ _ (a, Any) = return (a, [])
unify _ _ (Any, b) = return (b, [])
unify _ _ (Unit, Unit) = return (Unit, [])
unify _ _ (IntT, IntT) = return (IntT, [])
unify _ _ (NumT, NumT) = return (NumT, [])
unify _ _ (Int i, Int i') | i == i' = return (Int i, [])
unify _ _ (Num n, Num n') | n == n' = return (Num n, [])
unify ops env (Var x, b) = case b of
  Var x' | x == x' -> return (Var x, [])
  Ann (Var x') t | x == x' -> return (Var x, [])
  b | x `occurs` b -> Fail [occursError x b]
  b -> return (b, [(x, b)])
unify ops env (a, Var x) = unify ops env (Var x, a)
unify ops env (Tag k a1, Tag k' a2) | k == k' = do
  (a, s) <- unify ops env (a1, a2)
  return (Tag k a, s)
unify ops env (a, Tag k b) | Just def <- lookup k env = do
  let x = newName ((k ++ "$") : map fst env) (k ++ "$")
  let env' = (x, Var x) : env
  ((a, ta), (b, tb), s1) <- infer2 ops env' a b
  (ctr, s2) <- unify ops (s1 `compose` env') (substitute s1 def, Fun (Ann b tb) (Fun (Ann a ta) (Var x)))
  let s = s2 `compose` s1 `compose` [(x, Var x)]
  -- let c = eval ops (Let (env) (curry' ctr [substitute s2 b, substitute s2 a]))
  let c = fromMaybe (Var x) $ lookup x (s `compose` env)
  return (dropTypes $ eval ops (Let env c), s)
unify ops env (Tag k a, b) | Just def <- lookup k env = do
  let x = newName ((k ++ "$") : map fst env) (k ++ "$")
  let env' = (x, Var x) : env
  ((a, ta), (b, tb), s1) <- infer2 ops env' a b
  (ctr, s2) <- unify ops (s1 `compose` env') (substitute s1 def, Fun (Ann a ta) (Fun (Ann b tb) (Var x)))
  let s = s2 `compose` s1 `compose` [(x, Var x)]
  -- let c = eval ops (Let (env) (curry' ctr [substitute s2 a, substitute s2 b]))
  let c = fromMaybe (Var x) $ lookup x (s `compose` env)
  return (dropTypes $ eval ops (Let env c), s)
unify ops env (For x a, b) = do
  let y = newName (freeVars b `union` map fst env) x
  (c, s) <- unify ops ((y, Var y) : env) (substitute [(x, Var y)] a, b)
  -- return (for' [x] $ substitute [(y, Var x)] c, s)
  return (for' [y] c, s)
unify ops env (a, For x b) = do
  let y = newName (freeVars a `union` map fst env) x
  (c, s) <- unify ops ((y, Var y) : env) (a, substitute [(x, Var y)] b)
  -- return (for' [x] $ substitute [(y, Var x)] c, s)
  return (for' [y] c, s)
unify ops env (Fix x a, Fix x' b) | x == x' = do
  (c, s) <- unify ops ((x, Var x) : env) (a, b)
  return (fix' [x] c, s)
unify ops env (Fix x a, Fix y b) = error "TODO: unify Fix with different names"
unify ops env (Ann a1 t1, Ann a2 t2) = do
  (a, t, s) <- unify2 ops env (a1, a2) (t1, t2)
  return (Ann a t, s)
unify ops env (Ann a _, b) = unify ops env (a, b)
unify ops env (a, Ann b _) = unify ops env (a, b)
unify ops env (And a1 b1, And a2 b2) = do
  (a, b, s) <- unify2 ops env (a1, a2) (b1, b2)
  return (And a b, s)
unify ops env (Fun a1 b1, Fun a2 b2) = do
  (a, b, s) <- unify2 ops env (a1, a2) (b1, b2)
  return (Fun a b, s)
unify ops env (App a1 b1, App a2 b2) = do
  (a, b, s) <- unify2 ops env (a1, a2) (b1, b2)
  return (App a b, s)
unify ops env (Call op a1, Call op' a2) | op == op' = do
  (a, s) <- unify ops env (a1, a2)
  return (Call op a, s)
-- unify ops env (Let env' a) b = error "TODO: unify Let -- reduce first? also on App and Call?"
-- unify ops env a (Let env' b) = error "TODO: unify Let -- reduce first? also on App and Call?"
unify _ _ (Err, Err) = return (Err, [])
unify _ _ (a, b) = Fail [typeMismatch a b]

unify2 :: Ops -> Env -> (Expr, Expr) -> (Expr, Expr) -> Typed (Expr, Expr, Substitution)
unify2 ops env aa bb = do
  (a, s1) <- unify ops env aa
  (b, s2) <- unify ops (s1 `compose` env) (substitute s1 bb)
  return (substitute s2 a, b, s2 `compose` s1)

infer :: Ops -> Env -> Expr -> Typed ((Expr, Type), Substitution)
infer _ env Any = do
  let y = newName ("_" : map fst env) "_"
  return ((Any, Var y), [(y, Var y)])
infer _ _ Unit = return ((Unit, Unit), [])
infer _ _ IntT = return ((IntT, IntT), [])
infer _ _ NumT = return ((NumT, NumT), [])
infer _ _ (Int i) = return ((Int i, IntT), [])
infer _ _ (Num n) = return ((Num n, NumT), [])
infer ops env (Var x) = case lookup x env of
  Just Any -> do
    let y = newName (map fst env) (x ++ "T")
    return ((Var x, Var y), [(y, Var y), (x, Ann (Var x) (Var y))])
  Just (Var x') | x == x' -> do
    let y = newName (map fst env) (x ++ "T")
    return ((Var x, Var y), [(y, Var y), (x, Ann (Var x) (Var y))])
  Just (Ann (Var x') ty) | x == x' -> do
    return ((Var x, ty), [])
  Just a -> do
    -- TODO: does this work when inferring generic functions?
    -- [ ((Var x, ta), [(x, Ann (Var x) ta)] `compose` s)
    ((_, ta), s) <- infer ops env a
    return ((Var x, ta), s)
  Nothing -> Fail [undefinedVar x]
infer ops env (Tag k a) = do
  ((a, ta), s) <- infer ops env a
  return ((Tag k a, Tag k ta), s)
infer ops env (For x a) = do
  let y = newName (map fst env) x
  let yT = newName (y : map fst env) (y ++ "T")
  let vars = [(yT, Var yT), (y, Ann (Var y) (Var yT))]
  ((a, ta), s) <- infer ops (vars `compose` env) (substitute [(x, Var y)] a)
  -- return ((for' [y, yT] a, ta), s `compose` vars)
  return ((for' [x, yT] $ substitute [(y, Var x)] a, ta), s `compose` vars)
infer ops env (Fix x a) | x `occurs` a = do
  ((a, ta), s) <- infer ops ((x, Var x) : env) a
  return ((Fix x a, ta), s `compose` [(x, Var x)])
infer ops env (Fix _ a) = infer ops env a
infer ops env (Ann a t) = check ops env (a, t)
infer ops env (And a b) = do
  ((a, ta), (b, tb), s) <- infer2 ops env a b
  return ((And a b, And ta tb), s)
infer ops env (Or a b) = case (infer ops env a, infer ops env b) of
  (Ok xs, Ok ys) -> Ok (xs `union` ys)
  (Ok xs, Fail _) -> Ok xs
  (Fail _, Ok ys) -> Ok ys
  (Fail e1, Fail e2) -> Fail (e1 ++ e2)
infer ops env (Fun a b) = do
  ((a, ta), (b, tb), s) <- infer2 ops env a b
  return ((Fun (ann a ta) (ann b tb), Fun ta tb), s)
infer ops env (App a b) = do
  ((b, tb), s1) <- infer ops env b
  ((a, ta), s2) <- check ops (s1 `compose` env) (substitute s1 a, Fun tb Any)
  let (t1', t2') = case asFun ta of
        Just ta -> ta
        -- Nothing -> (substitute s2 tb, Any)
        Nothing -> error ("Not a function:\n" ++ show (Ann a ta))
  -- ((b, tb), s3) <- check ops (s12 `compose` env) (substitute s12 b, t1')
  return ((App a (ann b t1'), t2'), s2 `compose` s1)
-- infer ops env (App a b) = do
--   ((_, tb), s1) <- infer ops env b
--   ((a, ta), s2) <- check ops (s1 `compose` env) (substitute s1 a, Fun tb Any)
--   let s12 = s2 `compose` s1
--   let (t1', t2') = case asFun ta of
--         Just ta -> ta
--         -- Nothing -> (substitute s2 tb, Any)
--         Nothing -> error ("Not a function:\n" ++ show (Ann a ta))
--   ((b, tb), s3) <- check ops (s12 `compose` env) (substitute s12 b, t1')
--   return ((App (substitute s3 a) (ann b t1'), substitute s3 t2'), s3 `compose` s12)
infer ops env (Call op a) = do
  let x = newName ("$" : map fst env) "$"
  ((a, ta), s) <- infer ops ((x, Var x) : env) a
  return ((Call op (Ann a ta), substitute s (Var x)), s `compose` [(x, Var x)])
infer ops env (Let defs a) = do
  ((a, t), s) <- infer ops (defs ++ env) a
  return ((Let defs a, t), s)
infer ops env (Meta _ a) = infer ops env a
infer _ _ Err = return ((Err, Err), [])

infer2 :: Ops -> Env -> Expr -> Expr -> Typed ((Expr, Type), (Expr, Type), Substitution)
infer2 ops env a b = do
  (at, s1) <- infer ops env a
  (bt, s2) <- infer ops (s1 `compose` env) (substitute s1 b)
  return (substitute s2 at, bt, s2 `compose` s1)

check :: Ops -> Env -> (Expr, Type) -> Typed ((Expr, Type), Substitution)
check ops env (Any, t) = Ok [((Any, t), [])]
check ops env (a, Any) = infer ops env a
check ops env (Meta _ a, t) = check ops env (a, t)
check ops env (a, Meta _ t) = check ops env (a, t)
check ops env (a, Or t1 t2) = case (check ops env (a, t1), check ops env (a, t2)) of
  (Ok xs, Ok ys) -> Ok (xs `union` ys)
  (Ok xs, Fail _) -> Ok xs
  (Fail _, Ok ys) -> Ok ys
  (Fail e1, Fail e2) -> Fail (e1 ++ e2)
check ops env (Or a1 a2, t) = case (check ops env (a1, t), check ops env (a2, t)) of
  (Ok xs, Ok ys) -> Ok (xs `union` ys)
  (Ok xs, Fail _) -> Ok xs
  (Fail _, Ok ys) -> Ok ys
  (Fail e1, Fail e2) -> Fail (e1 ++ e2)
check ops env (For x a, t)
  | x `occurs` t = do
      let y = newName (freeVars (Ann a t)) x
      check ops env (For y (substitute [(x, Var y)] a), t)
  | otherwise = do
      let y = newName (map fst env) x
      ((a, t), s) <- check ops ((y, Var y) : env) (substitute [(x, Var y)] a, t)
      -- let xs = fromMaybe [y] (fmap freeVars (lookup y s))
      -- let xs = [y] `intersect` freeVars (Ann a t) `intersect` map fst s
      -- return ((for' xs a, t), s `compose` [(y, Var y)])
      let a' = substitute [(x, Var y)] a
      let xs = [x] `intersect` freeVars (Ann a' t) `intersect` map fst s
      return ((for' xs a', t), s)
check ops env (a, For x t)
  | x `occurs` a = do
      let y = newName (freeVars (Ann a t)) x
      check ops env (a, for' [y] (substitute [(x, Var y)] t))
  | otherwise = check ops env (For x a, t)
check ops env (Fix x a, t) | x `occurs` a = do
  ((a, t), s) <- check ops ((x, Var x) : env) (a, t)
  return ((fix' [x] a, t), s `compose` [(x, Var x)])
check ops env (Fix _ a, t) = check ops env (a, t)
check ops env (Var x, t) = case lookup x env of
  -- Just Any -> return ((Var x, t), [(x, Ann (Var x) t)])
  Just (Var x') | x == x' -> return ((Var x, t), [(x, Ann (Var x) t)])
  Just (Ann (Var x') ty) | x == x' -> do
    (t, s) <- unify ops env (ty, t)
    return ((Var x, t), [(x, Ann (Var x) t)] `compose` s)
  Just a -> do
    ((_, ta), s) <- check ops env (a, t)
    return ((Var x, ta), s)
  Nothing -> Fail [undefinedVar x]
check ops env (And a b, And ta tb) = do
  ((a, ta), (b, tb), s) <- check2 ops env (a, ta) (b, tb)
  return ((And a b, And ta tb), s)
check ops env (Fun a b, Fun ta tb) = do
  ((a, ta), (b, tb), s) <- check2 ops env (a, ta) (b, tb)
  return ((Fun (ann a ta) (ann b tb), Fun ta tb), s)
-- check ops env (App a b, t) = do
--   ((a, ta), s1) <- check ops env (a, Fun Any t)
--   let (t1, t2) = case asFun ta of
--         Just ta -> ta
--         Nothing -> error ("Not a function:\n" ++ show (Ann a ta))
--   ((b, tb), s2) <- check ops env (substitute s1 b, t1)
--   return ((App (substitute s2 a) (ann b tb), substitute s2 t2), s2 `compose` s1)
check ops env (App a b, t) = do
  ((b, tb), s1) <- infer ops env b
  ((a, ta), s2) <- check ops (s1 `compose` env) (substitute s1 a, Fun tb (substitute s1 t))
  let (t1, t2) = case asFun ta of
        Just ta -> ta
        -- Nothing -> (substitute s2 t1, substitute s12 t2)
        Nothing -> error ("Not a function:\n" ++ show (Ann a ta))
  return ((App a (ann (substitute s2 b) t1), t2), s2 `compose` s1)
check ops env (Let defs a, t) = do
  ((a, t), s) <- check ops (defs ++ env) (a, t)
  return ((Let defs a, t), s)
check ops env (a, t) = do
  ((a, ta), s1) <- infer ops env a
  (t, s2) <- unify ops (s1 `compose` env) (ta, substitute s1 t)
  return ((substitute s2 a, t), s2 `compose` s1)

check2 :: Ops -> Env -> (Expr, Type) -> (Expr, Type) -> Typed ((Expr, Type), (Expr, Type), Substitution)
check2 ops env at bt = do
  (at, s1) <- check ops env at
  (bt, s2) <- check ops (s1 `compose` env) (substitute s1 bt)
  return (substitute s2 at, bt, s2 `compose` s1)
