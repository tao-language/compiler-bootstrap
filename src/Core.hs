module Core where

import Data.Bifunctor (Bifunctor (bimap, first, second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.Either (fromRight)
import Data.Function ((&))
import Data.List (delete, intercalate, nub, nubBy, sort, union, unionBy)
import Data.Maybe (fromMaybe, maybeToList)
import Debug.Trace (trace)
import Error
import Grammar as G
import Location (Location (..), Position (..), Range (..))
import qualified Parser as P
import qualified PrettyPrint as PP
import Stdlib

-- https://simon.peytonjones.org/verse-calculus
-- https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/gadt-pldi.pdf
-- https://youtu.be/ytPAlhnAKro -- https://github.com/kritzcreek/fby19
-- https://www.youtube.com/live/utyBNDj7s2w
-- https://www.cl.cam.ac.uk/~nk480/bidir.pdf
-- https://mroman42.github.io/mikrokosmos/tutorial.html

type Parser a = P.Parser String a

data Expr
  = Any
  | Unit
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Tag String Expr
  | Var String
  | And Expr Expr
  | Or Expr Expr
  | Ann Expr Type
  | For String Expr
  | Fix String Expr
  | Fun Expr Expr
  | App Expr Expr
  | Call String [Expr]
  | Let [(String, Expr)] Expr
  | Meta (Metadata Expr) Expr
  | Err
  -- deriving (Eq, Show)
  deriving (Eq)

instance Show Expr where
  show :: Expr -> String
  show = Core.format 80

showCtr :: Expr -> String
showCtr = \case
  Any -> "Any"
  Unit -> "Unit"
  IntT -> "IntT"
  NumT -> "NumT"
  Int _ -> "Int"
  Num _ -> "Num"
  Tag _ _ -> "Tag"
  Var _ -> "Var"
  And _ _ -> "And"
  Or _ _ -> "Or"
  Ann _ _ -> "Ann"
  For _ _ -> "For"
  Fix _ _ -> "Fix"
  Fun _ _ -> "Fun"
  App _ _ -> "App"
  Call _ _ -> "Call"
  Let _ _ -> "Let"
  Meta _ _ -> "Meta"
  Err -> "Err"

type Type = Expr

type Ops = [(String, (Expr -> Expr) -> [Expr] -> Maybe Expr)]

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
parse prec = P.parse (parser grammar prec)

format :: Int -> Expr -> String
format width = G.format grammar width "  "

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
          G.atom (\_ _ -> IntT) (P.word "^Int") $ \_ -> \case
            IntT -> Just [PP.Text "^Int"]
            _ -> Nothing,
          -- Grammar.NumT
          G.atom (\_ _ -> NumT) (P.word "^Num") $ \_ -> \case
            NumT -> Just [PP.Text "^Num"]
            _ -> Nothing,
          -- Grammar.Int
          G.atom (const Int) P.integer $ \_ -> \case
            Int i -> Just [PP.Text $ show i]
            _ -> Nothing,
          -- Grammar.Num
          G.atom (const Num) P.number $ \_ -> \case
            Num n -> Just [PP.Text $ show n]
            _ -> Nothing,
          -- Grammar.Tag
          let parser expr = do
                k <- parseNameTag
                _ <- P.spaces
                args <-
                  P.oneOf
                    [ do
                        _ <- P.char '('
                        _ <- P.spaces
                        arg <- expr
                        args <- P.zeroOrMore $ do
                          _ <- P.char ','
                          _ <- P.spaces
                          expr
                        _ <- P.char ')'
                        _ <- P.spaces
                        return (arg : args),
                      return []
                    ]
                return (tag k args)
           in G.Atom parser $ \layout -> \case
                Tag k a -> do
                  let showTag = \case
                        k | all (\c -> isAlphaNum c || c `elem` "_-$") k -> k
                        k -> "(" ++ k ++ ")"
                  let showArgs a = case andOf a of
                        [] -> []
                        args -> PP.Text "(" : intercalate [PP.Text ", "] (map layout args) ++ [PP.Text ")"]
                  Just (PP.Text (showTag k) : showArgs a)
                _ -> Nothing,
          -- Grammar.Var
          G.atom (const Var) parseNameVar $ \_ -> \case
            Var x -> do
              let showVar = \case
                    x | all (\c -> isAlphaNum c || c `elem` "_-$") x -> x
                    x -> "(" ++ x ++ ")"
              Just [PP.Text (showVar x)]
            _ -> Nothing,
          -- Grammar.And
          let parser expr = do
                _ <- P.char '('
                _ <- P.whitespaces
                arg <- expr
                _ <- P.whitespaces
                args <- P.oneOrMore $ do
                  _ <- P.char ','
                  _ <- P.whitespaces
                  expr
                _ <- P.char ')'
                _ <- P.spaces
                return (and' (arg : args))
           in G.Atom parser $ \layout -> \case
                And a b -> do
                  let items = map layout (andOf (And a b))
                  Just (PP.Text "(" : intercalate [PP.Text ", "] items ++ [PP.Text ")"])
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
                App a b -> case forOf a of
                  (xs, Fun a c) -> do
                    Just (PP.Text ("^let<" ++ unwords xs ++ "> ") : layout a ++ PP.Text " = " : layout b ++ PP.Text "; " : layout c)
                  _ -> Nothing
                _ -> Nothing,
          -- Grammar.Or
          G.infixR 1 (const Or) "|" $ \case
            Or a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.Fix
          let parser expr = do
                _ <- P.char '&'
                _ <- P.spaces
                xs <- P.oneOrMore $ do
                  x <- parseNameVar
                  _ <- P.spaces
                  return x
                _ <- P.char '.'
                _ <- P.whitespaces
                a <- expr
                _ <- P.spaces
                return (fix xs a)
           in G.Atom parser $ \layout -> \case
                Fix x a -> do
                  let (xs, a') = fixOf (Fix x a)
                  Just (PP.Text ("&" ++ unwords xs ++ ". ") : layout a')
                _ -> Nothing,
          -- Grammar.Ann
          G.infixR 3 (const Ann) ":" $ \case
            Ann a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.For
          let parser expr = do
                _ <- P.char '@'
                _ <- P.spaces
                xs <- P.oneOrMore $ do
                  x <- parseNameVar
                  _ <- P.spaces
                  return x
                _ <- P.oneOf [P.char '.', P.char '\n']
                _ <- P.whitespaces
                a <- expr
                _ <- P.spaces
                return (for xs a)
           in G.Prefix 4 parser $ \layout -> \case
                For x a -> do
                  let (xs, a') = forOf (For x a)
                  Just (PP.Text ("@" ++ unwords xs ++ ". ") : layout a')
                _ -> Nothing,
          -- Grammar.Fun
          G.infixR 4 (const Fun) "->" $ \case
            Fun a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Grammar.App
          let parser x expr = do
                y <- expr
                _ <- P.spaces
                return (App x y)
           in G.InfixL 5 parser $ \lhs rhs -> \case
                App a b -> Just (lhs a ++ PP.Text " " : rhs b)
                _ -> Nothing,
          -- Grammar.Call
          let parser expr = do
                _ <- P.char '%'
                x <- parseNameVar
                _ <- P.spaces
                _ <- P.char '('
                _ <- P.whitespaces
                args <-
                  P.oneOf
                    [ do
                        arg <- expr
                        _ <- P.whitespaces
                        args <- P.zeroOrMore $ do
                          _ <- P.char ','
                          _ <- P.whitespaces
                          arg <- expr
                          _ <- P.whitespaces
                          return arg
                        return (arg : args),
                      return []
                    ]
                _ <- P.char ')'
                _ <- P.spaces
                return (Call x args)
           in G.Atom parser $ \layout -> \case
                Call f args -> do
                  Just (PP.Text ("%" ++ f ++ "(") : intercalate [PP.Text ", "] (map layout args) ++ [PP.Text ")"])
                _ -> Nothing,
          -- Grammar.Let
          let parser expr = do
                _ <- P.text "@{"
                _ <- P.whitespaces
                env <- do
                  let parseDef = do
                        x <- parseNameVar
                        _ <- P.whitespaces
                        _ <- P.char '='
                        _ <- P.whitespaces
                        a <- expr
                        _ <- P.whitespaces
                        return (x, a)
                  P.oneOf
                    [ do
                        def <- parseDef
                        defs <- P.zeroOrMore $ do
                          _ <- P.char ','
                          _ <- P.whitespaces
                          parseDef
                        return (def : defs),
                      return []
                    ]
                _ <- P.char '}'
                _ <- P.whitespaces
                a <- expr
                _ <- P.spaces
                return (Let env a)
           in G.Prefix 1 parser $ \layout -> \case
                Let env a -> do
                  let layoutDef (x, a)
                        | a == Var x = [PP.Text (show $ Var x)]
                        -- \| otherwise = PP.Text (show x ++ " = ") : layout a
                        | otherwise = [PP.Text (show $ Var x)]
                  Just (PP.Text "@{" : intercalate [PP.Text " "] (map layoutDef env) ++ PP.Text "} " : layout a)
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
                Err -> Just [PP.Text "!Err"]
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

ann :: (Expr, Type) -> Expr
ann (a, t) = Ann a t

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

asFor :: Expr -> Maybe ([String], Expr)
asFor = \case
  For x a -> case asFor a of
    Just (ys, a') -> Just (x : ys, a')
    Nothing -> Just ([x], a)
  Meta m a -> do
    (xs, a') <- asFor a
    Just (xs, Meta m a')
  _ -> Nothing

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

isCall :: Expr -> Bool
isCall (Call _ _) = True
isCall (Ann a _) = isCall a
isCall (Meta _ a) = isCall a
isCall _ = False

err :: Error Expr -> Expr
err e = Meta (Error e) Err

-- TODO: centralize into a single kind of errors
isErr :: Expr -> Bool
isErr Err = True
isErr (Ann a _) = isErr a
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
  Call _ args -> any hasErr args
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
    Call x args -> Call x (map f args)
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
  Call _ args -> unionMap f args
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
  For x a -> For x (bind (x : xs ++ freeVars a) a)
  Fun a b -> case filter (`notElem` xs) (freeVars a) of
    [] -> Fun (bind xs a) (bind xs b)
    ys -> for ys (Fun (bind (xs ++ ys) a) (bind (xs ++ ys) b))
  -- Ann a b -> do
  --   let ys = filter (`notElem` xs) (freeVars b)
  --   for ys (Ann (bind (xs ++ ys) a) (bind (xs ++ ys) b))
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

-- Evaluation
-- step :: Ops -> Expr -> Maybe Expr
-- step ops = \case
--   Var _ -> Nothing
--   Tag k a -> step1 ops (Tag k) a
--   Ann a _ -> Just a
--   And a b -> step2 ops And a b
--   Or a b -> case a of
--     Any -> Just a
--     Unit -> Just a
--     IntT -> Just a
--     NumT -> Just a
--     Int _ -> Just a
--     Num _ -> Just a
--     Tag _ _ -> Just a
--     -- Var String
--     -- And Expr Expr
--     -- Or Expr Expr
--     Ann a _ -> Just (Or a b)
--     For _ _ -> do
--       a <- step ops a
--       Just (Or a b)
--     -- Fix String Expr
--     Fun _ _ -> Nothing
--     App _ _ -> do
--       a <- step ops a
--       Just (Or a b)
--     -- Call String [Expr]
--     Let env a -> do
--       a <- step ops (Let env a)
--       Just (Or a b)
--     -- Meta (Metadata Expr) Expr
--     Err -> Just b
--     a -> error $ "TODO: step Or: " ++ show a
--   For x a -> step ops (Let [(x, Var x)] a)
--   Fix x a -> Nothing
--   Fun a b -> step2 ops Fun a b
--   App a b -> case a of
--     Any -> Just Any
--     Var x -> error $ "TODO: stepApp Var"
--     Ann a _ -> Just (App a b)
--     Or a1 a2 -> Just (Or (App a1 b) (App a2 b))
--     For x a -> step ops (App (Let [(x, Var x)] a) b)
--     Fix x a -> Just (App (Let [(x, Fix x a)] a) b)
--     Fun a c -> case (a, b) of
--       (Any, _) -> Just c
--       (Let env a, b) -> do
--         a <- step ops (Let env a)
--         Just (letP (a, b) c)
--       (a, Let env b) -> do
--         b <- step ops (Let env b)
--         Just (letP (a, b) c)
--       (Unit, Unit) -> Just c
--       (IntT, IntT) -> Just c
--       (NumT, NumT) -> Just c
--       (Int i, Int i') | i == i' -> Just c
--       (Num n, Num n') | n == n' -> Just c
--       (Tag k1 a, Tag k2 b) | k1 == k2 -> Just (letP (a, b) c)
--       (Var x, b) -> Just (Let [(x, b)] c)
--       (Ann a1 a2, Ann b1 b2) -> Just (letP (a2, b2) (letP (a1, b1) c))
--       (And a1 a2, And b1 b2) -> Just (letP (a1, b1) (letP (a2, b2) c))
--       -- TODO: remove this last case and replace with:
--       -- _ -> Just Err
--       (a, b) -> case a of
--         Unit -> Just Err
--         IntT -> Just Err
--         NumT -> Just Err
--         Int _ -> Just Err
--         Num _ -> Just Err
--         Tag _ _ -> Just Err
--         a -> error $ "TODO: beta " ++ show (a, b)
--     App _ _ -> error "TODO: stepApp App"
--     Call _ _ -> error "TODO: stepApp Call"
--     Let env a -> do
--       a <- step ops (Let env a)
--       Just (App a b)
--     Meta _ a -> Just (App a b)
--     Err -> Just Err
--     a -> Just (err $ cannotApply a b)
--   -- App a b -> reduceApp ops (reduce ops (Let env a)) (reduce ops (Let env b))
--   Call f args -> do
--     call <- lookup f ops
--     call (eval ops) args
--   -- Call f args -> case (lookup f ops, Let env <$> args) of
--   --   (Just call, args) | Just result <- call (eval ops) args -> result
--   --   (_, args) -> Call f args
--   Let env a -> case a of
--     Tag k a -> step1 ops (Tag k) (Let env a)
--     Var x -> case lookup x env of
--       Just (Var x') | x == x' -> Just (Var x)
--       Just a -> Just a
--       Nothing -> Just (Var x)
--     And a b -> step2 ops And (Let env a) (Let env b)
--     Or a b -> step2 ops Or (Let env a) (Let env b)
--     Ann a b -> step2 ops Ann (Let env a) (Let env b)
--     For x a -> step1 ops (For x) (Let ((x, Var x) : env) a)
--     Fix x a -> step1 ops (Fix x) (Let ((x, Var x) : env) a)
--     Fun a b -> step2 ops Fun (Let env a) (Let env b)
--     App a b -> step2 ops App (Let env a) (Let env b)
--     Call f args -> do
--       let step' a = fromMaybe a (step ops $ Let env a)
--       Just (Call f (map step' args))
--     Let env' a -> step ops (Let (env ++ env') a)
--     Meta _ a -> step ops (Let env a)
--     a -> Just a
--   Meta _ a -> step ops a
--   _ -> Nothing

-- step1 :: Ops -> (Expr -> Expr) -> Expr -> Maybe Expr
-- step1 ops f a = do
--   a <- step ops a
--   Just (f a)

-- step2 :: Ops -> (Expr -> Expr -> Expr) -> Expr -> Expr -> Maybe Expr
-- step2 ops f a b = case (step ops a, step ops b) of
--   (Just a, Just b) -> Just (f a b)
--   (Just a, Nothing) -> Just (f a b)
--   (Nothing, Just b) -> Just (f a b)
--   (Nothing, Nothing) -> Nothing

-- stepApp :: Ops -> Expr -> Expr -> Maybe Expr
-- stepApp ops a b = case a of
--   Any -> Just Any
--   Var x -> error $ "TODO: stepApp Var"
--   Ann a _ -> Just (App a b)
--   Or a1 a2 -> Just (Or (App a1 b) (App a2 b))
--   For x a -> Just (App (Let [(x, Var x)] a) b)
--   Fix x a -> Just (App (Let [(x, Fix x a)] a) b)
--   Fun a c -> case match False ops a b of
--     Matched env -> Just (let' env c)
--     MaybeMatched a b -> Nothing
--     NotMatched a b -> Just Err
--   App _ _ -> error "TODO: stepApp App"
--   Call _ _ -> error "TODO: stepApp Call"
--   Let env a -> do
--     a <- step ops (Let env a)
--     Just (App a b)
--   Meta _ a -> Just (App a b)
--   Err -> Just Err
--   a -> Just (err $ cannotApply a b)

-- reduceApp :: Ops -> Expr -> Expr -> Expr
-- reduceApp ops a b = case (a, reduce ops b) of
--   (Any, _) -> Any
--   (a, b) | isVar a || isApp a -> App a b
--   (Ann a _, b) -> reduceApp ops (reduce ops a) b
--   (Or a1 a2, b) -> Or (reduceApp ops (reduce ops a1) b) (App a2 b)
--   (For x a, b) -> reduceApp ops (reduce ops (Let [(x, Var x)] a)) b
--   -- (Fix x a, b) | isOpen b -> error $ show $ dropMeta $ App (Fix x a) b
--   (Fix x a, b) -> reduceApp ops (reduce ops (Let [(x, Fix x a)] a)) b
--   (Fun a c, b) -> case match False ops a b of
--     Matched env -> reduce ops (Let env c)
--     MaybeMatched a b -> App (Fun a c) b
--     NotMatched a b -> err (unhandledCase a b)
--   (Call f args, b) -> App (Call f args) b
--   (Meta _ a, b) -> reduceApp ops a b
--   _ -> err (cannotApply a b)

-- steps :: Ops -> Expr -> [Expr]
-- steps ops expr =
--   expr : case step ops expr of
--     Just next -> steps ops next
--     Nothing -> []

-- steps ops env expr =
--   case expr of
--     -- Var x -> case lookup x env of
--     --   Just (Var x') | x == x' -> Var x
--     --   Just (Ann (Var x') t) | x == x' -> Ann (Var x) t
--     --   Just a -> reduce ops a
--     --   Nothing -> Var x
--     Var x -> error "TODO: steps Var"
--     Tag k a -> [Tag k a | a <- steps ops env a]
--     Ann a b -> [Ann a b | a <- steps ops env a, b <- steps ops env b]
--     And a b -> [And a b | a <- steps ops env a, b <- steps ops env b]
--     Or a b -> [Or a b | a <- steps ops env a, b <- steps ops env b]
--     For x a -> [For x a | a <- steps ops ((x, Var x) : env) a]
--     Fix x a -> [Fix x a | a <- steps ops ((x, Fix x a) : env) a]
--     Fun a b -> [Fun a b | a <- steps ops env a, b <- steps ops env b]
--     App a b -> error "TODO: steps App"
--     -- App a b -> reduceApp ops (reduce ops (Let env a)) (reduce ops (Let env b))
--     -- Call f args -> case (lookup f ops, Let env <$> args) of
--     --   (Just call, args) | Just result <- call (eval ops) args -> result
--     --   (_, args) -> Call f args
--     Call f args -> error "TODO: steps Call"
--     Let env' a -> [a | a <- steps ops (env ++ env') a]
--     Meta m a -> [Meta m a | a <- steps ops env a]
--     a -> [a]

reduce :: Ops -> Expr -> Expr
reduce ops = \case
  App a b -> reduceApp ops (reduce ops a) (reduce ops b)
  Let env a -> reduceLet ops env a
  Meta m a -> Meta m (reduce ops a)
  expr -> expr

reduceLet :: Ops -> Env -> Expr -> Expr
reduceLet ops env = \case
  Var x -> case lookup x env of
    Just (Var x') | x == x' -> Var x
    Just (Ann (Var x') t) | x == x' -> Ann (Var x) t
    Just a -> reduce ops a
    Nothing -> Var x
  Tag k a -> Tag k (Let env a)
  Ann a b -> Ann (Let env a) (Let env b)
  And a b -> And (Let env a) (Let env b)
  Or a b -> Or (Let env a) (Let env b)
  For x a -> For x (Let env a)
  Fix x a -> Fix x (Let env a)
  Fun a b -> Fun (Let env a) (Let env b)
  App a b -> reduceApp ops (reduce ops (Let env a)) (reduce ops (Let env b))
  Call f args -> case (lookup f ops, Let env <$> args) of
    (Just call, args) | Just result <- call (eval ops) args -> result
    (_, args) -> Call f args
  Let env' a -> reduce ops (Let (env ++ env') a)
  Meta m a -> Meta m (reduce ops (Let env a))
  Err -> Err
  expr -> expr

reduceApp :: Ops -> Expr -> Expr -> Expr
reduceApp ops a b = case (a, reduce ops b) of
  (Any, _) -> Any
  (a, b) | isVar a || isApp a -> App a b
  (Ann a _, b) -> reduceApp ops (reduce ops a) b
  (Or a1 a2, b) -> Or (reduceApp ops (reduce ops a1) b) (App a2 b)
  (For x a, b) -> reduceApp ops (reduce ops (Let [(x, Var x)] a)) b
  -- (Fix x a, b) | isOpen b -> error $ show $ dropMeta $ App (Fix x a) b
  (Fix x a, b) -> reduceApp ops (reduce ops (Let [(x, Fix x a)] a)) b
  (Fun a c, b) -> case match False ops a b of
    Matched env -> reduce ops (Let env c)
    MaybeMatched a b -> App (Fun a c) b
    NotMatched a b -> err (unhandledCase a b)
  (Call f args, b) -> App (Call f args) b
  (Meta _ a, b) -> reduceApp ops a b
  _ -> err (cannotApply a b)

match :: Bool -> Ops -> Expr -> Expr -> MatchResult Env
-- match unify ops (Let env (Tag k a)) b = case lookup k env of
--   Just def -> do
--     let b' = curry' (Let env def) [a, b]
--     match True ops (Tag k (Let env a)) (b' `Or` b)
--   Nothing -> match unify ops (Tag k (Let env a)) b
-- match unify ops (Let env (Meta _ a)) b =
--   match unify ops (Let env a) b
-- match unify ops (Let env (Let env' a)) b =
--   match unify ops (Let (env ++ env') a) b
match unify ops a b = case (reduce ops a, reduce ops b) of
  (Meta _ a, b) -> match unify ops a b
  (Any, _) -> Matched []
  (_, Any) | unify -> Matched []
  (Unit, Unit) -> Matched []
  (IntT, IntT) -> Matched []
  (NumT, NumT) -> Matched []
  (Int i, Int i') | i == i' -> Matched []
  (Num n, Num n') | n == n' -> Matched []
  (Tag k a, Tag k' b) | k == k' -> match unify ops a b
  (Var x, b) -> Matched [(x, b)]
  (a, Var x) | unify -> Matched [(x, a)]
  (Ann a ta, Ann b tb) -> do
    env1 <- match True ops ta tb
    env2 <- match unify ops (Let env1 a) b
    return (env1 ++ env2)
  (And a1 a2, And b1 b2) -> do
    env1 <- match unify ops a1 b1
    env2 <- match unify ops (Let env1 a2) b2
    return (env1 ++ env2)
  (Or a1 a2, b) -> case match unify ops a1 b of
    Matched env1 -> case match unify ops (Let env1 a2) b of
      Matched env2 -> Matched (env1 ++ env2)
      MaybeMatched a2 b -> MaybeMatched (Or a1 a2) b
      NotMatched _ _ -> Matched env1
    MaybeMatched a1 b -> MaybeMatched (Or a1 a2) b
    NotMatched a1 b -> case match unify ops a2 b of
      Matched env -> Matched env
      MaybeMatched a2 b -> MaybeMatched a2 b
      NotMatched a2 b -> NotMatched (Or a1 a2) b
  (a, Or b1 b2) -> case match unify ops a b1 of
    Matched env1 -> case match unify ops (Let env1 a) b2 of
      Matched env2 -> Matched (env1 ++ env2)
      MaybeMatched a b2 -> MaybeMatched a (Or b1 b2)
      NotMatched _ _ -> Matched env1
    MaybeMatched a b1 -> MaybeMatched a (Or b1 b2)
    NotMatched a b1 -> case match unify ops a b2 of
      Matched env -> Matched env
      MaybeMatched a b2 -> MaybeMatched a b2
      NotMatched a b2 -> NotMatched a (Or b1 b2)
  (For x a, b) -> match unify ops (Let [(x, Var x)] a) b
  (a, For x b) -> match unify ops a (Let [(x, Var x)] b)
  (Fix x a, Fix x' b) | x == x' -> case match unify ops (Let [(x, Var x)] a) (Let [(x', Fix x' b)] b) of
    Matched env -> Matched env
    MaybeMatched a b -> MaybeMatched (Fix x a) (Fix x b)
    NotMatched a b -> NotMatched (Fix x a) (Fix x b)
  (Fix x a, Fix y b) -> do
    match unify ops (Fix x a) (Fix x (substitute [(y, Var x)] b))
  (Fun a1 a2, Fun b1 b2) -> match unify ops (And a1 a2) (And b1 b2)
  (App a1 a2, App b1 b2) -> match unify ops (And a1 a2) (And b1 b2)
  (Call x args, Call x' args') | x == x' -> do
    match unify ops (and' args) (and' args')
  (a, Ann b _) -> match unify ops a b
  (Ann a _, b) -> match unify ops a b
  (Err, Err) -> Matched []
  (_, Meta _ b) -> match unify ops a b
  (a, b) | isVar b || isApp b || isCall b -> MaybeMatched a b
  (a, b) -> NotMatched a b

eval :: Ops -> Expr -> Expr
eval ops expr = case reduce ops expr of
  Tag k a -> Tag k (eval ops a)
  Ann a b -> case (eval ops a, eval ops b) of
    (a, b) | Just (a, _) <- asAnn a -> eval ops (Ann a b)
    (a, _) | isErr a -> a
    (a, b) -> Ann a b
  And a b -> And (eval ops a) (eval ops b)
  Or a b -> case eval ops a of
    a | isErr a -> eval ops b
    a | isVar a || isApp a || isFun a || isOr a || isCall a -> case eval ops b of
      b | isErr b -> a
      b -> Or a b
    a -> a
  For x a -> for' [x] (eval ops (Let [(x, Var x)] a))
  Fix x a -> fix' [x] (eval ops (Let [(x, Var x)] a))
  Fun a b -> Fun (eval ops a) (eval ops b)
  App a b -> App (eval ops a) (eval ops b)
  Call f args -> Call f (eval ops <$> args)
  Meta (Error e) _ -> Meta (Error $ eval ops <$> e) Err
  Meta m a -> Meta m (eval ops a)
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
  -- substitute [] (Var x) = Var x
  -- substitute ((x, a) : s) b | x `occurs` a = substitute s b
  -- substitute ((x, a) : _) (Var x') | x == x' = a
  -- substitute (_ : s) (Var x) = substitute s (Var x)
  substitute s (Tag k a) = Tag k (substitute s a)
  substitute s (Ann a b) = Ann (substitute s a) (dropTypes $ substitute s b)
  substitute s (And a b) = And (substitute s a) (substitute s b)
  substitute s (Or a b) = Or (substitute s a) (substitute s b)
  substitute s (For x a) = For x (substitute (filter ((/= x) . fst) s) a)
  substitute s (Fix x a) = Fix x (substitute (filter ((/= x) . fst) s) a)
  substitute s (Fun a b) = Fun (substitute s a) (substitute s b)
  substitute s (App a b) = App (substitute s a) (substitute s b)
  substitute s (Call op args) = Call op (map (substitute s) args)
  substitute s (Let env b) = do
    let sub (x, a) = (x, substitute s a)
    let s' = filter (\(x, _) -> x `notElem` map fst env) s
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
  let sub s (x, a) = case lookup x s of
        Just b -> (x, b)
        Nothing -> (x, substitute s a)
  unionBy (\a b -> fst a == fst b) s1 (map (sub s1) s2)

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
dropTypes (Call op args) = Call op (map dropTypes args)
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
dropMeta (Call op args) = Call op (map dropMeta args)
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
dropLet (Call op args) = Call op (map dropLet args)
dropLet (Let _ b) = dropLet b
dropLet (Meta m a) = Meta m (dropLet a)
dropLet a = a

findLocation :: Expr -> Maybe Location
findLocation = \case
  Meta (Loc loc) _ -> Just loc
  Meta _ a -> findLocation a
  _ -> Nothing

unify :: Ops -> Env -> Expr -> Expr -> Either (Error Expr) [(Expr, Substitution)]
unify ops env a b = case (a, b) of
  (Ann a ta, Ann b tb) -> do
    unify2 ops env Ann (a, b) (ta, tb)
  (Ann a _, b) -> unify ops env a b
  (a, Ann b _) -> unify ops env a b
  (a, Meta m b) | not (isErr (Meta m b)) -> do
    Right
      [ (Meta m a, s)
      | (a, s) <- fromRight [] $ unify ops env a b
      ]
  (Meta m a, b) | not (isErr (Meta m a)) -> do
    Right
      [ (Meta m a, s)
      | (a, s) <- fromRight [] $ unify ops env a b
      ]
  (a, Any) -> Right [(a, [])]
  (Any, b) -> Right [(b, [])]
  (Unit, Unit) -> Right [(Unit, [])]
  (IntT, IntT) -> Right [(IntT, [])]
  (Int _, IntT) -> Right [(IntT, [])]
  (IntT, Int _) -> Right [(IntT, [])]
  (NumT, NumT) -> Right [(NumT, [])]
  (Num _, NumT) -> Right [(NumT, [])]
  (NumT, Num _) -> Right [(NumT, [])]
  (Int i, Int i') | i == i' -> Right [(Int i, [])]
  (Num n, Num n') | n == n' -> Right [(Num n, [])]
  (Or a1 a2, b) -> case (unify ops env a1 b, unify ops env a2 b) of
    (Right alts1, Right alts2) -> Right (alts1 ++ alts2)
    (Right alts, Left _) -> Right alts
    (Left _, Right alts) -> Right alts
    (Left _, Left _) -> Left (typeMismatch a b)
  (a, Or b1 b2) -> case (unify ops env a b1, unify ops env a b2) of
    (Right alts1, Right alts2) -> Right (alts1 ++ alts2)
    (Right alts, Left _) -> Right alts
    (Left _, Right alts) -> Right alts
    (Left _, Left _) -> Left (typeMismatch a b)
  (Var x, Var x') | x == x' -> Right [(Var x, [])]
  (Var x, b) | x `occurs` b -> Left (occursError x b)
  (Var x, b) -> Right [(b, [(x, b)])]
  (a, Var x) -> unify ops env (Var x) a
  (Tag k a, Tag k' b) | k == k' -> do
    alts <- unify ops env a b
    Right [(Tag k c, s) | (c, s) <- alts]
  (a, Tag k b) | Just def <- lookup k env -> do
    -- let env' = filter (\(x, _) -> x /= k) env
    let altb = eval ops (App (Let env def) b)
    alts <- unify ops env (Fun a (Tag k b)) altb
    Right [(snd (funOf alt), s) | (alt, s) <- alts]
  (Tag k a, b) | Just def <- lookup k env -> do
    -- let env' = filter (\(x, _) -> x /= k) env
    let alta = eval ops (App (Let env def) a)
    alts <- unify ops env alta (Fun b (Tag k a))
    Right [(snd (funOf alt), s) | (alt, s) <- alts]
  (And a1 b1, And a2 b2) -> do
    unify2 ops env And (a1, a2) (b1, b2)
  (a, For x b) -> do
    let (b', s1) = instantiate (freeVars a) (For x b)
    alts <- unify ops (s1 `compose` env) a b'
    Right $ map (\(c, s2) -> (c, s2 `compose` s1)) alts
  (For x a, b) -> do
    let (a', s1) = instantiate (freeVars b) (For x a)
    alts <- unify ops (s1 `compose` env) a' b
    Right $ map (\(c, s2) -> (c, s2 `compose` s1)) alts
  (Fix _ a, b) -> unify ops env a b
  (a, Fix _ b) -> unify ops env a b
  -- (Fun a1 b1, Fun a2@(Tag "::" _) b2@(Tag "List" _)) -> do
  --   (error . intercalate "\n")
  --     [ "",
  --       "env: " ++ show (map fst env),
  --       "unify " ++ show (a1, a2),
  --       "a: " ++ show (unify ops env a1 a2),
  --       "unify " ++ show (b1, b2),
  --       "b: " ++ show (unify ops env b1 b2),
  --       show (unify2 ops env Fun (a1, a2) (b1, b2)),
  --       ""
  --     ]
  (Fun a1 b1, Fun a2 b2) -> do
    unify2 ops env Fun (a1, a2) (b1, b2)
  (Call op args, Call op' args') | op == op' -> do
    alts <- unifyAll ops env args args'
    Right $ map (first $ Call op) alts
  (a, b) -> Left (typeMismatch a b)

unify2 :: Ops -> Env -> (Expr -> Expr -> Expr) -> (Expr, Expr) -> (Expr, Expr) -> Either (Error Expr) [(Expr, Substitution)]
unify2 ops env f (a1, a2) (b1, b2) = do
  Right
    [ (f x y, s2 `compose` s1)
    | (x, s1) <- fromRight [] $ unify ops env a1 a2,
      (y, s2) <- fromRight [] $ unify ops (s1 `compose` env) (substitute s1 b1) (substitute s1 b2)
    ]

unifyAll :: Ops -> Env -> [Expr] -> [Expr] -> Either (Error Expr) [([Expr], Substitution)]
unifyAll ops env (a : bs) (a' : bs') = do
  Right
    [ (c : cs, s2 `compose` s1)
    | (c, s1) <- fromRight [] $ unify ops env a a',
      (cs, s2) <- fromRight [] $ unifyAll ops env (map (substitute s1) bs) (map (substitute s1) bs')
    ]
unifyAll ops env _ _ = error $ show "unifyAll size mismatch"

-- collapse :: Ops -> Env -> [Expr] -> Either (Error Expr) [(Expr, Substitution)]
-- collapse ops env [] = error "collapse: empty list"
-- collapse ops env [a] = Right [(a, [])]
-- collapse ops env (a : bs) = do
--   Right
--     [ (c, s2 `compose` s1)
--     | (b, s1) <- fromRight [] $ collapse ops env bs,
--       (c, s2) <- fromRight [] $ unify ops (s1 `compose` env) (substitute s1 a) b
--     ]

infer :: Ops -> Env -> Expr -> Either (Error Expr) [((Expr, Type), Substitution)]
infer _ env Any = do
  let y = newName ("_" : map fst env) "_"
  Right [((Any, Var y), [(y, Var y)])]
infer _ _ Unit = Right [((Unit, Unit), [])]
infer _ _ IntT = Right [((IntT, IntT), [])]
infer _ _ NumT = Right [((NumT, NumT), [])]
infer _ _ (Int i) = Right [((Int i, IntT), [])]
infer _ _ (Num n) = Right [((Num n, NumT), [])]
infer ops env (Tag k a) = do
  Right
    [ ((Tag k a, Tag k t), s)
    | ((a, t), s) <- fromRight [] $ infer ops env a
    ]
infer ops env (Var x) = case lookup x env of
  Just (Var x') | x == x' -> do
    let y = newName (map fst env) (x ++ "T")
    Right [((Var x, Var y), [(y, Var y), (x, Ann (Var x) (Var y))])]
  Just (Ann (Var x') ty) | x == x' -> Right [((Var x, ty), [])]
  Just a -> do
    (Right . nubBy (\a b -> fst a == fst b))
      [ ((Var x, t), s)
      | ((_, t), s) <- fromRight [] $ infer ops env a
      ]
  Nothing -> Left (undefinedVar x)
infer ops env (Ann a t) = check ops env a t
infer ops env (And a b) = do
  Right
    [ ((And a b, And ta tb), s)
    | ((a, ta), (b, tb), s) <- fromRight [] $ infer2 ops env a b
    ]
infer ops env (Or a b) = do
  let alts1 = fromRight [] $ infer ops env a
  let alts2 = fromRight [] $ infer ops env b
  Right (alts1 ++ alts2)
-- infer ops env (For x@"xs" a) | "length" `occurs` a = do
--   let y = newName ((x ++ "$") : map fst env) (x ++ "$")
--   let sub x y = substitute [(x, Var y)]
--   (error . intercalate "\n")
--     ( ""
--         : ("infer " ++ show (For x a))
--         : ("env: " ++ show (map fst env))
--         : ("List: " ++ show (lookup "List" env))
--         : "alts:"
--         : [ " - " ++ show ((for' [x] (sub y x a), sub y x t), s)
--           | ((a, t), s) <- fromRight [] $ infer ops ((y, Var y) : env) (sub x y a)
--           ]
--     )
infer ops env (For x a) = do
  let y = newName ((x ++ "$") : map fst env) (x ++ "$")
  let sub x y = substitute [(x, Var y)]
  Right
    [ ((for' [x] (sub y x a), sub y x t), s)
    | ((a, t), s) <- fromRight [] $ infer ops ((y, Var y) : env) (sub x y a)
    ]
infer ops env (Fix x a) = do
  let y = newName ((x ++ "$") : map fst env) (x ++ "$")
  let sub x y = substitute [(x, Var y)]
  Right
    [ ((Fix x (sub y x a), sub y x t), pop y s)
    | ((a, t), s) <- fromRight [] $ infer ops ((y, Var y) : env) (sub x y a)
    ]
infer ops env (Fun a b) = do
  Right
    [ ((Fun (Ann a ta) (Ann b tb), Fun ta tb), s)
    | ((a, ta), (b, tb), s) <- fromRight [] $ infer2 ops env a b
    ]
infer ops env (App a b) = do
  let funAlts :: Expr -> [(Expr, Expr, Substitution)]
      funAlts (Var x) = do
        let x1 = newName ((x ++ "$") : map fst env) (x ++ "$")
        let x2 = newName ((x ++ "$") : x1 : map fst env) (x ++ "$")
        [(Var x1, Var x2, [(x1, Var x1), (x2, Var x2)])]
      funAlts (Fun a b) = [(a, b, [])]
      funAlts (Or a b) = funAlts a ++ funAlts b
      funAlts (Ann a _) = funAlts a
      funAlts (Meta _ a) = funAlts a
      funAlts _ = []
  Right
    [ (substitute s (App a (Ann b t1), substitute s t2), s)
    | ((a, ta), (b, tb), s1) <- fromRight [] $ infer2 ops env a b,
      (t1, t2, s2) <- funAlts ta,
      (_, s3) <- fromRight [] $ unify ops (s2 `compose` s1 `compose` env) t1 (substitute s1 tb),
      let s = s3 `compose` s2 `compose` s1
    ]
-- infer ops env (App a b) = do
--   let x = newName ("$" : map fst env) "$"
--   Right
--     [ do
--         let s = s2 `compose` s1
--         let t2 = fromMaybe (Var x) (lookup x s)
--         ((App a (substitute s2 $ Ann b tb), t2), s `compose` [(x, Var x)])
--     | ((b, tb), s1) <- fromRight [] $ infer ops env b,
--       ((a, _), s2) <- fromRight [] $ check ops ((x, Var x) : s1 `compose` env) (substitute s1 a) (Fun tb (Var x))
--     ]
infer ops env (Let defs a) = do
  Right
    [ ((Let defs a, t), s)
    | ((a, t), s) <- fromRight [] $ infer ops (defs ++ env) a
    ]
infer ops env (Call op args) = do
  let x = newName ("$" : map fst env) "$"
  Right
    [ ((Call op (map (uncurry Ann) args), substitute s (Var x)), [(x, Var x)] `compose` s)
    | (args, s) <- fromRight [] $ inferAll ops ((x, Var x) : env) args
    ]
-- infer _ _ a | isErr a = ((a, Err), [])
infer ops env (Meta m a) = do
  Right
    [ ((Meta m a, t), s)
    | ((a, t), s) <- fromRight [] $ infer ops env a
    ]
infer _ _ Err = Right [((Err, Err), [])]

infer2 :: Ops -> Env -> Expr -> Expr -> Either (Error Expr) [((Expr, Type), (Expr, Type), Substitution)]
infer2 ops env a b = do
  Right
    [ (substitute s2 at, bt, s2 `compose` s1)
    | (at, s1) <- fromRight [] $ infer ops env a,
      (bt, s2) <- fromRight [] $ infer ops (s1 `compose` env) (substitute s1 b)
    ]

inferAll :: Ops -> Env -> [Expr] -> Either (Error Expr) [([(Expr, Type)], Substitution)]
inferAll _ _ [] = Right [([], [])]
inferAll ops env (a : bs) = do
  Right
    [ (at : bts, s2 `compose` s1)
    | (at, s1) <- fromRight [] $ infer ops env a,
      (bts, s2) <- fromRight [] $ inferAll ops (s1 `compose` env) (substitute s1 bs)
    ]

check :: Ops -> Env -> Expr -> Type -> Either (Error Expr) [((Expr, Type), Substitution)]
check ops env a (For x t) = infer ops env (For x (Ann a t))
check ops env (For x a) t = infer ops env (For x (Ann a t))
check ops env (Var x) t = case lookup x env of
  Just (Var x') | x == x' -> Right [((Var x, t), [(x, Ann (Var x) t)])]
  Just (Ann (Var x') ty) | x == x' -> do
    Right [((Var x, ty), [])]
  -- Just a | x == "+" -> do
  --   ats <- check ops env a t
  --   (error . intercalate "\n")
  --     [ "\n",
  --       "check Var " ++ show (Var x, t),
  --       "env: " ++ show (map fst env),
  --       "a: " ++ show a,
  --       "alts:",
  --       (intercalate "\n")
  --         ["| " ++ show ((Var x, ta), s) | ((_, ta), s) <- ats],
  --       ""
  --     ]
  Just a -> do
    ats <- check ops env a t
    Right [((Var x, ta), s) | ((_, ta), s) <- ats]
  Nothing -> Left (undefinedVar x)
check ops env (Or a b) t = do
  -- check ops env (Or a b) t@(Fun And {} IntT) = do
  case check ops env a t of
    Left _ -> check ops env b t
    Right [] -> check ops env b t
    Right ats -> do
      Right
        [ ((Or (substitute s2 a) b, t), s2 `compose` s1)
        | ((a, t), s1) <- ats,
          ((b, t), s2) <- fromRight [] $ check ops env b t
        ]
check ops env (Or a b) t@(Fun (Tag "List" _) _) = do
  (error . intercalate "\n")
    [ "\n",
      "check Or " ++ show (Or a b, t),
      "env: " ++ show (map fst env),
      "at: " ++ show (check ops env a t),
      "bt: " ++ show (check ops env b t),
      "alts:",
      (intercalate "\n")
        [ "| " ++ show ((Or a b, substitute s t), s)
        | ((a, _), (b, _), s) <- fromRight [] $ check2 ops env (a, t) (b, t)
        ],
      ""
    ]
check ops env (Or a b) t = do
  Right
    [ ((Or a b, substitute s t), s)
    | ((a, _), (b, _), s) <- fromRight [] $ check2 ops env (a, t) (b, t)
    ]
check ops env (And a b) (And ta tb) = do
  Right
    [ ((And a b, And ta tb), s)
    | ((a, ta), (b, tb), s) <- fromRight [] $ check2 ops env (a, ta) (b, tb)
    ]
-- check ops env (Fun a@(Tag "::" _) b) (Fun ta tb) = do
--   abts <- check2 ops env (a, ta) (b, tb)
--   (error . intercalate "\n")
--     [ "\n",
--       "check Fun " ++ show (Fun a b, Fun ta tb),
--       "env: " ++ show (map fst env),
--       "at: " ++ show (check ops env a ta),
--       "bt: " ++ show (check ops env b tb),
--       "alts:",
--       (intercalate "\n")
--         [ show ((Fun (Ann a ta) (Ann b tb), Fun ta tb), s)
--         | ((a, ta), (b, tb), s) <- abts
--         ],
--       ""
--     ]
check ops env (Fun a b) (Fun ta tb) = do
  abts <- check2 ops env (a, ta) (b, tb)
  Right
    [ ((Fun (Ann a ta) (Ann b tb), Fun ta tb), s)
    | ((a, ta), (b, tb), s) <- abts
    ]
-- check ops env (App a@(Var "+") b) t = do
--   bts <- infer ops env b
--   (error . intercalate "\n")
--     [ "\n",
--       "check App " ++ show (App a b, t),
--       "env: " ++ show (map fst env),
--       "bts: " ++ show bts,
--       "alts: check ((+),(^Int, lengthT$2) -> ^Int)",
--       (intercalate "\n")
--         [ "| " ++ show ((App a (substitute s2 $ Ann b tb), substitute s t), s)
--         | ((b, tb), s1) <- bts,
--           ((a, _), s2) <- fromRight [] $ check ops (s1 `compose` env) (substitute s1 a) (Fun tb (substitute s1 t)),
--           let s = s2 `compose` s1
--         ],
--       ""
--     ]
check ops env (App a b) t = do
  bts <- infer ops env b
  Right
    [ ((App a (substitute s2 $ Ann b tb), substitute s t), s)
    | ((b, tb), s1) <- bts,
      ((a, _), s2) <- fromRight [] $ check ops (s1 `compose` env) (substitute s1 a) (Fun tb (substitute s1 t)),
      let s = s2 `compose` s1
    ]
check ops env (Meta m a) t = do
  ats <- check ops env a t
  Right [((Meta m a, t), s) | ((a, t), s) <- ats]
check ops env a (Meta m t) = do
  ats <- check ops env a t
  Right [((a, Meta m t), s) | ((a, t), s) <- ats]
check ops env a t = do
  ats <- infer ops env a
  Right
    [ ((a, t), s2 `compose` s1)
    | ((a, ta), s1) <- ats,
      (t, s2) <- fromRight [] $ unify ops (s1 `compose` env) ta (substitute s1 t)
    ]

check2 :: Ops -> Env -> (Expr, Type) -> (Expr, Type) -> Either (Error Expr) [((Expr, Type), (Expr, Type), Substitution)]
check2 ops env (a, ta) (b, tb) = do
  ats <- check ops env a ta
  Right
    [ (substitute s2 at, bt, s2 `compose` s1)
    | (at, s1) <- ats,
      (bt, s2) <- fromRight [] $ check ops (s1 `compose` env) (substitute s1 b) (substitute s1 tb)
    ]

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
  Call f args -> Call f (collapseAll vars args)
  Let env a -> Let env (collapse vars a)
  a -> apply (collapse vars) a

collapse2 :: [String] -> (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
collapse2 vars f a b = do
  let a' = collapse vars a
  f a' (collapse (freeVars a' `union` vars) b)

collapseAll :: [String] -> [Expr] -> [Expr]
collapseAll _ [] = []
collapseAll vars (a : bs) = do
  let a' = collapse vars a
  a' : collapseAll (freeVars a' `union` vars) bs
