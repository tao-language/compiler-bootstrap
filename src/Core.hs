module Core where

import Data.Bifunctor (Bifunctor (bimap, first, second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.Either (fromRight)
import Data.Function ((&))
import Data.List (delete, intercalate, sort, union, unionBy)
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
                        _ <- P.char '<'
                        _ <- P.spaces
                        arg <- expr
                        args <- P.zeroOrMore $ do
                          _ <- P.char ','
                          _ <- P.spaces
                          expr
                        _ <- P.char '>'
                        _ <- P.spaces
                        return (arg : args),
                      return []
                    ]
                return (tag k args)
           in G.Atom parser $ \layout -> \case
                Tag k Unit -> Just [PP.Text k]
                Tag k a -> do
                  let args = map layout (andOf a)
                  Just (PP.Text (k ++ "<") : intercalate [PP.Text ", "] args ++ [PP.Text ">"])
                _ -> Nothing,
          -- Grammar.Var
          G.atom (const Var) parseNameVar $ \_ -> \case
            Var x -> Just [PP.Text x]
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
           in G.Atom parser $ \layout -> \case
                Let env a -> do
                  let layoutDef (x, a) = PP.Text (x ++ " = ") : layout a
                  Just (PP.Text "@{" : intercalate [PP.Text ", "] (map layoutDef env) ++ PP.Text "} " : layout a)
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

letOf :: Expr -> (Env, Expr)
letOf (Let env a) = (env, a)
letOf (Ann a _) = letOf a
letOf (Meta _ a) = letOf a
letOf a = ([], a)

isLet :: Expr -> Bool
isLet (Let _ _) = True
isLet (Meta _ a) = isLet a
isLet (Ann a _) = isLet a
isLet _ = False

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
pushAll :: [(String, Expr)] -> Env -> Env
pushAll vars env = foldr (:) env vars

popAll :: [String] -> Env -> Env
popAll xs env = foldl (flip pop) env xs

pushVars :: [String] -> Env -> Env
pushVars xs = pushAll (map (\x -> (x, Var x)) xs)

freeNames :: (Bool, Bool, Bool) -> Expr -> [String]
freeNames (vars, tags, calls) = \case
  Any -> []
  Unit -> []
  IntT -> []
  NumT -> []
  Int _ -> []
  Num _ -> []
  Var x
    | vars -> [x]
    | otherwise -> []
  Tag k a
    | tags -> k : freeNames' a
    | otherwise -> freeNames' a
  Ann a b -> freeNames' a `union` freeNames' b
  And a b -> freeNames' a `union` freeNames' b
  Or a b -> freeNames' a `union` freeNames' b
  For x a -> delete x (freeNames' a)
  Fix x a -> delete x (freeNames' a)
  Fun a b -> freeNames' a `union` freeNames' b
  App a b -> freeNames' a `union` freeNames' b
  Call f args
    | calls -> foldr (union . freeNames') [f] args
    | otherwise -> foldr (union . freeNames') [] args
  -- TODO: This is much more subtle than it appears for Let.
  --       Free names should be done recursively on definitions used.
  --       More of a graph traversal problem, visiting nodes (definitions).
  --       This could also be used to only keep the relevant definitions and drop irrelevant ones.
  --        e.g. : a -> Bool
  --             (==) = x -> (y -> True | _ -> False) x
  -- Let [] b -> freeNames' b
  -- Let ((x, a) : defs) b -> delete x (freeNames' a `union` freeNames' (Let defs b))
  -- Let defs b -> filter (`notElem` map fst defs) (foldr ((union . freeNames') . snd) (freeNames' b) defs)
  -- Let _ b -> freeNames' b
  Let env b -> freeNames' (reduce [] (Let env b))
  Meta _ a -> freeNames' a
  Err -> []
  where
    freeNames' = freeNames (vars, tags, calls)

freeVars :: Expr -> [String]
freeVars = freeNames (True, False, False)

freeTags :: Expr -> [String]
freeTags = freeNames (False, True, False)

occurs :: String -> Expr -> Bool
occurs x (Var x') | x == x' = False
occurs x (Or a b) = occurs x a || occurs x b
occurs x (Meta _ a) = occurs x a
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
  (Fix x a, b) | isOpen b -> error $ show $ dropMeta $ App (Fix x a) b
  (Fix x a, b) -> reduceApp ops (reduce ops (Let [(x, Fix x a)] a)) b
  (Fun a c, b) -> case match False ops a b of
    Matched env -> reduce ops (Let env c)
    MaybeMatched a b -> App (Fun a c) b
    NotMatched a b -> err (unhandledCase a b)
  (Call f args, b) -> App (Call f args) b
  (Meta _ a, b) -> reduceApp ops a b
  _ -> err (cannotApply a b)

match :: Bool -> Ops -> Expr -> Expr -> MatchResult Env
match unify ops (Let env (Tag k a)) b = case lookup k env of
  Just def -> do
    let b' = curry' (Let env def) [a, b]
    match True ops (Tag k (Let env a)) (b' `Or` b)
  Nothing -> match unify ops (Tag k (Let env a)) b
match unify ops (Let env (Meta _ a)) b =
  match unify ops (Let env a) b
match unify ops (Let env (Let env' a)) b =
  match unify ops (Let (env ++ env') a) b
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
  (a, Var x) -> MaybeMatched a (Var x)
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
    a | isVar a || isApp a || isFun a -> Or a (eval ops b)
    a -> a
  For x a -> For x (eval ops (Let [(x, Var x)] a))
  Fix x a -> Fix x (eval ops (Let [(x, Var x)] a))
  Fun a b -> Fun (eval ops a) (eval ops b)
  App a b -> App (eval ops a) (eval ops b)
  Call f args -> Call f (eval ops <$> args)
  Meta (Error e) _ -> Meta (Error $ eval ops <$> e) Err
  Meta m a -> Meta m (eval ops a)
  Err -> Err
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
  substitute [] (Var x) = Var x
  substitute ((x, a) : _) (Var x') | x == x' = a
  substitute (_ : s) (Var x) = substitute s (Var x)
  substitute ((x, a) : s) b | x `occurs` a = substitute s b
  -- substitute ((x, a) : s) b | x `occurs` a = error $ "TODO substitute: " ++ x ++ " occurs in  " ++ show a
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
  (_, Any) -> Right [(Any, [])]
  (Any, _) -> Right [(Any, [])]
  (Unit, Unit) -> Right [(Unit, [])]
  (IntT, IntT) -> Right [(IntT, [])]
  (Int _, IntT) -> Right [(IntT, [])]
  (IntT, Int _) -> Right [(IntT, [])]
  (NumT, NumT) -> Right [(NumT, [])]
  (Num _, NumT) -> Right [(NumT, [])]
  (NumT, Num _) -> Right [(NumT, [])]
  (Int i, Int i') | i == i' -> Right [(Int i, [])]
  (Num n, Num n') | n == n' -> Right [(Num n, [])]
  (Or a1 a2, b) -> error $ show ("unify", Or a1 a2, b)
  (a, Or b1 b2) -> error $ show ("unify", a, Or b1 b2)
  (Var x, Var x') | x == x' -> Right [(Var x, [])]
  (Var x, b) | x `occurs` b -> Left (occursError x b)
  (Var x, b) -> Right [(b, [(x, b)])]
  (a, Var x) -> unify ops env (Var x) a
  (Tag k a, Tag k' b) | k == k' -> do
    Right
      [ (Tag k a, s)
      | (a, s) <- fromRight [] $ unify ops env a b
      ]
  (a, Tag k b) | Just def <- lookup k env -> do
    let a' = eval ops (curry' (Let env def) [b, a])
    let env' = filter (\(x, _) -> x /= k) env
    unify ops env' a' (Tag k b)
  (Tag k a, b) | Just def <- lookup k env -> do
    let b' = eval ops (curry' (Let env def) [a, b])
    let env' = filter (\(x, _) -> x /= k) env
    unify ops env' (Tag k a) b'
  (And a1 b1, And a2 b2) -> do
    unify2 ops env And (a1, a2) (b1, b2)
  (Ann a ta, Ann b tb) -> do
    unify2 ops env Ann (a, b) (ta, tb)
  (Ann a _, b) -> unify ops env a b
  (a, Ann b _) -> unify ops env a b
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

collapse :: Ops -> Env -> [Expr] -> Either (Error Expr) [(Expr, Substitution)]
collapse ops env [] = error "collapse: empty list"
collapse ops env [a] = Right [(a, [])]
collapse ops env (a : bs) = do
  Right
    [ (c, s2 `compose` s1)
    | (b, s1) <- fromRight [] $ collapse ops env bs,
      (c, s2) <- fromRight [] $ unify ops (s1 `compose` env) (substitute s1 a) b
    ]

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
    Right
      [ ((Var x, t), s)
      | ((_, t), s) <- fromRight [] $ infer ops env a
      ]
  Nothing -> Left (undefinedVar x)
infer ops env (Ann a t) = check ops env a t
-- infer ops env (Ann a t) = do
--   Right
--     [ ((Ann a t, t), s)
--       | ((a, t), s) <- fromRight [] $ check ops env a t
--     ]
infer ops env (And a b) = do
  Right
    [ ((And a b, And ta tb), s)
    | ((a, ta), (b, tb), s) <- fromRight [] $ infer2 ops env a b
    ]
infer ops env (Or a b) = do
  alts1 <- infer ops env a
  alts2 <- infer ops env b
  Right (alts1 ++ alts2)
infer ops env (For x a) = do
  let y = newName ((x ++ "$") : map fst env) (x ++ "$")
  let sub x y = substitute [(x, Var y)]
  Right
    [ ((For x (sub y x a), sub y x t), s)
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
    [ do
        let s = s3 `compose` s2 `compose` s1
        (substitute s (App a (Ann b t1), substitute s t2), s)
    | ((a, ta), (b, tb), s1) <- fromRight [] $ infer2 ops env a b,
      (t1, t2, s2) <- funAlts ta,
      (_, s3) <- fromRight [] $ unify ops (s2 `compose` s1 `compose` env) t1 (substitute s1 tb)
    ]
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
-- infer _ _ Err = ((Err, Err), [])
infer ops env a =
  (error . intercalate "\n")
    [ "infer " ++ show a,
      "env: " ++ show (env & filter (\(x, a) -> a == Var x) & map fst),
      intercalate "\n" (env & filter (\(x, a) -> a /= Var x) & map (\x -> "- " ++ show x)),
      ""
    ]

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
  Just a -> do
    Right
      [ ((Var x, ta), s)
      | ((_, ta), s) <- fromRight [] $ check ops env a t
      ]
  Nothing -> Left (undefinedVar x)
check ops env (Or a b) t = do
  Right
    [ ((Or (substitute s2 a) b, t), s2 `compose` s1)
    | ((a, t), s1) <- fromRight [] $ check ops env a t,
      ((b, t), s2) <- fromRight [] $ check ops (s1 `compose` env) (substitute s1 b) t
    ]
check ops env (And a b) (And ta tb) = do
  Right
    [ ((And a b, And ta tb), s)
    | ((a, ta), (b, tb), s) <- fromRight [] $ check2 ops env (a, ta) (b, tb)
    ]
check ops env (Fun a b) (Fun ta tb) = do
  Right
    [ ((Fun (Ann a ta) (Ann b tb), Fun ta tb), s)
    | ((a, ta), (b, tb), s) <- fromRight [] (check2 ops env (a, ta) (b, tb))
    ]
check ops env (Meta m a) t = do
  Right [((Meta m a, t), s) | ((a, t), s) <- fromRight [] (check ops env a t)]
check ops env a (Meta m t) = do
  Right [((a, Meta m t), s) | ((a, t), s) <- fromRight [] (check ops env a t)]
check ops env a t | False = do
  (error . intercalate "\n")
    [ "check " ++ show (a, t),
      "env: " ++ show (env & filter (\(x, a) -> a == Var x) & map fst),
      intercalate "\n" (env & filter (\(x, a) -> a /= Var x) & map (\x -> "- " ++ show x)),
      "a: " ++ show (infer ops env a),
      show
        [ ((a, t), s2 `compose` s1)
        | ((a, ta), s1) <- fromRight [] $ infer ops env a,
          (t, s2) <- fromRight [] $ unify ops (s1 `compose` env) ta (substitute s1 t)
        ],
      ""
    ]
check ops env a t = do
  Right
    [ ((a, t), s2 `compose` s1)
    | ((a, ta), s1) <- fromRight [] $ infer ops env a,
      (t, s2) <- fromRight [] $ unify ops (s1 `compose` env) ta (substitute s1 t)
    ]

check2 :: Ops -> Env -> (Expr, Type) -> (Expr, Type) -> Either (Error Expr) [((Expr, Type), (Expr, Type), Substitution)]
check2 ops env (a, ta) (b, tb) = do
  Right
    [ (substitute s2 at, bt, s2 `compose` s1)
    | (at, s1) <- fromRight [] $ check ops env a ta,
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

instantiate' :: [String] -> Expr -> ([Expr], Substitution)
instantiate' vars (For x a) | x `occurs` a = do
  let y = newName vars x
  let (alts, s) = instantiate' (y : vars) (substitute [(x, Var y)] a)
  (alts, (y, Var y) : s)
instantiate' vars (For _ a) = instantiate' vars a
instantiate' vars (Meta _ a) = instantiate' vars a
instantiate' _ a = (orOf a, [])
