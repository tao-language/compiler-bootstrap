module Core where

import Data.Bifunctor (Bifunctor (bimap, second))
import Data.Char (isAlphaNum, isLower, isUpper)
import Data.Function ((&))
import Data.List (delete, intercalate, sort, union, unionBy)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)
import Error
import Grammar as G
import Location (Location (..), Position (..), Range (..))
import qualified Parser as P
import qualified PrettyPrint as PP
import Stdlib (replace, replaceString)

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
  | Tag String
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
  | Meta Metadata Expr
  | Err (Error Expr)
  -- deriving (Eq, Show)
  deriving (Eq)

instance Show Expr where
  show :: Expr -> String
  show = Core.format 80

type Type = Expr

type Ops = [(String, (Expr -> Expr) -> [Expr] -> Maybe Expr)]

type Env = [(String, Expr)]

type Substitution = [(String, Expr)]

data Metadata
  = Loc Location
  | Comments [String]
  | TrailingComment String
  deriving (Eq, Show)

data MatchResult a
  = Matched a
  | MaybeMatched Expr Expr
  | NotMatched
  deriving (Eq, Show)

instance Functor MatchResult where
  fmap :: (a -> b) -> MatchResult a -> MatchResult b
  fmap f (Matched env) = Matched (f env)
  fmap _ (MaybeMatched a b) = MaybeMatched a b
  fmap _ NotMatched = NotMatched

instance Applicative MatchResult where
  pure :: a -> MatchResult a
  pure = Matched

  (<*>) :: MatchResult (a -> b) -> MatchResult a -> MatchResult b
  (<*>) (Matched f) m = fmap f m
  (<*>) (MaybeMatched a b) _ = MaybeMatched a b
  (<*>) NotMatched _ = NotMatched

instance Monad MatchResult where
  (>>=) :: MatchResult a -> (a -> MatchResult b) -> MatchResult b
  (>>=) (Matched env) f = f env
  (>>=) (MaybeMatched a b) _ = MaybeMatched a b
  (>>=) NotMatched _ = NotMatched

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
          G.atom (const Tag) parseNameTag $ \_ -> \case
            Tag k -> Just [PP.Text k]
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
                  let items = andOf (And a b)
                  Just (PP.Text "(" : intercalate [PP.Text ", "] (map layout items) ++ [PP.Text ")"])
                _ -> Nothing,
          -- Grammar.sugar.def
          let parser expr = do
                _ <- P.word "^let"
                _ <- P.spaces
                a <- expr
                _ <- P.char '='
                _ <- P.whitespaces
                b <- expr
                _ <- P.oneOf [P.char ';', P.char '\n']
                _ <- P.whitespaces
                def (a, b) <$> expr
           in G.Atom parser $ \layout -> \case
                App (Fun a c) b -> do
                  Just (PP.Text "^let " : layout a ++ PP.Text " = " : layout b ++ PP.Text "; " : layout c)
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
                return (err a)
           in G.Atom parser $ \layout -> \case
                Err e -> case e of
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
tag :: String -> [Expr] -> Expr
tag k args = and' (Tag k : args)

and' :: [Expr] -> Expr
and' [] = Unit
and' [a] = a
and' (a : bs) = And a (and' bs)

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

isAnn :: Expr -> Bool
isAnn (Ann _ _) = True
isAnn (Meta _ a) = isAnn a
isAnn _ = False

annOf :: Expr -> Maybe (Expr, Expr)
annOf (Ann a b) = Just (a, b)
annOf (Meta _ a) = annOf a
annOf _ = Nothing

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

for' :: [String] -> Expr -> Expr
for' [] a = a
for' (x : xs) a | x `occurs` a = For x (for' xs a)
for' (_ : xs) a = for' xs a

forOf :: Expr -> ([String], Expr)
forOf (For x a) = let (xs, b) = forOf a in (x : xs, b)
forOf a = ([], a)

fix :: [String] -> Expr -> Expr
fix xs a = foldr Fix a xs

fix' :: [String] -> Expr -> Expr
fix' [] a = a
fix' (x : xs) a | isRec x a = Fix x (fix' xs a)
fix' (_ : xs) a = fix' xs a

isRec :: String -> Expr -> Bool
isRec _ (Var _) = False
isRec x (Ann a _) = isRec x a
isRec x (Fun a b) = not (x `occurs` a) && x `occurs` b
isRec x (Meta _ a) = isRec x a
isRec _ _ = False

fixOf :: Expr -> ([String], Expr)
fixOf (Fix x a) = let (xs, b) = fixOf a in (x : xs, b)
fixOf a = ([], a)

fun :: [Expr] -> Expr -> Expr
fun ps = Fun (and' ps)

funOf :: Expr -> ([Expr], Expr)
funOf (Fun arg ret) = (andOf arg, ret)
funOf a = ([], a)

lam :: [Expr] -> Expr -> Expr
lam ps b = for' (freeVars (and' ps)) (fun ps b)

app :: Expr -> [Expr] -> Expr
app fun args = App fun (and' args)

appT :: Expr -> [Expr] -> [Type] -> Expr
appT fun args types = App fun (Ann (and' args) (and' types))

appOf :: Expr -> (Expr, [Expr])
appOf (App a b) = let (a', bs) = appOf a in (a', bs ++ [b])
appOf a = (a, [])

curry' :: Expr -> [Expr] -> Expr
curry' fun [] = fun
curry' fun (arg : args) = app (App fun arg) args

let' :: Env -> Expr -> Expr
let' [] a = a
let' env (Let env' a) = let' (env ++ env') a
let' env a = Let env a

def :: (Expr, Expr) -> Expr -> Expr
def (a, b) c = App (Fun (for' (freeVars a) a) c) b

list :: Expr -> Expr -> [Expr] -> Expr
list _ nil [] = nil
list cons nil (a : bs) = app cons [a, list cons nil bs]

match' :: [Expr] -> [([Expr], Expr)] -> Expr
match' args cases = app (matchFun cases) args

matchFun :: [([Expr], Expr)] -> Expr
matchFun [] = Unit
matchFun [(ps, b)] = fun ps b
matchFun ((ps, b) : cases) = fun ps b `Or` matchFun cases

err :: Expr -> Expr
err a = Err (customError a)

isErr :: Expr -> Bool
isErr (Err _) = True
isErr (Meta _ a) = isErr a
isErr _ = False

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
pop :: (Eq k) => k -> [(k, v)] -> [(k, v)]
pop _ [] = []
pop x ((x', _) : kvs) | x == x' = kvs
pop x (_ : kvs) = pop x kvs

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
  Tag k
    | tags -> [k]
    | otherwise -> []
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
  Err _ -> []
  where
    freeNames' = freeNames (vars, tags, calls)

freeVars :: Expr -> [String]
freeVars = freeNames (True, False, False)

freeTags :: Expr -> [String]
freeTags = freeNames (False, True, False)

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
reduce :: Ops -> Expr -> Expr
reduce ops = \case
  App a b -> reduceApp ops (reduce ops a) (reduce ops b)
  Let env expr -> reduceLet ops env expr
  Meta m a -> Meta m (reduce ops a)
  expr -> expr

reduceLet :: Ops -> Env -> Expr -> Expr
reduceLet ops env = \case
  Var x -> case lookup x env of
    Just (Var x') | x == x' -> Var x
    Just (Ann (Var x') t) | x == x' -> Ann (Var x) t
    Just a -> reduce ops a
    Nothing -> Var x
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
  Err e -> Err (Let env <$> e)
  expr -> expr

reduceApp :: Ops -> Expr -> Expr -> Expr
reduceApp ops a b = case (a, reduce ops b) of
  (Any, _) -> Any
  (a@Var {}, b) -> App a b
  (a@App {}, b) -> App a b
  (Ann a _, b) -> reduceApp ops (reduce ops a) b
  (Or a1 a2, b) -> case reduceApp ops (reduce ops a1) b of
    Err _ -> reduceApp ops (reduce ops a2) b
    c@App {} -> Or c (App a2 b)
    c -> c
  (For x a, b) -> reduceApp ops (reduce ops (Let [(x, Var x)] a)) b
  (Fix x a, b) -> reduceApp ops (reduce ops (Let [(x, Fix x a)] a)) b
  (Fun a c, b) -> case match False ops a b of
    Matched env -> reduce ops (Let env c)
    MaybeMatched a b -> App (Fun a c) b
    NotMatched -> Err (unhandledCase a b)
  (Call f args, b) -> App (Call f args) b
  (Meta _ a, b) -> reduceApp ops a b
  _ -> Err (cannotApply a b)

match :: Bool -> Ops -> Expr -> Expr -> MatchResult Env
match unify ops (Let env (Tag k)) b = case lookup k env of
  Just def -> do
    let b' = App (Let env def) b
    match unify ops (Tag k) (b' `Or` b)
  Nothing -> match unify ops (Tag k) b
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
  (Tag k, Tag k') | k == k' -> Matched []
  (Var x, b) -> Matched [(x, b)]
  (a, Var x)
    | unify -> Matched [(x, a)]
    | otherwise -> MaybeMatched a (Var x)
  (Ann a ta, Ann b tb) -> do
    env1 <- match True ops ta tb
    env2 <- match unify ops (Let env1 a) b
    return (env1 ++ env2)
  (a, Ann b _) -> match unify ops a b
  (And (Let env (Tag k)) a, b) -> case lookup k env of
    Just def -> do
      let b' = curry' (Let env def) [a, b]
      match unify ops (And (Tag k) a) (b' `Or` b)
    Nothing -> match unify ops (And (Tag k) a) b
  (And (Let env (Meta _ a1)) a2, b) ->
    match unify ops (Let env (And a1 a2)) b
  (And (Let env (Let env' a1)) a2, b) ->
    match unify ops (And (Let (env ++ env') a1) a2) b
  (And a1 a2, And b1 b2) -> do
    env1 <- match unify ops a1 b1
    env2 <- match unify ops (Let env1 a2) b2
    return (env1 ++ env2)
  (Or a1 a2, b) -> case match unify ops a1 b of
    Matched env1 -> case match unify ops (Let env1 a2) b of
      Matched env2 -> Matched (env1 ++ env2)
      MaybeMatched a2 b -> MaybeMatched (Or a1 a2) b
      NotMatched -> Matched env1
    MaybeMatched a1 b -> MaybeMatched (Or a1 a2) b
    NotMatched -> match unify ops a2 b
  (a, Or b1 b2) -> case match unify ops a b1 of
    Matched env1 -> case match unify ops (Let env1 a) b2 of
      Matched env2 -> Matched (env1 ++ env2)
      MaybeMatched a b2 -> MaybeMatched a (Or b1 b2)
      NotMatched -> Matched env1
    MaybeMatched a b1 -> MaybeMatched a (Or b1 b2)
    NotMatched -> match unify ops a b2
  (For x a, b) -> match unify ops (Let [(x, Var x)] a) b
  (a, For x b) -> match unify ops a (Let [(x, Var x)] b)
  (Fix x a, Fix x' b) | x == x' -> do
    match unify ops (Let [(x, Var x)] a) (Let [(x', Fix x' b)] b)
  (Fix x a, Fix y b) -> do
    match unify ops (Fix x a) (Fix x (substitute [(y, Var x)] b))
  (Fun a1 a2, Fun b1 b2) -> match unify ops (And a1 a2) (And b1 b2)
  (App a1 a2, App b1 b2) -> match unify ops (And a1 a2) (And b1 b2)
  (Call x args, Call x' args') | x == x' -> do
    match unify ops (and' args) (and' args')
  (_, Meta _ b) -> match unify ops a b
  (Err _, Err _) -> Matched []
  _ -> NotMatched

eval :: Ops -> Expr -> Expr
eval ops expr = case reduce ops expr of
  Ann a b -> Ann (eval ops a) (eval ops b)
  And a b -> And (eval ops a) (eval ops b)
  Or a b -> Or (eval ops a) (eval ops b)
  For x a -> For x (eval ops (Let [(x, Var x)] a))
  Fix x a -> Fix x (eval ops (Let [(x, Var x)] a))
  Fun a b -> Fun (eval ops a) (eval ops b)
  App a b -> App (eval ops a) (eval ops b)
  Call f args -> Call f (eval ops <$> args)
  Meta m a -> Meta m (eval ops a)
  Err e -> Err (fmap (eval ops) e)
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
  substitute _ (Tag k) = Tag k
  substitute s (Ann a b) = Ann (dropTypes (substitute s a)) (dropTypes (substitute s b))
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
  substitute s (Err e) = Err (substitute s e)

instance Substitute (Error Expr) where
  substitute :: Substitution -> Error Expr -> Error Expr
  substitute s = fmap (substitute s)

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = do
  let sub s (x, a) = case lookup x s of
        Just b -> (x, b)
        Nothing -> (x, substitute s a)
  unionBy (\a b -> fst a == fst b) s1 (map (sub s1) s2)

dropTypes :: Expr -> Expr
dropTypes (Ann a@Call {} t) = Ann (dropTypes a) (dropTypes t)
dropTypes (Ann a _) = dropTypes a
dropTypes (And a b) = And (dropTypes a) (dropTypes b)
dropTypes (Or a b) = Or (dropTypes a) (dropTypes b)
dropTypes (For x a) = For x (dropTypes a)
dropTypes (Fix x a) = Fix x (dropTypes a)
dropTypes (Fun (Ann a ta) b) = case andOf ta of
  [Ann ta _] -> Fun (Ann (dropTypes a) (dropTypes ta)) (dropTypes b)
  _ -> Fun (Ann (dropTypes a) (dropTypes ta)) (dropTypes b)
dropTypes (Fun a b) = Fun (dropTypes a) (dropTypes b)
dropTypes (App a (Ann b tb)) = case andOf tb of
  [Ann tb _] -> App (dropTypes a) (Ann (dropTypes b) (dropTypes tb))
  _ -> App (dropTypes a) (Ann (dropTypes b) (dropTypes tb))
dropTypes (App a b) = App (dropTypes a) (dropTypes b)
dropTypes (Call op args) = Call op (map dropTypes args)
dropTypes (Let defs b) = Let (map (second dropTypes) defs) (dropTypes b)
dropTypes (Meta m a) = Meta m (dropTypes a)
dropTypes a = a

dropMeta :: Expr -> Expr
dropMeta (Ann a b) = Ann (dropMeta a) (dropMeta b)
dropMeta (And a b) = And (dropMeta a) (dropMeta b)
dropMeta (Or a b) = Or (dropMeta a) (dropMeta b)
dropMeta (For x a) = For x (dropMeta a)
dropMeta (Fix x a) = Fix x (dropMeta a)
dropMeta (Fun a b) = Fun (dropMeta a) (dropMeta b)
dropMeta (App a b) = App (dropMeta a) (dropMeta b)
dropMeta (Call op args) = Call op (map dropMeta args)
dropMeta (Let defs b) = Let (map (second dropMeta) defs) (dropMeta b)
dropMeta (Meta _ a) = dropMeta a
dropMeta (Err e) = Err (fmap dropMeta e)
dropMeta a = a

dropLet :: Expr -> Expr
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

unify :: Ops -> Env -> Expr -> Expr -> (Expr, Substitution)
unify ops env a b = case (a, b) of
  (a, Meta m b) -> case unify ops env a b of
    (Err (TypeError (TypeMismatch a b)), s) -> (Err $ typeMismatch a (Meta m b), s)
    result -> result
  (Meta m a, b) -> case unify ops env a b of
    (Err (TypeError (TypeMismatch a b)), s) -> (Err $ typeMismatch (Meta m a) b, s)
    result -> result
  (_, Any) -> (Any, [])
  (Any, _) -> (Any, [])
  (Unit, Unit) -> (Unit, [])
  (IntT, IntT) -> (IntT, [])
  (Int _, IntT) -> (IntT, [])
  (IntT, Int _) -> (IntT, [])
  (NumT, NumT) -> (NumT, [])
  (Num _, NumT) -> (NumT, [])
  (NumT, Num _) -> (NumT, [])
  (Int i, Int i') | i == i' -> (Int i, [])
  (Num n, Num n') | n == n' -> (Num n, [])
  (Var x, Var x') | x == x' -> (Var x, [])
  (Var x, b) | x `occurs` b -> (Err $ occursError x b, [])
  (Var x, b) -> (b, [(x, b)])
  (a, Var x) -> unify ops env (Var x) a
  (Tag k, Tag k') | k == k' -> (Tag k, [])
  (a, Tag k) | Just def <- lookup k env -> do
    let a' = eval ops (App (Let env def) a)
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s) = unify ops env' a' (Tag k)
    (t, [(k, def)] `compose` s)
  (Tag k, b) | Just def <- lookup k env -> do
    let b' = eval ops (App (Let env def) b)
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s) = unify ops env' (Tag k) b'
    (t, [(k, def)] `compose` s)
  (a, And (Tag k) b) | Just def <- lookup k env -> do
    let a' = eval ops (curry' (Let env def) [b, a])
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s) = unify ops env' a' (And (Tag k) b)
    (t, [(k, def)] `compose` s)
  (And (Tag k) a, b) | Just def <- lookup k env -> do
    let b' = eval ops (curry' (Let env def) [a, b])
    let env' = filter (\(x, _) -> x /= k) env
    let (t, s) = unify ops env' (And (Tag k) a) b'
    (t, [(k, def)] `compose` s)
  (And a1 b1, And a2 b2) -> do
    let ((a, b), s) = unify2 ops env (a1, a2) (b1, b2)
    (And a b, s)
  (Ann a ta, Ann b tb) -> do
    let ((a', ta'), s) = unify2 ops env (a, b) (ta, tb)
    (Ann a' ta', s)
  (Ann a _, b) -> unify ops env a b
  (a, Ann b _) -> unify ops env a b
  (Or a1 a2, b) -> case unify ops env a1 b of
    (e1, _) | isErr e1 -> case unify ops env a2 b of
      (e2, _) | isErr e2 -> (Or e1 e2, [])
      (c2, s2) -> (c2, s2)
    (c1, s1) -> do
      let env1 = s1 `compose` env
      let (a2', b') = (substitute s1 a2, substitute s1 b)
      case unify ops env1 a2' b' of
        (e, _) | isErr e -> (c1, s1)
        (c2, s2) -> do
          let env2 = s2 `compose` env1
          let c1' = substitute s2 c1
          case unify ops env2 c1' c2 of
            (e, _) | isErr e -> (Or c1' c2, s2 `compose` s1)
            (c, s3) -> (c, s3 `compose` s2 `compose` s1)
  (a, Or b1 b2) -> case unify ops env a b1 of
    (e1, _) | isErr e1 -> case unify ops env a b2 of
      (e2, _) | isErr e2 -> (Or e1 e2, [])
      (c2, s2) -> (c2, s2)
    (c1, s1) -> do
      let env1 = s1 `compose` env
      let (a', b2') = (substitute s1 a, substitute s1 b2)
      case unify ops env1 a' b2' of
        (e, _) | isErr e -> (c1, s1)
        (c2, s2) -> do
          let env2 = s2 `compose` env1
          let c1' = substitute s2 c1
          case unify ops env2 c1' c2 of
            (e, _) | isErr e -> (Or c1' c2, s2 `compose` s1)
            (c, s3) -> (c, s3 `compose` s2 `compose` s1)
  (a, For x b) -> do
    let (b', s1) = instantiate (freeVars a) (For x b)
    let (c, s2) = unify ops (s1 `compose` env) a b'
    (c, s2 `compose` s1)
  (For x a, b) -> do
    let (a', s1) = instantiate (freeVars b) (For x a)
    let (c, s2) = unify ops (s1 `compose` env) a' b
    (c, s2 `compose` s1)
  (Fix _ a, b) -> unify ops env a b
  (a, Fix _ b) -> unify ops env a b
  (Fun a1 b1, Fun a2 b2) -> case unify2 ops env (a1, a2) (b1, b2) of
    ((a, _), _) | isErr a -> (a, [])
    ((_, b), _) | isErr b -> (b, [])
    ((a, b), s) -> (Fun a b, s)
  (Call op args, Call op' args') | op == op' -> do
    let (args'', s) = unifyAll ops env args args'
    (Call op args'', s)
  (a, b) -> (Err $ typeMismatch a b, [])

unify2 :: Ops -> Env -> (Expr, Expr) -> (Expr, Expr) -> ((Expr, Expr), Substitution)
unify2 ops env (a1, a2) (b1, b2) = do
  let (ta, s1) = unify ops env a1 a2
  let (tb, s2) = unify ops env (substitute s1 b1) (substitute s1 b2)
  ((substitute s2 ta, tb), s2 `compose` s1)

unifyAll :: Ops -> Env -> [Expr] -> [Expr] -> ([Expr], Substitution)
unifyAll ops env (a : bs) (a' : bs') = do
  let (ta, s1) = unify ops env a a'
  let (tbs, s2) = unifyAll ops env (map (substitute s1) bs) (map (substitute s1) bs')
  (ta : tbs, s2 `compose` s1)
unifyAll _ _ _ _ = ([], [])

infer :: Ops -> Env -> Expr -> ((Expr, Type), Substitution)
infer _ env Any = do
  let y = newName ("_" : map fst env) "_"
  ((Any, Var y), [(y, Var y)])
infer _ _ Unit = ((Unit, Unit), [])
infer _ _ IntT = ((IntT, IntT), [])
infer _ _ NumT = ((NumT, NumT), [])
infer _ _ (Int i) = ((Int i, IntT), [])
infer _ _ (Num n) = ((Num n, NumT), [])
infer _ _ (Tag k) = ((Tag k, Tag k), [])
infer ops env (Var x) = do
  let (ta, s) = case lookup x env of
        Just (Var x') | x == x' -> do
          let y = newName (map fst env) (x ++ "T")
          (Var y, [(y, Var y), (x, Ann (Var x) (Var y))])
        Just (Ann (Var x') ty) | x == x' -> do
          instantiate (map fst env) ty
        Just a -> do
          let ((_, ta), s) = infer ops env a
          (ta, s)
        Nothing -> (Err (undefinedVar x), [])
  ((Var x, ta), s)
infer ops env (Ann a t) = check ops env a t
infer ops env (And a b) = do
  let ((a', ta), (b', tb), s) = infer2 ops env a b
  ((And a' b', And ta tb), s)
infer ops env (Or a b) = do
  let ((a', ta), (b', tb), s) = infer2 ops env a b
  case unify ops (s `compose` env) ta tb of
    (t, []) | not (isErr t) -> ((Or a' b', t), s)
    _ -> ((Or a' b', Or ta tb), s)
infer ops env (For x a) = do
  let y = newName (map fst env) x
  let ((a', ta), s) = infer ops ((y, Var y) : env) (substitute [(x, Var y)] a)
  ((For x (substitute [(y, Var x)] a'), ta), s `compose` [(y, Var y)])
infer ops env (Fix x a) = do
  let y = newName (map fst env) x
  let ((a', ta), s) = infer ops ((y, Var y) : env) (substitute [(x, Var y)] a)
  ((Fix x (substitute [(y, Var x)] a'), ta), s `compose` [(y, Var y)])
infer ops env (Fun a b) = do
  let ((a', ta), (b', tb), s) = infer2 ops env a b
  ((Fun (typed a' ta) (typed b' tb), Fun ta tb), s)
infer ops env (App a b) = do
  let ((a_, ta), s1) = infer ops env a
  let ((a', b'), (t1, t2), s2) = checkApp ops (s1 `compose` env) (a_, ta) (substitute s1 b)
  ((App a' (typed b' t1), t2), s2 `compose` s1)
infer ops env (Let defs a) = do
  let ((a', ta), s) = infer ops (defs ++ env) a
  ((Let defs a', ta), s)
infer ops env (Call op args) = do
  let y = newName ("_" : map fst env) "_"
  let (args', s) = inferAll ops ((y, Var y) : env) args
  ((Call op (map fst args'), substitute s (Var y)), s)
infer ops env (Meta m a) = do
  let ((a', ta), s) = infer ops env a
  case (a', ta) of
    (a', Err e) -> ((Ann (Meta m a') (Err e), Err e), s)
    (a', ta) -> ((Meta m a', ta), s)
infer _ _ (Err e) = ((Err e, Any), [])

infer2 :: Ops -> Env -> Expr -> Expr -> ((Expr, Type), (Expr, Type), Substitution)
infer2 ops env a b = do
  let ((a', ta), s1) = infer ops env a
  let ((b', tb), s2) = infer ops (s1 `compose` env) (substitute s1 b)
  ((substitute s2 a', substitute s2 ta), (b', tb), s2 `compose` s1)

inferAll :: Ops -> Env -> [Expr] -> ([(Expr, Type)], Substitution)
inferAll _ _ [] = ([], [])
inferAll ops env (a : bs) = do
  let ((a', ta), s1) = infer ops env a
  let (bts, s2) = inferAll ops (s1 `compose` env) (map (substitute s1) bs)
  ((substitute s2 a', substitute s2 ta) : bts, s2 `compose` s1)

check :: Ops -> Env -> Expr -> Type -> ((Expr, Type), Substitution)
check ops env a (For x t) = do
  let y = newName (map fst env) x
  let ((a', t'), s) = check ops ((y, Var y) : env) a (substitute [(x, Var y)] t)
  ((a', For x (substitute [(y, Var x)] t')), s `compose` [(y, Var y)])
check ops env (Or a b) t = do
  let ((a', ta'), (b', tb'), s) = check2 ops env (a, t) (b, t)
  case unify ops (s `compose` env) ta' tb' of
    (t', []) | not (isErr t) -> ((Or a' b', t'), s)
    _ -> ((Or a' b', Or ta' tb'), s)
check ops env (For x a) t = do
  -- let y = newName (map fst env) x
  -- let ((a', t'), s) = check ops ((y, Var y) : env) (substitute [(x, Var y)] a) t
  -- ((For x (substitute [(y, Var x)] a'), t'), s `compose` [(y, Var y)])
  error "🚨 TODO: do not output For, make infer instantiate all with unique names"
check ops env (Fun a b) (Fun ta tb) = do
  let ((a', ta'), (b', tb'), s) = check2 ops env (a, ta) (b, tb)
  ((Fun (typed a' ta') (typed b' tb), Fun ta' tb'), s)
check ops env (App a b) t2 = do
  let ((b', t1), s1) = infer ops env b
  let ((a', _), s2) = check ops (s1 `compose` env) (substitute s1 a) (Fun t1 (substitute s1 t2))
  let s = s2 `compose` s1
  ((App a' (substitute s2 (typed b' t1)), substitute s t2), s)
check ops env a (Err _) = infer ops env a
check ops env a t = do
  let ((a', ta), s1) = infer ops env a
  let (t', s2) = unify ops env ta (substitute s1 t)
  ((substitute s2 a', t'), s2 `compose` s1)

check2 :: Ops -> Env -> (Expr, Type) -> (Expr, Type) -> ((Expr, Type), (Expr, Type), Substitution)
check2 ops env (a, ta) (b, tb) = do
  let ((a', ta'), s1) = check ops env a ta
  let ((b', tb'), s2) = check ops (s1 `compose` env) (substitute s1 b) (substitute s1 tb)
  ((substitute s2 a', substitute s2 ta'), (b', tb'), s2 `compose` s1)

checkApp :: Ops -> Env -> (Expr, Type) -> Expr -> ((Expr, Expr), (Type, Type), Substitution)
checkApp ops env (a, ta) b = case ta of
  Var x -> do
    let x1 = newName ((x ++ "$") : map fst env) (x ++ "$")
    let x2 = newName (x1 : (x ++ "$") : map fst env) (x ++ "$")
    let ((a', _), (b', t1), s) = check2 ops (pushVars [x1, x2] env) (a, Fun (Var x1) (Var x2)) (b, Var x1)
    ((a', b'), (t1, substitute s (Var x2)), s `compose` [(x1, Var x1), (x2, Var x2)])
  For x ta -> do
    let (ta', s1) = instantiate (map fst env) (For x ta)
    let (ab, ts, s2) = checkApp ops (s1 `compose` env) (substitute s1 a, ta') (substitute s1 b)
    (ab, ts, s2 `compose` s1)
  Or ta1 ta2 -> case checkApp ops env (a, ta1) b of
    ((a, b), (t1, t2), s1) | not (isErr t1) && not (isErr t2) -> case checkApp ops env (a, ta2) b of
      ((a, b), (t1', t2'), s2) | not (isErr t1') && not (isErr t2') -> do
        ((a, b), (merge ops env t1 t1', merge ops env t2 t2'), s2 `compose` s1)
      _ -> ((a, b), (t1, t2), s1)
    _ -> checkApp ops env (a, ta2) b
  Fun t1 t2 -> do
    let ((a', _), (b', t1'), s) = check2 ops env (a, Fun t1 t2) (b, t1)
    let t2' = case substitute s t2 of
          Err _ -> Any
          t2 -> t2
    ((a', b'), (t1', t2'), s)
  Meta _ ta -> checkApp ops env (a, ta) b
  _ -> do
    let ((b', tb), s) = infer ops env b
    ((substitute s a, b'), (Err $ TypeError $ NotAFunction (substitute s a) (substitute s ta), tb), s)

merge :: Ops -> Env -> Expr -> Expr -> Expr
merge ops env a b = case unify ops env a b of
  (a, []) | not (isErr a) -> a
  _ -> Or a b

instantiate :: [String] -> Expr -> (Expr, Substitution)
instantiate vars (For x a) | x `occurs` a = do
  let y = newName vars x
  let (b, s) = instantiate (y : vars) (substitute [(x, Var y)] a)
  (b, (y, Var y) : s)
instantiate vars (For _ a) = instantiate vars a
instantiate vars (Meta _ a) = instantiate vars a
instantiate _ a = (a, [])

-- -- Core parser
-- type Parser a = P.Parser String a

-- parseEnv :: Parser Env
-- parseEnv = do
--   env <- P.zeroOrMore parseDef
--   _ <- P.endOfFile
--   return env

-- parseDef :: Parser (String, Expr)
-- parseDef = do
--   x <- parseName
--   _ <- P.spaces
--   _ <- P.char '='
--   _ <- P.spaces
--   a <- parseExpr
--   _ <- P.spaces
--   _ <- P.char '\n'
--   _ <- P.whitespaces
--   return (x, a)

-- parseName :: Parser String
-- parseName =
--   (P.oneOrMore . P.oneOf)
--     [ P.alphanumeric,
--       P.char '_',
--       P.char '-'
--     ]

-- parseExpr :: Parser Expr
-- parseExpr =
--   P.oneOf
--     [ Int <$> P.integer,
--       Num <$> P.number,
--       Tag <$> do
--         _ <- P.char ':'
--         parseName,
--       do
--         name <- parseName
--         let expr = case name of
--               "@IntT" -> IntT
--               "@NumT" -> NumT
--               "@Err" -> Err
--               x -> Var x
--         return expr,
--       do
--         _ <- P.char '('
--         tag <- parseName
--         _ <- P.spaces
--         expr <- case tag of
--           "@Ann" -> expr2 Ann parseExpr parseExpr
--           "@And" -> expr2 And parseExpr parseExpr
--           "@Or" -> expr2 Or parseExpr parseExpr
--           "@For" -> expr2 For parseName parseExpr
--           "@Fix" -> expr2 Fix parseName parseExpr
--           "@Fun" -> expr2 Fun parseExpr parseExpr
--           "@App" -> expr2 App parseExpr parseExpr
--           "@Call" -> do
--             f <- parseName
--             args <- P.zeroOrMore $ do
--               _ <- P.spaces
--               parseExpr
--             return (Call f args)
--           _ -> P.fail'
--         _ <- P.spaces
--         _ <- P.char ')'
--         return expr
--     ]
--   where
--     expr2 f p q = do
--       a <- p
--       _ <- P.spaces
--       f a <$> q
