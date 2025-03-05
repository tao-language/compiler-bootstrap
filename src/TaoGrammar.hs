module TaoGrammar where

import Control.Monad (void)
import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import Data.Char (chr, ord)
import Data.Function ((&))
import Data.List (delete, isPrefixOf, union, unionBy)
import Error
import qualified Grammar as G
import Location (Location (Location), Position (Pos), Range (Range))
import qualified Parser as P
import qualified PrettyPrint as PP
import Stdlib (split)

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
  | App Expr [(String, Expr)]
  | Call String [Expr]
  | Op1 Op1 Expr
  | Op2 Op2 Expr Expr
  | Match [Expr] [Case]
  | If Expr Expr Expr
  | Let (Pattern, Expr) Expr
  | Bind (Pattern, Expr) Expr
  | Record [(String, Expr)]
  | Select Expr [(String, Expr)]
  | With Expr [(String, Expr)]
  | Meta C.Metadata Expr
  | Err (Error Expr)
  deriving (Eq, Show)

-- instance Show Expr where
--   show :: Expr -> String
--   show = format 80

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

instance Show Op1 where
  show :: Op1 -> String
  show = \case
    Neg -> "-"

data Op2
  = Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge
  | Add
  | Sub
  | Mul
  | Div
  | DivI
  | Pow
  deriving (Eq)

instance Show Op2 where
  show :: Op2 -> String
  show = \case
    Eq -> "=="
    Ne -> "!="
    Lt -> "<"
    Le -> "<="
    Gt -> ">"
    Ge -> ">="
    Add -> "+"
    Sub -> "-"
    Mul -> "*"
    Div -> "/"
    DivI -> "//"
    Pow -> "^"

data Stmt
  = Import String String [(String, String)]
  | Def (Pattern, Expr)
  | TypeDef (String, [Expr], [(Expr, Maybe Type)])
  | Test UnitTest
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
  [ "and",
    "or",
    "xor",
    "if",
    "then",
    "else",
    "match",
    "type",
    "with"
  ]

string :: String -> Expr
string str = String [Str str]

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
    App fun kwargs -> App (f fun) (second f <$> kwargs)
    Call x args -> Call x (map f args)
    Op1 op a -> Op1 op (f a)
    Op2 op a b -> Op2 op (f a) (f b)
    Match args cases -> do
      let applyCase (xs, a, b) = (xs, f a, f b)
      Match (map f args) (map applyCase cases)
    If a b c -> If (f a) (f b) (f c)
    Let (a, b) c -> Let (f a, f b) (f c)
    Bind (a, b) c -> Bind (f a, f b) (f c)
    Record fields -> Record (second f <$> fields)
    Select a fields -> Select (f a) (second f <$> fields)
    With a fields -> With (f a) (second f <$> fields)
    Meta m a -> Meta m (f a)
    Err e -> Err (fmap f e)

dropMeta :: Expr -> Expr
dropMeta = \case
  Meta _ a -> dropMeta a
  a -> apply dropMeta a

collect :: (Expr -> [String]) -> Expr -> [String]
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
  For xs a -> filter (`notElem` xs) (f a)
  Fun a b -> f a `union` f b
  App fun kwargs -> f fun `union` unionMap (f . snd) kwargs
  Call x args -> unionMap f args
  Op1 op a -> f a
  Op2 op a b -> f a `union` f b
  Match args cases -> do
    let collectCase (xs, a, b) = f (For xs (Fun a b))
    unionMap f args `union` unionMap collectCase cases
  If a b c -> f a `union` f b `union` f c
  Let (a, b) c -> f a `union` f b `union` f c
  Bind (a, b) c -> f a `union` f b `union` f c
  Record fields -> unionMap (f . snd) fields
  Select a fields -> f a `union` unionMap (f . snd) fields
  With a fields -> f a `union` unionMap (f . snd) fields
  Meta m a -> f a
  Err e -> []
  where
    unionMap f = foldr (union . f) []

freeVars :: Expr -> [String]
freeVars = \case
  Var x -> [x]
  a -> collect freeVars a

freeTags :: Expr -> [String]
freeTags = \case
  Tag k [] -> [k]
  Tag k (a : args) -> freeTags a `union` freeTags (Tag k args)
  a -> collect freeTags a

freeNames :: Expr -> [String]
freeNames a = freeVars a `union` freeTags a

parse :: Int -> FilePath -> String -> Either (P.State String) (Expr, P.State String)
parse prec = P.parse (G.parse grammar prec)

format :: Int -> Expr -> String
format width = G.format grammar width "  "

grammar :: G.Grammar String Expr
grammar = do
  let withLoc start end = Meta (C.Loc (Location start.filename (Range start.pos end.pos)))
  let loc0 f location _ = Meta (C.Loc location) f
  let loc1 f location x = Meta (C.Loc location) (f x)
  let loc2 f location x y = Meta (C.Loc location) (f x y)
  G.Grammar
    { group = ("(", ")"),
      operators =
        [ -- Any _
          G.atom (loc0 Any) (P.word "_") $ \_ -> \case
            Any -> Just [PP.Text "_"]
            _ -> Nothing,
          -- IntT
          G.atom (loc0 IntT) (P.word "Int") $ \_ -> \case
            IntT -> Just [PP.Text "Int"]
            _ -> Nothing,
          -- NumT
          G.atom (loc0 NumT) (P.word "Num") $ \_ -> \case
            NumT -> Just [PP.Text "Num"]
            _ -> Nothing,
          -- Int
          G.atom (loc1 Int) P.integer $ \_ -> \case
            Int i -> Just [PP.Text $ show i]
            _ -> Nothing,
          -- Num
          G.atom (loc1 Num) P.number $ \_ -> \case
            Num n -> Just [PP.Text $ show n]
            _ -> Nothing,
          -- Char
          let parser _ = do
                start <- P.getState
                _ <- P.char 'c'
                quote <- P.oneOf [P.char '\'', P.char '"']
                ch <- P.anyChar
                _ <- P.char quote
                end <- P.getState
                _ <- P.spaces
                return (withLoc start end $ Char ch)
           in G.Atom parser $ \_ -> \case
                Char ch -> Just [PP.Text $ "c" ++ show ch]
                _ -> Nothing,
          -- Var
          G.atom (loc1 Var) parseNameVar $ \_ -> \case
            Var x -> Just [PP.Text x]
            _ -> Nothing,
          -- Tag
          let parser expr = do
                start <- P.getState
                k <- parseNameTag
                end <- P.getState
                _ <- P.spaces
                args <- P.zeroOrMore $ do
                  arg <- expr
                  _ <- P.spaces
                  return arg
                return (withLoc start end $ Tag k args)
           in G.Prefix 0 parser $ \layout -> \case
                Tag k args -> do
                  let layoutArg a = PP.Text " " : layout a
                  Just (PP.Text k : concatMap layoutArg args)
                _ -> Nothing,
          G.infixR 1 (loc2 Ann) ":" $ \case
            Ann a b -> Just (a, " ", b)
            _ -> Nothing,
          -- Tuple
          let parser expr = do
                start <- P.getState
                _ <- P.char '('
                _ <- P.whitespaces
                items <- collectionParser P.whitespaces expr
                _ <- P.whitespaces
                _ <- P.char ')'
                end <- P.getState
                _ <- P.spaces
                return (withLoc start end $ Tuple items)
           in G.Atom parser $ \layout -> \case
                Tuple items -> do
                  Just (PP.Text "(" : collectionLayout layout items ++ [PP.Text ")"])
                _ -> Nothing,
          -- List
          let parser expr = do
                start <- P.getState
                _ <- P.char '['
                _ <- P.whitespaces
                items <- collectionParser P.whitespaces expr
                _ <- P.whitespaces
                _ <- P.char ']'
                end <- P.getState
                _ <- P.spaces
                return (withLoc start end $ List items)
           in G.Atom parser $ \layout -> \case
                List items -> do
                  Just (PP.Text "[" : collectionLayout layout items ++ [PP.Text "]"])
                _ -> Nothing,
          -- String
          let parser expr = do
                start <- P.getState
                quote <- P.oneOf [P.char '\'', P.char '"']
                _ <- P.char quote
                end <- P.getState
                _ <- P.spaces
                let segments = []
                return (withLoc start end $ String segments)
           in G.Atom parser $ \layout -> \case
                String segments -> do
                  let layoutSegment = \case
                        Str s -> [PP.Text s]
                        Val a -> error "TODO: layout string interpolation"
                  Just ([PP.Text "'"] ++ concatMap layoutSegment segments ++ [PP.Text "'"])
                _ -> Nothing,
          -- Or
          G.infixL 1 (loc2 Or) "|" $ \case
            Or a b -> Just (a, " ", b)
            _ -> Nothing,
          -- For
          let parser expr = do
                start <- P.getState
                _ <- P.char '@'
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
                _ <- lineBreak
                _ <- P.whitespaces
                a <- expr
                _ <- P.spaces
                return (withLoc start end $ For xs a)
           in G.Prefix 1 parser $ \layout -> \case
                For xs a ->
                  Just (PP.Text ('@' : unwords xs ++ "; ") : layout a)
                _ -> Nothing,
          -- Fun
          G.infixR 1 (loc2 Fun) "->" $ \case
            Fun a b -> Just (a, " ", b)
            _ -> Nothing,
          -- App
          let parser x expr = do
                start <- P.getState
                _ <- P.char '('
                _ <- P.whitespaces
                args <- collectionParser P.whitespaces $ do
                  a <- expr
                  return ("", a)
                _ <- P.whitespaces
                _ <- P.char ')'
                end <- P.getState
                _ <- P.spaces
                return (withLoc start end $ App x args)
           in G.InfixL 1 parser $ \lhs rhs -> \case
                App fun args -> do
                  let layoutArg ("", a) = rhs a
                      layoutArg (x, a) = PP.Text (x ++ " = ") : rhs a
                  Just (lhs fun ++ PP.Text "(" : collectionLayout layoutArg args ++ [PP.Text ")"])
                _ -> Nothing,
          -- Call String [(String, Expr)]
          -- Op1 Op1 Expr
          -- Op2 Op2 Expr Expr
          -- Match [Expr] [Case]
          -- If Expr Expr Expr
          -- Let (Pattern, Expr) Expr
          -- Bind (Pattern, Expr) Expr
          -- Record [(String, Expr)]
          -- Select Expr [(String, Expr)]
          -- With Expr [(String, Expr)]
          -- Metadata Comments
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
          -- Metadata TrailingComment
          let parser x _expr = do
                _ <- P.char '#'
                _ <- P.spaces
                comment <- P.zeroOrMore (P.charIf (/= '\n'))
                _ <- P.whitespaces
                return (Meta (C.TrailingComment comment) x)
           in G.InfixL 1 parser $ \lhs _ -> \case
                Meta (C.TrailingComment comment) a ->
                  Just (lhs a ++ [PP.Text ("  # " ++ comment), PP.NewLine])
                _ -> Nothing,
          -- Metadata Location
          let parser expr = do
                _ <- P.text "!["
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
                Meta (C.Loc (Location filename (Range (Pos row1 col1) (Pos row2 col2)))) <$> expr
           in G.Atom parser $ \layout -> \case
                Meta (C.Loc _) a -> Just (layout a)
                _ -> Nothing,
          -- Err
          G.prefix 0 (loc1 $ Err . customError) "!error" $ \case
            Err (RuntimeError (CustomError a)) -> Just (" ", a)
            Err _ -> Just (" ", Any)
            _ -> Nothing
        ]
    }
  where
    collectionParser spaces expr =
      P.oneOf
        [ do
            a <- expr
            bs <- P.zeroOrMore $ do
              _ <- P.char ','
              _ <- spaces
              expr
            _ <- P.maybe' (P.char ',')
            return (a : bs),
          return []
        ]
    collectionLayout layout = \case
      [] -> []
      [a] -> layout a
      a : bs -> layout a ++ [PP.Text ", "] ++ collectionLayout layout bs

lowerExpr :: Expr -> C.Expr
lowerExpr = \case
  Any -> C.Any
  IntT -> C.IntT
  NumT -> C.NumT
  Int i -> C.Int i
  Num n -> C.Num n
  Char c -> C.tag "Char" [C.Int (ord c)]
  Var x -> C.Var x
  Tag k [] -> C.Tag k
  Tag k args -> lowerExpr (Tuple (Tag k [] : args))
  Ann a b -> C.Ann (lowerExpr a) (lowerExpr b)
  Tuple items -> C.and' (map lowerExpr items)
  List [] -> C.Tag "[]"
  List (a : bs) -> C.and' [C.Tag "::", lowerExpr a, lowerExpr (List bs)]
  String [] -> C.Tag "''"
  String segments -> error "TODO: lower String"
  Or a b -> C.Or (lowerExpr a) (lowerExpr b)
  -- For xs (For ys a) -> lowerExpr (For (xs ++ ys) a)
  For [] (Fun a b) -> C.Fun (lowerExpr a) (lowerExpr b)
  For [] a -> lowerExpr a
  For xs a -> C.for xs (lowerExpr (For [] a))
  Fun a b -> lowerExpr (For (freeVars a) (Fun a b))
  App fun args -> C.App (lowerExpr fun) (lowerExpr $ Tuple (map snd args))
  -- Call op args -> C.Call op (map lowerExpr args)
  -- Op1 op a -> lowerExpr (App (Var (show op)) a)
  -- Op2 op a b -> lowerExpr (app (Var (show op)) [a, b])
  Let (a, b) c -> case a of
    Var x | c == Var x -> lowerExpr b
    -- Var x -> C.App (lowerExpr (Fun a c)) (C.fix [x] (lowerExpr b))
    -- Ann (Or a1 a2) t -> lowerExpr (lets [(Ann a1 t, b), (Ann a2 t, b)] c)
    -- Ann (App a1 a2) t -> lowerExpr (Let (Ann a1 t, Fun a2 b) c)
    -- Ann (Op1 op a) t -> lowerExpr (Let (Ann (Var (show op)) t, Fun a b) c)
    -- Ann (Op2 op a1 a2) t -> lowerExpr (Let (Ann (Var (show op)) t, fun [a1, a2] b) c)
    -- Ann (Meta _ a) t -> lowerExpr (Let (Ann a t, b) c)
    -- Ann a t -> lowerExpr (Let (a, Ann b t) c)
    -- Or a1 a2 -> lowerExpr (lets [(a1, b), (a2, b)] c)
    -- App a1 a2 -> lowerExpr (Let (a1, Fun a2 b) c)
    -- Op1 op a -> lowerExpr (Let (Var (show op), Fun a b) c)
    -- Op2 op a1 a2 -> lowerExpr (Let (Var (show op), fun [a1, a2] b) c)
    -- For xs a -> lowerExpr (App (For xs (Fun a c)) b)
    -- Meta _ a -> lowerExpr (Let (a, b) c)
    -- a -> lowerExpr (App (Fun [("", a)] c) [("", b)])
    a -> error $ "TODO: lowerExpr " ++ show (Let (a, b) c)
  -- -- lowerExpr env (Bind (ts, p, a) b) = lowerExpr env (App (Trait a "<-") (Function [p] b))
  -- If a b c -> lowerExpr (Match [a] [([], [Tag "True"], b), ([], [], c)])
  -- Match args [(xs, ps, b)] -> lowerExpr (app (For xs $ fun ps b) args)
  -- Match args cases -> do
  --   let n = foldl max 0 (map (\(_, ps, _) -> length ps) cases)
  --   let rpad :: Int -> a -> [a] -> [a]
  --       rpad n x xs = xs ++ replicate (n - length xs) x
  --   let cases' = map (\(xs, ps, b) -> For xs $ fun (rpad n Any ps) b) cases
  --   let args' = map (\i -> Var ("$" ++ show i)) [length args + 1 .. n]
  --   let match' = fun args' (app (or' cases') (args ++ args'))
  --   -- let a = lowerExpr match'
  --   -- (error . intercalate "\n")
  --   --   [ show match',
  --   --     C.format (C.dropMeta a),
  --   --     C.format (C.dropMeta $ C.eval buildOps a),
  --   --     C.format (C.eval buildOps $ C.dropMeta a)
  --   --   ]
  --   lowerExpr match'
  -- Record fields -> do
  --   let k = '~' : intercalate "," (map fst fields)
  --   lowerExpr (tag k (map snd fields))
  -- Select a kvs -> do
  --   let sub = case a of
  --         Record fields -> map (second lowerExpr) fields
  --         a -> do
  --           let xs = freeVars (and' (map snd kvs))
  --           map (\x -> (x, C.App (C.Var x) (lowerExpr a))) xs
  --   let k = '~' : intercalate "," (map fst kvs)
  --   let args = map ((C.substitute sub . lowerExpr) . snd) kvs
  --   C.tag k args
  Meta m a -> C.Meta m (lowerExpr a)
  Err e -> C.Err (fmap lowerExpr e)
  a -> error $ "TODO: lowerExpr " ++ show a

liftExpr :: C.Expr -> Expr
liftExpr = \case
  C.Any -> Any
  C.Unit -> Tuple []
  C.IntT -> IntT
  C.NumT -> NumT
  C.Int i -> Int i
  C.Num n -> Num n
  C.Var x -> Var x
  C.Tag "~" -> Record []
  C.Tag "[]" -> List []
  C.Tag "''" -> String []
  C.Tag k -> Tag k []
  C.Ann a b -> Ann (liftExpr a) (liftExpr b)
  C.And (C.Tag "Char") (C.Int i) -> Char (chr i)
  C.And (C.Tag ('~' : names)) args -> do
    let keys = split ',' names
    let values = map liftExpr (C.andOf args)
    Record (zip keys values)
  C.And (C.Tag "::") (C.And a b) -> case (liftExpr a, liftExpr b) of
    (a, List bs) -> List (a : bs)
    (a, String segments) -> error "TODO: lift String"
    (a, b) -> Tag "::" [a, b]
  C.And (C.Tag k) args -> Tag k (map liftExpr (C.andOf args))
  C.And a bs -> Tuple (map liftExpr (a : C.andOf bs))
  C.Or a b -> Or (liftExpr a) (liftExpr b)
  C.For x a -> case liftExpr a of
    For xs a -> For (x : xs) a
    a -> For [x] a
  C.Fun a b -> Fun (liftExpr a) (liftExpr b)
  -- C.Fix x a
  --   | x `C.occurs` a -> Let (Var x, liftExpr a) (liftExpr a)
  --   | otherwise -> liftExpr a
  C.App a b -> case (liftExpr a, liftExpr b) of
    (fun, Ann (Tuple args) (Tuple targs)) ->
      App fun (zipWith (\a ta -> ("", Ann a ta)) args targs)
    (fun, arg) -> App fun [("", arg)]
  -- C.Call op args -> Call op (map liftExpr args)
  -- C.Let [] b -> liftExpr b
  -- C.Let ((x, b) : env) c -> Let (Var x, liftExpr b) (liftExpr (C.Let env c))
  C.Meta (C.Loc _) (C.Meta (C.Loc loc) a) -> Meta (C.Loc loc) (liftExpr a)
  C.Meta m a -> Meta m (liftExpr a)
  C.Err e -> Err (fmap liftExpr e)
  a -> error $ "TODO: liftExpr " ++ show a

lineBreak :: P.Parser String ()
lineBreak = do
  _ <- P.oneOf [P.char '\n', P.char ';']
  _ <- P.whitespaces
  return ()

parseNameVar :: P.Parser String String
parseNameVar =
  P.oneOf
    [ parseNameBase P.lowercase,
      parseNameEscaped,
      parseNameOp
    ]

parseNameBase :: P.Parser String Char -> P.Parser String String
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

parseNameEscaped :: P.Parser String String
parseNameEscaped = do
  _ <- P.char '`'
  name <- P.zeroOrMore $ do
    P.oneOf
      [ fmap (const '`') (P.text "\\`"),
        P.charIf (/= '`')
      ]
  _ <- P.char '`'
  return name

parseNameOp :: P.Parser String String
parseNameOp = do
  _ <- P.char '('
  _ <- P.whitespaces
  op <-
    P.oneOf
      [ P.word "and",
        P.word "or",
        P.word "xor",
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

parseNameTag :: P.Parser String String
parseNameTag =
  P.oneOf
    [ parseNameBase P.uppercase,
      P.paddedL (P.char '^') parseNameEscaped,
      parseNameOpTag
    ]

parseNameOpTag :: P.Parser String String
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

-- [ atom Var (P.oneOrMore P.letter) $ \_ -> \case
--     Var x -> Just [PP.Text x]
--     _ -> Nothing,
--   infixL 1 Add "+" $ \case
--     Add a b -> Just (a, b)
--     _ -> Nothing,
--   infixL 1 Sub "-" $ \case
--     Sub a b -> Just (a, b)
--     _ -> Nothing,
--   infixL 2 Mul "*" $ \case
--     Mul a b -> Just (a, b)
--     _ -> Nothing,
--   prefix 3 Neg "-" $ \case
--     Neg a -> Just a
--     _ -> Nothing,
--   infixR 4 Pow "^" $ \case
--     Pow a b -> Just (a, b)
--     _ -> Nothing,
--   suffix 5 Fac "!" $ \case
--     Fac a -> Just a
--     _ -> Nothing,
--   prefix 5 At "@" $ \case
--     At a -> Just a
--     _ -> Nothing
-- ]

eval :: Context -> FilePath -> Expr -> Expr
eval ctx path expr = do
  let (env, expr') = compile ctx path expr
  let result = C.eval runtimeOps (C.Let env expr')
  liftExpr result

bindings :: Expr -> [String]
bindings = \case
  Var x -> [x]
  -- For xs _ -> xs
  -- Ann a _ -> bindings a
  -- App a _ -> bindings a
  -- Op1 op _ -> [show op]
  -- Op2 op _ _ -> [show op]
  Meta _ a -> bindings a
  -- a -> freeVars a
  a -> error $ "TODO bindings " ++ show a

buildOps :: C.Ops
buildOps = do
  let call op f =
        (op, \eval args -> f (eval . C.dropTypes . C.dropMeta <$> args))
  let intOp1 op f = call op $ \case
        [C.Int x] -> Just (f x)
        _ -> Nothing
  let numOp1 op f = call op $ \case
        [C.Num x] -> Just (f x)
        _ -> Nothing
  let intOp2 op f = call op $ \case
        [C.Int x, C.Int y] -> Just (f x y)
        _ -> Nothing
  let numOp2 op f = call op $ \case
        [C.Num x, C.Num y] -> Just (f x y)
        _ -> Nothing
  [ intOp1 "int_neg" (\x -> C.Int (-x)),
    intOp2 "int_lt" (\x y -> C.Tag (if x < y then "True" else "False")),
    intOp2 "int_add" (\x y -> C.Int (x + y)),
    intOp2 "int_sub" (\x y -> C.Int (x - y)),
    intOp2 "int_mul" (\x y -> C.Int (x * y)),
    intOp2 "int_div" (\x y -> C.Num (fromIntegral x / fromIntegral y)),
    intOp2 "int_divi" (\x y -> C.Int (Prelude.div x y)),
    intOp2 "int_pow" (\x y -> C.Int (x ^ y)),
    numOp1 "num_neg" (\x -> C.Num (-x)),
    numOp2 "num_lt" (\x y -> C.Tag (if x < y then "True" else "False")),
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
      -- let resolveAlt (a, Just b) = Fun a b
      --     resolveAlt (a, Nothing) = Fun a (tag name' args)
      -- [(path, fun args (or' (map resolveAlt alts)))]
      error $ "TODO: resolve " ++ show stmt
    _ -> []

class Compile a where
  compile :: Context -> FilePath -> a -> (C.Env, C.Expr)

instance Compile Expr where
  compile :: Context -> FilePath -> Expr -> (C.Env, C.Expr)
  compile ctx path expr =
    compile ctx path (C.newName (freeVars expr) "", expr)

instance Compile (String, Expr) where
  compile :: Context -> FilePath -> (String, Expr) -> (C.Env, C.Expr)
  compile ctx path (name, expr) = do
    let dependencies = delete name (freeNames expr)
    let env = concatMap (fst . compile ctx path) dependencies
    let ((a, t), s) = C.infer buildOps env (lowerExpr expr)
    let xs = filter (`notElem` map fst env) (map fst s)
    (env, C.Ann (C.for xs a) t)

instance Compile String where
  compile :: Context -> FilePath -> String -> (C.Env, C.Expr)
  compile ctx path name = do
    let compileDef :: (FilePath, Expr) -> (C.Env, [C.Expr]) -> (C.Env, [C.Expr])
        compileDef (path, alt) (env, alts) = do
          let (env', alt') = compile ctx path (name, alt)
          (unionBy (\a b -> fst a == fst b) env' env, C.let' env' alt' : alts)
    let (env, alts) = foldr compileDef ([], []) (resolve ctx path name)
    let def = case alts of
          [] -> []
          [C.Var x] | x == name -> [(name, C.Var x)]
          [C.Ann (C.Var x) t] | x == name -> [(name, C.Ann (C.Var x) t)]
          alts -> [(name, C.fix [name] (C.or' alts))]
    let env' = unionBy (\a b -> fst a == fst b) def env
    (env', C.Var name)
