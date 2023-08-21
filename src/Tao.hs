module Tao where

import qualified Core as C
import Data.Bifunctor (second)
import Data.Char (isUpper)
import Data.List (delete, foldl', union)

{-
Syntax sugar (https://en.wikibooks.org/wiki/Haskell/Syntactic_sugar)
  - Do notation
  - Where definitions
  - Case and Match
  - Infix operators (x `op` y)
  - Partial operators (+ x) (y -)
  - IfElse
  - Char
  - Maybe
  - Tuple
  - Record
  - List
  - String
  - Set
  - Dict
  - Vector
  - Matrix
  - Tensor
  - List sequence [1..n] [1..] [1, 3..] ['a'..'z']
  - List comprehension
  - Unnamed Union types
  - Unnamed Record types
-}

-- data Expr
--   = Int !Int
--   | Num !Double
--   | Var !String
--   | For !String !Expr
--   | Fun !Expr !Expr
--   | App !Expr !Expr
--   | Ann !Expr !Type
--   | Let ![Definition] !Expr
--   | Ctr !String ![Expr]
--   | Case !Expr ![(String, Expr)] !Expr
--   | CaseI !Expr ![(Int, Expr)] !Expr
--   | Match ![Branch]
--   | Op !String ![Expr]
--   | Op2 !BinaryOp !Expr !Expr
--   deriving (Eq, Show)

-- data BinaryOp
--   = Eq
--   | Lt
--   | Add
--   | Sub
--   | Mul
--   deriving (Eq)

-- instance Show BinaryOp where
--   show Eq = "=="
--   show Lt = "<"
--   show Add = "+"
--   show Sub = "-"
--   show Mul = "*"

-- data Pattern
--   = AnyP
--   | VarP !String
--   | IntP !Int
--   | CtrP !String ![Pattern]
--   deriving (Eq, Show)

-- type Type = Expr

-- data Branch
--   = Br ![Pattern] !Expr
--   deriving (Eq, Show)

-- data Definition
--   = Untyped !String !Expr
--   | Typed !String !Type !Expr
--   | Unpack !Pattern ![(String, Type)] !Expr
--   deriving (Eq, Show)

-- data ContextDefinition
--   = UnionType !String ![(String, Type)] ![(String, Type)]
--   | Value !Definition
--   deriving (Eq, Show)

-- type Context = [ContextDefinition]

-- data CompileError
--   = EmptyMatch
--   | MatchMissingArgs !Expr
--   | NotAUnionAlt !String !Expr
--   | TypeError !C.TypeError
--   | UndefinedCtrField !String !String
--   | UndefinedUnionAlt !String
--   | UndefinedUnionType !String
--   deriving (Eq, Show)

-- nameType :: String
-- nameType = "Type"

-- nameIntType :: String
-- nameIntType = "Int"

-- nameNumType :: String
-- nameNumType = "Num"

-- lam :: [String] -> Expr -> Expr
-- lam xs a = Match [Br (map VarP xs) a]

-- for :: [String] -> Expr -> Expr
-- for xs a = foldr For a xs

-- app :: Expr -> [Expr] -> Expr
-- app = foldl' App

-- asApp :: Expr -> (Expr, [Expr])
-- asApp (App a b) = second (++ [b]) (asApp a)
-- asApp a = (a, [])

-- fun :: [Expr] -> Expr -> Expr
-- fun args b = foldr Fun b args

-- match :: [Branch] -> Expr
-- match (Br [] a : _) = a
-- match brs = Match brs

-- typeVars :: Type -> [String]
-- typeVars (Var (ch : _)) | isUpper ch = []
-- typeVars (Var x) = [x]
-- typeVars (For x a) = x : typeVars a
-- typeVars (Fun a b) = typeVars a `union` typeVars b
-- typeVars (App a b) = foldr (union . typeVars) [] (snd (asApp (App a b)))
-- typeVars (Ann a _) = typeVars a
-- typeVars (Let [] a) = typeVars a
-- typeVars (Let ((Untyped x _) : defs) a) = delete x (typeVars (Let defs a))
-- typeVars (Let ((Typed x _ _) : defs) a) = delete x (typeVars (Let defs a))
-- typeVars (Ctr _ args) = foldr (union . typeVars) [] args
-- typeVars (Op _ args) = foldr (union . typeVars) [] args
-- typeVars (Op2 _ a b) = typeVars a `union` typeVars b
-- typeVars _ = []

-- toCore :: Expr -> Either CompileError C.Expr
-- toCore (Int i) = Right (C.Int i)
-- toCore (Num n) = Right (C.Num n)
-- toCore (Var "Type") = Right C.Knd
-- toCore (Var "Int") = Right C.IntT
-- toCore (Var "Num") = Right C.NumT
-- toCore (Var x) = Right (C.Var x)
-- -- toCore (For x a) = do
-- --   a <- toCore a
-- --   Right (C.For x a)
-- -- toCore (Fun a b) = do
-- --   a <- toCore a
-- --   b <- toCore b
-- --   Right (C.Fun a b)
-- toCore (App a b) = do
--   a <- toCore a
--   b <- toCore b
--   Right (C.App a b)
-- -- toCore (Ann a b) = do
-- --   a <- toCore a
-- --   b <- toCore b
-- --   Right (C.Ann a b)
-- toCore (Let defs a) = do
--   defs <- mapM toCoreDefs defs
--   a <- toCore a
--   Right (C.Let (concat defs) a)
-- toCore (Ctr k args) = do
--   args <- mapM toCore args
--   Right (C.Ctr "TODO" k args)

-- -- toCore (Case a cases c) = do
-- --   a <- toCore a
-- --   cases <- mapM toCoreSecond cases
-- --   c <- toCore c
-- --   Right (C.Case a cases c)
-- -- toCore (CaseI a cases c) = do
-- --   a <- toCore a
-- --   cases <- mapM toCoreSecond cases
-- --   c <- toCore c
-- --   Right (C.CaseI a cases c)
-- -- toCore (Match branches) = do
-- --   branches <- mapM toCoreBranch branches
-- --   case C.match branches of
-- --     Right expr -> Right expr
-- --     Left err -> Left (TypeError err)
-- -- toCore (Op op args) = do
-- --   args <- mapM toCore args
-- --   Right (C.Op op args)
-- -- toCore (Op2 op a b) = do
-- --   a <- toCore a
-- --   b <- toCore b
-- --   Right (C.Op (show op) [a, b])

-- toCoreSecond :: (a, Expr) -> Either CompileError (a, C.Expr)
-- toCoreSecond (k, b) = do
--   b <- toCore b
--   Right (k, b)

-- toCoreDefs :: Definition -> Either CompileError C.Env
-- toCoreDefs (Untyped x a) = do
--   a <- toCore a
--   Right [(x, a)]
-- -- toCoreDefs (Typed x t a) = do
-- --   t <- toCore t
-- --   a <- toCore a
-- --   Right [(x, C.Ann a t)]
-- toCoreDefs (Unpack p ts a) = do
--   let unpackVar x = do
--         let value = App (match [Br [p] (Var x)]) a
--         case lookup x ts of
--           Just type' -> (x, Ann value type')
--           Nothing -> (x, value)
--   mapM (toCoreSecond . unpackVar) (bindings p)

-- bindings :: Pattern -> [String]
-- bindings AnyP = []
-- bindings (IntP _) = []
-- bindings (VarP x) = [x]
-- bindings (CtrP _ ps) = concatMap bindings ps

-- -- toCoreBranch :: Branch -> Either CompileError C.Branch
-- -- toCoreBranch (Br ps b) = do
-- --   b <- toCore b
-- --   Right (C.Br (map toCorePattern ps) b)

-- -- toCorePattern :: Pattern -> C.Pattern
-- -- toCorePattern AnyP = C.VarP ""
-- -- toCorePattern (VarP x) = C.VarP x
-- -- toCorePattern (IntP i) = C.IntP i
-- -- toCorePattern (CtrP k ps) = C.CtrP "TODO" k (map toCorePattern ps)

-- toCoreSymbols :: Definition -> Either CompileError C.Env
-- toCoreSymbols (Untyped x a) = Right []
-- toCoreSymbols (Typed x t a) = Right []
-- toCoreSymbols (Unpack p ts a) = Right []

-- toCoreContext :: [Definition] -> Either CompileError C.Env
-- toCoreContext [] = Right []
-- toCoreContext (def : defs) = do
--   ctx1 <- toCoreSymbols def
--   ctx2 <- toCoreContext defs
--   Right (ctx1 ++ ctx2)

-- fromCore :: C.Expr -> Expr
-- fromCore C.Knd = Var nameType
-- fromCore C.IntT = Var nameIntType
-- fromCore C.NumT = Var nameNumType
-- fromCore (C.Int i) = Int i
-- fromCore (C.Num n) = Num n
-- fromCore (C.Var x) = Var x
-- -- TODO: Lam
-- -- fromCore (C.For x a) = For x (fromCore a)
-- -- fromCore (C.Fun a b) = Fun (fromCore a) (fromCore b)
-- fromCore (C.App a b) = App (fromCore a) (fromCore b)
-- -- fromCore (C.Ann a b) = Ann (fromCore a) (fromCore b)
-- fromCore (C.Let defs a) = Let (map (\(x, b) -> Untyped x (fromCore b)) defs) (fromCore a)
-- fromCore (C.Fix x a) = Let [Untyped x (fromCore a)] (Var x)
-- fromCore (C.Ctr tx k args) = Ctr k (map fromCore args)

-- -- fromCore (C.Case a cases c) = Case (fromCore a) (map (second fromCore) cases) (fromCore c)
-- -- fromCore (C.CaseI a cases c) = CaseI (fromCore a) (map (second fromCore) cases) (fromCore c)
-- -- fromCore (C.Op "==" [a, b]) = Op2 Eq (fromCore a) (fromCore b)
-- -- fromCore (C.Op "<" [a, b]) = Op2 Lt (fromCore a) (fromCore b)
-- -- fromCore (C.Op "+" [a, b]) = Op2 Add (fromCore a) (fromCore b)
-- -- fromCore (C.Op "-" [a, b]) = Op2 Sub (fromCore a) (fromCore b)
-- -- fromCore (C.Op "*" [a, b]) = Op2 Mul (fromCore a) (fromCore b)
-- -- fromCore (C.Op op args) = Op op (map fromCore args)

-- eval :: [Definition] -> Expr -> Either CompileError (Expr, Type)
-- eval defs a = do
--   ctx <- toCoreContext defs
--   a <- toCore a
--   case C.infer ctx a of
--     Right (t, _) -> do
--       let b = C.eval ctx a
--       Right (fromCore b, fromCore t)
--     Left err -> Left (TypeError err)
