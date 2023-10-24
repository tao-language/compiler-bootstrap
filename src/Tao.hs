{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Tao where

import qualified Core as C
import Data.Bifunctor (Bifunctor (second))

{- TODO: syntax sugar
- Match
- Let
- Do
- Char
- Maybe
- Tuple
- Record
- Text
- List
- Set
- Dict
- From
- Until
- Range
- IfElse
- Vector
- Matrix
- Tensor
- List comprehension
- Set comprehension
- Dict comprehension
-}

data Pattern
  = PAny
  | PKnd
  | PIntT
  | PNumT
  | PInt !Int
  | PTag !String
  | PVar !String
  | PTuple ![Pattern]
  | PRecord ![(String, Pattern)]
  | PFun !Pattern !Pattern
  | PApp !Pattern !Pattern
  | PMeta ![C.Metadata] !Pattern
  deriving (Eq, Show)

data Expr
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Tag !String
  | Var !String
  | Lam !Pattern !Expr
  | Tuple ![Expr]
  | Record ![(String, Expr)]
  | Block ![Statement] !Expr
  | App !Expr !Expr
  | Fun !Expr !Expr
  | Or !Expr !Expr
  | Eq !Expr !Expr
  | Lt !Expr !Expr
  | Add !Expr !Expr
  | Sub !Expr !Expr
  | Mul !Expr !Expr
  | Pow !Expr !Expr
  | Ann !Expr !Type
  | Meta ![C.Metadata] !Expr
  deriving (Eq, Show)

data Type
  = For ![String] !Expr
  deriving (Eq, Show)

data DocString = DocString
  { public :: Bool,
    description :: String
  }
  deriving (Eq, Show)

newDocString :: DocString
newDocString = DocString {public = False, description = ""}

data Statement
  = LetDef
      { docs :: Maybe DocString,
        name :: String,
        type' :: Maybe Type,
        rules :: [([Pattern], Expr)],
        meta :: [C.Metadata]
      }
  | Unpack
      { docs :: Maybe DocString,
        types :: [(String, Type)],
        pattern :: Pattern,
        value :: Expr,
        meta :: [C.Metadata]
      }
  | TypeDef
      { docs :: Maybe DocString,
        name :: String,
        args :: [Expr],
        alts :: (String, Type),
        meta :: [C.Metadata]
      }
  | Import
      { path :: String,
        name :: String,
        exposing :: [String],
        meta :: [C.Metadata]
      }
  | Prompt
      { description :: String,
        expression :: Expr,
        result :: Maybe Expr,
        meta :: [C.Metadata]
      }
  deriving (Eq, Show)

-- TODO: remove imports, handle them at `loadModule`
data Module = Module
  { name :: String,
    docs :: Maybe DocString,
    body :: [Statement]
  }
  deriving (Eq, Show)

data ParserContext
  = CStatement
  | CEndOfFile
  deriving (Eq, Show)

fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

lam :: [Pattern] -> Expr -> Expr
lam ps b = foldr Lam b ps

app :: Expr -> [Expr] -> Expr
app = foldl App

ann :: Expr -> Expr -> Expr
ann a t = Ann a (For [] t)

pApp :: Pattern -> [Pattern] -> Pattern
pApp = foldl PApp

toCoreP :: [String] -> Pattern -> C.Pattern
toCoreP fvs PAny = C.PVar (C.newName fvs "_")
toCoreP _ PKnd = C.PKnd
toCoreP _ PIntT = C.PIntT
toCoreP _ PNumT = C.PNumT
toCoreP _ (PInt i) = C.PInt i
toCoreP _ (PTag k) = C.PTag k
toCoreP _ (PVar x) = C.PVar x
toCoreP fvs (PTuple ps) = toCoreP fvs (pApp (PTag "()") ps)
toCoreP fvs (PRecord fields) = C.PRec (second (toCoreP fvs) <$> fields)
toCoreP fvs (PFun p q) = C.PFun (toCoreP fvs p) (toCoreP fvs q)
toCoreP fvs (PApp p q) = C.PApp (toCoreP fvs p) (toCoreP fvs q)
toCoreP fvs (PMeta m p) = C.PMeta m (toCoreP fvs p)

toCore :: Expr -> C.Expr
toCore Knd = C.Knd
toCore IntT = C.IntT
toCore NumT = C.NumT
toCore (Int i) = C.Int i
toCore (Num n) = C.Num n
toCore (Tag k) = C.Tag k
toCore (Var x) = C.Var x
toCore (Lam p b) = do
  let b' = toCore b
  C.Lam (toCoreP (C.freeVars b') p) b'
toCore (Tuple items) = toCore (app (Tag "()") items)
toCore (Record fields) = C.Rec (second toCore <$> fields)
toCore (Block defs b) = error "TODO: toCore Block"
toCore (App a b) = C.App (toCore a) (toCore b)
toCore (Fun a b) = C.Fun (toCore a) (toCore b)
toCore (Or a b) = C.Or (toCore a) (toCore b)
toCore (Eq a b) = C.eq (toCore a) (toCore b)
toCore (Lt a b) = C.lt (toCore a) (toCore b)
toCore (Add a b) = C.add (toCore a) (toCore b)
toCore (Sub a b) = C.sub (toCore a) (toCore b)
toCore (Mul a b) = C.mul (toCore a) (toCore b)
toCore (Pow a b) = C.pow (toCore a) (toCore b)
toCore (Ann a (For xs t)) = C.Ann (toCore a) (C.For xs $ toCore t)
toCore (Meta m a) = C.Meta m (toCore a)
