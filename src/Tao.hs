{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module Tao where

import Core (Comment (..), Env, Error (..), Metadata (..))
import qualified Core as C
import Data.Bifunctor (Bifunctor (second))
import Flow ((|>))

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

-- data Pattern
--   = PAny
--   | PKnd
--   | PIntT
--   | PNumT
--   | PInt Int
--   | PTag String
--   | PVar String
--   | PTuple [Pattern]
--   | PRecord [(String, Pattern)]
--   | PFun Pattern Pattern
--   | PApp Pattern Pattern
--   | PMeta [Metadata] Pattern
--   | PErr Error
--   deriving (Eq, Show)

data Expr
  = Knd
  | IntT
  | NumT
  | Int Int
  | Num Double
  | Tag String
  | Var String
  | Tuple [Expr]
  | Record [(String, Expr)]
  | Trait Expr String
  | Lam Expr Expr
  | Block [Statement] Expr
  | App Expr Expr
  | Fun Expr Expr
  | Or Expr Expr
  | Eq Expr Expr
  | Lt Expr Expr
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Pow Expr Expr
  | Ann Expr Type
  | Meta Metadata Expr
  | Err Error
  deriving (Eq, Show)

data Type
  = For [String] Expr
  deriving (Eq, Show)

data Statement
  = LetDef
      { docs :: Maybe DocString,
        types :: Maybe Expr,
        binding :: Expr,
        value :: Expr
      }
  | Import
      { path :: String,
        alias :: Maybe String,
        exposing :: [String]
      }
  | Prompt
      { expression :: Expr,
        result :: Maybe Expr
      }
  deriving (Eq, Show)

-- letDef :: String -> Expr -> Statement
-- letDef name value =
--   LetDef
--     { docs = Nothing,
--       type' = Nothing,
--       name = name,
--       value = value
--     }

-- letTrait :: Pattern -> String -> Expr -> Statement
-- letTrait self name value =
--   LetTrait
--     { docs = Nothing,
--       name = name,
--       typeVars = [],
--       self = self,
--       returns = Nothing,
--       value = value
--     }

-- letType :: String -> [Expr] -> [(String, Type)] -> Statement
-- letType name args alts =
--   LetType
--     { docs = Nothing,
--       name = name,
--       args = args,
--       alts = alts
--     }

-- unbox :: Pattern -> Expr -> Statement
-- unbox pattern value =
--   Unbox
--     { docs = Nothing,
--       types = [],
--       pattern = pattern,
--       value = value
--     }

import' :: String -> Statement
import' path =
  Import
    { path = path,
      alias = Nothing,
      exposing = []
    }

prompt :: Expr -> Statement
prompt expr =
  Prompt
    { expression = expr,
      result = Nothing
    }

-- TODO: remove imports, handle them at `loadModule`
data Module = Module
  { name :: String,
    docs :: Maybe DocString,
    stmts :: [Statement]
  }
  deriving (Eq, Show)

newModule :: Module
newModule = Module {name = "", docs = Nothing, stmts = []}

data DocString = DocString
  { public :: Bool,
    description :: String,
    meta :: [Metadata]
  }
  deriving (Eq, Show)

newDocString :: DocString
newDocString =
  DocString
    { public = True,
      description = "",
      meta = []
    }

data ParserContext
  = CDocString
  | CExpression
  | CLetDef
  | CLetDefTyped String
  | CLetDefTypedVar String
  | CLetDefUntyped String
  | COperator String
  | CPAny
  | CParentheses
  | CPrompt
  | CRecordField String
  | CTrait
  | CTuple
  | CLetType
  | CTODO -- TODO: REMOVE THIS
  deriving (Eq, Show)

fun :: [Expr] -> Expr -> Expr
fun bs b = foldr Fun b bs

-- lam :: [Pattern] -> Expr -> Expr
-- lam ps b = foldr Lam b ps

app :: Expr -> [Expr] -> Expr
app = foldl App

ann :: Expr -> Expr -> Expr
ann a t = Ann a (For [] t)

or' :: [Expr] -> Expr
or' [] = error "`or'` must have at least one expression"
or' [a] = a
or' (a : bs) = Or a (or' bs)

-- pApp :: Pattern -> [Pattern] -> Pattern
-- pApp = foldl PApp

asFun :: Expr -> ([Expr], Expr)
asFun (Fun a1 a2) = let (bs, b) = asFun a2 in (a1 : bs, b)
asFun (Meta _ a) = asFun a
asFun a = ([], a)

asApp :: Expr -> (Expr, [Expr])
asApp (App a b) = let (a', bs) = asApp a in (a', bs ++ [b])
asApp a = (a, [])

meta :: [Metadata] -> Expr -> Expr
meta ms b = foldr Meta b ms

-- let' :: (Pattern, Expr) -> Expr -> Expr
-- let' (p, a) b = App (Lam p b) a

-- lets :: [(Pattern, Expr)] -> Expr -> Expr
-- lets defs b = foldr let' b defs

-- lamMatch :: [([Pattern], Expr)] -> Expr
-- lamMatch [] = Err NotImplementedError
-- lamMatch (([], b) : _) = b
-- lamMatch [(ps, b)] = lam ps b
-- lamMatch rules = LamMatch rules

-- lamMatchArgs :: String -> [([Pattern], Expr)] -> [String]
-- lamMatchArgs _ [] = []
-- lamMatchArgs x rules@((ps, _) : _) = do
--   let freeVars = C.freeVars (toCore [] $ lamMatch rules)
--   take (length ps) (C.newNames (x : freeVars) x)

-- toCoreP :: [String] -> Pattern -> C.Pattern
-- toCoreP fvs PAny = C.PVar (C.newName fvs "_")
-- toCoreP _ PKnd = C.PKnd
-- toCoreP _ PIntT = C.PIntT
-- toCoreP _ PNumT = C.PNumT
-- toCoreP _ (PInt i) = C.PInt i
-- toCoreP _ (PTag k) = C.PTag k
-- toCoreP _ (PVar x) = C.PVar x
-- toCoreP fvs (PTuple ps) = toCoreP fvs (pApp (PTag "()") ps)
-- -- toCoreP fvs (PRecord fields) = C.PRec (second (toCoreP fvs) <$> fields)
-- toCoreP fvs (PFun p q) = C.PFun (toCoreP fvs p) (toCoreP fvs q)
-- toCoreP fvs (PApp p q) = C.PApp (toCoreP fvs p) (toCoreP fvs q)
-- toCoreP fvs (PMeta m p) = C.PMeta m (toCoreP fvs p)
-- toCoreP fvs a = error $ "TODO: toCoreP " ++ show a

toCore :: Env -> Expr -> C.Expr
toCore _ Knd = C.Knd
toCore _ IntT = C.IntT
toCore _ NumT = C.NumT
toCore _ (Int i) = C.Int i
toCore _ (Num n) = C.Num n
toCore _ (Tag k) = C.Tag k
toCore _ (Var x) = C.Var x
-- toCore env (Lam p b) = do
--   let b' = toCore env b
--   C.Lam (toCoreP (C.freeVars b') p) b'
-- toCore env (LamMatch rules) = toCore env (or' $ map (uncurry lam) rules)
-- toCore env (Match args rules) = toCore env (app (LamMatch rules) args)
toCore env (Tuple items) = toCore env (app (Tag "()") items)
-- toCore (Record fields) = C.Rec (second toCore <$> fields)
toCore env (Block defs b) = error "TODO: toCore Block"
toCore env (Trait a x) = do
  let a' = toCore env a
  let (ta, _) = C.infer [] a'
  C.app (C.Var x) [ta, a']
toCore env (App a b) = C.App (toCore env a) (toCore env b)
-- toCore env (Fun a b) = C.Fun (toCore env a) (toCore env b)
toCore env (Or a b) = C.Or (toCore env a) (toCore env b)
toCore env (Eq a b) = C.eq (toCore env a) (toCore env b)
toCore env (Lt a b) = C.lt (toCore env a) (toCore env b)
toCore env (Add a b) = C.add (toCore env a) (toCore env b)
toCore env (Sub a b) = C.sub (toCore env a) (toCore env b)
toCore env (Mul a b) = C.mul (toCore env a) (toCore env b)
toCore env (Pow a b) = C.pow (toCore env a) (toCore env b)
-- toCore env (Ann a (For xs t)) = C.Ann (toCore env a) (C.For xs $ toCore env t)
toCore env (Meta m a) = C.Meta m (toCore env a)
toCore env (Err e) = C.Err e
toCore env a = error $ "TODO: toCore " ++ show a

-- fromCoreP :: C.Pattern -> Pattern
-- -- PKnd
-- fromCoreP C.PIntT = PIntT
-- -- PNumT
-- -- PInt Int
-- -- PTag String
-- fromCoreP (C.PVar x) = PVar x
-- -- PFun Pattern Pattern
-- -- PApp Pattern Pattern
-- -- PMeta [Metadata] Pattern
-- fromCoreP p = error $ "TODO: fromCoreP " ++ show p

fromCore :: C.Expr -> Expr
-- fromCore (Knd) = _
fromCore C.IntT = IntT
-- fromCore (NumT) = _
fromCore (C.Int i) = Int i
-- fromCore (Num Double) = _
-- fromCore (Tag String) = _
fromCore (C.Var x) = Var x
-- fromCore (Ann Expr Type) = _
-- fromCore (C.Lam p b) = Lam (fromCoreP p) (fromCore b)
-- fromCore (Fix String Expr) = _
-- fromCore (Fun Expr Expr) = _
-- fromCore (Or Expr Expr) = _
fromCore (C.App a b) = App (fromCore a) (fromCore b)
-- fromCore (Typ String [String]) = _
-- fromCore (Op1 UnaryOp Expr) = _
-- fromCore (Op2 BinaryOp Expr Expr) = _
fromCore (C.Meta meta a) = Meta meta (fromCore a)
-- fromCore (Err Error) = _
fromCore (C.Err e) = Err e
fromCore a = error $ "fromCore: not implemented: " ++ show a

-- matches :: Pattern -> Pattern -> Bool
-- matches PAny _ = True
-- matches PKnd PKnd = True
-- matches PIntT PIntT = True
-- matches PNumT PNumT = True
-- matches (PInt i) (PInt i') = i == i'
-- matches (PTag k) (PTag k') = k == k'
-- matches (PVar _) (PVar _) = True
-- --  PTuple [Pattern]
-- --  PRecord [(String, Pattern)]
-- matches (PFun p q) (PFun p' q') = matches p p' && matches q q'
-- matches (PApp p q) (PApp p' q') = matches p p' && matches q q'
-- --  PMeta [Metadata] Pattern
-- --  PErr Error
-- matches _ _ = False

-- findTraits :: Pattern -> [Statement] -> [Statement]
-- findTraits _ [] = []
-- findTraits p (stmt@LetTrait {self} : stmts) | matches p self = stmt : findTraits p stmts
-- findTraits p (_ : stmts) = findTraits p stmts

-- define :: ([(Pattern, Expr)], Expr) -> Statement -> ([(Pattern, Expr)], Expr)
-- define (defs, expr) LetDef {type', name, value} = case type' of
--   Just typ -> ((PVar name, Ann value typ) : defs, expr)
--   Nothing -> ((PVar name, value) : defs, expr)
-- define (defs, expr) LetPat {types, pattern, value} =
--   ((pattern, value) : defs, expr)
-- -- define (defs, expr) LetTrait {name, typeVars, self, returns, value} = case returns of
-- --   Just returns -> ((PVar name, Lam self $ ann value returns) : defs, expr)
-- --   Nothing -> ((PVar name, Lam self value) : defs, expr)
-- -- define (defs, expr) Unbox {types, pattern, value} = do
-- --   (defs, App (Trait value "*=") (Lam pattern expr))
-- -- define (defs, expr) Import {path, name, exposing} = do
-- --   define (defs, expr) (unbox)
-- -- define' Import {path, name, exposing, meta} expr = do
-- --   let import' =
-- --         Unbox
-- --           { docs = Nothing,
-- --             types = [],
-- --             pattern = PVar name,
-- --             value = app (Var "import-module") [Var path],
-- --             meta = meta
-- --           }
-- --   define' import' expr
-- -- \| LetType
-- --     { docs :: Maybe DocString,
-- --       name :: String,
-- --       args :: [Expr],
-- --       alts :: [(String, Type)],
-- --       meta :: [Metadata]
-- --     }
-- -- \| Prompt
-- --     { expression :: Expr,
-- --       result :: Maybe Expr,
-- --       meta :: [Metadata]
-- --     }
-- define (defs, expr) stmt = error $ "TODO: define'" ++ show stmt

-- moduleToCore :: Module -> C.Env
-- moduleToCore Module {stmts} = foldl stmtToCore [] stmts

-- toEnv :: [(Pattern, Expr)] -> Env
-- toEnv [] = []
-- -- PAny
-- -- PKnd
-- -- PIntT
-- -- PNumT
-- -- PInt Int
-- -- PTag String
-- toEnv ((PVar x, a) : defs) = (x, toCore [] a) : toEnv defs
-- -- PTuple [Pattern]
-- -- PRecord [(String, Pattern)]
-- -- PFun Pattern Pattern
-- -- PApp Pattern Pattern
-- -- PMeta [Metadata] Pattern
-- -- PErr Error
-- toEnv ((p, a) : defs) = error $ "TODO: toEnv " ++ show p

-- eval :: Module -> Expr -> Expr
-- eval mod expr = do
--   let (defs, expr') = foldl define ([], expr) mod.stmts
--   let env = toEnv defs
--   toCore env expr'
--     |> C.eval env
--     |> fromCore

-- stmtToCore :: C.Env -> Statement -> C.Env
-- stmtToCore env LetDef {type', name, value, meta} = case type' of
--   Just typ -> (name, toCore $ Ann (Meta meta value) typ) : env
--   Nothing -> (name, toCore $ Meta meta value) : env
-- -- stmtToCore LetPat {types, pattern, value, meta} env = (pattern, value) : env
-- --    TODO: list all names, then stmtToCore each with LetDef
-- stmtToCore env Trait {name, self, returns, value, meta} = do
--   let impl = toCore $ Meta meta $ Lam self (Ann value returns)
--   case lookup name env of
--     Just def -> (name, def `C.Or` impl) : env
--     Nothing -> (name, impl) : env
-- -- stmtToCore' Unbox {types, pattern, value, meta} expr = do
-- --   app (Var "*=") [Lam pattern expr, value]
-- -- stmtToCore' Import {path, name, exposing, meta} expr = do
-- --   let import' =
-- --         Unbox
-- --           { docs = Nothing,
-- --             types = [],
-- --             pattern = PVar name,
-- --             value = app (Var "import-module") [Var path],
-- --             meta = meta
-- --           }
-- --   stmtToCore' import' expr
-- -- \| LetType
-- --     { docs :: Maybe DocString,
-- --       name :: String,
-- --       args :: [Expr],
-- --       alts :: [(String, Type)],
-- --       meta :: [Metadata]
-- --     }
-- -- \| Prompt
-- --     { expression :: Expr,
-- --       result :: Maybe Expr,
-- --       meta :: [Metadata]
-- --     }
-- stmtToCore env stmt = error $ "TODO: stmtToCore'" ++ show stmt

-- define' :: Statement -> Expr -> Expr
-- define' LetDef {type', name, value, meta} expr = case type' of
--   Just typ -> let' (PVar name, Ann value typ) expr
--   Nothing -> let' (PVar name, value) expr
-- define' LetPat {types, pattern, value, meta} expr = do
--   let' (pattern, value) expr
-- define' Trait {typeVars, self, returns, value, meta} expr = error "TODO"
-- define' Unbox {types, pattern, value, meta} expr = do
--   app (Var "*=") [Lam pattern expr, value]
-- define' Import {path, name, exposing, meta} expr = do
--   let import' =
--         Unbox
--           { docs = Nothing,
--             types = [],
--             pattern = PVar name,
--             value = app (Var "import-module") [Var path],
--             meta = meta
--           }
--   define' import' expr
-- -- \| LetType
-- --     { docs :: Maybe DocString,
-- --       name :: String,
-- --       args :: [Expr],
-- --       alts :: [(String, Type)],
-- --       meta :: [Metadata]
-- --     }
-- -- \| Prompt
-- --     { expression :: Expr,
-- --       result :: Maybe Expr,
-- --       meta :: [Metadata]
-- --     }
-- define' stmt expr = error $ "TODO: define'" ++ show stmt
