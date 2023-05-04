module Tao where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (foldl')

{- TODO

Unify Context with Env
Clean up compile* functions

Patterns
- `IfP !Pattern !Expr` -- pattern guard
- `AnnP !Pattern !Pattern` -- get type information (TypeOf)
- `OrP !Pattern !Pattern`

-}

data Expr
  = Knd
  | IntT
  | NumT
  | Int !Int
  | Num !Double
  | Var !String
  | For !String !Expr
  | Fun !Expr !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Typ !String ![Expr]
  | Ctr !String ![Expr]
  | Get !String !Expr !String
  | Match ![Branch]
  | Lam !Pattern !Expr
  | Let ![Definition] !Expr
  | TypeOf !Expr
  | Op1 !String !Expr
  | Op2 !String !Expr !Expr
  | Op !String ![Expr]
  deriving (Eq, Show)

data Pattern
  = AnyP
  | VarP !String
  | CtrP !String ![Pattern]
  deriving (Eq, Show)

type Type = Expr

data Branch
  = Case ![Pattern] !Expr
  deriving (Eq, Show)

data Symbol
  = Val !Expr
  | UnionType ![(String, Type)] ![String]
  | UnionAlt !String ![(String, Type)] !Type
  deriving (Eq, Show)

type Context = [(String, Symbol)]

data Definition
  = Def ![(String, Type)] !Pattern !Expr
  deriving (Eq, Show)

data CompileError
  = MatchMissingArgs !Expr
  | MissingCases
  | NotAUnionAlt !String !Symbol
  | NotAUnionType !String !Symbol
  | TypeError !C.TypeError
  | UndefinedCtrField !String !String
  | UndefinedUnionAlt !String
  | UndefinedUnionType !String
  deriving (Eq, Show)

lam :: [Pattern] -> Expr -> Expr
lam ps a = foldr Lam a ps

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

fun :: [Expr] -> Expr -> Expr
fun args b = foldr Fun b args

match :: Branch -> [Branch] -> Expr
match (Case ps a) [] = lam ps a
match branch branches = Match (branch : branches)

bindings :: Pattern -> [String]
bindings AnyP = []
bindings (VarP x) = [x]
bindings (CtrP _ ps) = concatMap bindings ps

unpack :: Definition -> [(String, Expr)]
unpack (Def types p a) = do
  let unpackVar x = do
        let value = App (Match [Case [p] (Var x)]) a
        case lookup x types of
          Just type' -> (x, Ann value type')
          Nothing -> (x, value)
  unpackVar <$> bindings p

getUnionType :: Context -> String -> Either CompileError ([(String, Type)], [String])
getUnionType ctx t = case lookup t ctx of
  Just (UnionType args ks) -> Right (args, ks)
  Just a -> Left (NotAUnionType t a)
  Nothing -> Left (UndefinedUnionType t)

getUnionAlt :: Context -> String -> Either CompileError (String, [(String, Type)], Type)
getUnionAlt ctx ctr = case lookup ctr ctx of
  Just (UnionAlt t args retT) -> Right (t, args, retT)
  Just a -> Left (NotAUnionAlt ctr a)
  Nothing -> Left (UndefinedUnionAlt ctr)

expandUnionType :: Context -> String -> Either CompileError ([(String, Type)], [(String, ([(String, Type)], Type))])
expandUnionType ctx t = do
  (typeArgs, ks) <- getUnionType ctx t
  altDefs <- mapM (getUnionAlt ctx) ks
  let altArgs = map (\(_, args, retT) -> (args, retT)) altDefs
  Right (typeArgs, zip ks altArgs)

findPatternsType :: Context -> [[Pattern]] -> Either CompileError (Maybe String)
findPatternsType _ [] = Right Nothing
findPatternsType ctx ((CtrP ctr _ : _) : _) = do
  (t, _, _) <- getUnionAlt ctx ctr
  Right (Just t)
findPatternsType ctx (_ : ps) = findPatternsType ctx ps

branchVars :: C.Ops -> Context -> Branch -> Either CompileError (String, [String])
branchVars ops ctx (Case [] a) = do
  ys <- freeVars ops ctx a
  Right ("", ys)
branchVars ops ctx (Case (AnyP : ps) a) = do
  (y, ys) <- branchVars ops ctx (Case ps a)
  Right ("", y : ys)
branchVars ops ctx (Case (VarP x : ps) a) = do
  (y, ys) <- branchVars ops ctx (Case ps a)
  Right (x, y : ys)
branchVars ops ctx (Case (CtrP ctr qs : ps) a) = do
  (y, ys) <- branchVars ops ctx (Case (qs ++ ps) a)
  Right (ctr, y : ys)

matchArg :: C.Ops -> Context -> String -> (String, Int) -> [Branch] -> Either CompileError [Branch]
matchArg _ _ _ _ [] = Right []
matchArg _ _ _ _ (Case [] b : _) = Left (MatchMissingArgs b)
matchArg ops ctx x (ctr, arity) (Case (AnyP : ps) b : branches) = do
  matched <- matchArg ops ctx x (ctr, arity) branches
  Right (Case (replicate arity AnyP ++ ps) b : matched)
matchArg ops ctx x (ctr, arity) (Case (VarP y : ps) b : branches) = do
  matched <- matchArg ops ctx x (ctr, arity) branches
  varIsUsed <- occurs ops ctx y b
  let body = if x /= y && varIsUsed then Let [Def [] (VarP y) (Var x)] b else b
  Right (Case (replicate arity AnyP ++ ps) body : matched)
matchArg ops ctx x (ctr, arity) (Case (CtrP ctr' qs : ps) b : branches) | ctr == ctr' = do
  matched <- matchArg ops ctx x (ctr, arity) branches
  Right (Case (qs ++ ps) b : matched)
matchArg ops ctx x alt (Case (CtrP _ _ : _) _ : branches) =
  matchArg ops ctx x alt branches

compile :: C.Ops -> Context -> Expr -> Either CompileError C.Term
compile _ _ Knd = Right C.Knd
compile _ _ IntT = Right C.IntT
compile _ _ NumT = Right C.NumT
compile _ _ (Int i) = Right (C.Int i)
compile _ _ (Num n) = Right (C.Num n)
compile _ _ (Var x) = Right (C.Var x)
compile ops ctx (For x a) = do
  a <- compile ops ctx a
  Right (C.For x a)
compile ops ctx (Fun a b) = do
  a <- compile ops ctx a
  b <- compile ops ctx b
  Right (C.Fun a b)
compile ops ctx (App a b) = do
  a <- compile ops ctx a
  b <- compile ops ctx b
  Right (C.App a b)
compile ops ctx (Ann a b) = do
  a <- compile ops ctx a
  b <- compile ops ctx b
  Right (C.Ann a b)
compile ops ctx (Typ t args) = do
  args <- mapM (compile ops ctx) args
  Right (C.Typ t args)
compile ops ctx (Ctr ctr args) = do
  (t, _, _) <- getUnionAlt ctx ctr
  (_, ctrs) <- getUnionType ctx t
  body <- compile ops ctx (app (Var ctr) args)
  Right (C.lam ctrs body)
compile ops ctx (Get ctr a x) = do
  (_, args, _) <- getUnionAlt ctx ctr
  case fst <$> args of
    xs | x `elem` xs -> do
      a <- compile ops ctx a
      Right (C.App a (C.lam xs (C.Var x)))
    _else -> Left (UndefinedCtrField ctr x)
compile _ _ (Match []) = Left MissingCases
compile ops ctx (Match (Case [] b : _)) = compile ops ctx b
compile ops ctx (Match branches) = do
  let compileBranch :: String -> (String, ([(String, Type)], Type)) -> Either CompileError C.Term
      compileBranch x (ctr, (args, _)) = do
        matched <- matchArg ops ctx x (ctr, length args) branches
        compile ops ctx (Match matched)
  vars <- mapM (branchVars ops ctx) branches
  let (xs, names) = second concat (unzip vars)
  let x = case filter (/= "") (reverse xs) of
        [] -> "_"
        x : _ -> C.newName x names
  maybeTypeName <- findPatternsType ctx (map (\(Case ctr _) -> ctr) branches)
  case maybeTypeName of
    Just t -> do
      (_, alts) <- expandUnionType ctx t
      args <- mapM (compileBranch x) alts
      Right (C.Lam x (C.app (C.Var x) args))
    Nothing -> do
      matched <- matchArg ops ctx x ("", 0) branches
      body <- compile ops ctx (Match matched)
      Right (C.Lam x body)
compile ops ctx (Lam p b) = compile ops ctx (Match [Case [p] b])
compile ops ctx (Let [] b) = compile ops ctx b
compile ops ctx (Let defs b) = do
  env <- compileEnv ops ctx (concatMap unpack defs)
  b <- compile ops ctx b
  Right (C.Let env b)
compile ops ctx (TypeOf a) = do
  (aT, _) <- infer ops ctx a
  compile ops ctx aT
compile ops ctx (Op1 op a) = compile ops ctx (Op op [a])
compile ops ctx (Op2 op a b) = compile ops ctx (Op op [a, b])
compile ops ctx (Op op args) = do
  args <- mapM (compile ops ctx) args
  Right (C.Op op args)

compileEnv :: C.Ops -> Context -> [(String, Expr)] -> Either CompileError C.Env
compileEnv ops ctx = mapM (compileNamed ops ctx)

compileCtx :: C.Ops -> Context -> Either CompileError C.Context
compileCtx ops ctx = do
  let compileDef :: (String, Symbol) -> Either CompileError (String, C.Symbol)
      compileDef (x, sym) = do
        sym <- compileSym ops ctx sym
        Right (x, sym)
  mapM compileDef ctx

compileNamed :: C.Ops -> Context -> (String, Expr) -> Either CompileError (String, C.Term)
compileNamed ops ctx (x, a) = do
  a <- compile ops ctx a
  Right (x, a)

compileSym :: C.Ops -> Context -> Symbol -> Either CompileError C.Symbol
compileSym ops ctx (Val a) = do
  a <- compile ops ctx a
  Right (C.Val a)
compileSym ops ctx (UnionType args ctrs) = do
  args <- mapM (compileNamed ops ctx) args
  Right (C.UnionType args ctrs)
compileSym ops ctx (UnionAlt t args a) = do
  args <- mapM (compileNamed ops ctx) args
  a <- compile ops ctx a
  Right (C.UnionAlt t args a)

decompile :: C.Term -> Expr
decompile C.Knd = Knd
decompile C.IntT = IntT
decompile C.NumT = NumT
decompile (C.Int i) = Int i
decompile (C.Num n) = Num n
decompile (C.Var x) = Var x
decompile (C.Lam x a) = lam [VarP x] (decompile a)
decompile (C.For x a) = For x (decompile a)
decompile (C.Fun a b) = Fun (decompile a) (decompile b)
decompile (C.App a b) = App (decompile a) (decompile b)
decompile (C.Ann a b) = Ann (decompile a) (decompile b)
decompile (C.Let env b) = do
  let decompileDef (x, a) = Def [] (VarP x) (decompile a)
  Let (decompileDef <$> env) (decompile b)
decompile (C.Fix x a) = Let [Def [] (VarP x) (decompile a)] (Var x)
decompile (C.Typ t args) = Typ t (decompile <$> args)
decompile (C.Op op args) = Op op (decompile <$> args)

decompileNamed :: (String, C.Term) -> (String, Expr)
decompileNamed (x, a) = (x, decompile a)

decompileSym :: C.Symbol -> Symbol
decompileSym (C.Val a) = Val (decompile a)
decompileSym (C.UnionType args ctrs) = UnionType (decompileNamed <$> args) ctrs
decompileSym (C.UnionAlt t args a) = UnionAlt t (decompileNamed <$> args) (decompile a)

decompileCtx :: C.Context -> Context
decompileCtx ctx = do
  let decompileDef :: (String, C.Symbol) -> (String, Symbol)
      decompileDef (x, sym) = (x, decompileSym sym)
  decompileDef <$> ctx

freeVars :: C.Ops -> Context -> Expr -> Either CompileError [String]
freeVars ops ctx a = do
  a <- compile ops ctx a
  Right (C.freeVars a)

occurs :: C.Ops -> Context -> String -> Expr -> Either CompileError Bool
occurs ops ctx x a = do
  vars <- freeVars ops ctx a
  Right (x `elem` vars)

infer :: C.Ops -> Context -> Expr -> Either CompileError (Type, Context)
infer ops ctx a = do
  a <- compile ops ctx a
  ctx <- compileCtx ops ctx
  case C.infer ops ctx a of
    Right (b, ctx) -> Right (decompile b, decompileCtx ctx)
    Left err -> Left (TypeError err)
