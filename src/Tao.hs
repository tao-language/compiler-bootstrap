module Tao where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (foldl')

{- TODO

Remove `For`, infer it
Clean up compile* functions
Infer type variables used in definitions (e.g. length of a vector)
Records on inferred type variables for function overloading

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
  | Lam !String !Expr
  | For !String !Expr
  | Fun !Expr !Expr
  | App !Expr !Expr
  | Ann !Expr !Type
  | Ctr !String ![Expr]
  | Typ !String ![(String, Expr)] ![String]
  | Case !Expr ![(String, Expr)] !Expr
  | CaseInt !Expr ![(Int, Expr)] !Expr
  | Match ![Branch]
  | Let ![Definition] !Expr
  | TypeOf !Expr
  | Op1 !String !Expr
  | Op2 !String !Expr !Expr
  | Op !String ![Expr]
  deriving (Eq, Show)

data Pattern
  = AnyP
  | VarP !String
  | IntP !Int
  | CtrP !String ![Pattern]
  deriving (Eq, Show)

type Type = Expr

data Branch
  = Br ![Pattern] !Expr
  deriving (Eq, Show)

type Env = [(String, Expr)]

data Definition
  = Def ![(String, Type)] !Pattern !Expr
  | DefT !String ![(String, Type)] ![(String, ([(String, Type)], Type))]
  deriving (Eq, Show)

data CompileError
  = EmptyMatch
  | MatchMissingArgs !Expr
  | NotAUnionAlt !String !Expr
  | TypeError !C.TypeError
  | UndefinedCtrField !String !String
  | UndefinedUnionAlt !String
  | UndefinedUnionType !String
  deriving (Eq, Show)

lam :: [String] -> Expr -> Expr
lam xs a = foldr Lam a xs

lamP :: [Pattern] -> Expr -> Expr
lamP [] a = a
lamP (VarP x : ps) a = Lam x (lamP ps a)
lamP ps a = Match [Br ps a]

for :: [String] -> Expr -> Expr
for xs a = foldr For a xs

app :: Expr -> [Expr] -> Expr
app = foldl' App

fun :: [Expr] -> Expr -> Expr
fun args b = foldr Fun b args

letVar :: (String, Expr) -> Expr -> Expr
letVar (x, a) = letVars [(x, a)]

letVars :: [(String, Expr)] -> Expr -> Expr
letVars [] b = b
letVars defs b = Let (map (\(x, a) -> Def [] (VarP x) a) defs) b

match :: [Branch] -> Expr
match (Br [] a : _) = a
match [Br ps a] = lamP ps a
match brs = Match brs

bindings :: Pattern -> [String]
bindings AnyP = []
bindings (IntP _) = []
bindings (VarP x) = [x]
bindings (CtrP _ ps) = concatMap bindings ps

unpack :: Definition -> Env
unpack (Def types p a) = do
  let unpackVar x = do
        let value = App (match [Br [p] (Var x)]) a
        case lookup x types of
          Just type' -> (x, Ann value type')
          Nothing -> (x, value)
  unpackVar <$> bindings p
unpack (DefT t args alts) = do
  let unpackAlt (ctr, (ctrArgs, retT)) = do
        let value = lam (map fst ctrArgs) (Ctr ctr (map (Var . fst) ctrArgs))
        let type' = for (map fst args) (fun (snd <$> ctrArgs) retT)
        (ctr, Ann value type')
  (t, Typ t args (fst <$> alts)) : map unpackAlt alts

-- findTyped :: C.Ops -> Env -> String -> Either CompileError (Expr, Type)
-- findTyped ops env x = do
--   env <- compileEnv ops env env
--   case C.findTyped ops env x of
--     Right (a, t) -> Right (decompile a, decompile t)
--     Left err -> Left (TypeError err)

-- expandUnionAlt :: C.Ops -> Env -> String -> Either CompileError ([Type], Type)
-- expandUnionAlt ops env k = do
--   env <- compileEnv ops env env
--   case C.findTyped ops env k of
--     Right (_, ctrT) -> do
--       let (_, argsT, retT) = C.splitFun ctrT
--       Right (map decompile argsT, decompile retT)
--     Left err -> Left (TypeError err)

-- expandUnionType :: C.Ops -> Env -> String -> Either CompileError ([(String, Type)], [(String, ([Type], Type))])
-- expandUnionType ops env t = do
--   (_, typeArgs, ctrs) <- case lookup t env of
--     Just a -> do
--       term <- compile ops env a
--       case C.asTypeDef term of
--         Right (t, args, ctrs) -> Right (t, map (second decompile) args, ctrs)
--         Left err -> Left (TypeError err)
--     Nothing -> Left (UndefinedUnionType t)
--   altArgs <- mapM (expandUnionAlt ops env) ctrs
--   Right (typeArgs, zip ctrs altArgs)

-- data MatchState
--   = MatchEnd !Expr
--   | MatchAny ![Branch]
--   | MatchVar !String ![Branch]
--   | MatchInt ![(Int, [Branch])] ![Branch]
--   | MatchCtr ![(String, [Branch])] ![Branch]
--   deriving (Show, Eq)

-- -- compileMatch :: C.Ops -> Env -> [Branch] -> Either CompileError MatchState
-- -- compileMatch _ _ [] = Left EmptyMatch
-- -- compileMatch _ _ (Br [] b : _) = Right (MatchEnd b)
-- -- compileMatch ops env (Br (p : ps) b : brs) = do
-- --   state <- compileMatch ops env brs
-- --   case (p, state) of
-- --     (_, MatchEnd _) -> error "different number of patterns"
-- --     (AnyP, MatchAny brs) -> Right (MatchAny (Br ps b : brs))
-- --     (VarP x, MatchAny brs) -> Right (MatchVar (br : brs))

-- findPatternsType :: C.Ops -> Env -> [[Pattern]] -> Either CompileError (Maybe String)
-- findPatternsType _ _ [] = Right Nothing
-- findPatternsType ops env ((CtrP ctr _ : _) : _) = do
--   env <- compileEnv ops env env
--   case C.findCtrType ops env ctr of
--     Right (t, _, _) -> Right (Just t)
--     Left err -> Left (TypeError err)
-- findPatternsType ops env (_ : ps) = findPatternsType ops env ps

-- branchVars :: C.Ops -> Env -> Branch -> Either CompileError (String, [String])
-- branchVars ops env (Br [] a) = do
--   ys <- freeVars ops env a
--   Right ("", ys)
-- branchVars ops env (Br (AnyP : ps) a) = do
--   (y, ys) <- branchVars ops env (Br ps a)
--   Right ("", y : ys)
-- branchVars ops env (Br (IntP _ : ps) a) = do
--   (y, ys) <- branchVars ops env (Br ps a)
--   Right ("", y : ys)
-- branchVars ops env (Br (VarP x : ps) a) = do
--   (y, ys) <- branchVars ops env (Br ps a)
--   Right (x, y : ys)
-- branchVars ops env (Br (CtrP ctr qs : ps) a) = do
--   (y, ys) <- branchVars ops env (Br (qs ++ ps) a)
--   Right (ctr, y : ys)

-- matchArg :: C.Ops -> Env -> String -> (String, Int) -> [Branch] -> Either CompileError [Branch]
-- matchArg _ _ _ _ [] = Right []
-- matchArg _ _ _ _ (Br [] b : _) = Left (MatchMissingArgs b)
-- matchArg ops env x (ctr, arity) (Br (AnyP : ps) b : branches) = do
--   matched <- matchArg ops env x (ctr, arity) branches
--   Right (Br (replicate arity AnyP ++ ps) b : matched)
-- matchArg ops env x (ctr, arity) (Br (VarP y : ps) b : branches) = do
--   matched <- matchArg ops env x (ctr, arity) branches
--   varIsUsed <- occurs ops env y b
--   let body = if x /= y && varIsUsed then Let [Def [] (VarP y) (Var x)] b else b
--   Right (Br (replicate arity AnyP ++ ps) body : matched)
-- matchArg ops env x (ctr, arity) (Br (CtrP ctr' qs : ps) b : branches) | ctr == ctr' = do
--   matched <- matchArg ops env x (ctr, arity) branches
--   Right (Br (qs ++ ps) b : matched)
-- matchArg ops env x alt (Br (CtrP _ _ : _) _ : branches) =
--   matchArg ops env x alt branches

-- -- data MatchArg
-- --   = MatchAny ![Branch]
-- --   | MatchInt ![(Int, [Branch])] ![Branch]
-- --   | MatchCtr ![(String, [Branch])] ![Branch]
-- --   deriving (Show, Eq)

-- -- matchAny :: String -> Branch -> Maybe Branch
-- -- matchAny _ (Br (AnyP : ps) b) = Just (Br ps b)
-- -- matchAny x (Br (VarP y : ps) b) = Just (Br ps (letVar (y, Var x) b))
-- -- matchAny _ (Br _ _) = Nothing

-- -- matchInt :: Int -> String -> Branch -> Maybe Branch
-- -- matchInt _ _ (Br (AnyP : ps) b) = Just (Br ps b)
-- -- matchInt i _ (Br (IntP i' : ps) b) | i == i' = Just (Br ps b)
-- -- matchInt _ x (Br (VarP y : ps) b) = Just (Br ps (letVar (y, Var x) b))
-- -- matchInt _ _ (Br _ _) = Nothing

-- -- matchCtr :: (String, Int) -> String -> Branch -> Maybe Branch
-- -- matchCtr (_, n) _ (Br (AnyP : ps) b) = Just (Br (replicate n AnyP ++ ps) b)
-- -- matchCtr (_, n) x (Br (VarP y : ps) b) = Just (Br (replicate n AnyP ++ ps) (letVar (y, Var x) b))
-- -- matchCtr (k, _) _ (Br (CtrP k' qs : ps) b) | k == k' = Just (Br (qs ++ ps) b)
-- -- matchCtr _ _ (Br _ _) = Nothing

-- -- matchFilter :: Pattern -> String -> [Branch] -> [Branch]
-- -- matchFilter _ _ [] = []
-- -- matchFilter _ _ (Br [] _ : _) = []
-- -- -- matchFilter AnyP x (br : brs) = case matchAny x br of
-- -- matchFilter p@(CtrP _ qs) x (Br (AnyP : ps) b : brs) = Br (map (const AnyP) qs ++ ps) b : matchFilter p x brs
-- -- matchFilter p x (Br (AnyP : ps) b : brs) = Br ps b : matchFilter p x brs
-- -- matchFilter p x (Br (VarP y : ps) b : brs) = matchFilter p x (Br (AnyP : ps) (letVar (y, Var x) b) : brs)
-- -- matchFilter p@(IntP i) x (Br (IntP i' : ps) b : brs) | i == i' = Br ps b : matchFilter p x brs
-- -- matchFilter p x (Br (IntP _ : _) _ : brs) = matchFilter p x brs
-- -- matchFilter p@(CtrP k _) x (Br (CtrP k' qs : ps) b : brs) | k == k' = Br (qs ++ ps) b : matchFilter p x brs
-- -- matchFilter p x (Br (CtrP _ _ : _) _ : brs) = matchFilter p x brs

-- -- matchArg :: String -> [Branch] -> MatchArg
-- -- matchArg _ [] = MatchAny []
-- -- matchArg x (Br (p : ps) b : brs) = case (p, matchArg x brs) of
-- --   (AnyP, MatchAny brs) -> MatchAny (Br ps b : brs)
-- --   (VarP y, MatchAny brs) -> MatchAny (Br ps (letVar (y, Var x) b) : brs)
-- --   (IntP i, MatchAny brs) -> MatchInt [(i, matchFilter (IntP i) x brs)] brs
-- --   (CtrP k qs, MatchAny brs) -> MatchCtr [(k, matchFilter (CtrP k qs) x brs)] brs
-- --   (AnyP, MatchInt cases brs) -> MatchInt (second (Br ps b :) <$> cases) (Br ps b : brs)
-- --   (VarP y, MatchInt cases brs) -> MatchInt (second (Br ps (letVar (y, Var x) b) :) <$> cases) (Br ps b : brs)
-- --   (_, MatchCtr cases brs) -> _
-- --   _ -> _
-- -- -- matchArg x ((Br (AnyP : ps) b : brs)) = case matchArg x brs of
-- -- --   MatchAny brs -> MatchAny (Br ps b : brs)
-- -- --   MatchInt cases brs -> MatchInt (map (\(i, brs) -> (i, Br ps b : brs)) cases) (Br ps b : brs)
-- -- --   MatchCtr cases brs -> MatchCtr (map (\(i, brs) -> (i, Br ps b : brs)) cases) (Br ps b : brs)
-- -- -- matchArg x ((Br (VarP y : ps) b : brs)) =
-- -- --   matchArg x ((Br (AnyP : ps) (letVar (y, Var x) b) : brs))
-- -- matchArg _ _ = error "TODO"

-- -- matchArg x (MatchAny (Br (CtrP ctr qs : ps) b : brs)) = case matchArg x (MatchCtr )

-- compile :: C.Ops -> Env -> Expr -> Either CompileError C.Expr
-- compile _ _ Knd = Right C.Knd
-- compile _ _ IntT = Right C.IntT
-- compile _ _ NumT = Right C.NumT
-- compile _ _ (Int i) = Right (C.Int i)
-- compile _ _ (Num n) = Right (C.Num n)
-- compile _ _ (Var x) = Right (C.Var x)
-- compile ops env (For x a) = do
--   a <- compile ops env a
--   Right (C.For x a)
-- compile ops env (Fun a b) = do
--   a <- compile ops env a
--   b <- compile ops env b
--   Right (C.Fun a b)
-- compile ops env (App a b) = do
--   a <- compile ops env a
--   b <- compile ops env b
--   Right (C.App a b)
-- compile ops env (Ann a b) = do
--   a <- compile ops env a
--   b <- compile ops env b
--   Right (C.Ann a b)
-- compile ops env (Ctr k args) = do
--   args <- mapM (compile ops env) args
--   Right (C.Ctr k args)
-- compile ops env (Typ t args ctrs) = do
--   let xs = map fst args
--   args <- mapM (compile ops env . snd) args
--   Right (C.Typ t (zip xs args) ctrs)
-- compile _ _ (Match []) = Left EmptyMatch
-- compile ops env (Match (Br [] b : _)) = compile ops env b
-- compile ops env (Match branches) = do
--   let compileBranch :: String -> (String, ([Type], Type)) -> Either CompileError C.Expr
--       compileBranch x (ctr, (args, _)) = do
--         matched <- matchArg ops env x (ctr, length args) branches
--         compile ops env (match matched)
--   vars <- mapM (branchVars ops env) branches
--   let (xs, names) = second concat (unzip vars)
--   let x = case filter (/= "") (reverse xs) of
--         [] -> "_"
--         x : _ -> C.newName x names
--   maybeTypeName <- findPatternsType ops env (map (\(Br ctr _) -> ctr) branches)
--   case maybeTypeName of
--     Just t -> do
--       (_, alts) <- expandUnionType ops env t
--       args <- mapM (compileBranch x) alts
--       Right (C.Lam x (C.app (C.Var x) args))
--     Nothing -> do
--       matched <- matchArg ops env x ("", 0) branches
--       body <- compile ops env (match matched)
--       Right (C.Lam x body)
-- compile ops env (Lam x b) = do
--   b <- compile ops ((x, Var x) : env) b
--   Right (C.Lam x b)
-- compile ops env (Let [] b) = compile ops env b
-- compile ops env (Let defs b) = do
--   defs <- compileEnv ops env (concatMap unpack defs)
--   b <- compile ops env b
--   Right (C.Let defs b)
-- compile ops env (TypeOf a) = do
--   -- (aT, _) <- infer ops env a
--   -- compile ops env aT
--   error "TODO: compile TypeOf"
-- compile ops env (Op1 op a) = compile ops env (Op op [a])
-- compile ops env (Op2 op a b) = compile ops env (Op op [a, b])
-- compile ops env (Op op args) = do
--   args <- mapM (compile ops env) args
--   Right (C.Op op args)

-- compileEnv :: C.Ops -> Env -> Env -> Either CompileError C.Env
-- compileEnv ops env = mapM (compileNamed ops env)

-- compileNamed :: C.Ops -> Env -> (String, Expr) -> Either CompileError (String, C.Expr)
-- compileNamed ops env (x, a) = do
--   -- a <- compile ops ((x, Var x) : env) a
--   a <- compile ops env a
--   Right (x, a)

-- decompile :: C.Expr -> Expr
-- decompile C.Knd = Knd
-- decompile C.IntT = IntT
-- decompile C.NumT = NumT
-- decompile (C.Int i) = Int i
-- decompile (C.Num n) = Num n
-- decompile (C.Var x) = Var x
-- decompile (C.Lam x a) = Lam x (decompile a)
-- decompile (C.For x a) = For x (decompile a)
-- decompile (C.Fun a b) = Fun (decompile a) (decompile b)
-- decompile (C.App a b) = App (decompile a) (decompile b)
-- decompile (C.Ann a b) = Ann (decompile a) (decompile b)
-- decompile (C.Let env b) = do
--   let decompileDef (x, a) = Def [] (VarP x) (decompile a)
--   Let (decompileDef <$> env) (decompile b)
-- decompile (C.Fix x a) = letVar (x, decompile a) (Var x)
-- decompile (C.Ctr k args) = Ctr k (map decompile args)
-- decompile (C.Typ t args ctrs) = Typ t (map (second decompile) args) ctrs
-- decompile (C.Op op args) = Op op (decompile <$> args)

-- decompileNamed :: (String, C.Expr) -> (String, Expr)
-- decompileNamed (x, a) = (x, decompile a)

-- decompileEnv :: C.Env -> Env
-- decompileEnv = map decompileNamed

-- freeVars :: C.Ops -> Env -> Expr -> Either CompileError [String]
-- freeVars ops env a = do
--   a <- compile ops env a
--   Right (C.freeVars a)

-- occurs :: C.Ops -> Env -> String -> Expr -> Either CompileError Bool
-- occurs ops env x a = do
--   vars <- freeVars ops env a
--   Right (x `elem` vars)

-- infer :: C.Ops -> Env -> Expr -> Either CompileError (Type, Env)
-- infer ops env expr = do
--   term <- compile ops env expr
--   env <- compileEnv ops env env
--   case C.infer ops env term of
--     Right (type', env) -> Right (decompile type', decompileEnv env)
--     Left err -> Left (TypeError err)

-- eval :: C.Ops -> Env -> Expr -> Either CompileError (Expr, Type)
-- eval ops env expr = do
--   term <- compile ops env expr
--   env <- compileEnv ops env env
--   case C.infer ops env term of
--     Right (type', _) -> Right (decompile (C.eval ops env term), decompile type')
--     Left err -> Left (TypeError err)
