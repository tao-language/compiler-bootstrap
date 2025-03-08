module Compile where

import qualified Core as C
import Data.Bifunctor (second)
import Data.List (delete, intercalate, isPrefixOf, unionBy)
import Error (Error (RuntimeError), TypeError (..))
import Stdlib (split)
import Tao

bindings :: Expr -> [String]
bindings = \case
  For xs _ -> xs
  Ann a _ -> bindings a
  App a _ -> bindings a
  Op1 op _ -> [show op]
  Op2 op _ _ -> [show op]
  Meta _ a -> bindings a
  a -> freeVars a

lower :: Expr -> C.Expr
lower = \case
  Any -> C.Any
  Unit -> C.Unit
  IntT -> C.IntT
  NumT -> C.NumT
  Int i -> C.Int i
  Num n -> C.Num n
  Var x -> C.Var x
  Tag k -> C.Tag k
  Ann a b -> C.Ann (lower a) (lower b)
  And a b -> C.And (lower a) (lower b)
  Or a b -> C.Or (lower a) (lower b)
  For xs (Meta _ a) -> lower (For xs a)
  For xs (For ys a) -> lower (For (xs ++ ys) a)
  For [] (Fun a b) -> do
    let (args, body) = funOf (Fun a b)
    C.fun (map lower args) (lower body)
  For [] a -> lower a
  For xs a -> C.for xs (lower (For [] a))
  Fun a b -> do
    let (args, body) = funOf (Fun a b)
    lower (For (freeVars (and' args)) (fun args body))
  App a b -> C.App (lower a) (lower b)
  Call op args -> C.Call op (map lower args)
  Op1 op a -> lower (App (Var (show op)) a)
  Op2 op a b -> lower (app (Var (show op)) [a, b])
  Let (a, b) c -> case a of
    Var x | c == Var x -> lower b
    Var x -> C.App (lower (Fun a c)) (C.fix [x] (lower b))
    Ann (Or a1 a2) t -> lower (lets [(Ann a1 t, b), (Ann a2 t, b)] c)
    Ann (App a1 a2) t -> lower (Let (Ann a1 t, Fun a2 b) c)
    Ann (Op1 op a) t -> lower (Let (Ann (Var (show op)) t, Fun a b) c)
    Ann (Op2 op a1 a2) t -> lower (Let (Ann (Var (show op)) t, fun [a1, a2] b) c)
    Ann (Meta _ a) t -> lower (Let (Ann a t, b) c)
    Ann a t -> lower (Let (a, Ann b t) c)
    Or a1 a2 -> lower (lets [(a1, b), (a2, b)] c)
    App a1 a2 -> lower (Let (a1, Fun a2 b) c)
    Op1 op a -> lower (Let (Var (show op), Fun a b) c)
    Op2 op a1 a2 -> lower (Let (Var (show op), fun [a1, a2] b) c)
    For xs a -> lower (App (For xs (Fun a c)) b)
    Meta _ a -> lower (Let (a, b) c)
    a -> lower (App (Fun a c) b)
  -- lower env (Bind (ts, p, a) b) = lower env (App (Trait a "<-") (Function [p] b))
  If a b c -> lower (Match [a] [([], [Tag "True"], b), ([], [], c)])
  Match args [(xs, ps, b)] -> lower (app (For xs $ fun ps b) args)
  Match args cases -> do
    let n = foldl max 0 (map (\(_, ps, _) -> length ps) cases)
    let rpad :: Int -> a -> [a] -> [a]
        rpad n x xs = xs ++ replicate (n - length xs) x
    let cases' = map (\(xs, ps, b) -> For xs $ fun (rpad n Any ps) b) cases
    let args' = map (\i -> Var ("$" ++ show i)) [length args + 1 .. n]
    let match' = fun args' (app (or' cases') (args ++ args'))
    -- let a = lower match'
    -- (error . intercalate "\n")
    --   [ show match',
    --     C.format (C.dropMeta a),
    --     C.format (C.dropMeta $ C.eval buildOps a),
    --     C.format (C.eval buildOps $ C.dropMeta a)
    --   ]
    lower match'
  Record fields -> do
    let k = '~' : intercalate "," (map fst fields)
    lower (tag k (map snd fields))
  Select a kvs -> do
    let sub = case a of
          Record fields -> map (second lower) fields
          a -> do
            let xs = freeVars (and' (map snd kvs))
            map (\x -> (x, C.App (C.Var x) (lower a))) xs
    let k = '~' : intercalate "," (map fst kvs)
    let args = map ((C.substitute sub . lower) . snd) kvs
    C.tag k args
  Meta m a -> C.Meta m (lower a)
  Err e -> C.Err (lowerErr e)
  a -> error $ "TODO: lower " ++ show a

lowerErr :: Error Expr -> Error C.Expr
lowerErr = fmap lower

lift :: C.Expr -> Expr
lift = \case
  C.Any -> Any
  C.Unit -> Unit
  C.IntT -> IntT
  C.NumT -> NumT
  C.Int i -> Int i
  C.Num n -> Num n
  C.Var x -> Var x
  C.Tag "~" -> Record []
  C.Tag k -> Tag k
  C.Ann a b -> Ann (lift a) (lift b)
  C.And a b -> case (a, map lift (C.andOf b)) of
    (C.Tag ('~' : names), values) -> do
      let keys = split ',' names
      Record (zip keys values)
    (a, items) -> and' (lift a : items)
  C.Or a b -> Or (lift a) (lift b)
  C.For x a -> case lift a of
    For xs a -> for (x : xs) a
    a -> for [x] a
  C.Fix x a
    | x `C.occurs` a -> Let (Var x, lift a) (lift a)
    | otherwise -> lift a
  C.Fun a b -> Fun (lift a) (lift b)
  C.App a b -> App (lift a) (lift b)
  C.Call op args -> Call op (map lift args)
  C.Let [] b -> lift b
  C.Let ((x, b) : env) c -> Let (Var x, lift b) (lift (C.Let env c))
  C.Meta m a -> Meta m (lift a)
  C.Err e -> Err (liftErr e)

liftErr :: Error C.Expr -> Error Expr
liftErr = fmap lift

-- liftTypeError :: TypeError C.Expr -> TypeError Expr
-- liftTypeError = \case
--   OccursError x a -> OccursError x (lift a)
--   TypeMismatch a b -> TypeMismatch (lift a) (lift b)
--   NotAFunction a -> NotAFunction (lift a)
--   UndefinedVar x -> UndefinedVar x

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
      [] | alias == name -> [(path, Tag path')]
      [] -> []
    Def (p, b) | name `elem` bindings p -> do
      [(path, Let (p, b) (Var name))]
    TypeDef (name', args, alts) | name == name' -> do
      let resolveAlt (a, Just b) = Fun a b
          resolveAlt (a, Nothing) = Fun a (tag name' args)
      [(path, fun args (or' (map resolveAlt alts)))]
    _ -> []

class Compile a where
  compile :: Context -> String -> a

instance Compile (String -> C.Env) where
  compile :: Context -> String -> String -> C.Env
  -- compile ctx path name@"==" = do
  --   let compileDef :: (FilePath, Expr) -> (C.Env, [C.Expr]) -> (C.Env, [C.Expr])
  --       compileDef (path, alt) (env, alts) = do
  --         let (env', alt') = compile ctx path (name, alt)
  --         (unionBy (\a b -> fst a == fst b) env' env, C.let' env' alt' : alts)
  --   let (env, alts) = foldr compileDef ([], []) (resolve ctx path name)
  --   let def = case alts of
  --         [] -> []
  --         [C.Var x] | x == name -> [(name, C.Var x)]
  --         [C.Ann (C.Var x) t] | x == name -> [(name, C.Ann (C.Var x) t)]
  --         alts -> [(name, C.fix [name] (C.or' alts))]
  --   -- unionBy (\a b -> fst a == fst b) def env
  --   error . intercalate "\n" $
  --     [ "-- compile/1 " ++ show path ++ " " ++ show name,
  --       show (map fst ctx),
  --       show env,
  --       show $ map C.format alts,
  --       ""
  --     ]
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
    unionBy (\a b -> fst a == fst b) def env

instance Compile ((String, Expr) -> (C.Env, C.Expr, C.Type)) where
  compile :: Context -> String -> (String, Expr) -> (C.Env, C.Expr, C.Type)
  -- compile ctx path (name@"", expr) = do
  --   let a = lower expr
  --   let env = concatMap (compile ctx path) (delete name (C.freeNames (True, True, False) a))
  --   let ((a', t), s, e) = C.infer buildOps env a
  --   let xs = filter (`notElem` map fst env) (map fst s)
  --   error . intercalate "\n" $
  --     [ "-- compile/2 " ++ name,
  --       -- show ctx,
  --       "a: " ++ C.format a,
  --       "t: " ++ C.format t,
  --       "env: " ++ C.format (C.Let env C.Any),
  --       "     " ++ show (map fst env),
  --       "a': " ++ C.format a',
  --       -- C.format (C.for xs $ C.dropTypes a'),
  --       -- C.format t,
  --       ""
  --     ]
  compile ctx path (name, expr) = do
    let a = lower expr
    let env = concatMap (compile ctx path) (delete name (C.freeNames (True, True, False) a))
    let ((a', t), s) = C.infer buildOps env a
    let xs = filter (`notElem` map fst env) (map fst s)
    (env, C.for xs a', t)

instance Compile ((String, Expr) -> (C.Env, C.Expr)) where
  compile :: Context -> String -> (String, Expr) -> (C.Env, C.Expr)
  compile ctx path (name, expr) = do
    let (env, a, t) = compile ctx path (name, expr) :: (C.Env, C.Expr, C.Type)
    (env, C.Ann a t)

instance Compile (Expr -> (C.Env, C.Expr, C.Type)) where
  compile :: Context -> String -> Expr -> (C.Env, C.Expr, C.Type)
  compile ctx path expr =
    compile ctx path (C.newName (freeVars expr) "", expr)

instance Compile (Expr -> (C.Env, C.Expr)) where
  compile :: Context -> String -> Expr -> (C.Env, C.Expr)
  compile ctx path expr =
    compile ctx path (C.newName (freeVars expr) "", expr)
