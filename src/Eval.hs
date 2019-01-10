{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

-- | This module defines monadic computations (reader and state) for
-- big-step term evaluation.

module Eval (
  eval, Value(..), Env(..)
  ) where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.List (intercalate, sortBy)

import Ast
import Symtab (Symtab, Id(..), empty, add, exists, fold, assocGet)
import qualified Symtab as S (map, get)
import Util (debugPrint, mapSndM)

newtype Env = Env { unEnv :: Symtab Value }
  deriving Eq

data Value =
  VUnit
  | VBool Bool
  | VInt Integer
  | VChar Char
  | VClos Env Id (Term ())
  | VLoc Id
  | VVariant Id [Value]
  | VRecord [(Id, Value)]
  deriving Eq

instance Show Value where
  show VUnit = "VUnit"
  show (VBool b) = "(VBool " ++ show b ++ ")"
  show (VInt i) = "(VInt " ++ show i ++ ")"
  show (VChar c) = "(VChar " ++ show c ++ ")"
  show (VClos env x t) = "(VClos " ++ show x ++ " " ++ show t ++ ")"
  -- show (VClos env x t) = "(VClos (env = " ++ show env ++ ") " ++ show x ++
  --   " " ++ show t ++ ")"
  show (VLoc x) = "(VLoc " ++ show x ++ ")"
  show (VVariant x vs) = "(VVariant " ++ show x ++ " " ++
    intercalate " " (show <$> vs) ++ ")"
  show (VRecord fields) =
    "(VRecord " ++ intercalate " " (show <$> fields) ++ ")"

instance Show Env where
  show =
    fold (\acc nm v -> acc ++ show nm ++ ": " ++ show v ++ "\n") "" . unEnv

intOfValue :: Value -> Integer
intOfValue (VInt i) = i
intOfValue _ = error "intOfValue: expected VInt"

charOfValue :: Value -> Char
charOfValue (VChar c) = c
charOfValue _ = error "charOfValue: expected VChar"

boolOfValue :: Value -> Bool
boolOfValue (VBool b) = b
boolOfValue _ = error "boolOfValue: expected VBool"

freshLoc :: MonadState (Int, Env) m => m Id
freshLoc = do
  (i, env) <- get
  put (i+1, env)
  return $ Id $ show i

evalError :: (MonadReader Env m, MonadState (b, Env) m) => String -> m a
evalError s = do
  -- env <- ask
  -- (_, heap) <- get
  -- error $ "runtime error!\nenvironment:\n" ++ show env ++ "\n\nheap: "
  --   ++ show heap ++ "\n\n" ++ s
  error $ "runtime error!\n" ++ s


------------------------
-- | Big-step evaluation

eval :: (MonadReader Env m, MonadFix m, MonadState (Int, Env) m) =>
        Term () -> m Value

eval (TmVar _ nm) = do
  Env ctx <- ask
  case S.get nm ctx of
    Just v -> return v
    _ -> evalError $ "eval: unbound variable " ++ show nm

eval (TmAbs _ nm ty tm) = do
  ctx <- ask -- close over the current environment
  return $ VClos ctx nm tm

eval (TmApp _ t1 t2) = do
  v1 <- eval t1
  v2 <- eval t2
  case v1 of
    VClos clos nm body ->
      -- Force call-by-value order with seq
      seq v2 $ local (const $ extendEnv nm v2 clos) $ eval body
    _ -> do
      env <- ask
      evalError $ "eval: " ++ show v1 ++ " isn't a closure"

eval (TmUnit _) = return VUnit
eval (TmBool _ b) = return $ VBool b

eval (TmIf _ t1 t2 t3) = do
  v1 <- eval t1
  case v1 of
    VBool True  -> eval t2
    VBool False -> eval t3
    _ -> evalError $ "eval: " ++ show v1 ++ " isn't a bool"

eval (TmInt _ i) = return $ VInt i

eval (TmChar _ c) = return $ VChar c

eval (TmUnop _ u tm) = do
  v <- eval tm
  case u of
    UMinus ->
      case v of
        VInt i -> return $ VInt (-i)
        _ -> evalError $ "eval: " ++ show v ++ " isn't an integer"
    UNot ->
      case v of
        VBool True  -> return $ VBool False
        VBool False -> return $ VBool True
        _ -> evalError $ "eval: " ++ show v ++ " isn't a bool"
    -- UFix ->
    --   case v of
    --     VClos clos nm tm' ->
    --       mfix $ \f -> local (const $ extendEnv nm f clos) $ eval tm'
    --     _ -> evalError $ "eval: " ++ show v ++ " isn't a closure"
    URef -> do
      loc <- freshLoc
      modify $ \(i, Env env) -> (i, Env $ add loc v env)
      return $ VLoc loc
    UDeref ->
      case v of
        VLoc x -> do
          (_, Env env) <- get
          case S.get x env of
            Just val -> return val
            _ -> evalError $ "eval: bad dereference of " ++ show x
        _ -> evalError $ "eval: " ++ show v ++ " isn't a loc"

eval (TmBinop _ b t1 t2) = do
  v1 <- eval t1
  v2 <- eval t2
  case binopType b of
    TyInt ->
      case b of
        BPlus   -> return $ VInt $ intOfValue v1 + intOfValue v2
        BMinus  -> return $ VInt $ intOfValue v1 - intOfValue v2
        BMult   -> return $ VInt $ intOfValue v1 * intOfValue v2
        BDiv    -> return $ VInt $ intOfValue v1 `div` intOfValue v2
        _ -> evalError $ "eval: " ++ show b ++ " isn't an arithmetic binop"
    TyBool ->
      case b of
        BEq     -> return $ VBool $ intOfValue v1 == intOfValue v2
        BNeq    -> return $ VBool $ intOfValue v1 /= intOfValue v2
        BLt     -> return $ VBool $ intOfValue v1 < intOfValue v2
        BLe     -> return $ VBool $ intOfValue v1 <= intOfValue v2
        BGt     -> return $ VBool $ intOfValue v1 > intOfValue v2
        BGe     -> return $ VBool $ intOfValue v1 >= intOfValue v2
        BAnd    -> return $ VBool $ boolOfValue v1 && boolOfValue v2
        BOr     -> return $ VBool $ boolOfValue v1 || boolOfValue v2
        _ -> evalError $ "eval: " ++ show b ++ " isn't a boolean binop"
    TyUnit ->
      case b of
        BUpdate ->
          case v1 of
            VLoc x ->
              modify (\(i, Env env) -> (i, Env $ add x v2 env)) >>
              return VUnit
            _ -> evalError $ "eval: " ++ show v1 ++ " isn't a loc"
        _ -> evalError $ "eval: " ++ show b ++
             " isn't a reference update binop"

eval (TmLet _ x tm1 tm2) = do
  v1 <- eval tm1
  local (Env . add x v1 . unEnv) $ eval tm2

eval (TmVariant _ x tms) = VVariant x <$> mapM eval tms

eval (TmRecord _ fields) = VRecord <$> mapM (mapSndM eval) fields

-- Here we do the actual pattern matching work (extending environment
-- with bindings from the pattern match).
eval (TmMatch _ discrim cases) =
  eval discrim >>= go cases
  where
    go ((p, tm) : cs) v = do
      env <- ask
      case bindPattern p v env of
        Just e -> local (const e) $ eval tm
        -- If the pattern fails to match, try the next one.
        Nothing -> go cs v
    go [] _ =
      evalError "eval: failed to match any pattern"

eval tm@(TmPlaceholder _ _ _ _) =
  error $ "eval: unexpected placeholder: " ++ show tm

-- Given a pattern, a value to match against the pattern, and an
-- initial environment, produce an extended environment with bindings
-- produced by the pattern match. If it fails to match, return
-- Nothing.
bindPattern :: Pattern -> Value -> Env -> Maybe Env
bindPattern (PVar x) v = Just . extendEnv x v
bindPattern PUnit VUnit = Just . id
bindPattern (PBool True) (VBool True) = Just . id
bindPattern (PBool False) (VBool False) = Just . id
bindPattern (PInt n) (VInt m) =
  if n == m then Just . id else const Nothing
bindPattern (PChar n) (VChar m) =
  if n == m then Just . id else const Nothing
bindPattern (PPair p1 p2) (VVariant _ vs) =
  bindPattern p1 (vs!!0) >=> bindPattern p2 (vs!!1)
bindPattern (PConstructor x ps) (VVariant y vs) =
  if x == y then
    \e -> foldM (\acc (p, v) -> bindPattern p v acc) e $ zip ps vs
  else const Nothing
bindPattern (PRecord pfields) (VRecord vfields) =
  \e -> 
    foldM (\acc (x, p) ->
              case assocGet x vfields of
                Just v ->
                  bindPattern p v acc
                Nothing ->
                  Nothing) e pfields
bindPattern _ _ = const Nothing


-- Extend an environment with a new binding. If the identifier is "_",
-- this is a noop. This prevents unnecessary binding of unused
-- variables.
extendEnv :: Id -> Value -> Env -> Env
extendEnv x v =
  case x of
    Id "_" -> id
    _ -> Env . add x v . unEnv
