{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

-- | This module defines monadic computations (reader and state) for
-- big-step term evaluation.

module Eval (
  eval, Value(..), Env(..)
  ) where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

import Ast
import Symtab (Symtab, Id(..), empty, add, exists, fold)
import qualified Symtab as S (map, get)

newtype Env = Env { unEnv :: Symtab Value }
  deriving Eq

data Value =
  VUnit
  | VBool Bool
  | VInt Integer
  | VClos Env Id (Term ())
  | VPair Value Value
  | VInl Value
  | VInr Value
  | VLoc Id
  deriving Eq

instance Show Value where
  show VUnit = "VUnit"
  show (VBool b) = "(VBool " ++ show b ++ ")"
  show (VInt i) = "(VInt " ++ show i ++ ")"
  show (VClos env x t) = "(VClos " ++ show x ++ " " ++ show t ++ ")"
  show (VPair v1 v2) = "(VPair " ++ show v1 ++ " " ++ show v2 ++ ")"
  show (VInl v) = "(VInl " ++ show v ++ ")"
  show (VInr v) = "(VInr " ++ show v ++ ")"
  show (VLoc x) = "(VLoc " ++ show x ++ ")"

instance Show Env where
  show =
    fold (\acc nm v -> acc ++ show nm ++ ": " ++ show v ++ "\n") "" . unEnv

intOfValue :: Value -> Integer
intOfValue (VInt i) = i
intOfValue _ = error "intOfValue: expected VInt"

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
  env <- ask
  (_, heap) <- get
  error $ "environment:\n" ++ show env ++ "\n\n heap: " ++
    show heap ++ "\n\n" ++ s


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
    _ -> evalError $ "eval: " ++ show v1 ++ " isn't a closure"

eval (TmUnit _) = return VUnit
eval (TmBool _ b) = return $ VBool b

eval (TmIf _ t1 t2 t3) = do
  v1 <- eval t1
  case v1 of
    VBool True  -> eval t2
    VBool False -> eval t3
    _ -> evalError $ "eval: " ++ show v1 ++ " isn't a bool"

eval (TmInt _ i) = return $ VInt i

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
    UFix ->
      case v of
        VClos clos nm tm' ->
          mfix $ \f -> local (const $ extendEnv nm f clos) $ eval tm'
        _ -> evalError $ "eval: " ++ show v ++ " isn't a closure"
    UFst ->
      case v of
        VPair x _ -> return x
        _ -> evalError $ "eval: " ++ show v ++ " isn't a pair"
    USnd ->
      case v of
        VPair _ y -> return y
        _ -> evalError $ "eval: " ++ show v ++ " isn't a pair"
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

eval (TmPair _ t1 t2) = do
  v1 <- eval t1
  v2 <- eval t2
  return $ VPair v1 v2

eval (TmInl _ tm _) = VInl <$> eval tm
eval (TmInr _ tm _) = VInr <$> eval tm

eval (TmCase _ discrim nm1 t1 nm2 t2) = do
  v <- eval discrim
  case v of
    VInl x -> local (extendEnv nm1 x) $ eval t1
    VInr x -> local (extendEnv nm2 x) $ eval t2
    _ -> evalError $ "eval: " ++ show v ++
         " isn't a left or right injection"

eval (TmLet _ x tm1 tm2) = do
  v1 <- eval tm1
  local (Env . add x v1 . unEnv) $ eval tm2


extendEnv :: Id -> Value -> Env -> Env
extendEnv x v =
  case x of
    Id "_" -> id
    _ -> Env . add x v . unEnv
