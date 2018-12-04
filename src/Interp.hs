module Interp (
  interpProg
  ) where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Ast
import Symtab (Symtab, Id(..), empty, add, fold)
import qualified Symtab (get)
import Eval (eval, Value(..), Env(..))
import Util (debugPrint)

type InterpM a =
  WriterT [String] (ReaderT Env (StateT (Int, Env) Identity)) a

initEnv = Env empty
initState = (0, initEnv)

-- | Interpret a program by interpreting its commands in sequence.
-- For now since we have no I/O, we can build up a list of strings to
-- print at the end.
interpProg :: Prog α -> (Value, [String])
interpProg =
  debugPrint "\ninterpProg" $
  runIdentity . flip evalStateT initState . flip runReaderT initEnv .
  runWriterT . interpCommands . prog_of . eraseData

interpCommands :: [Command ()] -> InterpM Value
interpCommands [] = return VUnit
interpCommands (CDecl _ _ _ : cs) = interpCommands cs
interpCommands (CCheck _ _ : cs) = interpCommands cs
interpCommands (CClass _ _ _ _ _ : cs) = interpCommands cs
interpCommands (CInstance _ _ _ _ _ : cs) = interpCommands cs
interpCommands (CLet _ nm tm : cs) = do
  v <- eval tm
  local (Env . add nm v . unEnv) $ interpCommands cs
interpCommands (CEval _ tm : []) = eval tm
interpCommands (CEval _ tm : cs) = eval tm >> interpCommands cs

-- Build constructor functions and add them to the environment.
interpCommands (CData _ nm _ ctors : cs) = do
  funs <-
    mapM (\(x, tys) -> do
             let ids = map (Id . (:[])) $
                       take (length tys) ['a'..]
             val <- eval $ mkAbs ids (TmVariant () x $ map (TmVar ()) ids)
             return $ (x, val)) ctors
  local (\(Env e) -> Env $ foldl (\acc (x, f) -> add x f acc) e funs) $
    interpCommands cs
    
-- Build field projection functions and add them to the environment. 
interpCommands (CRecord _ nm _ fields : cs) = do
  funs <- mapM (\(x, ty) -> do
                   val <- eval $ TmAbs () (Id "x") TyUnit
                          (TmMatch () (TmVar () (Id "x"))
                           [(PRecord [(x, PVar (Id "y"))],
                             TmVar () (Id "y"))])
                   return (x, val)) fields
  local (\(Env e) -> Env $ foldl (\acc (x, f) -> add x f acc) e funs) $
    interpCommands cs

-- Check that an assertion is true.
interpCommands (CAssert _ tm : cs) = do
  v <- eval tm
  case v of
    VBool True -> interpCommands cs
    VBool False -> error $ "Assertion failed: " ++ show tm
    _ -> error $ "Interp: bad assertion: " ++ show tm
