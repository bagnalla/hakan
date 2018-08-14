module Interp (
  interpProg
  ) where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Ast
import Symtab (Symtab, Id, empty, add, fold)
import qualified Symtab (get, Id(..))
import Eval (eval, Value(..), Env(..))

type InterpM a = WriterT [String] (ReaderT Env (StateT (Int, Env) Identity)) a

initEnv = Env empty
initState = (0, Env empty)

-- | Interpret a program by interpreting its commands in sequence.
-- For now since we have no I/O, we can build up a list of strings to
-- print at the end.
interpProg :: Prog α -> (Value, [String])
interpProg =
  runIdentity . flip evalStateT initState . flip runReaderT initEnv .
  runWriterT . interpCommands . prog_of . eraseData

interpCommands :: [Command ()] -> InterpM Value
interpCommands [] = return VUnit
interpCommands (CDecl _ _ _ : cs) = interpCommands cs
interpCommands (CLet _ nm tm : cs) = do
  v <- eval tm
  local (Env . add nm v . unEnv) $ interpCommands cs
interpCommands (CEval _ tm : []) = eval tm
interpCommands (CEval _ tm : cs) = eval tm >> interpCommands cs
-- Build constructor functions and add them to the context.
interpCommands (CData _ nm _ ctors : cs) = do
  funs <-
    mapM (\(x, tys) -> do
             let ids = map (Symtab.Id . (:[])) $
                       take (length tys) ['a'..]
             val <- eval $ mkAbs ids (TmVariant () nm $ map (TmVar ()) ids)
             return $ (x, val)) ctors
  local (\(Env e) -> Env $ foldl (\acc (x, f) -> add x f acc) e funs) $
    interpCommands cs
