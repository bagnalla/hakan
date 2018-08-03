module Interp (
  interpProg
  ) where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Ast
import Symtab (Symtab, Id, empty, add, fold)
import qualified Symtab (get)
import Eval (eval, Value(..), Env(..))

type InterpM a = ReaderT Env (StateT (Int, Env) Identity) a

initEnv = Env empty
initState = (0, Env empty)

-- | Interpret a program by interpreting its commands in sequence.
interpProg :: Prog α -> Value
interpProg =
  runIdentity . flip evalStateT initState . flip runReaderT initEnv .
  interpCommands . prog_of . eraseData

interpCommands :: [Command ()] -> InterpM Value
interpCommands [] = return VUnit
interpCommands (CDecl _ _ _ : cs) = interpCommands cs
interpCommands (CLet _ nm tm : cs) = do
  v <- eval tm
  local (Env . add nm v . unEnv) $ interpCommands cs
interpCommands (CEval _ tm : []) = eval tm
interpCommands (CEval _ tm : cs) = eval tm >> interpCommands cs
