-- | This module defines an infinite sequence of fresh variable names.

module Gensym (
  nextSym, nextSym2, nextSym3, nextSymN
  ) where

import Control.Monad.State

-- Works for any string-valued state monad as long as its state is
-- numeric and showable.
nextSym :: (Num s, Show s, MonadState s m) => String -> m String
nextSym prefix = do
  i <- get
  put $ i + 1
  return $ prefix ++ show i

nextSym2 :: (Num s, Show s, MonadState s m) => String -> m (String, String)
nextSym2 prefix = do
  i <- get
  put $ i + 2
  return (prefix ++ show i, prefix ++ show (i+1))

nextSym3 :: (Num s, Show s, MonadState s m) => String ->
            m (String, String, String)
nextSym3 prefix = do
  i <- get
  put $ i + 3
  return (prefix ++ show i, prefix ++ show (i+1), prefix ++ show (i+2))

nextSymN :: (Enum s, Num s, Show s, MonadState s m) =>
            String -> s -> m [String]
nextSymN prefix n = do
  i <- get
  put $ i + n
  return $ map ((++) prefix . show) [i..i+n-1]
