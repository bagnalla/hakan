-- | This module defines a type for identifiers along with an abstract
-- datatype for maps indexed by them.

module Symtab (
  Id(..),
  Symtab,
  empty,
  add,
  get,
  exists,
  keys,
  fold,
  Symtab.map,
  mapi
  ) where

-- Use Haskell's map data structure
import qualified Data.Map.Strict as Map

-- an Id is just a String
newtype Id = Id String
  deriving (Eq, Ord)

-- A Symtab maps Ids to values of some type
type Symtab a = Map.Map Id a

-- The empty Symtab
empty = Map.empty 

-- Add a binding to a Symtab
add k = Map.insert k

-- Get the value bound to an Id
get :: Id -> Symtab a -> Maybe a
get = Map.lookup

-- Check if an Id is bound in a Symtab
exists :: Id -> Symtab a -> Bool
exists = Map.member

-- Return list of Ids bound in a Symtab
keys :: Symtab a -> [Id]
keys = Map.keys

-- Fold over all key/value pairs
fold :: (a -> Id -> b -> a) -> a -> Symtab b -> a
fold = Map.foldlWithKey

-- Map values
map :: (a -> b) -> Symtab a -> Symtab b
map = Map.map

-- Map where the function receives the Id as well as the value
mapi :: (Id -> a -> b) -> Symtab a -> Symtab b
mapi = Map.mapWithKey

----------------------
-- | Typeclass instances

instance Show Id where
  show (Id s) = s
