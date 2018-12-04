-- | This module defines a type for identifiers along with an abstract
-- datatype for maps indexed by them.

module Symtab (
  Id(..), Symtab, empty, add, get, exists, keys, fold, Symtab.map, mapi,
  assocGet, assocSet, assocUpdate, assocIndex, fromList
  ) where

-- Use Haskell's map data structure
import qualified Data.Map as Map
import Test.QuickCheck


-- an Id is just a String
newtype Id = Id { unId :: String }
  deriving (Eq, Ord)

intToId :: Int -> Id
intToId 0 = Id "a"
intToId 1 = Id "b"
intToId _ = Id "c"

instance Arbitrary Id where
  arbitrary = intToId <$> choose (0, 2)

assocGet :: Id -> [(Id, a)] -> Maybe a
assocGet _ [] = Nothing
assocGet x ((y, v) : ys) = if x == y then Just v else assocGet x ys

-- Replace existing binding if it exists.
assocSet :: Id -> a -> [(Id, a)] -> [(Id, a)]
assocSet nm x [] = [(nm, x)]
assocSet nm x ((nm', x'):ys) =
  if nm == nm' then (nm, x) : ys else (nm', x') : assocSet nm x ys

-- Update the value associated with an Id.
assocUpdate :: Id -> (a -> a) -> [(Id, a)] -> [(Id, a)]
assocUpdate nm f [] = error $ "assocUpdate: " ++ show nm ++ " not found"
assocUpdate nm f ((nm', x):ys) =
  if nm == nm' then (nm, f x) : ys else (nm', x) : assocUpdate nm f ys

assocIndex :: Id -> [(Id, a)] -> Maybe Int
assocIndex nm ((x, _):xs) =
  if nm == x then Just 0 else (+ 1) <$> assocIndex nm xs
assocIndex nm [] = Nothing

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

fromList :: [(Id, a)] -> Symtab a
fromList = Map.fromList

----------------------
-- | Typeclass instances

instance Show Id where
  show (Id s) = s
