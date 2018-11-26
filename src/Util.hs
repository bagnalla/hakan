module Util where

import Data.Bifunctor
import Data.Either
import Data.List (elemIndices, isInfixOf)
import Data.Maybe (catMaybes, listToMaybe)
import Debug.Trace (trace)
import System.IO.Unsafe

debugPrint :: String -> b -> b
debugPrint = trace

-- debugPrint :: String -> b -> b
-- debugPrint = const id

tupleFun :: (a -> b) -> (a -> c) -> a -> (b, c)
tupleFun f g x = (f x, g x)

app2 :: (c -> d -> e) -> (a -> c) -> (b -> d) -> a -> b -> e
app2 h f g = (. g) . (h . f)

pairFun :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
pairFun = (. (. snd)) . (tupleFun . (. fst))

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst = flip bimap id

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd = bimap id

mapFstM :: Monad m => (a -> m c) -> (a, b) -> m (c, b)
mapFstM f (x, y) = flip (,) y <$> f x

mapSndM :: Monad m => (b -> m c) -> (a, b) -> m (a, c)
mapSndM f (x, y) = (,) x <$> f y

-- Specialized to 3-tuples.
trimap :: (a -> d) -> (b -> e) -> (c -> f) -> (a, b, c) -> (d, e, f)
trimap f g h (x, y, z) = (f x, g y, h z)

-- Specialized to 4-tuples.
quadmap :: (a -> e) -> (b -> f) -> (c -> g) -> (d -> h) ->
           (a, b, c, d) -> (e, f, g, h)
quadmap f g h k (x, y, z, w) = (f x, g y, h z, k w)

allEq :: Eq a => [a] -> Bool
allEq [] = True
allEq (x:xs) = all (== x) xs

isSubsetOf :: Eq a => [a] -> [a] -> Bool
isSubsetOf xs ys = all (`elem` ys) xs

isEqualSet :: Eq a => [a] -> [a] -> Bool
isEqualSet xs ys = isSubsetOf xs ys && isSubsetOf ys xs

elemCount :: Eq a => a -> [a] -> Int
-- elemCount x xs = length $ elemIndices x xs
elemCount = (.) length . elemIndices

-- TODO: this may not be quite right...
isPermutationOf :: Eq a => [a] -> [a] -> Bool
isPermutationOf xs ys =
  -- length xs == length ys && all (`elem` ys) xs && all (`elem` xs) ys
  -- all (\x -> elemCount x xs == elemCount x ys) xs &&
  -- all (\y -> elemCount y ys == elemCount y xs) ys
  isEqualSet xs ys && all (\x -> elemCount x xs == elemCount x ys) xs

firstJust :: [Maybe a] -> Maybe a
firstJust = listToMaybe . catMaybes

-- removeLast :: [a] -> [a]
-- removeLast [] = error "removeLast: empty list"
-- removeLast l = take (length l - 1) l

-- Is this more efficient (n vs 2n)?
removeLast :: [a] -> [a]
removeLast [] = error "removeLast: empty list"
removeLast (_:[]) = []
removeLast (x:xs) = x : removeLast xs

-- Better name?
flattenSnd :: [(a, [b])] -> [(a, b)]
flattenSnd = concat . fmap (\(x, ys) -> zip (repeat x) ys)

mapEither :: (a -> c) -> (b -> d) -> Either a b -> Either c d
mapEither f _ (Left x)  = Left $ f x
mapEither _ g (Right y) = Right $ g y

mapEitherLeft :: (a -> c) -> Either a b -> Either c b
mapEitherLeft = flip mapEither id

mapEitherRight :: (b -> d) -> Either a b -> Either a d
mapEitherRight = mapEither id
