module Util where

import Data.Bifunctor
import Debug.Trace (trace)
import System.IO.Unsafe

-- debugPrint :: String -> b -> b
-- debugPrint = trace

debugPrint :: String -> b -> b
debugPrint = const id

tupleFun :: (a -> b) -> (a -> c) -> a -> (b, c)
tupleFun f g x = (f x, g x)

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
