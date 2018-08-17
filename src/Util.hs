
module Util where

import Data.Bifunctor
import System.IO.Unsafe

debugPrint :: String -> b -> b
debugPrint s x = seq (unsafePerformIO $ putStrLn $ s) x

-- debugPrint :: String -> b -> b
-- debugPrint _ = id

tupleFun :: (a -> b) -> (a -> c) -> a -> (b, c)
tupleFun f g x = (f x, g x)

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst = flip bimap id

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd = bimap id

-- Is there a cooler way to implement this?
mapSndM :: Monad m => (b -> m c) -> m (a, b) -> m (a, c)
mapSndM f x = do
  (y, z) <- x
  z' <- f z
  return (y, z')

-- Specialized to 3-tuples.
trimap :: (a -> d) -> (b -> e) -> (c -> f) -> (a, b, c) -> (d, e, f)
trimap f g h (x, y, z) = (f x, g y, h z)

-- Specialized to 4-tuples.
quadmap :: (a -> e) -> (b -> f) -> (c -> g) -> (d -> h) ->
           (a, b, c, d) -> (e, f, g, h)
quadmap f g h k (x, y, z, w) = (f x, g y, h z, k w)
