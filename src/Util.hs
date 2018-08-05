
module Util where

import System.IO.Unsafe

-- debugPrint :: String -> b -> b
-- debugPrint s x = seq (unsafePerformIO $ putStrLn $ s) x

debugPrint :: String -> b -> b
debugPrint _ x = x
