module Main where

import Control.Monad
import System.Environment (getArgs)
-- import System.IO (hGetContents)
import Ast (Prog(..))
import Core (genTypeVars)
import Interp (interpProg)
import JS (compileJS)
import Lexer (AlexPosn)
import Parser (parseProg)
import Preprocessor (importLines, substImports)
import Tycheck (tycheckProg, runTycheck, TyData)

main :: IO ()
main = do
  args <- getArgs

  -- Read in source file
  src <- readFile $ case args of
                      f:_ -> f
                      []  -> error "Error: no input file"
  -- Locate import commands
  let imports = importLines (lines src)

  -- Map imports to their corresponding source code
  import_srcs <- mapM
    (\(lnum, imps) ->
        sequence (lnum, (mapM (readFile . (++ ".hk")) imps)))
    imports

  -- Replace imports by inlining their source code
  let src' = substImports src import_srcs
  
  -- Parse and typecheck the final source code.
  -- On success, run the interpreter on the AST.
  result <- case parseAndTycheck src' of
              Left s -> putStrLn "" >> error s
              Right (p', warnings) -> do
                forM_ warnings putStrLn
                let js_src = compileJS "" $ prog_of p'
                -- putStrLn js_src
                if length args > 1 then do
                  putStrLn $ "Writing generated JS to " ++ (args!!1) ++ "."
                  writeFile (args!!1) js_src else
                  return ()
                return $ interpProg p'

  -- let result = parseGenOnly src'

  -- Print the result
  putStrLn $ show result

parseOnly :: String -> Either String (Prog AlexPosn)
parseOnly f = parseProg "" f

parseGenOnly :: String -> Either String (Prog AlexPosn)
parseGenOnly = fmap genTypeVars . parseProg ""

parseAndTycheck :: String -> Either String (Prog TyData, [String])
parseAndTycheck =
  parseProg "" >=> runTycheck . tycheckProg . genTypeVars
