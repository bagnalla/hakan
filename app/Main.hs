module Main where

import Control.Monad
import System.Environment (getArgs)
-- import System.IO (hGetContents)
import Ast
import Core (genTypeVars, unify, FreeTyVars(..), TySubstable(..))
import Interp (interpProg)
import Parser (parseProg)
import Preprocessor (importLines, substImports)
import Symtab (Id(..))
import Tycheck (tycheckProg, runTycheck)

main :: IO ()
main = do
  args <- getArgs

  -- Read in source file
  src <- readFile $ case args of
                      [f] -> f
                      []  -> error "Error: no input file"
  -- Locate import commands
  let imports = importLines (lines src)

  -- Map imports to their corresponding source code
  import_srcs <- mapM
    (\(lnum, imps) ->
        sequence (lnum, (mapM (readFile . (++ ".cf")) imps)))
    imports

  -- Replace imports by inlining their source code
  let src' = substImports src import_srcs

  -- let ast = parseAndTycheck src'
  -- putStrLn $ show ast

  -- let ty1 = TyVar False (Id "a")
  -- let ty2 = TyVar False (Id "b")
  -- let a = freetyvars (tysubst ty1 ty2 (TyPair ty1 ty2))
  -- let b = tysubst ty1 ty2 (freetyvars (TyPair ty1 ty2))
  -- putStrLn $ show a
  -- putStrLn $ show b

  -- let fvs = freetyvars $ TyVar False (Id "a")
  -- putStrLn $ show fvs

  -- putStrLn $ show $ unify [(TyVar $ Id "a", TyPair TyUnit TyUnit)]
  
  -- Parse and typecheck the final source code.
  -- On success, run the interpreter on the AST.
  let result = case parseAndTycheck src' of
                 Left s -> error s
                 Right p' -> interpProg p'

  -- Print the result
  putStrLn $ show result

parseOnly f = parseProg "" f

parseGenOnly f = do
  p <- parseProg "" f
  let p' = genTypeVars p
  return p'

parseAndTycheck f = do
  p <- parseProg "" f
  let p' = genTypeVars p
  p'' <- runTycheck (tycheckProg p')
  return p''
