module Main where

import Control.Monad
import System.Environment (getArgs)
-- import System.IO (hGetContents)
import Ast
import Core (genTypeVars, unify)
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
        sequence (lnum, (mapM (readFile . (++ ".hk")) imps)))
    imports

  -- Replace imports by inlining their source code
  let src' = substImports src import_srcs

  let ast = parseAndTycheck src'
  putStrLn $ show ast

  -- let tyx = TyVar False (Id "x")
  -- let tyy = TyVar False (Id "y")
  -- let typair = TyVariant (Id "Pair") [tyx, tyy] []
  -- let ty1 = TyAbs (Id "y") KStar typair
  -- let ty2 = TyAbs (Id "x") KStar ty1
  -- let ty3 = TyApp (TyApp ty2 TyBool) TyInt
  -- putStrLn $ show ty3
  -- putStrLn $ show $ normalize ty3

  -- putStrLn $ show $ freetyvars typair

  -- let ty2 = TyVar False (Id "b")
  -- let a = freetyvars (tysubst ty1 ty2 (TyPair ty1 ty2))
  -- let b = tysubst ty1 ty2 (freetyvars (TyPair ty1 ty2))
  -- putStrLn $ show a
  -- putStrLn $ show b
  
  -- Parse and typecheck the final source code.
  -- On success, run the interpreter on the AST.
  result <- case parseAndTycheck src' of
              Left s -> error s
              Right (p', warnings) -> do
                forM_ warnings putStrLn
                return $ interpProg p'

  -- let result = parseGenOnly src'

  -- Print the result
  putStrLn $ show result

parseOnly f = parseProg "" f

parseGenOnly = fmap genTypeVars . parseProg ""

parseAndTycheck =
  parseProg "" >=> runTycheck . tycheckProg . genTypeVars
