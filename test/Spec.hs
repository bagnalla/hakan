module Main where

import Control.Monad (forM)
import Data.Char (isSpace, toUpper)
import Data.List (isPrefixOf)
import Data.Maybe (catMaybes)
import System.Exit (exitFailure)

import Core (genTypeVars)
import Ast (Prog)
import Interp (interpProg)
import Parser (parseProg)
import Preprocessor (importLines, substImports)
import Tycheck (TyData, runTycheck, tycheckProg)

data ExpectedStatus =
  ExpectOk
  | ExpectError (Maybe String)
  deriving Show

data Expectations = Expectations
  { expectedStatus :: ExpectedStatus
  , expectedValue :: Maybe String
  } deriving Show

defaultExpectations :: Expectations
defaultExpectations = Expectations
  { expectedStatus = ExpectOk
  , expectedValue = Nothing
  }

casesFile :: FilePath
casesFile = "test/fixtures/cases.txt"

main :: IO ()
main = do
  casePaths <- loadCasePaths casesFile
  failures <- catMaybes <$> mapM runCase casePaths
  if null failures then
    putStrLn $ "All fixture tests passed (" ++ show (length casePaths) ++ ")."
  else do
    putStrLn $ "Fixture test failures: " ++ show (length failures)
    mapM_ putStrLn failures
    exitFailure

runCase :: FilePath -> IO (Maybe String)
runCase path = do
  src <- readFile path
  let ex = parseExpectations src
  result <- parseAndTycheck path src
  case result of
    Left err ->
      case expectedStatus ex of
        ExpectOk ->
          return $ Just $ path ++ ": expected success but failed:\n" ++ err
        ExpectError maybeNeedle ->
          case maybeNeedle of
            Just needle
              | needle `isInfix` err -> return Nothing
              | otherwise ->
                  return $ Just $
                    path ++ ": expected error containing " ++ show needle ++
                    " but got:\n" ++ err
            Nothing -> return Nothing
    Right (prog, _) ->
      case expectedStatus ex of
        ExpectError _ ->
          return $ Just $ path ++ ": expected failure but parse/typecheck succeeded."
        ExpectOk ->
          case expectedValue ex of
            Nothing -> return Nothing
            Just wanted ->
              let (val, _) = interpProg prog
                  actual = show val
              in if trim wanted == trim actual then
                   return Nothing
                 else
                   return $ Just $
                     path ++ ": expected value " ++ show wanted ++
                     " but got " ++ show actual

parseAndTycheck :: FilePath -> String -> IO (Either String (Prog TyData, [String]))
parseAndTycheck path src = do
  src' <- inlineImports src
  return $ parseProg path src' >>= runTycheck . tycheckProg . genTypeVars

inlineImports :: String -> IO String
inlineImports src = do
  let imports = importLines (lines src)
  importSrcs <- forM imports $ \(lineNum, modules) -> do
    srcs <- mapM (\m -> readFile (m ++ ".hk")) modules
    return (lineNum, srcs)
  return $ substImports src importSrcs

parseExpectations :: String -> Expectations
parseExpectations = foldl parseDirective defaultExpectations . lines

parseDirective :: Expectations -> String -> Expectations
parseDirective ex line =
  case commentBody line of
    Nothing -> ex
    Just body
      | "EXPECT-VALUE:" `isPrefixOfCI` body ->
          ex { expectedValue = Just $ trim $ dropPrefix "EXPECT-VALUE:" body }
      | "EXPECT-ERROR:" `isPrefixOfCI` body ->
          ex
            { expectedStatus =
                ExpectError (Just $ trim $ dropPrefix "EXPECT-ERROR:" body)
            }
      | "EXPECT:" `isPrefixOfCI` body ->
          parseExpectStatus ex $ trim $ dropPrefix "EXPECT:" body
      | otherwise -> ex

parseExpectStatus :: Expectations -> String -> Expectations
parseExpectStatus ex raw =
  case map toUpper raw of
    "OK" -> ex { expectedStatus = ExpectOk }
    "SUCCESS" -> ex { expectedStatus = ExpectOk }
    "PASS" -> ex { expectedStatus = ExpectOk }
    "ERROR" -> ex { expectedStatus = ExpectError Nothing }
    "FAIL" -> ex { expectedStatus = ExpectError Nothing }
    _ -> ex

loadCasePaths :: FilePath -> IO [FilePath]
loadCasePaths path = do
  raw <- readFile path
  return $ filter isCasePath $ map trim (lines raw)

isCasePath :: String -> Bool
isCasePath s =
  not (null s) &&
  not ("#" `isPrefixOf` s) &&
  not ("--" `isPrefixOf` s)

commentBody :: String -> Maybe String
commentBody line
  | "#" `isPrefixOf` t = Just $ trim $ drop 1 t
  | "--" `isPrefixOf` t = Just $ trim $ drop 2 t
  | otherwise = Nothing
  where
    t = trim line

isPrefixOfCI :: String -> String -> Bool
isPrefixOfCI prefix s =
  map toUpper prefix `isPrefixOf` map toUpper s

dropPrefix :: String -> String -> String
dropPrefix prefix s = drop (length prefix) s

isInfix :: String -> String -> Bool
isInfix needle haystack = any (needle `isPrefixOf`) (tails haystack)
  where
    tails [] = [[]]
    tails xs@(_:rest) = xs : tails rest

trim :: String -> String
trim = rstrip . lstrip
  where
    lstrip = dropWhile isSpace
    rstrip = reverse . dropWhile isSpace . reverse
