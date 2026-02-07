module Main where

import Control.Monad (forM)
import Data.Char (isSpace, toUpper)
import Data.List (intercalate, isPrefixOf)
import Data.Maybe (catMaybes)
import System.Directory (doesFileExist, findExecutable)
import System.Exit (ExitCode(..), exitFailure)
import System.Process (readProcessWithExitCode)

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
  , expectedJSOut :: Maybe String
  , expectedCOut :: Maybe String
  } deriving Show

defaultExpectations :: Expectations
defaultExpectations = Expectations
  { expectedStatus = ExpectOk
  , expectedValue = Nothing
  , expectedJSOut = Nothing
  , expectedCOut = Nothing
  }

casesFile :: FilePath
casesFile = "test/fixtures/cases.txt"

backendCasesFile :: FilePath
backendCasesFile = "test/fixtures/backend_cases.txt"

main :: IO ()
main = do
  casePaths <- loadCasePaths casesFile
  fixtureFailures <- catMaybes <$> mapM runCase casePaths
  backendFailures <- runBackendSuites
  let failures = fixtureFailures ++ backendFailures
  if null failures then
    putStrLn $
      "All fixture tests passed (" ++ show (length casePaths) ++
      " frontend + backend suites)."
  else do
    putStrLn $ "Fixture test failures: " ++ show (length failures)
    mapM_ putStrLn failures
    exitFailure

runBackendSuites :: IO [String]
runBackendSuites = do
  exists <- doesFileExist backendCasesFile
  if not exists then return [] else do
    casePaths <- loadCasePaths backendCasesFile
    jsFailures <- runBackendSuite "JS" ["stack", "node"] (runJSCase casePaths)
    cFailures <- runBackendSuite "C" ["stack", "gcc"] (runCCase casePaths)
    return $ jsFailures ++ cFailures

runBackendSuite :: String -> [String] -> IO [Maybe String] -> IO [String]
runBackendSuite name deps runCases = do
  missing <- missingExecutables deps
  if null missing then do
    failures <- catMaybes <$> runCases
    if null failures then
      putStrLn $ name ++ " backend fixtures passed."
    else
      putStrLn $ name ++ " backend fixture failures: " ++ show (length failures)
    return failures
  else do
    putStrLn $
      "Skipping " ++ name ++ " backend fixtures (missing tools: " ++
      intercalate ", " missing ++ ")."
    return []

missingExecutables :: [String] -> IO [String]
missingExecutables = fmap catMaybes . mapM missingExecutable
  where
    missingExecutable exe = do
      found <- findExecutable exe
      return $ case found of
        Just _ -> Nothing
        Nothing -> Just exe

runJSCase :: [FilePath] -> IO [Maybe String]
runJSCase = mapM runOne
  where
    jsOutPath = "/tmp/hakan_backend_test.js"
    runOne path = do
      src <- readFile path
      let ex = parseExpectations src
      case expectedJSOut ex of
        Nothing -> return $ Just $ path ++ ": missing EXPECT-JS-OUT directive."
        Just expectedOut -> do
          compiled <- runCmd "stack" ["exec", "hakan-exe", path, "js", jsOutPath]
          case compiled of
            Left e -> return $ Just $ path ++ ": JS compile failed:\n" ++ e
            Right () -> do
              ran <- runCmdOut "node" [jsOutPath]
              case ran of
                Left e -> return $ Just $ path ++ ": JS run failed:\n" ++ e
                Right actual ->
                  if trim actual == trim expectedOut then
                    return Nothing
                  else
                    return $ Just $
                      path ++ ": JS output mismatch. expected " ++ show expectedOut ++
                      ", got " ++ show (trim actual)

runCCase :: [FilePath] -> IO [Maybe String]
runCCase = mapM runOne
  where
    cOutPath = "/tmp/hakan_backend_test.c"
    cBinPath = "/tmp/hakan_backend_test.bin"
    runOne path = do
      src <- readFile path
      let ex = parseExpectations src
      case expectedCOut ex of
        Nothing -> return $ Just $ path ++ ": missing EXPECT-C-OUT directive."
        Just expectedOut -> do
          compiled <- runCmd "stack" ["exec", "hakan-exe", path, "c", cOutPath]
          case compiled of
            Left e -> return $ Just $ path ++ ": C compile failed:\n" ++ e
            Right () -> do
              built <- runCmd
                "gcc"
                ["-g", "-I", "out", cOutPath, "-no-pie", "out/gc.a", "-o", cBinPath]
              case built of
                Left e -> return $ Just $ path ++ ": C build failed:\n" ++ e
                Right () -> do
                  ran <- runCmdOut cBinPath []
                  case ran of
                    Left e -> return $ Just $ path ++ ": C run failed:\n" ++ e
                    Right actual ->
                      if trim actual == trim expectedOut then
                        return Nothing
                      else
                        return $ Just $
                          path ++ ": C output mismatch. expected " ++ show expectedOut ++
                          ", got " ++ show (trim actual)

runCmd :: FilePath -> [String] -> IO (Either String ())
runCmd prog args = do
  res <- readProcessWithExitCode prog args ""
  case res of
    (ExitSuccess, _, _) -> return $ Right ()
    (ExitFailure code, out, err) ->
      return $ Left $
        unlines
          [ "exit code: " ++ show code
          , "command: " ++ unwords (prog : args)
          , "stdout:"
          , out
          , "stderr:"
          , err
          ]

runCmdOut :: FilePath -> [String] -> IO (Either String String)
runCmdOut prog args = do
  res <- readProcessWithExitCode prog args ""
  case res of
    (ExitSuccess, out, _) -> return $ Right out
    (ExitFailure code, out, err) ->
      return $ Left $
        unlines
          [ "exit code: " ++ show code
          , "command: " ++ unwords (prog : args)
          , "stdout:"
          , out
          , "stderr:"
          , err
          ]

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
      | "EXPECT-JS-OUT:" `isPrefixOfCI` body ->
          ex { expectedJSOut = Just $ trim $ dropPrefix "EXPECT-JS-OUT:" body }
      | "EXPECT-C-OUT:" `isPrefixOfCI` body ->
          ex { expectedCOut = Just $ trim $ dropPrefix "EXPECT-C-OUT:" body }
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
