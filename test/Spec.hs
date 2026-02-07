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

data RunStatus =
  RunOk
  | RunError
  deriving (Eq, Show)

data ExecResult = ExecResult
  { execCode :: ExitCode
  , execStdout :: String
  , execStderr :: String
  } deriving Show

data Expectations = Expectations
  { expectedStatus :: ExpectedStatus
  , expectedValue :: Maybe String
  , expectedJSStatus :: RunStatus
  , expectedCStatus :: RunStatus
  , expectedJSOut :: Maybe String
  , expectedCOut :: Maybe String
  } deriving Show

defaultExpectations :: Expectations
defaultExpectations = Expectations
  { expectedStatus = ExpectOk
  , expectedValue = Nothing
  , expectedJSStatus = RunOk
  , expectedCStatus = RunOk
  , expectedJSOut = Nothing
  , expectedCOut = Nothing
  }

casesFile :: FilePath
casesFile = "test/fixtures/cases.txt"

backendCasesFile :: FilePath
backendCasesFile = "test/fixtures/backend_cases.txt"

backendKnownFailCCasesFile :: FilePath
backendKnownFailCCasesFile = "test/fixtures/backend_known_fail_c_cases.txt"

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
  normalFailures <- do
    exists <- doesFileExist backendCasesFile
    if not exists then return [] else do
      casePaths <- loadCasePaths backendCasesFile
      jsFailures <- runBackendSuite "JS" ["stack", "node"] (runJSCase casePaths)
      cFailures <- runBackendSuite "C" ["stack", "gcc"] (runCCase casePaths)
      return $ jsFailures ++ cFailures
  knownFailFailures <- do
    exists <- doesFileExist backendKnownFailCCasesFile
    if not exists then return [] else do
      casePaths <- loadCasePaths backendKnownFailCCasesFile
      runBackendSuite
        "C-known-fail"
        ["stack", "node", "gcc"]
        (runKnownFailCCase casePaths)
  return $ normalFailures ++ knownFailFailures

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
    runOne path = do
      src <- readFile path
      let ex = parseExpectations src
      case expectedJSStatus ex of
        RunOk ->
          case expectedJSOut ex of
            Nothing -> return $ Just $ path ++ ": missing EXPECT-JS-OUT directive."
            Just expectedOut ->
              expectBackendRun "JS" path RunOk (Just expectedOut) =<< runJSExec path
        RunError ->
          expectBackendRun "JS" path RunError (expectedJSOut ex) =<< runJSExec path

runCCase :: [FilePath] -> IO [Maybe String]
runCCase = mapM runOne
  where
    runOne path = do
      src <- readFile path
      let ex = parseExpectations src
      case expectedCStatus ex of
        RunOk ->
          case expectedCOut ex of
            Nothing -> return $ Just $ path ++ ": missing EXPECT-C-OUT directive."
            Just expectedOut ->
              expectBackendRun "C" path RunOk (Just expectedOut) =<< runCExec path
        RunError ->
          expectBackendRun "C" path RunError (expectedCOut ex) =<< runCExec path

runKnownFailCCase :: [FilePath] -> IO [Maybe String]
runKnownFailCCase = mapM runOne
  where
    runOne path = do
      src <- readFile path
      let ex = parseExpectations src
      case (expectedJSOut ex, expectedCOut ex) of
        (Nothing, _) ->
          return $ Just $ path ++ ": missing EXPECT-JS-OUT directive."
        (_, Nothing) ->
          return $ Just $ path ++ ": missing EXPECT-C-OUT directive."
        (Just jsExpected, Just cExpected) -> do
          jsResult <- runJSExec path
          jsFailure <- expectBackendRun "JS" path RunOk (Just jsExpected) jsResult
          case jsFailure of
            Just msg ->
              return $ Just $
                "known-fail C case has broken JS baseline (" ++ path ++ "):\n" ++ msg
            Nothing -> do
              cResult <- runCExec path
              case cResult of
                Left _ ->
                  return Nothing
                Right cExec ->
                  if execCode cExec == ExitSuccess &&
                     trim (execStdout cExec) == trim cExpected then
                    return $ Just $
                      path ++ ": known-fail C case now matches expected output; " ++
                      "promote it to test/fixtures/backend_cases.txt"
                  else
                    return Nothing

expectBackendRun
  :: String
  -> FilePath
  -> RunStatus
  -> Maybe String
  -> Either String ExecResult
  -> IO (Maybe String)
expectBackendRun backend path expectedStatus expectedOut result =
  case result of
    Left e ->
      return $ Just $ path ++ ": " ++ backend ++ " run failed:\n" ++ e
    Right exec ->
      case expectedStatus of
        RunOk ->
          case execCode exec of
            ExitSuccess ->
              case expectedOut of
                Nothing ->
                  return $ Just $
                    path ++ ": " ++ backend ++ " expected output directive is missing."
                Just wanted ->
                  if trim (execStdout exec) == trim wanted then
                    return Nothing
                  else
                    return $ Just $
                      path ++ ": " ++ backend ++ " output mismatch. expected " ++
                      show wanted ++ ", got " ++ show (trim $ execStdout exec)
            ExitFailure _ ->
              return $ Just $
                path ++ ": " ++ backend ++ " expected success but failed:\n" ++
                renderExecResult exec
        RunError ->
          case execCode exec of
            ExitSuccess ->
              return $ Just $
                path ++ ": " ++ backend ++ " expected runtime failure but succeeded."
            ExitFailure _ ->
              case expectedOut of
                Nothing -> return Nothing
                Just wanted ->
                  if trim (execStdout exec) == trim wanted then
                    return Nothing
                  else
                    return $ Just $
                      path ++ ": " ++ backend ++ " failure output mismatch. expected " ++
                      show wanted ++ ", got " ++ show (trim $ execStdout exec)

runJSExec :: FilePath -> IO (Either String ExecResult)
runJSExec path = do
  let jsOutPath = "/tmp/hakan_backend_test.js"
  compiled <- runCmd "stack" ["exec", "hakan-exe", path, "js", jsOutPath]
  case compiled of
    Left e -> return $ Left $ "JS compile failed:\n" ++ e
    Right () -> Right <$> runCmdCapture "node" [jsOutPath]

runCExec :: FilePath -> IO (Either String ExecResult)
runCExec path = do
  let cOutPath = "/tmp/hakan_backend_test.c"
  let cBinPath = "/tmp/hakan_backend_test.bin"
  compiled <- runCmd "stack" ["exec", "hakan-exe", path, "c", cOutPath]
  case compiled of
    Left e -> return $ Left $ "C compile failed:\n" ++ e
    Right () -> do
      built <- runCmd
        "gcc"
        ["-g", "-I", "out", cOutPath, "-no-pie", "out/gc.a", "-o", cBinPath]
      case built of
        Left e -> return $ Left $ "C build failed:\n" ++ e
        Right () -> Right <$> runCmdCapture cBinPath []

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

runCmdCapture :: FilePath -> [String] -> IO ExecResult
runCmdCapture prog args = do
  res <- readProcessWithExitCode prog args ""
  case res of
    (code, out, err) ->
      return ExecResult
        { execCode = code
        , execStdout = out
        , execStderr = err
        }

renderExecResult :: ExecResult -> String
renderExecResult exec =
  unlines
    [ "exit code: " ++ show (execCode exec)
    , "stdout:"
    , execStdout exec
    , "stderr:"
    , execStderr exec
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
      | "EXPECT-JS-STATUS:" `isPrefixOfCI` body ->
          ex { expectedJSStatus =
                 parseRunStatus (expectedJSStatus ex) $
                 trim $ dropPrefix "EXPECT-JS-STATUS:" body
             }
      | "EXPECT-C-STATUS:" `isPrefixOfCI` body ->
          ex { expectedCStatus =
                 parseRunStatus (expectedCStatus ex) $
                 trim $ dropPrefix "EXPECT-C-STATUS:" body
             }
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

parseRunStatus :: RunStatus -> String -> RunStatus
parseRunStatus fallback raw =
  case map toUpper raw of
    "OK" -> RunOk
    "SUCCESS" -> RunOk
    "PASS" -> RunOk
    "ERROR" -> RunError
    "FAIL" -> RunError
    "FAILURE" -> RunError
    _ -> fallback

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
