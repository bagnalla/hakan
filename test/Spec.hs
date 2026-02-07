module Main where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM, when)
import Data.Bits ((.&.))
import Data.Char (isSpace, toUpper)
import Data.List (intercalate, isPrefixOf)
import Data.Maybe (catMaybes)
import System.Directory (doesFileExist, findExecutable)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..), exitFailure)
import System.Process (readProcessWithExitCode)

import Core (genTypeVars)
import Ast (Prog)
import Eval (Value(..))
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

data FuzzConfig = FuzzConfig
  { fuzzCases :: Int
  , fuzzStartSeed :: Int
  , fuzzMaxDepth :: Int
  , fuzzProgressEvery :: Int
  } deriving Show

defaultFuzzConfig :: FuzzConfig
defaultFuzzConfig = FuzzConfig
  { fuzzCases = 0
  , fuzzStartSeed = 1
  , fuzzMaxDepth = 4
  , fuzzProgressEvery = 25
  }

data FuzzTy =
  FuzzInt
  | FuzzBool
  | FuzzOptInt
  | FuzzRec
  | FuzzList
  | FuzzTree
  | FuzzFun FuzzTy FuzzTy
  deriving (Eq, Show)

data FuzzExpr
  = FVar String
  | FIntLit Int
  | FBoolLit Bool
  | FOptNone
  | FOptSome FuzzExpr
  | FMatchOpt FuzzExpr FuzzExpr String FuzzExpr
  | FRecLit FuzzExpr FuzzExpr
  | FProjCount FuzzExpr
  | FProjOk FuzzExpr
  | FMatchRec FuzzExpr String String FuzzExpr
  | FListNil
  | FListCons FuzzExpr FuzzExpr
  | FMatchList FuzzExpr FuzzExpr String String FuzzExpr
  | FTreeLeaf FuzzExpr
  | FTreeNode FuzzExpr FuzzExpr
  | FMatchTree FuzzExpr String FuzzExpr String String FuzzExpr
  | FClassScoreInt FuzzExpr FuzzExpr
  | FClassScoreViaApply Int FuzzExpr FuzzExpr
  | FClassScoreViaPartial Int FuzzExpr FuzzExpr
  | FClassScoreViaWrap Int FuzzExpr FuzzExpr
  | FLam String FuzzExpr
  | FApp FuzzExpr FuzzExpr
  | FAdd FuzzExpr FuzzExpr
  | FSub FuzzExpr FuzzExpr
  | FEq FuzzExpr FuzzExpr
  | FIf FuzzExpr FuzzExpr FuzzExpr
  | FLet String FuzzExpr FuzzExpr
  deriving Show

casesFile :: FilePath
casesFile = "test/fixtures/cases.txt"

backendCasesFile :: FilePath
backendCasesFile = "test/fixtures/backend_cases.txt"

backendKnownFailCCasesFile :: FilePath
backendKnownFailCCasesFile = "test/fixtures/backend_known_fail_c_cases.txt"

differentialCasesFile :: FilePath
differentialCasesFile = "test/fixtures/backend_differential_cases.txt"

backendKnownFailDifferentialCasesFile :: FilePath
backendKnownFailDifferentialCasesFile =
  "test/fixtures/backend_known_fail_differential_cases.txt"

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
  differentialFailures <- do
    exists <- doesFileExist differentialCasesFile
    if not exists then return [] else do
      casePaths <- loadCasePaths differentialCasesFile
      runBackendSuite
        "Differential"
        ["stack", "node", "gcc"]
        (runDifferentialCase casePaths)
  knownDifferentialFailures <- do
    exists <- doesFileExist backendKnownFailDifferentialCasesFile
    if not exists then return [] else do
      casePaths <- loadCasePaths backendKnownFailDifferentialCasesFile
      runBackendSuite
        "Differential-known-fail"
        ["stack", "node", "gcc"]
        (runKnownFailDifferentialCase casePaths)
  knownFailFailures <- do
    exists <- doesFileExist backendKnownFailCCasesFile
    if not exists then return [] else do
      casePaths <- loadCasePaths backendKnownFailCCasesFile
      runBackendSuite
        "C-known-fail"
        ["stack", "node", "gcc"]
        (runKnownFailCCase casePaths)
  fuzzFailures <- runDifferentialFuzzSuite
  return $
    normalFailures ++
    differentialFailures ++
    knownDifferentialFailures ++
    knownFailFailures ++
    fuzzFailures

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

runDifferentialFuzzSuite :: IO [String]
runDifferentialFuzzSuite = do
  cfg <- loadFuzzConfig
  if fuzzCases cfg <= 0 then do
    putStrLn $
      "Skipping Differential-fuzz backend fixtures " ++
      "(set HAKAN_DIFF_FUZZ_CASES > 0 to enable)."
    return []
  else
    runBackendSuite
      "Differential-fuzz"
      ["stack", "node", "gcc"]
      (runDifferentialFuzzCases cfg)

loadFuzzConfig :: IO FuzzConfig
loadFuzzConfig = do
  cases <- readEnvInt "HAKAN_DIFF_FUZZ_CASES" (fuzzCases defaultFuzzConfig)
  startSeed <- readEnvInt "HAKAN_DIFF_FUZZ_START_SEED" (fuzzStartSeed defaultFuzzConfig)
  maxDepth <- readEnvInt "HAKAN_DIFF_FUZZ_MAX_DEPTH" (fuzzMaxDepth defaultFuzzConfig)
  progressEvery <- readEnvInt "HAKAN_DIFF_FUZZ_PROGRESS_EVERY" (fuzzProgressEvery defaultFuzzConfig)
  return FuzzConfig
    { fuzzCases = max 0 cases
    , fuzzStartSeed = startSeed
    , fuzzMaxDepth = max 1 maxDepth
    , fuzzProgressEvery = max 0 progressEvery
    }

readEnvInt :: String -> Int -> IO Int
readEnvInt key fallback = do
  raw <- lookupEnv key
  return $
    case raw of
      Nothing -> fallback
      Just val ->
        case reads val of
          [(n, rest)] | all isSpace rest -> n
          _ -> fallback

runDifferentialFuzzCases :: FuzzConfig -> IO [Maybe String]
runDifferentialFuzzCases cfg = do
  let seeds =
        take (fuzzCases cfg) [fuzzStartSeed cfg ..]
  forM (zip [1 ..] seeds) $ \(ix, seed) -> do
    let progress = fuzzProgressEvery cfg
    when (progress > 0 && (ix == 1 || ix `mod` progress == 0)) $
      putStrLn $
        "Differential fuzz progress: " ++ show ix ++ "/" ++ show (fuzzCases cfg)
    runDifferentialFuzzCase cfg seed

runDifferentialFuzzCase :: FuzzConfig -> Int -> IO (Maybe String)
runDifferentialFuzzCase cfg seed = do
  let (targetTy, expr) = genFuzzCase seed (fuzzMaxDepth cfg)
  let src = renderFuzzProgram seed targetTy expr
  let path = "/tmp/hakan_diff_fuzz_" ++ show seed ++ ".hk"
  writeFile path src
  parsed <- parseAndTycheck path src
  case parsed of
    Left err ->
      return $ Just $
        "fuzz seed " ++ show seed ++ ": generated program failed parse/typecheck:\n" ++
        err ++ "\nsource:\n" ++ src
    Right (prog, _) -> do
      interpOutcome <- runInterpExec prog
      jsOutcome <- toOutcome <$> runJSExec path
      cOutcome <- toOutcome <$> runCExec path
      mismatch <- compareOutcomes ("fuzz(seed=" ++ show seed ++ ")") interpOutcome jsOutcome cOutcome
      case mismatch of
        Nothing -> return Nothing
        Just msg ->
          return $ Just $ msg ++ "\nsource:\n" ++ src

genFuzzCase :: Int -> Int -> (FuzzTy, FuzzExpr)
genFuzzCase seed maxDepth =
  let depthLimit = max 1 maxDepth
      (s1, tyChoice) = chooseFrom 2 seed
      targetTy =
        if tyChoice == 0 then FuzzInt else FuzzBool
      (s2, depthOffset) = chooseFrom depthLimit s1
      depth = 1 + depthOffset
      (_, expr) = genFuzzExpr depth targetTy [] s2
  in (targetTy, expr)

genFuzzExpr :: Int -> FuzzTy -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genFuzzExpr depth ty env seed
  | depth <= 0 =
      case ty of
        FuzzInt -> genIntLeaf env seed
        FuzzBool -> genBoolLeaf env seed
        FuzzOptInt -> genOptLeaf env seed
        FuzzRec -> genRecLeaf env seed
        FuzzList -> genListLeaf env seed
        FuzzTree -> genTreeLeaf env seed
        FuzzFun fromTy toTy -> genFunLeaf fromTy toTy env seed
  | otherwise =
      case ty of
        FuzzInt ->
          let (s1, choice) = chooseFrom 15 seed
          in case choice of
            0 -> genIntLeaf env s1
            1 -> genIntBinary FAdd depth env s1
            2 -> genIntBinary FSub depth env s1
            3 -> genIfExpr depth FuzzInt env s1
            4 -> genLetExpr depth FuzzInt env s1
            5 -> genAppExpr depth FuzzInt env s1
            6 -> genMatchOptExpr depth FuzzInt env s1
            7 -> genProjCountExpr depth env s1
            8 -> genMatchRecExpr depth FuzzInt env s1
            9 -> genClassScoreIntExpr depth env s1
            10 -> genClassScoreViaApplyExpr depth env s1
            11 -> genClassScoreViaPartialExpr depth env s1
            12 -> genClassScoreViaWrapExpr depth env s1
            13 -> genMatchListExpr depth FuzzInt env s1
            _ -> genMatchTreeExpr depth FuzzInt env s1
        FuzzBool ->
          let (s1, choice) = chooseFrom 10 seed
          in case choice of
            0 -> genBoolLeaf env s1
            1 -> genEqExpr depth env s1
            2 -> genIfExpr depth FuzzBool env s1
            3 -> genLetExpr depth FuzzBool env s1
            4 -> genAppExpr depth FuzzBool env s1
            5 -> genMatchOptExpr depth FuzzBool env s1
            6 -> genProjOkExpr depth env s1
            7 -> genMatchRecExpr depth FuzzBool env s1
            8 -> genMatchListExpr depth FuzzBool env s1
            _ -> genMatchTreeExpr depth FuzzBool env s1
        FuzzOptInt ->
          let (s1, choice) = chooseFrom 5 seed
          in case choice of
            0 -> genOptLeaf env s1
            1 -> genOptSome depth env s1
            2 -> genIfExpr depth FuzzOptInt env s1
            3 -> genLetExpr depth FuzzOptInt env s1
            _ -> genAppExpr depth FuzzOptInt env s1
        FuzzRec ->
          let (s1, choice) = chooseFrom 5 seed
          in case choice of
            0 -> genRecLeaf env s1
            1 -> genRecLit depth env s1
            2 -> genIfExpr depth FuzzRec env s1
            3 -> genLetExpr depth FuzzRec env s1
            _ -> genAppExpr depth FuzzRec env s1
        FuzzList ->
          let (s1, choice) = chooseFrom 5 seed
          in case choice of
            0 -> genListLeaf env s1
            1 -> genListCons depth env s1
            2 -> genIfExpr depth FuzzList env s1
            3 -> genLetExpr depth FuzzList env s1
            _ -> genAppExpr depth FuzzList env s1
        FuzzTree ->
          let (s1, choice) = chooseFrom 5 seed
          in case choice of
            0 -> genTreeLeaf env s1
            1 -> genTreeNode depth env s1
            2 -> genIfExpr depth FuzzTree env s1
            3 -> genLetExpr depth FuzzTree env s1
            _ -> genAppExpr depth FuzzTree env s1
        FuzzFun fromTy toTy ->
          let (s1, choice) = chooseFrom 4 seed
          in case choice of
            0 -> genFunLeaf fromTy toTy env s1
            1 -> genLamExpr depth fromTy toTy env s1
            2 -> genIfExpr depth (FuzzFun fromTy toTy) env s1
            _ -> genLetExpr depth (FuzzFun fromTy toTy) env s1

genIntLeaf :: [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genIntLeaf env seed =
  let vars = varsOfType FuzzInt env
      literalCount = 21
      (s1, pick) = chooseFrom (length vars + literalCount) seed
  in if pick < length vars then
       (s1, FVar (vars !! pick))
     else
       (s1, FIntLit (pick - length vars))

genBoolLeaf :: [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genBoolLeaf env seed =
  let vars = varsOfType FuzzBool env
      (s1, pick) = chooseFrom (length vars + 2) seed
  in if pick < length vars then
       (s1, FVar (vars !! pick))
     else if pick - length vars == 0 then
       (s1, FBoolLit True)
     else
       (s1, FBoolLit False)

genOptLeaf :: [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genOptLeaf env seed =
  let vars = varsOfType FuzzOptInt env
      (s1, pick) = chooseFrom (length vars + 2) seed
  in if pick < length vars then
       (s1, FVar (vars !! pick))
     else if pick - length vars == 0 then
       (s1, FOptNone)
     else
       let (s2, intExpr) = genIntLeaf env s1
       in (s2, FOptSome intExpr)

genRecLeaf :: [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genRecLeaf env seed =
  let vars = varsOfType FuzzRec env
      (s1, pick) = chooseFrom (length vars + 1) seed
  in if pick < length vars then
       (s1, FVar (vars !! pick))
     else
       genRecLit 0 env s1

genListLeaf :: [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genListLeaf env seed =
  let vars = varsOfType FuzzList env
      (s1, pick) = chooseFrom (length vars + 2) seed
  in if pick < length vars then
       (s1, FVar (vars !! pick))
     else if pick - length vars == 0 then
       (s1, FListNil)
     else
       let (s2, intExpr) = genIntLeaf env s1
       in (s2, FListCons intExpr FListNil)

genTreeLeaf :: [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genTreeLeaf env seed =
  let vars = varsOfType FuzzTree env
      (s1, pick) = chooseFrom (length vars + 1) seed
  in if pick < length vars then
       (s1, FVar (vars !! pick))
     else
       let (s2, intExpr) = genIntLeaf env s1
       in (s2, FTreeLeaf intExpr)

genFunLeaf :: FuzzTy -> FuzzTy -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genFunLeaf fromTy toTy env seed =
  let funTy = FuzzFun fromTy toTy
      vars = varsOfType funTy env
      (s1, pick) = chooseFrom (length vars + 1) seed
  in if pick < length vars then
       (s1, FVar (vars !! pick))
     else
       genLamExpr 0 fromTy toTy env s1

varsOfType :: FuzzTy -> [(String, FuzzTy)] -> [String]
varsOfType ty env =
  [name | (name, varTy) <- env, varTy == ty]

genIntBinary
  :: (FuzzExpr -> FuzzExpr -> FuzzExpr)
  -> Int
  -> [(String, FuzzTy)]
  -> Int
  -> (Int, FuzzExpr)
genIntBinary ctor depth env seed =
  let nextDepth = depth - 1
      (s1, leftExpr) = genFuzzExpr nextDepth FuzzInt env seed
      (s2, rightExpr) = genFuzzExpr nextDepth FuzzInt env s1
  in (s2, ctor leftExpr rightExpr)

genEqExpr :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genEqExpr depth env seed =
  let nextDepth = depth - 1
      (s1, leftExpr) = genFuzzExpr nextDepth FuzzInt env seed
      (s2, rightExpr) = genFuzzExpr nextDepth FuzzInt env s1
  in (s2, FEq leftExpr rightExpr)

genOptSome :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genOptSome depth env seed =
  let nextDepth = depth - 1
      (s1, intExpr) = genFuzzExpr nextDepth FuzzInt env seed
  in (s1, FOptSome intExpr)

genRecLit :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genRecLit depth env seed =
  let nextDepth = depth - 1
      (s1, countExpr) = genFuzzExpr nextDepth FuzzInt env seed
      (s2, okExpr) = genFuzzExpr nextDepth FuzzBool env s1
  in (s2, FRecLit countExpr okExpr)

genListCons :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genListCons depth env seed =
  let nextDepth = depth - 1
      (s1, headExpr) = genFuzzExpr nextDepth FuzzInt env seed
      (s2, tailExpr) = genFuzzExpr nextDepth FuzzList env s1
  in (s2, FListCons headExpr tailExpr)

genTreeNode :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genTreeNode depth env seed =
  let nextDepth = depth - 1
      (s1, leftExpr) = genFuzzExpr nextDepth FuzzTree env seed
      (s2, rightExpr) = genFuzzExpr nextDepth FuzzTree env s1
  in (s2, FTreeNode leftExpr rightExpr)

genLamExpr
  :: Int
  -> FuzzTy
  -> FuzzTy
  -> [(String, FuzzTy)]
  -> Int
  -> (Int, FuzzExpr)
genLamExpr depth fromTy toTy env seed =
  let nextDepth = depth - 1
      param = freshVarName seed
      (s1, bodyExpr) = genFuzzExpr nextDepth toTy ((param, fromTy) : env) (nextSeed seed)
  in (s1, FLam param bodyExpr)

genAppExpr :: Int -> FuzzTy -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genAppExpr depth targetTy env seed =
  let nextDepth = depth - 1
      (s1, fromTyChoice) = chooseFrom 6 seed
      fromTy =
        case fromTyChoice of
          0 -> FuzzInt
          1 -> FuzzBool
          2 -> FuzzOptInt
          3 -> FuzzRec
          4 -> FuzzList
          _ -> FuzzTree
      (s2, funExpr) = genFuzzExpr nextDepth (FuzzFun fromTy targetTy) env s1
      (s3, argExpr) = genFuzzExpr nextDepth fromTy env s2
  in (s3, FApp funExpr argExpr)

genProjCountExpr :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genProjCountExpr depth env seed =
  let nextDepth = depth - 1
      (s1, recExpr) = genFuzzExpr nextDepth FuzzRec env seed
  in (s1, FProjCount recExpr)

genProjOkExpr :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genProjOkExpr depth env seed =
  let nextDepth = depth - 1
      (s1, recExpr) = genFuzzExpr nextDepth FuzzRec env seed
  in (s1, FProjOk recExpr)

genMatchOptExpr :: Int -> FuzzTy -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genMatchOptExpr depth targetTy env seed =
  let nextDepth = depth - 1
      (s1, discrimExpr) = genFuzzExpr nextDepth FuzzOptInt env seed
      (s2, noneExpr) = genFuzzExpr nextDepth targetTy env s1
      someName = freshVarName s2
      (s3, someExpr) = genFuzzExpr nextDepth targetTy ((someName, FuzzInt) : env) s2
  in (s3, FMatchOpt discrimExpr noneExpr someName someExpr)

genMatchRecExpr :: Int -> FuzzTy -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genMatchRecExpr depth targetTy env seed =
  let nextDepth = depth - 1
      (s1, recExpr) = genFuzzExpr nextDepth FuzzRec env seed
      countName = freshVarName s1
      okName = freshVarName (nextSeed s1)
      env' = (okName, FuzzBool) : (countName, FuzzInt) : env
      (s2, bodyExpr) = genFuzzExpr nextDepth targetTy env' (nextSeed s1)
  in (s2, FMatchRec recExpr countName okName bodyExpr)

genMatchListExpr :: Int -> FuzzTy -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genMatchListExpr depth targetTy env seed =
  let nextDepth = depth - 1
      (s1, listExpr) = genFuzzExpr nextDepth FuzzList env seed
      (s2, nilExpr) = genFuzzExpr nextDepth targetTy env s1
      headName = freshVarName s2
      tailName = freshVarName (nextSeed s2)
      env' = (tailName, FuzzList) : (headName, FuzzInt) : env
      (s3, consExpr) = genFuzzExpr nextDepth targetTy env' (nextSeed s2)
  in (s3, FMatchList listExpr nilExpr headName tailName consExpr)

genMatchTreeExpr :: Int -> FuzzTy -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genMatchTreeExpr depth targetTy env seed =
  let nextDepth = depth - 1
      (s1, treeExpr) = genFuzzExpr nextDepth FuzzTree env seed
      leafName = freshVarName s1
      (s2, leafExpr) = genFuzzExpr nextDepth targetTy ((leafName, FuzzInt) : env) (nextSeed s1)
      leftName = freshVarName s2
      rightName = freshVarName (nextSeed s2)
      env' = (rightName, FuzzTree) : (leftName, FuzzTree) : env
      (s3, nodeExpr) = genFuzzExpr nextDepth targetTy env' (nextSeed s2)
  in (s3, FMatchTree treeExpr leafName leafExpr leftName rightName nodeExpr)

genClassScoreIntExpr :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genClassScoreIntExpr depth env seed =
  let nextDepth = depth - 1
      (s1, xExpr) = genFuzzExpr nextDepth FuzzInt env seed
      (s2, yExpr) = genFuzzExpr nextDepth FuzzInt env s1
  in (s2, FClassScoreInt xExpr yExpr)

genClassScoreViaApplyExpr :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genClassScoreViaApplyExpr depth env seed =
  let nextDepth = depth - 1
      (s1, xExpr) = genFuzzExpr nextDepth FuzzInt env seed
      (s2, yExpr) = genFuzzExpr nextDepth FuzzInt env s1
  in (s2, FClassScoreViaApply seed xExpr yExpr)

genClassScoreViaPartialExpr :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genClassScoreViaPartialExpr depth env seed =
  let nextDepth = depth - 1
      (s1, xExpr) = genFuzzExpr nextDepth FuzzInt env seed
      (s2, yExpr) = genFuzzExpr nextDepth FuzzInt env s1
  in (s2, FClassScoreViaPartial seed xExpr yExpr)

genClassScoreViaWrapExpr :: Int -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genClassScoreViaWrapExpr depth env seed =
  let nextDepth = depth - 1
      (s1, xExpr) = genFuzzExpr nextDepth FuzzInt env seed
      (s2, yExpr) = genFuzzExpr nextDepth FuzzInt env s1
  in (s2, FClassScoreViaWrap seed xExpr yExpr)

genIfExpr :: Int -> FuzzTy -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genIfExpr depth targetTy env seed =
  let nextDepth = depth - 1
      (s1, condExpr) = genFuzzExpr nextDepth FuzzBool env seed
      (s2, trueExpr) = genFuzzExpr nextDepth targetTy env s1
      (s3, falseExpr) = genFuzzExpr nextDepth targetTy env s2
  in (s3, FIf condExpr trueExpr falseExpr)

genLetExpr :: Int -> FuzzTy -> [(String, FuzzTy)] -> Int -> (Int, FuzzExpr)
genLetExpr depth targetTy env seed =
  let nextDepth = depth - 1
      (s1, bindTyChoice) = chooseFrom 14 seed
      bindTy =
        case bindTyChoice of
          0 -> FuzzInt
          1 -> FuzzBool
          2 -> FuzzOptInt
          3 -> FuzzRec
          4 -> FuzzList
          5 -> FuzzTree
          _ -> simpleFunType bindTyChoice
      bindName = freshVarName s1
      (s2, boundExpr) = genFuzzExpr nextDepth bindTy env s1
      (s3, bodyExpr) = genFuzzExpr nextDepth targetTy ((bindName, bindTy) : env) s2
  in (s3, FLet bindName boundExpr bodyExpr)

simpleFunType :: Int -> FuzzTy
simpleFunType choice =
  let tys = [FuzzInt, FuzzBool, FuzzOptInt, FuzzRec, FuzzList, FuzzTree]
      pairs = [(fromTy, toTy) | fromTy <- tys, toTy <- tys]
      (fromTy, toTy) = pairs !! (choice `mod` length pairs)
  in FuzzFun fromTy toTy

freshVarName :: Int -> String
freshVarName seed = "v" ++ show (seed `mod` 1000000)

chooseFrom :: Int -> Int -> (Int, Int)
chooseFrom rawBound seed =
  let bound = max 1 rawBound
      next = nextSeed seed
  in (next, next `mod` bound)

nextSeed :: Int -> Int
nextSeed seed =
  (seed * 1103515245 + 12345) .&. 2147483647

renderFuzzProgram :: Int -> FuzzTy -> FuzzExpr -> String
renderFuzzProgram seed targetTy expr =
  unlines
    [ "# AUTO-GENERATED differential fuzz case"
    , "# seed: " ++ show seed ++ ", type: " ++ renderFuzzTy targetTy
    , "data FuzzOption ="
    , "  | FuzzNone"
    , "  | FuzzSome Int"
    , ""
    , "data FuzzList ="
    , "  | FuzzListNil"
    , "  | FuzzListCons Int FuzzList"
    , ""
    , "data FuzzTree ="
    , "  | FuzzTreeLeaf Int"
    , "  | FuzzTreeNode FuzzTree FuzzTree"
    , ""
    , "record FuzzRec ="
    , "  { count : Int"
    , "  , ok : Bool }"
    , ""
    , "class a is FuzzEq"
    , "  | fuzzEq : a -> a -> Bool"
    , ""
    , "instance Int is FuzzEq"
    , "  | fuzzEq = λx. λy. x = y"
    , ""
    , "pure fuzzScore : a is FuzzEq => a -> a -> Int"
    , "def fuzzScore = λx. λy. if fuzzEq x y then 1 else 0"
    , ""
    , "pure fuzzScoreInt : Int -> Int -> Int"
    , "def fuzzScoreInt = fuzzScore"
    , ""
    , "run " ++ renderFuzzExpr expr
    ]

renderFuzzTy :: FuzzTy -> String
renderFuzzTy ty =
  case ty of
    FuzzInt -> "Int"
    FuzzBool -> "Bool"
    FuzzOptInt -> "FuzzOption"
    FuzzRec -> "FuzzRec"
    FuzzList -> "FuzzList"
    FuzzTree -> "FuzzTree"
    FuzzFun fromTy toTy ->
      "(" ++ renderFuzzTy fromTy ++ " -> " ++ renderFuzzTy toTy ++ ")"

renderFuzzExpr :: FuzzExpr -> String
renderFuzzExpr expr =
  case expr of
    FVar name -> name
    FIntLit n -> show n
    FBoolLit True -> "true"
    FBoolLit False -> "false"
    FOptNone -> "FuzzNone"
    FOptSome intExpr -> "(FuzzSome " ++ renderFuzzExpr intExpr ++ ")"
    FMatchOpt discrim noneExpr someName someExpr ->
      "(destruct " ++ renderFuzzExpr discrim ++ " as\n" ++
      "  | FuzzNone -> " ++ renderFuzzExpr noneExpr ++ "\n" ++
      "  | FuzzSome " ++ someName ++ " -> " ++ renderFuzzExpr someExpr ++ ")"
    FRecLit countExpr okExpr ->
      "{ count = " ++ renderFuzzExpr countExpr ++
      ", ok = " ++ renderFuzzExpr okExpr ++ " }"
    FProjCount recExpr -> "(count " ++ renderFuzzExpr recExpr ++ ")"
    FProjOk recExpr -> "(ok " ++ renderFuzzExpr recExpr ++ ")"
    FMatchRec recExpr countName okName bodyExpr ->
      "(destruct " ++ renderFuzzExpr recExpr ++ " as\n" ++
      "  | { count = " ++ countName ++ ", ok = " ++ okName ++
      " } -> " ++ renderFuzzExpr bodyExpr ++ ")"
    FListNil -> "FuzzListNil"
    FListCons headExpr tailExpr ->
      "(FuzzListCons " ++ renderFuzzExpr headExpr ++ " " ++ renderFuzzExpr tailExpr ++ ")"
    FMatchList listExpr nilExpr headName tailName consExpr ->
      "(destruct " ++ renderFuzzExpr listExpr ++ " as\n" ++
      "  | FuzzListNil -> " ++ renderFuzzExpr nilExpr ++ "\n" ++
      "  | FuzzListCons " ++ headName ++ " " ++ tailName ++
      " -> " ++ renderFuzzExpr consExpr ++ ")"
    FTreeLeaf intExpr ->
      "(FuzzTreeLeaf " ++ renderFuzzExpr intExpr ++ ")"
    FTreeNode leftExpr rightExpr ->
      "(FuzzTreeNode " ++ renderFuzzExpr leftExpr ++ " " ++ renderFuzzExpr rightExpr ++ ")"
    FMatchTree treeExpr leafName leafExpr leftName rightName nodeExpr ->
      "(destruct " ++ renderFuzzExpr treeExpr ++ " as\n" ++
      "  | FuzzTreeLeaf " ++ leafName ++ " -> " ++ renderFuzzExpr leafExpr ++ "\n" ++
      "  | FuzzTreeNode " ++ leftName ++ " " ++ rightName ++
      " -> " ++ renderFuzzExpr nodeExpr ++ ")"
    FClassScoreInt x y ->
      "(fuzzScoreInt " ++ renderFuzzExpr x ++ " " ++ renderFuzzExpr y ++ ")"
    FClassScoreViaApply nameSeed x y ->
      let applyName = freshGeneratedName "fuzzApply" nameSeed
          fnName = freshGeneratedName "fuzzFn" (nextSeed nameSeed)
      in
        "(let " ++ applyName ++ " = (λ" ++ fnName ++ ". ((" ++ fnName ++
        " " ++ renderFuzzExpr x ++ ") " ++ renderFuzzExpr y ++ ")) in (" ++
        applyName ++ " fuzzScoreInt))"
    FClassScoreViaPartial nameSeed x y ->
      let leftName = freshGeneratedName "fuzzLeft" nameSeed
          stepName = freshGeneratedName "fuzzStep" (nextSeed nameSeed)
      in
        "(let " ++ leftName ++ " = " ++ renderFuzzExpr x ++
        " in (let " ++ stepName ++ " = (fuzzScoreInt " ++ leftName ++
        ") in (" ++ stepName ++ " " ++ renderFuzzExpr y ++ ")))"
    FClassScoreViaWrap nameSeed x y ->
      let wrapName = freshGeneratedName "fuzzWrap" nameSeed
          fnName = freshGeneratedName "fuzzFn" (nextSeed nameSeed)
      in
        "(let " ++ wrapName ++ " = (λ" ++ fnName ++ ". " ++ fnName ++
        ") in (((" ++ wrapName ++ " fuzzScoreInt) " ++ renderFuzzExpr x ++
        ") " ++ renderFuzzExpr y ++ "))"
    FLam name body -> "(λ" ++ name ++ ". " ++ renderFuzzExpr body ++ ")"
    FApp f x -> "(" ++ renderFuzzExpr f ++ " " ++ renderFuzzExpr x ++ ")"
    FAdd a b -> "(" ++ renderFuzzExpr a ++ " + " ++ renderFuzzExpr b ++ ")"
    FSub a b -> "(" ++ renderFuzzExpr a ++ " - " ++ renderFuzzExpr b ++ ")"
    FEq a b -> "(" ++ renderFuzzExpr a ++ " = " ++ renderFuzzExpr b ++ ")"
    FIf cond t f ->
      "(if " ++ renderFuzzExpr cond ++
      " then " ++ renderFuzzExpr t ++
      " else " ++ renderFuzzExpr f ++ ")"
    FLet name rhs body ->
      "(let " ++ name ++
      " = " ++ renderFuzzExpr rhs ++
      " in " ++ renderFuzzExpr body ++ ")"

freshGeneratedName :: String -> Int -> String
freshGeneratedName prefix seed =
  prefix ++ show (seed `mod` 1000000)

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

runDifferentialCase :: [FilePath] -> IO [Maybe String]
runDifferentialCase = mapM runOne
  where
    runOne path = do
      src <- readFile path
      parsed <- parseAndTycheck path src
      case parsed of
        Left err ->
          return $ Just $ path ++ ": differential parse/typecheck failed:\n" ++ err
        Right (prog, _) -> do
          interpOutcome <- runInterpExec prog
          jsOutcome <- toOutcome <$> runJSExec path
          cOutcome <- toOutcome <$> runCExec path
          compareOutcomes path interpOutcome jsOutcome cOutcome

runKnownFailDifferentialCase :: [FilePath] -> IO [Maybe String]
runKnownFailDifferentialCase = mapM runOne
  where
    runOne path = do
      src <- readFile path
      let ex = parseExpectations src
      jsResult <- runJSExec path
      jsFailure <- expectFromDirectives "JS" path (expectedJSStatus ex) (expectedJSOut ex) jsResult
      case jsFailure of
        Just msg ->
          return $ Just $
            "known-fail differential case has broken JS baseline (" ++ path ++ "):\n" ++ msg
        Nothing -> do
          cResult <- runCExec path
          cFailure <- expectFromDirectives "C" path (expectedCStatus ex) (expectedCOut ex) cResult
          case cFailure of
            Just msg ->
              return $ Just $
                "known-fail differential case has broken C baseline (" ++ path ++ "):\n" ++ msg
            Nothing -> do
              parsed <- parseAndTycheck path src
              case parsed of
                Left err ->
                  return $ Just $
                    path ++ ": known-fail differential parse/typecheck failed:\n" ++ err
                Right (prog, _) -> do
                  interpOutcome <- runInterpExec prog
                  let jsOutcome = toOutcome jsResult
                  let cOutcome = toOutcome cResult
                  mismatch <- compareOutcomes path interpOutcome jsOutcome cOutcome
                  case mismatch of
                    Nothing ->
                      return $ Just $
                        path ++ ": known differential gap resolved; move it to " ++
                        differentialCasesFile
                    Just _ -> return Nothing

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

expectFromDirectives
  :: String
  -> FilePath
  -> RunStatus
  -> Maybe String
  -> Either String ExecResult
  -> IO (Maybe String)
expectFromDirectives backend path status expectedOut result =
  case status of
    RunOk ->
      case expectedOut of
        Nothing ->
          return $ Just $
            path ++ ": missing EXPECT-" ++ backend ++ "-OUT directive."
        Just wanted ->
          expectBackendRun backend path RunOk (Just wanted) result
    RunError ->
      expectBackendRun backend path RunError expectedOut result

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
      case expectedStatus of
        RunError -> return Nothing
        RunOk ->
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

data Outcome = Outcome
  { outcomeStatus :: RunStatus
  , outcomeOutput :: Maybe String
  , outcomeDetail :: Maybe String
  } deriving Show

runInterpExec :: Prog TyData -> IO Outcome
runInterpExec prog = do
  result <- try (evaluate (showInterpResult prog)) :: IO (Either SomeException String)
  case result of
    Right out ->
      return Outcome
        { outcomeStatus = RunOk
        , outcomeOutput = Just out
        , outcomeDetail = Nothing
        }
    Left e ->
      return Outcome
        { outcomeStatus = RunError
        , outcomeOutput = Nothing
        , outcomeDetail = Just (show e)
        }
  where
    showInterpResult p =
      let (val, _) = interpProg p
      in trim (renderInterpValue val)

renderInterpValue :: Value -> String
renderInterpValue (VInt i) = show i
renderInterpValue (VBool True) = "1"
renderInterpValue (VBool False) = "0"
renderInterpValue (VChar c) = [c]
renderInterpValue VUnit = "0"
renderInterpValue v = show v

toOutcome :: Either String ExecResult -> Outcome
toOutcome result =
  case result of
    Left e ->
      Outcome
        { outcomeStatus = RunError
        , outcomeOutput = Nothing
        , outcomeDetail = Just e
        }
    Right exec ->
      case execCode exec of
        ExitSuccess ->
          Outcome
            { outcomeStatus = RunOk
            , outcomeOutput = Just (normalizeOutcomeOutput $ trim $ execStdout exec)
            , outcomeDetail = Nothing
            }
        ExitFailure _ ->
          Outcome
            { outcomeStatus = RunError
            , outcomeOutput = Nothing
            , outcomeDetail = Just (renderExecResult exec)
            }

compareOutcomes
  :: FilePath
  -> Outcome
  -> Outcome
  -> Outcome
  -> IO (Maybe String)
compareOutcomes path interp js c
  | outcomeStatus interp /= outcomeStatus js ||
    outcomeStatus interp /= outcomeStatus c =
      return $ Just $
        path ++ ": differential status mismatch. " ++
        "interp=" ++ show (outcomeStatus interp) ++
        ", js=" ++ show (outcomeStatus js) ++
        ", c=" ++ show (outcomeStatus c) ++
        "\ninterp detail:\n" ++ detail interp ++
        "\njs detail:\n" ++ detail js ++
        "\nc detail:\n" ++ detail c
  | outcomeStatus interp == RunOk =
      case (outcomeOutput interp, outcomeOutput js, outcomeOutput c) of
        (Just i, Just j, Just k)
          | i == j && i == k -> return Nothing
          | otherwise ->
              return $ Just $
                path ++ ": differential output mismatch. " ++
                "interp=" ++ show i ++
                ", js=" ++ show j ++
                ", c=" ++ show k
        _ ->
          return $ Just $
            path ++ ": differential output missing despite success status."
  | otherwise = return Nothing
  where
    detail o =
      case outcomeDetail o of
        Nothing ->
          case outcomeOutput o of
            Nothing -> "<none>"
            Just out -> out
        Just d -> d

normalizeOutcomeOutput :: String -> String
normalizeOutcomeOutput raw =
  case map toUpper (trim raw) of
    "TRUE" -> "1"
    "FALSE" -> "0"
    _ -> trim raw

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
