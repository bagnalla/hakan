{-# LANGUAGE LambdaCase #-}

module LambdaLift (lambdaLiftProg) where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Bifunctor (second)
import Data.List (intercalate, nub)
import Data.Maybe (catMaybes, fromJust)
import Data.Sort (sortOn)

import Ast
import Symtab (Id(..))
import Tycheck (TyData(..))
import Util (andf, debugPrint, elemIndex, mapSndM)
  
type LLState = Int
type LLM a = WriterT [Command TyData] (ReaderT [(Id, Type)] (StateT LLState Identity)) a
runLLM :: LLM a -> Int -> (a, [Command TyData])
runLLM f n = runIdentity $ evalStateT (runReaderT (runWriterT f) []) n

nextSym :: String -> LLM String
nextSym prefix = do
  i <- get
  put $ i + 1
  return $ prefix ++ show i

freshName :: LLM String
freshName = nextSym "_S"

-- | Algorithm from slpj page 227. We specialize to terms with type
-- data because we may need to abstract over variables that are bound
-- by patterns in match expressions which don't contain type
-- information syntactically, so we make use of type information
-- computed by the typechecker to determine their types.
lambdaLift :: Term TyData -> LLM (Term TyData)
lambdaLift = \case
  TmAbs fi x ty t1 ->
    local ((x, ty):) $ do
      t1' <- lambdaLift t1
      bvs <- ask
      debugPrint ("lambdaLift abs: " ++ show (x, ty, t1)) $
        debugPrint ("bvs: " ++ show bvs) $
        debugPrint ("freevars: " ++ show (freevars t1')) $ do
        
        -- TODO: negate here or not? see empirically which leads to fewer
        -- supercombinators when we do eta reduction to optimize them away.
        -- let fvs = sortOn (negate . elemIndex bvs) $
        --       map (\fv -> (fv, fromJust $ lookup fv bvs))
        --       (filter (not . (== x)) $ freevars t1')
        -- nm <- freshName
        -- tell $ [CSuperCombinator fi (Id nm) ((x, ty) : fvs) t1']

        let fvs = map (\fv -> (fv, fromJust $ lookup fv bvs)) $
                  filter (andf (`elem` (fst <$> bvs)) $ not . (== x)) $ freevars t1'
        nm <- freshName
        debugPrint ("fvs: " ++ show fvs) $
          -- tell $ [CSuperCombinator fi (Id nm) fvs t1']
          tell $ [CSuperCombinator fi (Id nm) ((x, ty) : fvs) t1']
        
        -- TODO: LHS of this application should be a closure/thunk that
        -- we allocate.. May need a new term constructor :/.. Also when
        -- we perform partial applications we should always perform a
        -- copy of the thunk and work with the copy.
        -- return $ mkApp (TmVar fi $ Id nm) $ TmVar fi . fst <$> fvs
        
      -- TODO: perhaps use a "multi-application" term here so it can
      -- be compiled more efficiently. We may not even need to do any
      -- runtime checking in the compiled code -- just load the
      -- arguments into the thunk object. I think this is the only
      -- place where we can safely do such a multi-application since
      -- we know that we're referring to an unapplied supercombinator
      -- (which we don't know in the general case given an arbitrary
      -- element of function type).
      -- return $ mkApp (TmThunk fi (Id nm) $ toInteger $ length fvs + 1) $ TmVar fi . fst <$> fvs
        return $ TmThunk fi (Id nm) fvs
  TmApp fi t1 t2 -> liftM2 (TmApp fi) (lambdaLift t1) (lambdaLift t2)
  TmIf fi t1 t2 t3 ->
    liftM3 (TmIf fi) (lambdaLift t1) (lambdaLift t2) (lambdaLift t3)
  TmUnop fi u t1 -> pure (TmUnop fi u) <*> lambdaLift t1
  TmBinop fi b t1 t2 -> liftM2 (TmBinop fi b) (lambdaLift t1) (lambdaLift t2)
  TmLet fi x t1 t2 -> local ((x, unTyData $ data_of_term t1):) $
    liftM2 (TmLet fi x) (lambdaLift t1) (lambdaLift t2)
  TmVariant fi x ts -> pure (TmVariant fi x) <*> mapM lambdaLift ts
  TmMatch fi t1 cases -> do
    t1' <- lambdaLift t1
    cases' <- forM cases $ \(p, t) ->
      local (patternVarTypes p (unTyData $ data_of_term t1) ++) $ do
      t' <- lambdaLift t
      return (p, t')
    return $ TmMatch fi t1' cases'
  TmRecord fi fields ->
    pure (TmRecord fi) <*> mapM (mapSndM lambdaLift) fields
  tm -> return tm

-- | Convert any let commands to a list of supercombinator
-- commands. Leave other commands unchanged.
lambdaLiftCommand :: Command TyData -> LLM (Maybe (Command TyData))
lambdaLiftCommand c@(CLet (TyData ty) nm tm) =
  -- debugPrint ("lambdaLiftCommand a: " ++ show c) $ do Consider the
  -- name of the top-level definition as being free within the body,
  -- so that it is abstracted out as a parameter for recursive
  -- occurrences. Then, each supercombinator is partially applied to it.
  local ((nm, ty):) $ do
  tm' <- lambdaLift tm
  -- debugPrint "lambdaLiftCommand b" $ do
  -- tell $ [CSuperCombinator fi nm [] tm']
  -- return Nothing
  return $ Just $ CSuperCombinator (TyData ty) nm [] tm'
lambdaLiftCommand c =
  -- debugPrint ("lambda lifting command: " ++ show c) $
  return $ Just c

lambdaLiftProg' :: Prog TyData -> LLM (Prog TyData)
lambdaLiftProg' p = do
  -- debugPrint "lambdaLiftProg'" $ do
  cs <- mapM lambdaLiftCommand $ prog_of p
  -- debugPrint "lambdaLiftProg' 2" $
  return $ p { prog_of = catMaybes cs }

-- | Lambda lift an entire program, removing all let commands and
-- replacing them with supercombinators appended to the end of the program.
lambdaLiftProg :: Prog TyData -> Prog TyData
lambdaLiftProg p =
  -- debugPrint ("lambdaLiftProg: " ++ (intercalate "\n" $ showCommand <$> prog_of p)) $
  debugPrint ("lambdaLiftProg p: " ++ show p) $
  let (p', supercombinators) = runLLM (lambdaLiftProg' p) 0 in
    -- debugPrint ("lambdaLiftProg 2: " ++ show (p, supercombinators)) $
    debugPrint ("lambdaLiftProg supercombinators: " ++ show supercombinators) $
    debugPrint ("lambdaLiftProg p': " ++ show p') $
    p' { prog_of = prog_of p' ++ supercombinators }
