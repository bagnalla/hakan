{-# LANGUAGE LambdaCase #-}

module Renamer (rename) where

import Control.Monad.Identity
import Control.Monad.State

import qualified Data.Map as Map

import Ast
import Symtab (Id(..))
import Tycheck (TyData(..))
import Util (bimapM, debugPrint, mapSndM)

data RenamerState =
  RenamerState { gensym :: Int
               , names :: Map.Map String String
               , type_names :: Map.Map String String
               , reserved_names :: [String] }

initRenamerState :: RenamerState
initRenamerState = RenamerState { gensym = 0
                                , names = Map.empty
                                , type_names = Map.empty
                                , reserved_names = [] }

type RenamerM a = StateT RenamerState Identity a

runRenamerM :: RenamerM a -> RenamerState -> a
runRenamerM f s = runIdentity $ evalStateT f s

nextSym :: String -> RenamerM String
nextSym prefix = do
  i <- gets gensym
  modify $ \s -> s { gensym = i + 1 }
  return $ prefix ++ show i

bad_ident :: String -> Bool
bad_ident = elem '\''

fix_ident :: String -> String
fix_ident = map (\c -> if c == '\'' then '_' else c)

freshen :: String -> [String] -> String
freshen s reserved =
  let s' = "_" ++ s in
    if s' `elem` reserved then
      freshen s' reserved
    else
      s'

process_ident :: String -> RenamerM String
process_ident ident = do
  m <- gets names
  reserved <- gets reserved_names
  case Map.lookup ident m of
    Just s -> return s
    Nothing -> do
      let s = if bad_ident ident then fix_ident ident else ident
      let s' = if s `elem` (Map.elems m ++ reserved) then
                 freshen s (Map.elems m ++ reserved) else s
      modify $ \st -> st { names = Map.insert ident s' m }
      return s'

process_type_ident :: String -> RenamerM String
process_type_ident ident = do
  m <- gets type_names
  reserved <- gets reserved_names
  case Map.lookup ident m of
    Just s -> return s
    Nothing -> do
      let s = "_t_" ++ ident
      let s' = if bad_ident s then fix_ident s else s
      let s'' = if s' `elem` (Map.elems m ++ reserved) then
                  freshen s' (Map.elems m ++ reserved) else s'
      modify $ \st -> st { type_names = Map.insert ident s'' m }
      return s''

renameId :: Id -> RenamerM Id
renameId (Id x) = Id <$> process_ident x

renameTypeId :: Id -> RenamerM Id
renameTypeId (Id x) = Id <$> process_type_ident x

renameClassNm :: ClassNm -> RenamerM ClassNm
renameClassNm (ClassNm x) = ClassNm <$> renameTypeId x

renameType :: Type -> RenamerM Type
renameType = \case
  TyVar b k nms x -> pure (TyVar b k) <*> mapM renameClassNm nms <*> renameTypeId x
  TyAbs x k ty -> pure (flip TyAbs k) <*> renameTypeId x <*> renameType ty
  TyApp s t -> pure TyApp <*> renameType s <*> renameType t
  TyArrow s t -> pure TyArrow <*> renameType s <*> renameType t
  TyRef ty -> TyRef <$> renameType ty
  TyName x -> TyName <$> renameTypeId x
  TyVariant nm tyvars ctors ->
    pure TyVariant <*> renameTypeId nm <*> mapM renameType tyvars <*>
    mapM (bimapM renameId (mapM renameType)) ctors
  TyRecord nm tyvars fields ->
    pure TyRecord <*> renameTypeId nm <*> mapM renameType tyvars <*>
    mapM (bimapM renameId renameType) fields
  TyConstructor (TypeConstructor { tycon_name = nm
                                 , tycon_tyvars = tyvars
                                 , tycon_kinds = kinds
                                 , tycon_tyargs = tyargs
                                 , tycon_ty = ty
                                 , tycon_instantiated = instantiated }) ->
    TyConstructor <$>
    (pure TypeConstructor <*> renameTypeId nm <*> mapM renameTypeId tyvars <*> pure kinds <*>
     mapM renameType tyargs <*> renameType ty <*> renameType instantiated)
  ty -> return ty

renameTyData :: TyData -> RenamerM TyData
renameTyData = (TyData <$>) . renameType . unTyData

renamePattern :: Pattern -> RenamerM Pattern
renamePattern = \case
  PVar x -> PVar <$> renameId x
  PPair p1 p2 -> pure PPair <*> renamePattern p1 <*> renamePattern p2
  PConstructor nm ps ->
    pure PConstructor <*> renameId nm <*> mapM renamePattern ps
  PRecord fields -> PRecord <$> mapM (bimapM renameId renamePattern) fields
  p -> return p

renameTerm :: Term TyData -> RenamerM (Term TyData)
renameTerm = \case
  TmVar d x -> pure TmVar <*> renameTyData d <*> renameId x
  TmAbs d x ty tm ->
    pure TmAbs <*> renameTyData d <*> renameId x <*> renameType ty <*> renameTerm tm
  TmApp d t1 t2 ->
    debugPrint "\nrenaming TmApp" $
    debugPrint ("t1: " ++ show t1) $
    debugPrint ("t2: " ++ show t2) $ do
    d' <- renameTyData d
    t1' <- renameTerm t1
    t2' <- renameTerm t2
    debugPrint ("d': " ++ show d') $
      debugPrint ("t1': " ++ show t1') $
      debugPrint ("t2': " ++ show t2') $
      return $ TmApp d' t1' t2'
    -- pure TmApp <*> renameTyData d <*> renameTerm t1 <*> renameTerm t2
  TmUnit d -> TmUnit <$> renameTyData d
  TmBool d b -> flip TmBool b <$> renameTyData d
  TmInt d i -> flip TmInt i <$> renameTyData d
  TmChar d c -> flip TmChar c <$> renameTyData d
  TmIf d t1 t2 t3 ->
    pure TmIf <*> renameTyData d <*> renameTerm t1 <*> renameTerm t2 <*> renameTerm t3
  TmUnop d u tm -> pure (flip TmUnop u) <*> renameTyData d <*> renameTerm tm
  TmBinop d b t1 t2 ->
    pure (flip TmBinop b) <*> renameTyData d <*> renameTerm t1 <*> renameTerm t2
  TmLet d x t1 t2 ->
    pure TmLet <*> renameTyData d <*> renameId x <*> renameTerm t1 <*> renameTerm t2
  TmVariant d x ts ->
    pure TmVariant <*> renameTyData d <*> renameId x <*> mapM renameTerm ts
  TmMatch d tm cases ->
    pure TmMatch <*> renameTyData d <*> renameTerm tm <*>
    mapM (bimapM renamePattern renameTerm) cases
    -- mapM (mapSndM renameTerm) cases
  TmRecord d fields ->
    pure TmRecord <*> renameTyData d <*> mapM (bimapM renameId renameTerm) fields
  TmPlaceholder d nm x ty ->
    pure TmPlaceholder <*> renameTyData d <*> renameClassNm nm <*>
    renameId x <*> renameType ty
  TmThunk d nm args ->
    pure TmThunk <*> renameTyData d <*> renameId nm <*>
    mapM (bimapM renameId renameType) args

renameCommand :: Command TyData -> RenamerM (Command TyData)
renameCommand = \case
  CDecl d x ty -> pure CDecl <*> renameTyData d <*> renameId x <*> renameType ty
  CLet d x tm -> pure CLet <*> renameTyData d <*> renameId x <*> renameTerm tm
  CEval d tm ->
    debugPrint ("\nrenaming CEval: " ++ show tm) $ do
    res <- pure CEval <*> renameTyData d <*> renameTerm tm
    debugPrint ("res: " ++ show res) $
      return res
  CCheck d tm -> pure CCheck <*> renameTyData d <*> renameTerm tm
  CData d nm typarams ctors ->
    pure CData <*> renameTyData d <*> renameTypeId nm <*> mapM renameTypeId typarams <*>
    mapM (bimapM renameId (mapM renameType)) ctors
  CRecord d nm typarams fields ->
    pure CRecord <*> renameTyData d <*> renameTypeId nm <*> mapM renameTypeId typarams <*>
    mapM (bimapM renameId renameType) fields
  CAssert d tm -> pure CAssert <*> renameTyData d <*> renameTerm tm
  CClass d supers nm typaram methods ->
    pure CClass <*> renameTyData d <*> mapM renameClassNm supers <*> renameClassNm nm <*>
    renameTypeId typaram <*> mapM (bimapM renameId renameType) methods
  CInstance d constraints nm ty methods ->
    pure CInstance <*> renameTyData d <*>
    mapM (bimapM renameId renameClassNm) constraints <*>
    renameClassNm nm <*> renameType ty <*> mapM (bimapM renameId renameTerm) methods
  CSuperCombinator d nm params body ->
    pure CSuperCombinator <*> renameTyData d <*> renameId nm <*>
    mapM (bimapM renameId renameType) params <*> renameTerm body

renameProg :: Prog TyData -> RenamerM (Prog TyData)
renameProg (Prog { pdata_of = d
                 , prog_of = cs }) = do
  d' <- renameTyData d
  cs' <- mapM renameCommand cs
  return $ Prog { pdata_of = d'
                , prog_of = cs' }

rename :: Prog TyData -> Prog TyData
rename p = runRenamerM (renameProg p) initRenamerState
