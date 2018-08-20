-- | This module contains the typechecker. It is a function from
-- untyped ASTs with line/column number metadata to ASTs with type
-- metadata.

module Tycheck (
  TyData, runTycheck, tycheckProg
  ) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.List (unzip4)
import Data.Maybe (fromJust)

import Ast
import Core (FreeTyVars(..), ConstrSet, TypeSubst, unify, idOfType,
             TySubstable(..), tysubstAll, fixTy, normalize, kindCheck,
             tysubst')
import Gensym (nextSym, nextSym2, nextSym3)
import Parser
import Symtab (Symtab, Id(..), empty, add, get, exists, assocGet)
import Util

-- TODO: Type synonyms and/or newtypes at some point.
-- TODO: add a newtype for type schemes

---------------------------------------------
-- | The type of metadata for typechecked terms.

newtype TyData = TyData { unTyData :: Type }
               deriving (Show)

mkData ty = TyData ty

mapTyData :: (Type -> Type) -> TyData -> TyData
mapTyData f (TyData ty) = TyData (f ty)

-- TyData can receive type substitution
instance TySubstable TyData where
  tysubst b s t fi = TyData (tysubst b s t (unTyData fi))


-----------------
-- | Typechecker

data Context =
  Context {
  -- explicit type declarations
  ctx_decls :: Symtab Type,
  -- regular typing context
  ctx_gamma :: Symtab Type,
  -- user-defined datatypes
  ctx_datatypes :: Symtab Type,
  -- map constructor names to their datatypes
  ctx_ctors :: Symtab Type,
  -- map field names to their record types
  ctx_fields :: Symtab Type
  }
  deriving Show

initCtx :: Context
initCtx = Context { ctx_decls = empty
                  , ctx_gamma = empty
                  , ctx_datatypes = empty
                  , ctx_ctors = empty
                  , ctx_fields = empty }

updDecls :: (Symtab Type -> Symtab Type) -> Context -> Context
updDecls f ctx = ctx { ctx_decls = f $ ctx_decls ctx }

updGamma :: (Symtab Type -> Symtab Type) -> Context -> Context
updGamma f ctx = ctx { ctx_gamma = f $ ctx_gamma ctx }

type TycheckM a =
  ReaderT Context (ExceptT String (StateT Int Identity)) a

runTycheck :: TycheckM a -> Either String a
runTycheck t =
  fst $ runIdentity (runStateT (runExceptT (runReaderT t initCtx)) 0)

unifyError :: Show α => Type -> Type -> α -> TycheckM b
unifyError s t fi =
  throwError $ "Type error: unable to unify " ++ show s ++ " and " ++
  show t ++ " at " ++ show fi

tryUnify :: Show α => α -> ConstrSet -> (TypeSubst -> TycheckM a) ->
            TycheckM a
tryUnify fi c f =
  case unify c of
    Left (s, t) -> unifyError s t fi
    Right tsubst ->
      f tsubst

tycheckTerm :: Show α => Term α -> TycheckM (Term TyData, ConstrSet)
tycheckTerm (TmVar fi x) =
  debugPrint "TmVar" $ do
  -- 'asks' takes a function mapping the context to a value
  tyscheme <- asks $ Symtab.get x . ctx_gamma
  case tyscheme of
    Just tyscheme' -> do
      ty <- instantiate_tyscheme tyscheme'
      debugPrint ("var nm: " ++ show x) $
        debugPrint ("var tyscheme: " ++ show tyscheme') $
        debugPrint ("var ty : " ++ show ty ++ "\n") $ do
        return $ (TmVar (mkData ty) x, [])
    Nothing ->
      throwError $ "Type error: unbound identifier " ++ show x ++
      " at " ++ show fi

tycheckTerm (TmAbs fi x ty tm) =
  debugPrint "TmAbs" $ do
  ty' <- normalize <$> resolveTyNames fi ty >>= wellKinded
  (tm', c) <- local (updGamma $ add x ty') $
              tycheckTerm tm
  let ty'' = ty_of_term tm'
  debugPrint ("abs nm: " ++ show x) $
    debugPrint ("abs tm: " ++ show tm') $
    debugPrint ("abs ty: " ++ show ty) $
    debugPrint ("abs ty': " ++ show ty') $
    debugPrint ("abs tyscheme: " ++ show ty') $
    debugPrint ("abs ty'': " ++ show ty'') $ do
    y <- nextSym "?Y_"
    let tyy = TyVar False (Id y)
    let c' = c ++ [(tyy, TyArrow ty' ty'')]
    -- debugPrint ("abs c: " ++ show c') $
    debugPrint "abs c: " $
      tryUnify fi c' $
      \tsubst ->
        -- debugPrint ("abs tsubst: " ++ show tsubst ++ "\n") $
        debugPrint "abs tsubst\n" $
        return (tysubstAll tsubst $
                TmAbs (mkData tyy) x ty' tm', c')
  
tycheckTerm (TmApp fi t1 t2) =
  debugPrint "TmApp" $ do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  debugPrint ("app tm1: " ++ show t1') $
    debugPrint ("app tm2: " ++ show t2') $
    debugPrint ("app ty1: " ++ show ty1) $
    debugPrint ("app ty2: " ++ show ty2) $ do
    x <- nextSym "?Y_"
    let tyx = TyVar False (Id x)
    let c = c1 ++ c2 ++ [(ty1, TyArrow ty2 tyx)]
    debugPrint ("app c: " ++ show c) $
      tryUnify fi c $
      \tsubst ->
        debugPrint ("app tsubst: " ++ show tsubst ++ "\n") $
        return (tysubstAll tsubst $ TmApp (mkData tyx) t1' t2', c)

tycheckTerm (TmBool _ b) =
  debugPrint "TmBool\n" $
  return (TmBool (mkData TyBool) b, [])

tycheckTerm (TmIf fi t1 t2 t3) =
  debugPrint "TmIf\n" $ do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  (t3', c3) <- tycheckTerm t3
  let (ty1, ty2, ty3) = (ty_of_term t1', ty_of_term t2', ty_of_term t3')
  let c = c1 ++ c2 ++ c3 ++ [(ty1, TyBool), (ty2, ty3)]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $ TmIf (mkData ty2) t1' t2' t3', c)

tycheckTerm (TmUnit _) =
  debugPrint "TmUnit\n" $
  return (TmUnit (mkData TyUnit), [])

tycheckTerm (TmInt _ i) =
    debugPrint "TmInt\n" $
  return (TmInt (mkData TyInt) i, [])

tycheckTerm (TmChar _ c) =
    debugPrint "TmChar\n" $
  return (TmChar (mkData TyChar) c, [])

tycheckTerm (TmUnop fi u tm) =
  debugPrint "TmUnop\n" $ do
  (tm', c) <- tycheckTerm tm
  let ty = ty_of_term tm'
  case u of

    UFix ->
      debugPrint "UFix" $ do
      y <- nextSym "?Y_"
      let tyy = TyVar False (Id y)
      let c' = c ++ [(ty, TyArrow tyy tyy)]
      -- let c' = c
      debugPrint "UFix 2" $
        tryUnify fi c' $
        \tsubst ->
          debugPrint "UFix tsubst" $
          return (tysubstAll tsubst $ TmUnop (mkData tyy) u tm', c')
  
    URef ->
      return (TmUnop (mkData $ TyRef ty) URef tm', c)

    UDeref -> do
      x <- nextSym "?Y_"
      let tyx = TyVar False (Id x)
      let c' = c ++ [(ty, TyRef tyx)]
      tryUnify fi c' $
        \tsubst ->
          return (tysubstAll tsubst $ TmUnop (mkData $ tyx) u tm',
                  c')

    -- UMinus, UNot
    -- This may be a little weird when we add floats. Maybe this is
    -- why OCaml has separate operators for them.
    _ -> do
      let c' = c ++ [(ty, case u of
                            UMinus -> TyInt
                            UNot -> TyBool)]
      tryUnify fi c' $
        \tsubst ->
          return (tysubstAll tsubst $ TmUnop (mkData ty) u tm', c')

-- When we add floats, we can just introduce a type variable for the
-- type of the binop term and add a constraint that it's equal to the
-- type of the arguments in the case of arithmetic operations (or
-- equal to bool in the other cases, etc.).
-- Is that really right though? We really need to ensure that the
-- operands have arithmetic types and not just arbitrary types that
-- happen to be the same on both sides.
-- Typeclasses would obviously fix the problem since we could have a
-- class for numeric types and provide instances for int and float.
tycheckTerm (TmBinop fi b t1 t2) =
  debugPrint "TmBinop\n" $ do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  let c = c1 ++ c2 ++
          if isBUpdate b then [(ty1, TyRef ty2)]
          else if isArithBinop b then [(ty1, ty2), (ty1, TyInt)]
          else if isComparisonBinop b then [(ty1, ty2), (ty1, TyBool)]
          else []
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $
              TmBinop (mkData $ binopType b) b t1' t2', c)

tycheckTerm (TmLet fi x tm1 tm2) =
  debugPrint "TmLet" $ do
  (tm1', c1) <- tycheckTerm tm1
  let ty1 = ty_of_term tm1'
  tyscheme <- if isValue tm1' then generalize_ty ty1
              else return ty1
  debugPrint ("ty: " ++ show ty1) $
    debugPrint ("tyscheme: " ++ show tyscheme ++ "\n") $ do
    (tm2', c2) <- local (updGamma $ add x tyscheme)  $
                  tycheckTerm tm2
    let c = c1 ++ c2
    tryUnify fi c $
      \tsubst ->
        return (tysubstAll tsubst $
                TmLet (mkData $ ty_of_term tm2') x tm1' tm2', c)

-- Not sure that we need this since TmVariants don't appear in the
-- syntax of the program, only as intermediate terms generated by the
-- interpreter.
-- tycheckTerm (TmVariant fi x tms) = do
--   (tms', cs) <- unzip <$> mapM tycheckTerm tms
--   error "TODO"
tycheckTerm (TmVariant _ _ _) =
  throwError "unexpected TmVariant in typechecker"

tycheckTerm (TmMatch fi discrim cases) =
  debugPrint "TmMatch 1\n" $ do
  (discrim', c1) <- tycheckTerm discrim
  debugPrint "TmMatch 2\n" $ do
    (tys, binds, c2, tms') <-
      quadmap id concat concat id . unzip4 <$>
      mapM (\(p, tm) -> do
               (ty, binds, cs) <- patternType fi p
               (tm', cs') <-
                 local (updGamma $
                        flip (foldl (\acc (x, t) ->
                                       add x t acc)) binds)
                 $ tycheckTerm tm
               return (ty, binds, cs ++ cs', tm')) cases
    debugPrint "TmMatch 3\n" $ do
      -- Need a type variable for the overall type, and if there are any
      -- cases then we constrain it to be equal to their type. Also need
      -- to constrain all of the case types to be the same.
      y <- TyVar False . Id <$> nextSym "_Y?"
      let c = c1 ++ c2 ++ map (\ty ->
                                 debugPrint ("fds: " ++ show ty) $
                                 (ty, ty_of_term discrim')) tys ++
              if length cases > 0 then
                -- debugPrint ("asdf: " ++ (show $ ty_of_term $ tms'!!0)) $
                (y, ty_of_term $ tms'!!0) :
                map (\tm ->
                       -- debugPrint ("asdf': " ++ (show $ ty_of_term tm)) $
                        (ty_of_term tm,
                         ty_of_term (tms'!!0))) tms'
              else []
      debugPrint (show c) $
        debugPrint "TmMatch 4\n" $ do
        ctx <- ask
        tryUnify fi c $
          \tsubst ->
            debugPrint "TmMatch 5\n" $
            return (tysubstAll tsubst $
                     TmMatch (mkData y) discrim' (zip (fst $ unzip cases)
                                                  (tms')),
                    c)

tycheckTerm (TmRecord fi fields) = do
  let (nms, tms) = unzip fields
  (tms', cs) <- unzip <$> (mapM tycheckTerm tms)
  γ <- asks ctx_fields
  recordTy@(TyRecord recordNm _ recordFields) <-
    instantiate_tyscheme =<< case Symtab.get (nms!!0) γ of
      Just ty ->
        debugPrint (show ty) $
        return ty
      Nothing -> throwError $ "unknown record field name " ++
                 show (nms!!0) ++ " at " ++ show fi
  if length nms /= length recordFields then
    throwError $ "wrong number of fields in record " ++
    show recordNm ++ " at " ++ show fi
    else do
    cs' <- mapM (\(nm, tm) ->
                    case assocGet nm recordFields of
                      Just ty -> return (ty, ty_of_term tm)
                      Nothing -> throwError $ "invalid record field name "
                                 ++ show nm ++ " at " ++ show fi) $
           zip nms tms'
    let c = concat cs ++ cs'
    tryUnify fi c $
      \tsubst ->
        return (tysubstAll tsubst $
                TmRecord (mkData recordTy) (zip nms tms'), c)

tycheckCommand :: Show α => Command α -> TycheckM (Command TyData)
tycheckCommand (CDecl fi x ty) =
  debugPrint ("CDecl ty: " ++ show ty) $ do
  ty' <- resolveTyNames fi ty
  let ty'' = normalize ty'
  debugPrint ("CDecl ty': " ++ show ty') $
    debugPrint ("CDecl ty'': " ++ show ty'') $
    CDecl (mkData TyUnit) x . normalize <$>
    (resolveTyNames fi ty >>= wellKinded)

tycheckCommand (CLet fi x t) =
  debugPrint "CLet 1" $
  debugPrint (show t) $ do
    (t', c) <- tycheckTerm t
    debugPrint "CLet 2" $
      tryUnify fi c $
      \tsubst ->
        debugPrint ("CLet " ++ show x) $
        debugPrint ("t': " ++ show t') $
        debugPrint ("ty: " ++ show (ty_of_term t')) $
        debugPrint ("c: " ++ show c) $
        debugPrint ("tsubst: " ++ show tsubst) $
        debugPrint ("ty': " ++ show (tysubstAll tsubst $ ty_of_term t')) $
        debugPrint ("ty'': " ++ show (ty_of_term $ tysubstAll tsubst t')
                     ++ "\n") $
        return $ CLet (mkData (tysubstAll tsubst $ ty_of_term t')) x $
        mapTyData normalize . tysubstAll tsubst <$>
        (termTypeRec normalize $ tysubstAll tsubst t')
        -- this tysubst on t' isn't doing quite what we want since it
        -- doesn't affect the type metadata... so we also fmap the
        -- tysubst over it. TODO: make it nicer somehow.

tycheckCommand (CEval fi t) = do
  (t', _) <- tycheckTerm t
  return $ CEval (mkData (ty_of_term t')) t'

tycheckCommand (CData fi nm tyvars ctors) =
  return $ CData (mkData TyUnit) nm tyvars ctors

tycheckCommand (CRecord fi nm tyvars fields) =
  return $ CRecord (mkData TyUnit) nm tyvars fields

tycheckCommand (CCheck _ _) =
  throwError "unexpected CCheck in typechecker"

tycheckCommand (CAssert _ _) =
  throwError "unexpected CAssert in typechecker"

tycheckCommands :: Show α => [Command α] -> TycheckM [Command TyData]
tycheckCommands [] = return []
tycheckCommands (com:coms) = do
  com' <- tycheckCommand com
  case com' of

    CDecl _ x ty -> do
      let fvs = freetyvars ty
      -- Don't generalize ty so when we pass this to unify_tyschemes
      -- it doesn't replace the rigid type variables with non rigid
      -- ones.
      debugPrint ("CDecl' ty: " ++ show ty) $
        debugPrint ("CDecl' fvs: " ++ show fvs ++ "\n") $ do
        coms' <- local (updDecls $ add x ty) $
                 tycheckCommands coms
        return $ com' : coms'

    CLet _ x tm ->
      debugPrint "CLet 3" $ do
      decls <- asks ctx_decls
      γ <- asks ctx_gamma
      let ty = ty_of_term tm
      -- Enforce value restriction since we have mutable references.
      -- I.e., only generalize the type when then term is a syntactic
      -- value. See TAPL or Xavier Leroy's PhD thesis.
      tyscheme <- if isValue tm then
                    generalize_ty ty >>= instantiate_tyscheme
                  else return ty
      case Symtab.get x decls of
        Just declTyscheme -> do
          _ <- unify_tyschemes (data_of_command com) tyscheme declTyscheme
          -- Ignore the result of unifying the type schemes since we
          -- want to use the exact type declared by the programmer.
          debugPrint "CLet 2" $
            debugPrint ("tyscheme: " ++ show tyscheme) $
            debugPrint ("declTyscheme: " ++ show declTyscheme ++ "\n") $ do
            tyscheme' <- generalize_ty declTyscheme
            coms' <- local (updGamma $ const $ add x tyscheme' γ) $
                     tycheckCommands coms
            return $ com' : coms'
        Nothing -> do
          coms' <- local (updGamma $ const $ add x tyscheme γ) $
                   tycheckCommands coms
          return $ com' : coms'

    -- TODO: ensure that all free type variables appearing in the
    -- constructor signatures are in the tyvars list, and generate a
    -- warning if any tyvars are unused.
    -- I really wonder if tying the knot like this is really
    -- necessary.. but it seems to work so we'll leave it for now.
    CData _ nm tyvars ctors ->
      debugPrint ("CData") $ do
      let ty = normalize $ fixTy nm $ nameToVar nm $
               abstractType tyvars $ TyVariant nm
               (TyVar False <$> tyvars) ctors
      let open = open_tyscheme ty
      debugPrint ("nm: " ++ show nm) $
        debugPrint ("ctors: " ++ show ctors) $
        debugPrint ("ty: " ++ show ty) $
        debugPrint ("open: " ++ show open) $ do
        coms' <-
          local (\ctx ->
                   ctx { ctx_datatypes = add nm ty $ ctx_datatypes ctx
                       , ctx_ctors =
                         foldl (\acc x -> add x ty acc)
                         (ctx_ctors ctx) (fst $ unzip ctors)

                       -- Add types of curried constructor functions
                       -- to the typing context.
                       , ctx_gamma =
                           foldl (\acc (ctorName, ctorTys) ->
                                     let tys = map (normalize .
                                                    tysubst' ty
                                                    (TyVar False nm) .
                                                    nameToVar nm) ctorTys in
                                       add ctorName
                                       (mkTypeScheme tyvars $ mkArrowType $
                                        tys ++ [open]) acc)
                           (ctx_gamma ctx) ctors
                       }) $
          tycheckCommands coms
        return $ com' : coms'

    -- TODO: same as above
    CRecord fi nm tyvars fields ->
      debugPrint ("CRecord") $ do
      γ <- asks ctx_gamma
      mapM_ (\nm -> case Symtab.get nm γ of
                      Just _ -> throwError $ "field name " ++ show nm
                                ++ " already exists at " ++ show fi
                      Nothing -> return ()) $ fst $ unzip fields
      let ty = normalize $ fixTy nm $ nameToVar nm $
               abstractType tyvars $ TyRecord nm
               (TyVar False <$> tyvars) fields
      let open = open_tyscheme ty
      debugPrint ("nm: " ++ show nm) $
        debugPrint ("fields: " ++ show fields) $
        debugPrint ("ty: " ++ show ty) $
        debugPrint ("open: " ++ show open) $ do
        coms' <-
          local (\ctx ->
                   ctx { ctx_datatypes = add nm ty $ ctx_datatypes ctx
                       , ctx_fields =
                         foldl (\acc x -> add x ty acc)
                         (ctx_fields ctx) (fst $ unzip fields)

                       -- Add types of field projection functions to
                       -- the typing context.
                       , ctx_gamma =
                           foldl (\acc (fieldName, fieldTy) ->
                                     let ty' = normalize $
                                               tysubst' ty
                                               (TyVar False nm) $
                                               nameToVar nm fieldTy in
                                       add fieldName
                                       (mkTypeScheme tyvars $
                                        TyArrow open ty') acc)
                           (ctx_gamma ctx) fields
                       }) $
          tycheckCommands coms
        return $ com' : coms'

    _ -> do
      coms' <- tycheckCommands coms
      return $ com' : coms'

tycheckProg :: Show α => Prog α -> TycheckM (Prog TyData)
tycheckProg p = do
  coms <- tycheckCommands (prog_of p)
  return $ Prog { pdata_of = mkData TyBool, prog_of = coms }


----------
-- | Misc

ty_of_term :: Term TyData -> Type
ty_of_term = unTyData . data_of_term

generalize_ty :: Type -> TycheckM Type
generalize_ty ty = do
  γ <- asks ctx_gamma
  let fvs= freetyvars ty
  let generalizable = map (fromJust . idOfType)
        (filter (\(TyVar _ x) -> not $ x `exists` γ) fvs)
  return $ mkTypeScheme generalizable ty

-- Passing False for the type variables rigidness doesn't matter since
-- the Eq instance for types ignores it.
instantiate_tyscheme :: Type -> TycheckM Type
instantiate_tyscheme (TyAbs x k s) = do
  s' <- instantiate_tyscheme s
  normalize . TyApp (TyAbs x k s') <$> TyVar False . Id <$> nextSym "?Y_"
instantiate_tyscheme ty = return ty

-- Strip off type abstractions, leaving the body unchanged.
open_tyscheme :: Type -> Type
open_tyscheme (TyAbs _ _ s) = open_tyscheme s
open_tyscheme ty = ty


-- The first type scheme argument should be that obtained from
-- typechecking the body of a let command, and the second should be
-- the declared type. We expect the first to be more general than the
-- second.
unify_tyschemes :: Show α => α -> Type -> Type -> TycheckM Type
unify_tyschemes fi tyscheme1 tyscheme2 = do
  ty1 <- instantiate_tyscheme tyscheme1
  ty2 <- instantiate_tyscheme tyscheme2
  debugPrint "unify_tyschemes" $
    debugPrint ("tyscheme1: " ++ show tyscheme1) $
    debugPrint ("tyscheme2: " ++ show tyscheme2) $
    debugPrint ("ty1: " ++ show ty1) $
    debugPrint ("ty2: " ++ show ty2) $
    case unify [(ty1, ty2)] of
      Left (s, t) -> unifyError s t fi
      Right tsubst -> do
        debugPrint ("tsubst: " ++ show tsubst ++ "\n") $ do
          return $ tysubstAll tsubst ty1


-- -- Make all type variables in a type non-rigid.
loosen_type :: Type -> Type
loosen_type = typeRec $
  \ty -> case ty of
    TyVar _ x -> TyVar False x
    _ -> ty


-- Given a pattern, generate a type for it containing type variables
-- for each variable in the pattern along with an association list
-- mapping the variables to their type variables. Using this we can
-- typecheck match cases by just constraining the type of the
-- discriminee to be equal to the type returned by this function by
-- the pattern, and typecheck the body of the case in a context
-- extended by the bindings returned.
-- Maybe we could use a writer monad to make this a bit nicer but it's
-- fine like this for now.
-- We also need to generate contraints for verifying that constructor
-- patterns are valid..
patternType :: Show α => α -> Pattern ->
               TycheckM (Type, [(Id, Type)], ConstrSet)
patternType _ (PVar x) = do
  ty <- TyVar False . Id <$> nextSym "?Y_"
  return (ty, [(x, ty)], [])
patternType _ PUnit = return (TyUnit, [], [])
patternType _ (PBool _) = return (TyBool, [], [])
patternType _ (PInt _) = return (TyInt, [], [])
patternType _ (PChar _) = return (TyChar, [], [])
patternType fi (PPair p1 p2) = do
  (ty1, binds1, cs1) <- patternType fi p1
  (ty2, binds2, cs2) <- patternType fi p2
  return (TyVariant (Id "Pair") [ty1, ty2] [],
          binds1 ++ binds2, cs1 ++ cs2)

-- We return a freshly instantiated copy of the variant type, with the
-- types it associates with the current constructor name constrained
-- to be equal to the types computed by recursion on the subpatterns.
patternType fi (PConstructor nm ps) = do
  (tys, binds, cs) <- trimap id concat concat . unzip3 <$>
                      mapM (patternType fi) ps
  variantTypeConstr <- asks (Symtab.get nm . ctx_ctors)
  case variantTypeConstr of
    Just vTyConstr -> do
      vTy@(TyVariant _ _ ctors) <- instantiate_tyscheme vTyConstr
      case assocGet nm ctors of
        Just tys' ->
          if length tys == length tys' then
            return (vTy, binds, cs ++ zip tys tys')
          else
            throwError $ "Type error: wrong number of arguments to " ++
            show nm ++ " constructor in pattern at " ++ show fi
        Nothing ->
          throwError $ "Type error: constructor " ++ show nm ++
          "not found in definition of type " ++ show vTy
    Nothing -> throwError $ "Type error: unbound identifier " ++
               show nm ++ " at " ++ show fi

-- We don't check for empty fields list here, since it should be
-- syntactically impossible, and never generated anywhere.
patternType fi (PRecord pfields) = do
  let (nms, ps) = unzip pfields
  (tys, binds, cs) <- trimap id concat concat . unzip3 <$>
                      mapM (patternType fi) ps
  δ <- asks ctx_fields
  tys' <-
    mapM (\nm -> case Symtab.get nm δ of
                   Just ty -> return ty
                   Nothing -> throwError $ "unknown record field name " ++
                              show nm ++ " at " ++ show fi) nms
  if not $ allEq tys' then
    throwError $ "mal-formed record pattern at " ++ show fi
    else do
    recTy@(TyRecord _ _ fields) <- instantiate_tyscheme $ tys'!!0
    cs' <- mapM (\(nm, ty) ->
                     case assocGet nm fields of
                       Just ty' -> return (ty, ty')
                       Nothing -> throwError $ "invalid record field " ++
                                  show nm ++ " at " ++ show fi) $
           zip nms tys
    return (recTy, binds, cs ++ cs')

-- Look up all TyNames and replace them with their actual types.
resolveTyNames :: Show α => α -> Type -> TycheckM Type
resolveTyNames fi =
  typeRecM $
  \ty -> case ty of
    TyName nm -> do
      δ <- asks ctx_datatypes
      case Symtab.get nm δ of
        Just ty' -> return ty'
        Nothing ->
          -- debugPrint (show δ) $
          throwError $ "Type error: unbound type identifier " ++
            show nm ++ " at " ++ show fi
    _ -> return ty


-- Abstract a type over a list of Ids. We assume their kinds to be *
-- for now.
abstractType :: [Id] -> Type -> Type
abstractType [] = id
abstractType (x:xs) = TyAbs x KStar . abstractType xs


-- Pass through the input type, raising an error if it isn't
-- well-kinded.
wellKinded :: Type -> TycheckM Type
wellKinded ty = case kindCheck ty of
                  Just _ -> return ty
                  _ -> throwError $ "Type error: " ++ show ty ++
                       " is not well-kinded"


-- Build a type supercombinator (type scheme) with the given Ids
-- (which may appear free in the given type body).
mkTypeScheme :: [Id] -> Type -> Type
mkTypeScheme [] ty = ty
mkTypeScheme (x:xs) ty = TyAbs x KStar $ mkTypeScheme xs ty


-- Replace all TyNames with TyVars of the same Id.
nameToVar :: Id -> Type -> Type
nameToVar nm = typeRec $
  \ty -> case ty of
    TyName nm' -> if nm == nm' then TyVar False nm else TyName nm'
    _ -> ty
