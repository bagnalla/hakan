{-# LANGUAGE FlexibleContexts #-}

-- | This module contains the typechecker. It is a function from
-- untyped ASTs with line/column number metadata to ASTs with type
-- metadata.

module Tycheck (
  TyData(..), runTycheck, tycheckProg
  ) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor
import Data.List (nub, unzip4, intercalate)
import Data.Maybe (fromJust)
import Data.Tree
import Data.Tuple (swap)

import Ast
import Core (idOfType, isTyVar, constraintOfPlaceholder)
import Gensym (nextSym, nextSymN)
import Kind (kindCheck, runKindCheck, kindOfType, kindCheckVariantOrRecord)
import Symtab (Id(..), add, get, assocGet, assocIndex, Symtab)
import Context
import Unify (ConstrSet, unify, printConstrSet, printUnifyLog)
import Util

instance MonadFail Identity where
  fail = error

-- TODO: Type synonyms and newtypes.


------------------------------------------------
-- | The type of metadata for typechecked terms.

newtype TyData = TyData { unTyData :: Type }
               deriving Eq

instance Show TyData where
  show (TyData ty) = show ty

mkData :: Type -> TyData
mkData ty = TyData ty

-- mapTyData :: (Type -> Type) -> TyData -> TyData
-- mapTyData f (TyData ty) = TyData $ f ty

-- mapTyDataM :: Functor f => (Type -> f Type) -> TyData -> f TyData
-- mapTyDataM g (TyData ty) = TyData <$> g ty

-- TyData can receive type substitution
instance TySubstable TyData where
  tysubst b s t fi = TyData (tysubst b s t (unTyData fi))


----------------
-- | Typechecker

type TycheckM a =
  WriterT [String]
  (ReaderT Context
   (ExceptT String
    (StateT Int Identity))) a

runTycheck :: TycheckM a -> Either String (a, [String])
runTycheck = fst . runIdentity . flip runStateT 0 . runExceptT .
             flip runReaderT initCtx . runWriterT

typeError :: Show α => α -> String -> TycheckM be
typeError fi msg = throwError $ "Type error: " ++ msg ++ " at " ++ show fi

unifyError :: Show α => Type -> Type -> α -> String -> TycheckM b
unifyError s t fi msg =
  throwError $ "Type error: unable to unify\n" ++ show s ++ "\nand\n" ++
  show t ++ " at " ++ show fi ++ ".\nReason: " ++ msg

tryUnify :: Show α => α -> ConstrSet -> (TypeSubst -> TycheckM a) ->
            TycheckM a
tryUnify fi c f = do
  η <- asks ctx_datatypes
  ψ <- asks ctx_instances
  let (result, log) = runWriter $ unify fi η ψ c
  case result of
    Left (s, t, msg) ->
      debugPrint (printUnifyLog log) $
      unifyError s t fi msg
    Right tsubst ->
      f tsubst


tycheckTerm :: Show α => Term α -> TycheckM (Term TyData, ConstrSet)

-- When the name refers to a class method, we replace the variable
-- with a placeholder to be filled in later with a selector for the
-- resolved instance.
tycheckTerm (TmVar fi x) = do
  tyscheme <- asks $ Symtab.get x . ctx_gamma
  cls <- asks $ Symtab.get x . ctx_methods
  case tyscheme of
    Just tyscheme' -> do
      ty <- set_rigid False <$> instantiate_tyscheme' fi tyscheme'
      debugPrint "" $
        if isMethod tyscheme' then
          case cls of
            Just (TypeClass { tyclass_name = classNm
                            , tyclass_index = classTyIndex }) -> do
              let open = open_tyscheme tyscheme'
              let tyIndex = fromJust $
                            match_type classTyIndex (normalize_ty ty) open
              return (TmPlaceholder (mkData ty) classNm x tyIndex, [])
            _ ->
              throwError $ "Type error: class not found for method "
              ++ show x
        else
          return (TmVar (mkData ty) x, [])
    _ ->
      throwError $ "Type error: unbound identifier " ++ show x ++
      " at " ++ show fi

tycheckTerm (TmAbs fi x ty tm) = do
  ty' <- wellKinded fi ty
  (tm', c) <- local (updGamma $ add x $ mkTypeScheme [] False ty') $
              tycheckTerm tm
  let ty'' = ty_of_term tm'
  y <- nextSym "?Y_"
  let tyy = mkTyVar (Id y)
  let c' = c ++ [(tyy, TyArrow ty' ty'')]
  tryUnify fi c' $
    \tsubst ->
      return (tysubstAll' tsubst $ TmAbs (mkData tyy) x ty' tm', c')

tycheckTerm (TmApp fi t1 t2) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  x <- nextSym "?Y_"
  let tyx = mkTyVar (Id x)
  let c = c1 ++ c2 ++ [(ty1, TyArrow ty2 tyx)]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll' tsubst $ TmApp (mkData tyx) t1' t2', c)

tycheckTerm (TmBool _ b) =
  return (TmBool (mkData TyBool) b, [])

tycheckTerm (TmIf fi t1 t2 t3) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  (t3', c3) <- tycheckTerm t3
  let (ty1, ty2, ty3) = (ty_of_term t1', ty_of_term t2', ty_of_term t3')
  let c = c1 ++ c2 ++ c3 ++ [(ty1, TyBool), (ty2, ty3)]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll' tsubst $ TmIf (mkData ty2) t1' t2' t3', c)

tycheckTerm (TmUnit _) =
  return (TmUnit (mkData TyUnit), [])

tycheckTerm (TmInt _ i) =
  return (TmInt (mkData TyInt) i, [])

tycheckTerm (TmChar _ c) =
  return (TmChar (mkData TyChar) c, [])

tycheckTerm (TmUnop fi u tm) = do
  (tm', c) <- tycheckTerm tm
  let ty = ty_of_term tm'
  case u of
    -- UFix -> do
    --   y <- nextSym "?Y_"
    --   let tyy = mkTyVar (Id y)
    --   let c' = c ++ [(ty, TyArrow tyy tyy)]
    --   tryUnify fi c' $
    --     \tsubst ->
    --       return (tysubstAll' tsubst $ TmUnop (mkData tyy) u tm', c')
    URef ->
      return (TmUnop (mkData $ TyRef ty) URef tm', c)
    UDeref -> do
      x <- nextSym "?Y_"
      let tyx = mkTyVar (Id x)
      let c' = c ++ [(ty, TyRef tyx)]
      tryUnify fi c' $
        \tsubst ->
          return (tysubstAll' tsubst $ TmUnop (mkData $ tyx) u tm',
                  c')
    -- UMinus, UNot
    -- This may be a little weird when we add floats. Maybe this is
    -- why OCaml has separate operators for them.
    -- TODO: revisit this now that we have typeclasses.
    _ -> do
      let c' = c ++ [(ty,
                      case u of
                        UMinus -> TyInt
                        UNot -> TyBool)]
      tryUnify fi c' $
        \tsubst ->
          return (tysubstAll' tsubst $ TmUnop (mkData ty) u tm', c')

tycheckTerm (TmBinop fi b t1 t2) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  let c = c1 ++ c2 ++
          if isBUpdate b then [(ty1, TyRef ty2)]
          else if isArithBinop b || b == BEq then [(ty1, ty2), (ty1, TyInt)]
          else if isBooleanBinop b then [(ty1, ty2), (ty1, TyBool)]
          else []
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll' tsubst $
              TmBinop (mkData $ binopType b) b t1' t2', c)

tycheckTerm (TmLet fi x tm1 tm2) = do
  (tm1', c1) <- tycheckTerm tm1
  tryUnify fi c1 $
    \tsubst -> do
      (gen, tyscheme) <- process_term fi tsubst tm1'
      (tm2', c2) <- local (updGamma $ add x tyscheme) $
                    tycheckTerm tm2
      let c = c1 ++ c2
      tryUnify fi c $
        \tsubst' ->
          return (tysubstAll' tsubst' $
                  TmLet (mkData $ ty_of_term tm2') x gen tm2', c)

-- Not sure that we need this since TmVariants don't appear in the
-- syntax of the program (the programmer creates them via
-- constructors), only as intermediate terms generated by the
-- interpreter.
tycheckTerm (TmVariant _ _ _) =
  throwError "unexpected TmVariant in typechecker"

tycheckTerm (TmMatch fi discrim cases) = do
  (discrim', c1) <- tycheckTerm discrim
  (tys, binds, c2, tms') <-
    quadmap id concat concat id . unzip4 <$>
    mapM (\(p, tm) -> do
             (ty, binds, cs) <- patternType fi p
             (tm', cs') <-
               local (updGamma $
                      flip (foldl (\acc (x, t) ->
                                     add x (mkTypeScheme [] False t) acc))
                       binds)
               $ tycheckTerm tm
             return (ty, binds, cs ++ cs', tm')) cases
      -- Need a type variable for the overall type, and if there are
      -- any cases then we constrain it to be equal to their
      -- type. Also need to constrain all of the case types to be the
      -- same.
  y <- mkTyVar . Id <$> nextSym "?Y_"
  let c = c1 ++ c2 ++ map (\ty ->
                              (ty, ty_of_term discrim')) tys ++
          if length cases > 0 then
            (y, ty_of_term $ tms'!!0) :
            map (\tm -> (ty_of_term tm, ty_of_term (tms'!!0))) tms'
          else []
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll' tsubst $
               TmMatch (mkData y) discrim' (zip (fst $ unzip cases)
                                             (tms')), c)

tycheckTerm (TmRecord fi fields) = do
  let (nms, tms) = unzip fields
  (tms', cs) <- unzip <$> (mapM tycheckTerm tms)
  ε <- asks ctx_fields
  η <- asks ctx_datatypes
  x <- case Symtab.get (nms!!0) ε of
         Just ty -> return ty
         Nothing -> throwError $ "unknown record field name " ++
                    show (nms!!0) ++ " at " ++ show fi
  y <- unfold fi η <$> instantiate_tyscheme' fi x
  recordTy@(TyConstructor (TypeConstructor
                            { tycon_instantiated =
                                TyRecord recordNm _ recordFields })) <-
    unfold fi η <$>
    (instantiate_tyscheme' fi =<< case Symtab.get (nms!!0) ε of
        Just ty ->
          return ty
        Nothing -> throwError $ "unknown record field name " ++
                   show (nms!!0) ++ " at " ++ show fi)
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
        return (tysubstAll' tsubst $
                 TmRecord (mkData recordTy) (zip nms tms'), c)

tycheckTerm (TmPlaceholder _ _ _ _) =
  error "tycheckTerm: unexpected TmPlaceholder"


tycheckCommand :: Show α => Command α -> TycheckM (Command TyData)
tycheckCommand (CDecl fi x ty) = do
  η <- asks ctx_datatypes
  CDecl (mkData TyUnit) x <$>
    (wellKinded fi $ rigidify_type $ normalize_ty $ resolveTyNames fi η ty)

    
-- tycheckCommand (CLet fi x tm) = do
--   tyy <- mkTyVar . Id <$> nextSym "?Y_"
--   (tm', c) <- local (updGamma $ add x $ mkTypeScheme' [] False tyy) $ tycheckTerm tm
--   let c' = c ++ [(tyy, ty_of_term tm')]
--   tryUnify fi c' $
--     \_ ->
--       tryUnify fi c $
--       \tsubst ->
--         return $ CLet (mkData (tysubstAll' tsubst $ ty_of_term tm')) x $
--         tysubstAll' tsubst <$> tysubstAll' tsubst tm'

tycheckCommand (CLet fi x tm) = do
  tyy <- mkTyVar . Id <$> nextSym "?Y_"
  -- local (updGamma $ add x tyscheme) $
  (tm', c) <- local (updGamma $ add x $ mkTypeScheme' [] False tyy) $
    tycheckTerm tm
  let c' = c ++ [(tyy, ty_of_term tm')]
  tryUnify fi c' $
    \tsubst ->
      return $ CLet (mkData (tysubstAll' tsubst $ ty_of_term tm')) x $
      tysubstAll' tsubst <$> tysubstAll' tsubst tm'

      -- ^^^ this tysubst thing appears in multiple places now. TODO:
      -- make a single function for doing tysubst on a term and also
      -- fmapping tysubst over it.

tycheckCommand (CEval fi tm) = do
  (tm', c) <- tycheckTerm tm
  tryUnify fi c $
    \tsubst -> do
      (gen, _) <- process_term fi tsubst tm'
      return $ CEval (mkData $ ty_of_term gen) gen
  
tycheckCommand (CData _ nm tyvars ctors) =
  return $ CData (mkData TyUnit) nm tyvars ctors

tycheckCommand (CRecord _ nm tyvars fields) =
  return $ CRecord (mkData TyUnit) nm tyvars fields
  -- return $ CRecord (mkData $ TyRecord nm tyvars fields) nm tyvars fields

tycheckCommand (CCheck fi tm) = do
  (tm', c) <- tycheckTerm tm
  tryUnify fi c $
    \_ -> do
      tell $ [show tm' ++ " : " ++ show (ty_of_term tm')]
      return $ CCheck (mkData $ ty_of_term tm') tm'

tycheckCommand (CAssert _ tm) = do
  (tm', _) <- tycheckTerm tm
  return $ CAssert (mkData $ ty_of_term tm') tm'

tycheckCommand (CClass _ constrs nm tyvar methods) =
  -- Ensure no duplicate method names.
  if nub (map fst methods) == map fst methods then
    -- Ensure that every method type contains the type index variable
    -- somewhere.
    if all (containsType $ mkTyVar tyvar) (snd <$> methods) then
      return $ CClass (mkData TyUnit) constrs nm tyvar methods
    else
      throwError $ "Type error: in declaration of class " ++ show nm ++
      ": every method's type must contain the type index variable"
    -- mapSnd rigidify_type <$> methods
  else
    throwError $ "Type error: duplicate method names in declaration of class "
    ++ show nm

-- Typecheck method bodies and make sure the instance is a well-formed
-- instance for the class (also ensuring the class exists of course).
tycheckCommand (CInstance fi constrs classNm ty methods) = do
  ϕ <- asks ctx_classes
  η <- asks ctx_datatypes
  case Symtab.get (unClassNm classNm) ϕ of
    Just (TypeClass { tyclass_index = tyIndex
                    , tyclass_index_kind = indexKind
                    , tyclass_methods = clsMethods }) -> do
      (methods', c) <- mapSnd concat . unzip <$>
                       mapM (\(x, tm) -> do
                                (tm', c) <- tycheckTerm tm
                                return ((x, tm'), c)) methods
      let super_constrs = concat $
            (\(x, nm) -> zip (repeat x) $ superclasses ϕ nm) <$> constrs
      let all_constrs = nub $ constrs ++ super_constrs
      -- Check that every method is implemented.
      if length methods' == length clsMethods then do
        c' <-
          mapM (\(methodNm, methodTy) ->
                   case assocGet methodNm methods' of
                     Just instanceTy ->
                       -- Try to unify the type of the method with
                       -- that of the class method with its type index
                       -- instantiated to the particular type for this
                       -- instance.
                       return (ty_of_term instanceTy,
                                propagateClassConstraints all_constrs
                                (rigidify_type (tysubst' ty (mkTyVar tyIndex) methodTy)))
                     Nothing ->
                       throwError $ "Type error: instance of class " ++
                       show classNm ++ " for type " ++ show ty ++
                       " doesn't implement the method " ++ show methodNm ++
                       " at " ++ show fi)
          clsMethods
        let ty' = normalize_ty $ unfold fi η ty
        ι <- asks ctx_kinds
        cs <- mapM (\(x, ClassNm clsNm) ->
                      case Symtab.get clsNm ϕ of
                        Just (TypeClass { tyclass_index_kind = k }) ->
                          return (x, k)
                        Nothing ->
                          typeError fi $ "unbound class name '" ++
                          show clsNm ++ "'") all_constrs
        case runKindCheck ι cs ty' of
          Right kty ->
            if kindOfType ι kty /= Just indexKind then
              typeError fi $ show kty ++ " has kind " ++
              show (kindOfType ι kty) ++ " but is expected to have kind "
              ++ show indexKind
            else
              tryUnify fi (c ++ c') $
              \tsubst ->
                let tys = ty_of_term . snd <$> methods'
                    tys' = tysubstAll' tsubst tys in
                  return $ tysubstAll' tsubst $
                  tysubstAll' tsubst <$>
                  CInstance (mkData TyUnit) all_constrs classNm ty' methods'
          Left msg ->
            typeError fi $ "type '" ++ show ty' ++
            " is not well-kinded: " ++ msg
        else
        throwError $ "Type error: instance of class " ++ show classNm ++
        " for type " ++ show ty ++ " has the wrong number of methods at "
        ++ show fi
    Nothing ->
      throwError $ "Type error: unknown class '" ++ show classNm ++
      "' at " ++ show fi


tycheckCommands :: Show α => [Command α] -> TycheckM [Command TyData]
tycheckCommands [] = return []
tycheckCommands (com:coms) = do
  ϕ <- asks ctx_classes
  ι <- asks ctx_kinds
  let fi = data_of_command com
  com' <- tycheckCommand com
  case com' of
    -- TODO: check for existing declarations of the same name (error).
    -- It should also probably be an error if a declaration is never
    -- given a definition.
    CDecl _ x ty -> do
      let tyscheme = generalize_ty False ty
      coms' <- local (updDecls $ add x $ tyscheme) $
               tycheckCommands coms
      return $ com' : coms'

    -- TODO: produce a warning if shadowing an existing binding.
    CLet fi' x tm -> do
      δ <- asks ctx_decls
      γ <- asks ctx_gamma      
      case Symtab.get x δ of
        Just declTyscheme -> do
          -- Before processing the term, we ensure that its type is
          -- specific as possible (since the declared type may be more
          -- specific than the inferred type) so that dictionaries can
          -- be inlined for concrete known types.
          tsubst <- unify_tyschemes (data_of_command com)
                    (mkTypeScheme' [] False $ ty_of_term tm) declTyscheme
          (gen, tyscheme) <- process_term fi tsubst tm
          coms' <- local (updGamma $ const $
                          add x declTyscheme γ) $
                   tycheckCommands coms
          return $ CLet fi' x gen : coms'
        Nothing -> do
          (gen, tyscheme) <- process_term fi [] tm
          coms' <- local (updGamma $ const $
                           add x tyscheme γ) $
                   tycheckCommands coms
          return $ CLet fi' x gen : coms'

    CData _ nm tyvars ctors ->
      if any (== '_') $ unId nm then
        throwError $ "Type error: underscore in variant type name"
      else
      case kindCheckVariantOrRecord nm tyvars (concat $ snd <$> ctors) ι of
        Right (k, ks) -> do
          let ty = mkTypeConstructor' nm tyvars ks $
                   TyVariant nm (mkTyVar <$> tyvars) ctors
          let tyscheme =
                mkTypeScheme (zip3 tyvars ks $ repeat [])
                False (normalize_ty $ mkTyApp ty $ mkTyVar <$> tyvars)
          let open = open_tyscheme tyscheme
          ctorFuns <-
            mapM (mapSndM $ \ctorTys ->
                     return $
                     mkTypeScheme (zip3 tyvars ks $ repeat [])
                     False (mkArrowType $ ctorTys ++ [open])) ctors
          let fvs = nub $ concat $ map (freetyvars . snd) ctors
          if not $ all (`elem` map mkTyVar tyvars) fvs then
            throwError $ "Type error: free type variable in definition of "
            ++ show nm
            else do
            if not $ all (`elem` fvs) (mkTyVar <$> tyvars) then
              tell ["Type warning: unused type variable in definition of "
                    ++ show nm] else return ()
          coms' <-
            local (\ctx ->
                     ctx { ctx_datatypes = add nm tyscheme $
                                           ctx_datatypes ctx
                         , ctx_ctors =
                           foldl (\acc x -> add x tyscheme acc)
                           (ctx_ctors ctx) (fst $ unzip ctors)
                           -- Add types of curried constructor functions
                           -- to the typing context.
                         , ctx_gamma =
                           foldl (\acc (ctorName, ctorTy) ->
                                     add ctorName ctorTy acc)
                           (ctx_gamma ctx) ctorFuns
                         , ctx_kinds = add nm k $ ctx_kinds ctx
                         }) $
            tycheckCommands coms
          return $ (TyData open <$ com') : coms'
        Left msg -> typeError fi msg
  
    CRecord _ nm tyvars fields ->
      if any (== '_') $ unId nm then
        throwError $ "Type error: underscore in record type name"
      else
        case kindCheckVariantOrRecord nm tyvars (snd <$> fields) ι of
          Right (k, ks) -> do
            γ <- asks ctx_gamma
            mapM_ (\x -> case Symtab.get x γ of
                           Just _ -> throwError $ "field name " ++ show x
                                     ++ " already exists at " ++ show fi
                           Nothing -> return ()) $ fst $ unzip fields
            let ty = mkTypeConstructor' nm tyvars ks $
                     TyRecord nm (mkTyVar <$> tyvars) fields
            let tyscheme =
                  mkTypeScheme (zip3 tyvars ks $ repeat [])
                  False (normalize_ty $ mkTyApp ty $ mkTyVar <$> tyvars)
            let open = open_tyscheme tyscheme
            fieldFuns <-
              mapM (mapSndM $ \fieldTy ->
                       return $
                     mkTypeScheme (zip3 tyvars ks $ repeat [])
                     False (TyArrow open fieldTy))
              fields
            let fvs = concat $ map (freetyvars . snd) fields
            if not $ all (`elem` (mkTyVar <$> tyvars)) fvs then
              throwError $ "Type error : free type variable in definition of "
              ++ show nm
              else do
              if not $ all (`elem` fvs) (mkTyVar <$> tyvars) then
                tell ["Type warning: unused type variable in definition of "
                      ++ show nm] else return ()
            coms' <-
              local (\ctx ->
                       ctx { ctx_datatypes = add nm tyscheme $ ctx_datatypes ctx
                           , ctx_fields =
                             foldl (\acc x -> add x tyscheme acc)
                             (ctx_fields ctx) (fst $ unzip fields)
                           -- Add types of field projection functions to
                           -- the typing context.
                           , ctx_gamma =
                             foldl (\acc (fieldName, fieldTy) ->
                                      add fieldName fieldTy acc)
                             (ctx_gamma ctx) fieldFuns
                           , ctx_kinds = add nm k $ ctx_kinds ctx
                           }) $
              tycheckCommands coms
            return $ (TyData open <$ com') : coms'
          Left msg -> typeError fi msg

    CClass _ constrs classNm tyIndex methods -> do
      η <- asks ctx_datatypes
      ι <- asks ctx_kinds
      ks <- mapM (\(ClassNm clsNm) ->
                     case Symtab.get clsNm ϕ of
                       Just (TypeClass { tyclass_index_kind = k }) ->
                         return k
                       Nothing ->
                         typeError fi $ "unbound class name '" ++
                         show clsNm ++ "'") constrs
      case sequence $ (runKindCheck ι $ zip (repeat tyIndex) ks) <$>
        unfold fi η . snd <$> methods of
        Left msg -> typeError fi msg
        Right ktys ->
          let kind = maybeAllEq $ (fromJust . (kindOfType ι) <$>) <$>
                     ((\ty -> match_type tyIndex ty ty) <$> ktys)
          in
            case kind of
              Just k ->
                let cls = TypeClass { tyclass_constrs = constrs
                                    , tyclass_name = classNm
                                    , tyclass_index = tyIndex
                                    , tyclass_index_kind = k
                                    , tyclass_methods = methods } in
                  local (\ctx ->
                           ctx {
                            -- Add class to φ
                            ctx_classes =
                                flip (add $ unClassNm classNm)
                                (ctx_classes ctx) cls
                            -- Add methods to φ
                            , ctx_methods =
                              foldl (flip $ flip add cls) (ctx_methods ctx)
                              (fst <$> methods)
                            -- Add methods to γ
                            , ctx_gamma =
                              foldl (\acc (nm, ty) ->
                                       Symtab.add nm
                                      (generalize_ty True
                                       (propagateClassConstraints
                                        (zip (repeat tyIndex)
                                         (classNm : constrs)) ty)) acc)
                              (ctx_gamma ctx) methods } ) $ do
                  coms' <- tycheckCommands coms
                  return $ com' : coms'
              Nothing -> typeError fi  $ ""

    CInstance fi' constrs classNm ty methods -> do
      ctx <- ask
      let supers = superclasses (ctx_classes ctx) classNm
      -- Check for the existence of instances for superclasses.
      forM_ supers $
        \super ->
          case get_instance ctx ty super of
            Just _ -> return ()
            Nothing ->
              throwError $ "No instance of " ++ show super ++
              " found for type " ++ show ty ++
              ", which is a superclass constraint on " ++
              show classNm ++ ". at " ++ show fi      
      let all_constrs = constrs
      -- Resolve instances as much as possible within the method
      -- bodies, generating dictionary variables for unknown type
      -- variable instances. Any such dictionary variable should
      -- correspond to one of our instance constraints -- otherwise it
      -- isn't satisfiable.
      let spec =
            mapSnd (specialize_term ctx . snd . fill_placeholders ctx)
            <$> methods
      let filled = mapSnd (snd . fill_placeholders ctx) <$> methods
      let ty' = ty
      inst <- buildInstance fi all_constrs classNm ty' spec
      local (updInstances $ \ψ ->
                Symtab.add (unClassNm classNm)
                (inst :
                  case Symtab.get (unClassNm classNm) ψ of
                    Just instances -> instances
                    Nothing -> []) ψ) $ do
        coms' <- tycheckCommands coms
        return $ CInstance fi' all_constrs classNm ty' spec : coms'
    _ -> do
      coms' <- tycheckCommands coms
      return $ com' : coms'

buildInstance :: Show α => α -> [(Id, ClassNm)] -> ClassNm -> Type ->
                 [(Id, Term TyData)] -> TycheckM ClassInstance
buildInstance fi constrs classNm ty methods = do
  ctx <- ask
  let vars = uncurry mkDictId . swap <$> constrs
  let dict = mkAbs vars $ mkTuple $ eraseData . snd <$> methods
  return $ ClassInstance { instance_ctx = constrs
                         , instance_classname = classNm
                         , instance_ty =
                             normalize_ty
                             (resolveTyNames fi (ctx_datatypes ctx) ty)
                         , instance_dict = dict }


tycheckProg :: Show α => Prog α -> TycheckM (Prog TyData)
tycheckProg p = do
  coms <- tycheckCommands (prog_of p)
  return $ Prog { pdata_of = mkData TyBool, prog_of = coms }


----------
-- | Misc

ty_of_term :: Term TyData -> Type
ty_of_term = unTyData . data_of_term


get_placeholders :: Term TyData -> [Term TyData]
get_placeholders = (.) nub $ termRec2 $
  \tm -> case tm of
    TmPlaceholder _ _ _ _ -> [tm]
    _ -> []


-- Ignore constraints on type variables. Just produce the instance for
-- the given class.
instance_tree :: Context -> Type -> ClassNm -> Tree (Term ())
instance_tree ctx ty classNm =
  case ty of
    -- We no longer recursively generate applications to
    -- superclasses. Instead we assume that the missing dictionary
    -- will be provided from the context pre-assembled.
    TyVar _ _ _ x ->
      Node (TmVar () $ mkDictId classNm x) []
    -- When it's not a variable...
    -- For known types, we still assemble as much of the dictionary as
    -- possible and just assume that any missing pieces will be
    -- provided by the context.
    _ ->
      let Just (ClassInstance { instance_ctx = constrs
                              , instance_ty = inst_ty
                              , instance_dict = dict }) =
            get_instance ctx ty classNm in
        Node dict $
        map (\(var, classNm') ->
               case match_type var ty inst_ty of
                 Just ty' ->
                   instance_tree ctx ty' classNm'
                 Nothing ->
                   error "instance_tree: incompatible types.. \
                         \this shouldn't be possible!")
        constrs


-- Find the instance record matching a given type for a specific
-- class.
get_instance :: Context -> Type -> ClassNm -> Maybe ClassInstance
get_instance ctx ty classNm = do
  case Symtab.get (unClassNm classNm) (ctx_instances ctx) of
    Just insts -> go ty insts
    Nothing -> Nothing
  where
    go :: Type -> [ClassInstance] -> Maybe ClassInstance
    go ty [] = Nothing
    go ty (inst@(ClassInstance { instance_ty = ty' }) : insts) =
      if compatible ty ty' then Just inst else go ty insts


-- If the type is a type variable, then just produce a dictionary
-- variable. Else look for the instance. Note that this doesn't
-- recursively build a fully applied dictionary, it just grabs the
-- dict value from the appropriate instance.
get_dict :: Context -> Type -> ClassNm -> Term ()
get_dict ctx ty classNm =
  case ty of
    TyVar _ _ _ x -> TmVar () $ mkDictId classNm x
    _ ->
      case get_instance ctx ty classNm of
        Just (ClassInstance { instance_dict = dict }) -> dict
        Nothing ->
          error $ "get_dict: " ++ show ty ++
          " is not a type variable and no instance found for class "
          ++ show classNm


-- The first type scheme argument should be that obtained from
-- typechecking the body of a let command, and the second should be
-- the declared type. We expect the first to be more general than the
-- second.
unify_tyschemes :: Show α => α -> TypeScheme -> TypeScheme -> TycheckM TypeSubst
unify_tyschemes fi tyscheme1 tyscheme2 = do
  η <- asks ctx_datatypes
  ψ <- asks ctx_instances
  ty1 <- instantiate_tyscheme fi False tyscheme1
  -- Hold type variables of this one rigid (skolem).
  ty2 <- instantiate_tyscheme fi True tyscheme2
  let (result, log) = runWriter $ unify fi η ψ [(ty1, ty2)]
  case result of
    Left (s, t, msg) ->
      debugPrint (printUnifyLog log) $
      unifyError s t fi msg
    Right tsubst ->
      return tsubst


set_rigid :: Bool -> Type -> Type
set_rigid b = typeRec $
  \ty -> case ty of
    TyVar _ k ctx x -> TyVar b k ctx x
    _ -> ty

-- Make all type variables in a type non-rigid. This may not be
-- necessary now that we just choose rigidness at typescheme
-- instantiation time.
rigidify_type :: Type -> Type
rigidify_type = set_rigid True


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
  ty <- mkTyVar . Id <$> nextSym "?Y_"
  return (ty, [(x, ty)], [])
patternType _ PUnit     = return (TyUnit, [], [])
patternType _ (PBool _) = return (TyBool, [], [])
patternType _ (PInt _)  = return (TyInt, [], [])
patternType _ (PChar _) = return (TyChar, [], [])
patternType fi (PPair p1 p2) = do
  (ty1, binds1, cs1) <- patternType fi p1
  (ty2, binds2, cs2) <- patternType fi p2
  return (mkTypeConstructor (Id "Pair") [Id "a", Id "b"] [KStar, KStar]
          [ty1, ty2] $ TyVariant (Id "Pair")
          [mkTyVar $ Id "a", mkTyVar $ Id "b"] [],
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
      temp <- pure (unfold fi) <*> asks ctx_datatypes <*>
              instantiate_tyscheme' fi vTyConstr
      vTy@(TyConstructor (TypeConstructor { tycon_instantiated =
                                              TyVariant _ _ ctors })) <-
        pure (unfold fi) <*> asks ctx_datatypes <*>
        instantiate_tyscheme' fi vTyConstr
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
    -- asdf <- instantiate_tyscheme' fi $ tys'!!0
    -- debugPrint ("tyscheme: " ++ show asdf) $ do
      -- recTy@(TyRecord _ _ fields) <- instantiate_tyscheme' fi $ tys'!!0
    recTy@(TyConstructor (TypeConstructor { tycon_instantiated =
                                              TyRecord _ _ fields })) <-
      pure (unfold fi) <*> asks ctx_datatypes <*> (instantiate_tyscheme' fi $ tys'!!0)
    cs' <- mapM (\(nm, ty) ->
                    case assocGet nm fields of
                      Just ty' -> return (ty, ty')
                      Nothing -> throwError $ "invalid record field " ++
                                 show nm ++ " at " ++ show fi) $
           zip nms tys
    return (recTy, binds, cs ++ cs')


-- Pass through the input type, raising an error if it isn't
-- well-kinded.
wellKinded :: Show α => α -> Type -> TycheckM Type
wellKinded fi ty = do
  η <- asks ctx_datatypes
  ι <- asks ctx_kinds
  debugPrint ("η: " ++ show η) $
    debugPrint ("ι: " ++ show ι) $
    case runKindCheck ι [] $ unfold fi η ty of
      Right _ -> return ty
      Left msg -> typeError fi $ "Type error: " ++ show ty ++
                  " is not well-kinded: " ++ msg

mkDictId :: ClassNm -> Id -> Id
mkDictId classNm var = Id $ "?" ++ show classNm ++ "_" ++ show var


-- Given a type (possibly containing type variables) and a class name,
-- determine the constraints on type variables needed to resolve an
-- instance of the class for the type.
variable_constraints :: Show α => α -> Context -> ClassNm -> Type ->
                        TycheckM [(Id, Kind, ClassNm)]
variable_constraints fi ctx classNm ty = do
  case ty of
    TyVar _ k _ x ->
      return [(x, k, classNm)]
    _ ->
      case get_instance ctx ty classNm of
        Just (ClassInstance { instance_ctx = constrs
                            , instance_ty = inst_ty }) -> do
          concat <$>
            mapM (\(var, classNm') ->
                    case match_type var ty inst_ty of
                      Just ty' ->
                        variable_constraints fi ctx classNm' ty'
                      Nothing ->
                        error "variable_constraints: incompatible types.. \
                              \this shouldn't be possible!")
            constrs
        Nothing -> 
          throwError $ "Type error: no instance of class " ++ show classNm
          ++ " found for " ++ showTypeLight ty ++ " at " ++ show fi

-- Fill a placeholder by constructing the dictionary however possible
-- given the current context (fill in actual dictionaries for known
-- types but generate variables for instances for type variables) and
-- wrap it in a selector function to grab the correct method.
-- context, class, method name, type index

-- This is a bit of a premature optimization that I wish I hadn't
-- done. We should just fill all of the placeholders with variables
-- and then apply the known dictionary arguments afterward (I think
-- that would be doable and probably simpler). The extra overhead
-- could be reduced by some partial evaluation at a later pass.
fill_placeholder :: Context -> TypeClass -> Id -> Type -> Term ()
fill_placeholder ctx (TypeClass { tyclass_name = classNm
                                , tyclass_methods = classMethods })
  methodNm tyIndex =
  let index = fromJust $ assocIndex methodNm classMethods
      tree = instance_tree ctx tyIndex classNm
  in
    mkTupleProjection index (length classMethods) $ mkAppTree tree


-- Fill all placeholders in a term and also return the (class, type)
-- pairs that were encountered.
fill_placeholders :: Context -> Term TyData -> ([(ClassNm, Type)], Term TyData)
fill_placeholders ctx tm =
  bimap nub id $
  foldl (\(classes, acc) p@(TmPlaceholder _ classNm methodNm ty) ->
            ((classNm, ty) : classes,
              termSubst (mkData (ty_of_term p) <$
                          fill_placeholder ctx
                          (fromJust $ Symtab.get (unClassNm classNm) $
                            ctx_classes ctx) methodNm ty)
              p acc))
  ([], tm) (get_placeholders tm)


get_typescheme_constraints :: Context -> Term TyData -> [(Id, Kind, ClassNm)]
get_typescheme_constraints ctx = termRec2 $
  \tm -> case tm of
    TmVar _ x ->
      case Symtab.get x $ ctx_gamma ctx of
        Just tyscheme ->
          let ty = normalize_ty $ ty_of_term tm
              open = open_tyscheme tyscheme
              match = nub $ typesRec (\s t ->
                                        case t of
                                          TyVar _ _ _ _ -> [(s, t)]
                                          _ -> []) ty open
              constrs = flattenThird $ varsOfTypeScheme tyscheme
              constrs' =
                trimap (tysubstAll' match . mkTyVar) id id <$> constrs
          in
            mapFst3 idOfType <$> filter (isTyVar . fst3) constrs'
        Nothing -> []
    _ -> []


-- The old approach was to pass around unapplied instance dictionaries
-- and only assemble complete dictionaries at method use sites. Now,
-- when abstracting over a dictionary for a type variable, we assume
-- the context will provide it fully pre-assembled, so we don't have
-- to apply it any further. But this means that we much also do some
-- assembly of dictionaries when instantiating terms so ensure that we
-- pass fully applied dictionaries (even if they are further
-- abstracted by variables which we again assume will be provided
-- pre-assembled by our context).

specialize_term :: Context -> Term TyData -> Term TyData
specialize_term ctx =
  termRec $
  \tm ->
    case tm of
    TmVar _ x ->
      case Symtab.get x $ ctx_gamma ctx of
        Just tyscheme ->
          let ty = normalize_ty $ ty_of_term tm
              open = open_tyscheme tyscheme
              match = nub $ typesRec (\s t ->
                                        case t of
                                          TyVar _ _ _ _ -> [(s, t)]
                                          _ -> []) ty open
              constrs = flattenThird $ varsOfTypeScheme tyscheme
              constrs' = trimap (tysubstAll' match . mkTyVar) id id <$> constrs
              constrs'' = (\(ty, k, classNm) -> (ty, classNm)) <$> constrs'
              trees = uncurry (instance_tree ctx) <$> constrs''
              dicts = mkAppTree <$> trees
              result = mkApp tm $ (mkData TyUnit <$) <$> dicts
          in
            result
        Nothing -> tm
    _ -> tm


generalize_term :: Context -> [(Id, Kind, ClassNm)] -> Term TyData ->
                   (Term TyData, TypeScheme)
generalize_term ctx constrs tm =
  let ty = ty_of_term tm
      tyscheme = addConstraintsToTypeScheme constrs $ generalize_ty False ty
  in
    let args = fmap (\(var, k, classNm) -> mkDictId classNm var) constrs
        tm' = mkAbs args tm
    in
      (tm', tyscheme)


process_term :: Show α => α -> TypeSubst -> Term TyData -> TycheckM (Term TyData, TypeScheme)
process_term fi tsubst tm = do
  ctx <- ask
  let tm' = tysubstAll' tsubst <$> tysubstAll' tsubst tm
  let spec = specialize_term ctx tm'
  let (_, filled) = fill_placeholders ctx spec
  let constrs = flattenThird $ all_class_constraints (ty_of_term spec)
  let (gen, tyscheme) = generalize_term ctx constrs filled
  return (gen, tyscheme)
