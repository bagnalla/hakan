{-# LANGUAGE FlexibleContexts #-}

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
import Control.Monad.Writer
import Data.Bifunctor
import Data.List (nub, unzip4)
import Data.Maybe (fromJust)

import Ast
import Core (kindCheck)
import Gensym (nextSym)
import Symtab (Id(..), add, get, assocGet, Symtab)
import Context
import Unify (ConstrSet, unify)
import Util

-- TODO: Type synonyms and newtypes.


---------------------------------------------
-- | The type of metadata for typechecked terms.

newtype TyData = TyData { unTyData :: Type }
               deriving (Eq, Show)

mkData :: Type -> TyData
mkData ty = TyData ty

-- mapTyData :: (Type -> Type) -> TyData -> TyData
-- mapTyData f (TyData ty) = TyData $ f ty

-- mapTyDataM :: Functor f => (Type -> f Type) -> TyData -> f TyData
-- mapTyDataM g (TyData ty) = TyData <$> g ty

-- TyData can receive type substitution
instance TySubstable TyData where
  tysubst b s t fi = TyData (tysubst b s t (unTyData fi))


-----------------
-- | Typechecker

type TycheckM a =
  WriterT [String]
  (ReaderT Context
   (ExceptT String
    (StateT Int Identity))) a

runTycheck :: TycheckM a -> Either String (a, [String])
runTycheck = fst . runIdentity . flip runStateT 0 . runExceptT .
             flip runReaderT initCtx . runWriterT

unifyError :: Show α => Type -> Type -> α -> String -> TycheckM b
unifyError s t fi msg =
  throwError $ "Type error: unable to unify\n" ++ show s ++ "\nand\n" ++
  show t ++ " at " ++ show fi ++ ".\nReason: " ++ msg

tryUnify :: Show α => α -> ConstrSet -> (TypeSubst -> TycheckM a) ->
            TycheckM a
tryUnify fi c f = do
  η <- asks ctx_datatypes
  ψ <- asks ctx_instances
  -- case unify fi η ψ $ bimap (normalize fi η) (normalize fi η) <$> c of
  case unify fi η ψ c of
    Left (s, t, msg) -> unifyError s t fi msg
    Right tsubst ->
      f tsubst


tycheckTerm :: Show α => Term α -> TycheckM (Term TyData, ConstrSet)

-- When the name refers to a class method, we replace the variable
-- with a placeholder to be filled in later with a selector for the
-- resolved instance.
tycheckTerm (TmVar fi x) =
  debugPrint "TmVar" $ do
  tyscheme <- asks $ Symtab.get x . ctx_gamma
  -- classNm <- asks $ tyclass_name . fromJust . Symtab.get x . ctx_methods
  cls <- asks $ Symtab.get x . ctx_methods
  temp <- asks ctx_methods
  debugPrint (show x) $
    debugPrint (show temp) $
    case (cls, tyscheme) of
      (Just (TypeClass { tyclass_name = classNm }), Just tyscheme') -> do
        ty <- instantiate_tyscheme' fi tyscheme'
        debugPrint ("var nm: " ++ show x) $
          debugPrint ("var tyscheme: " ++ show tyscheme') $
          return (if isMethod tyscheme' then
                    TmPlaceholder (mkData ty) classNm x ty
                  else
                    TmVar (mkData ty) x,
                  [])
      _ ->
        throwError $ "Type error: unbound identifier " ++ show x ++
        " at " ++ show fi

tycheckTerm (TmAbs fi x ty tm) =
  debugPrint "TmAbs" $ do
  ty' <- wellKinded fi ty
  (tm', c) <- local (updGamma $ add x $ mkTypeScheme' [] ty') $
              tycheckTerm tm
  let ty'' = ty_of_term tm'
  debugPrint ("abs nm: " ++ show x) $
    debugPrint ("abs tm: " ++ show tm') $
    debugPrint ("abs ty: " ++ show ty) $
    debugPrint ("abs ty': " ++ show ty') $
    debugPrint ("abs tyscheme: " ++ show ty') $
    debugPrint ("abs ty'': " ++ show ty'') $ do
    y <- nextSym "?Y_"
    let tyy = mkTyVar (Id y)
    let c' = c ++ [(tyy, TyArrow ty' ty'')]
    -- debugPrint ("abs c: " ++ show c') $
    tryUnify fi c' $
      \tsubst ->
        -- debugPrint ("abs tsubst: " ++ show tsubst ++ "\n") $
        return (tysubstAll' tsubst $
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
    let tyx = mkTyVar (Id x)
    let c = c1 ++ c2 ++ [(ty1, TyArrow ty2 tyx)]
    debugPrint ("app c: " ++ show c) $
      tryUnify fi c $
      \tsubst ->
        debugPrint ("app tsubst: " ++ show tsubst ++ "\n") $
        return (tysubstAll' tsubst $ TmApp (mkData tyx) t1' t2', c)

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
      return (tysubstAll' tsubst $ TmIf (mkData ty2) t1' t2' t3', c)

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
      let tyy = mkTyVar (Id y)
      let c' = c ++ [(ty, TyArrow tyy tyy)]
      debugPrint "UFix 2" $
        tryUnify fi c' $
        \tsubst ->
          debugPrint "UFix tsubst" $
          return (tysubstAll' tsubst $ TmUnop (mkData tyy) u tm', c')

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
    _ -> do
      let c' = c ++ [(ty, case u of
                            UMinus -> TyInt
                            UNot -> TyBool
                            _ -> error "tycheckTerm TmUnop: impossible case")]
      tryUnify fi c' $
        \tsubst ->
          return (tysubstAll' tsubst $ TmUnop (mkData ty) u tm', c')

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
      return (tysubstAll' tsubst $
              TmBinop (mkData $ binopType b) b t1' t2', c)

tycheckTerm (TmLet fi x tm1 tm2) =
  debugPrint "TmLet" $ do
  (tm1', c1) <- tycheckTerm tm1
  ctx <- ask
  let (tm1'', tyscheme) = generalize_term ctx tm1'
  debugPrint ("tyscheme: " ++ show tyscheme ++ "\n") $ do
    (tm2', c2) <- local (updGamma $ add x tyscheme)  $
                  tycheckTerm tm2
    let c = c1 ++ c2
    tryUnify fi c $
      \tsubst ->
        return (tysubstAll' tsubst $
                TmLet (mkData $ ty_of_term tm2') x tm1'' tm2', c)

-- Not sure that we need this since TmVariants don't appear in the
-- syntax of the program, only as intermediate terms generated by the
-- interpreter.
-- tycheckTerm (TmVariant fi x tms) = do
--   (tms', cs) <- unzip <$> mapM tycheckTerm tms
--   error ""
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
                                        add x (mkTypeScheme' [] t) acc)) binds)
                 $ tycheckTerm tm
               return (ty, binds, cs ++ cs', tm')) cases
    debugPrint "TmMatch 3\n" $
      debugPrint ("tys: " ++ show tys) $ do
      -- Need a type variable for the overall type, and if there are any
      -- cases then we constrain it to be equal to their type. Also need
      -- to constrain all of the case types to be the same.
      y <- mkTyVar . Id <$> nextSym "?Y_"
      let c = c1 ++ c2 ++ map (\ty ->
                                 debugPrint ("asdf: " ++ show ty) $
                                 (ty, ty_of_term discrim')) tys ++
              if length cases > 0 then
                (y, ty_of_term $ tms'!!0) :
                map (\tm -> (ty_of_term tm, ty_of_term (tms'!!0))) tms'
              else []
      debugPrint "TmMatch 4\n" $
        tryUnify fi c $
          \tsubst ->
            debugPrint "TmMatch 5\n" $
            return (tysubstAll' tsubst $
                     TmMatch (mkData y) discrim' (zip (fst $ unzip cases)
                                                  (tms')),
                    c)

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
  debugPrint ("\nx: " ++ show x) $
    debugPrint ("\ny: " ++ show y ++ "\n") $ do
  
  -- recordTy@(TyRecord recordNm _ recordFields) <-
    recordTy@(TyConstructor (TypeConstructor
                             { tycon_instantiated =
                                 TyRecord recordNm _ recordFields })) <-
      unfold fi η <$>
      (instantiate_tyscheme' fi =<< case Symtab.get (nms!!0) ε of
          Just ty ->
            debugPrint (show ty) $
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

tycheckCommand :: Show α => Command α -> TycheckM (Command TyData)
tycheckCommand (CDecl fi x ty) =
  debugPrint ("\nCDecl ty: " ++ show ty) $
  CDecl (mkData TyUnit) x <$> (wellKinded fi $ rigidify_type ty)

tycheckCommand (CLet fi x t) =
  debugPrint "CLet 1" $
  debugPrint (show t) $ do
    (t', c) <- tycheckTerm t
    debugPrint "CLet 2" $
      tryUnify fi c $
      \tsubst ->
        debugPrint ("CLet " ++ show x) $
        return $ CLet (mkData (tysubstAll' tsubst $ ty_of_term t')) x $
        tysubstAll' tsubst <$> tysubstAll' tsubst t'
        
        -- this tysubst on t' isn't doing quite what we want since it
        -- doesn't affect the type metadata... so we also fmap the
        -- tysubst over it. TODO: make it nicer somehow.

tycheckCommand (CEval _ tm) = do
  (tm', _) <- tycheckTerm tm
  return $ CEval (mkData $ ty_of_term tm') tm'

tycheckCommand (CData _ nm tyvars ctors) =
  return $ CData (mkData TyUnit) nm tyvars ctors

tycheckCommand (CRecord _ nm tyvars fields) =
  return $ CRecord (mkData TyUnit) nm tyvars fields

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
    return $ CClass (mkData TyUnit) constrs nm tyvar $
    mapSnd rigidify_type <$> methods
  else
    throwError $ "Type error: duplicate method names in declaration of class "
    ++ show nm

-- Typecheck method bodies and make sure the instance is a well-formed
-- instance for the class (also ensuring the class exists of course).
tycheckCommand (CInstance fi constrs nm ty methods) = do
  ϕ <- asks ctx_classes
  ψ <- asks ctx_instances
  case Symtab.get nm ϕ of
    Just (TypeClass { tyclass_index = tyIndex
                    , tyclass_methods = clsMethods }) -> do
      (methods', c) <- mapSnd concat . unzip <$>
                       mapM (\(x, tm) -> do
                                (tm', c) <- tycheckTerm tm
                                return ((x, tm'), c)) methods

      -- For now we just require that every method is implemented.
      if length methods' == length clsMethods then do
        c' <-
          mapM (\(methodNm, methodTy) ->
                   case assocGet methodNm methods' of
                     Just instanceTy ->
                       -- Try to unify the type of the method with that of
                       -- the class method with its type index instantiated
                       -- to the particular type for this instance.
                       return (ty_of_term instanceTy,
                               tysubst' ty (mkTyVar tyIndex) methodTy)
                     Nothing ->
                       throwError $ "Type error: instance of class " ++
                       show nm ++ " for type " ++ show ty ++
                       " doesn't implement the method " ++ show methodNm ++
                       " at " ++ show fi)
          clsMethods
        tryUnify fi (c ++ c') $
          \tsubst ->
            return $ tysubstAll' tsubst $
            CInstance (mkData TyUnit) constrs nm ty methods'
        else
        throwError $ "Type error: instance of class " ++ show nm ++
        " for type " ++ show ty ++ " has the wrong number of methods at "
        ++ show fi
    Nothing ->
      throwError ""


tycheckCommands :: Show α => [Command α] -> TycheckM [Command TyData]
tycheckCommands [] = return []
tycheckCommands (com:coms) = do
  let fi = data_of_command com
  com' <- tycheckCommand com
  case com' of

    -- TODO: check for existing declarations of the same name (error).
    -- It should also probably be an error if a declaration is never
    -- given a definition.
    CDecl _ x ty -> do
      let tyscheme = generalize_ty' ty
      debugPrint ("CDecl' tyscheme: " ++ show tyscheme) $ do
        coms' <- local (updDecls $ add x $ tyscheme) $
                 tycheckCommands coms
        return $ com' : coms'

    -- TODO: produce a warning if shadowing an existing binding.
    CLet fi' x tm ->
      debugPrint "CLet 3" $ do
      ctx <- ask
      δ <- asks ctx_decls
      γ <- asks ctx_gamma
      let (tm', tyscheme) = generalize_term ctx tm
      case Symtab.get x δ of
        Just declTyscheme -> do
          -- Ignore the result of unifying the type schemes since we
          -- want to use the exact type declared by the programmer.
          _ <- unify_tyschemes (data_of_command com) tyscheme declTyscheme
          debugPrint "CLet 4" $
            debugPrint ("tyscheme: " ++ show tyscheme) $
            debugPrint ("declTyscheme: " ++ show declTyscheme) $ do
              coms' <- local (updGamma $ const $
                              add x declTyscheme γ) $
                       tycheckCommands coms
              return $ CLet fi' x tm' : coms'
        Nothing -> do
          coms' <- local (updGamma $ const $
                           add x tyscheme γ) $
                   tycheckCommands coms
          return $ com' : coms'

    CData _ nm tyvars ctors ->
      debugPrint ("\nCData") $ do
      let ty = mkTypeConstructor' nm tyvars (const KStar <$> tyvars) $
               TyVariant nm (mkTyVar <$> tyvars) ctors
      debugPrint (show ty) $ do
        let tyscheme = mkTypeScheme' (zip tyvars $ repeat []) $
                       mkTyApp ty $ mkTyVar <$> tyvars
        let open = open_tyscheme tyscheme
        debugPrint ("nm: " ++ show nm) $
          debugPrint ("ctors: " ++ show ctors) $
          debugPrint ("ty: " ++ show ty) $
          debugPrint ("tyscheme: " ++ show tyscheme) $
          debugPrint ("open: " ++ show open) $ do
          ctorFuns <-
            mapM (mapSndM $ \ctorTys ->
                     return $ mkTypeScheme' (zip tyvars $ repeat []) $
                     mkArrowType $ ctorTys ++ [open]) ctors
          let fvs = nub $ concat $ map (freetyvars . snd) ctors
          if not $ all (`elem` map mkTyVar tyvars) fvs then
            throwError $ "Type error : free type variable in definition of "
            ++ show nm
            else do
            debugPrint (show fvs) $
              debugPrint (show $ mkTyVar <$> tyvars) $ do
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
                             }) $
                tycheckCommands coms
              return $ com' : coms'
  
    CRecord _ nm tyvars fields ->
      debugPrint ("CRecord") $ do
      γ <- asks ctx_gamma
      mapM_ (\x -> case Symtab.get x γ of
                      Just _ -> throwError $ "field name " ++ show x
                                ++ " already exists at " ++ show fi
                      Nothing -> return ()) $ fst $ unzip fields
      let ty = mkTypeConstructor' nm tyvars (const KStar <$> tyvars) $
               TyRecord nm (mkTyVar <$> tyvars) fields
      let tyscheme = mkTypeScheme' (zip tyvars $ repeat []) $
                     mkTyApp ty $ mkTyVar <$> tyvars
      let open = open_tyscheme tyscheme
      debugPrint ("nm: " ++ show nm) $
        debugPrint ("fields: " ++ show fields) $
        debugPrint ("ty: " ++ show ty) $
        debugPrint ("tyscheme: " ++ show tyscheme) $
        debugPrint ("open: " ++ show open ++ "\n") $ do
        fieldFuns <- mapM (mapSndM $ \fieldTy ->
                              -- mkTypeScheme' tyvars <$> (normalize fi $
                              --   tysubst' ty (TyVar False nm) $
                              return $ mkTypeScheme' (zip tyvars $ repeat []) $
                              TyArrow open fieldTy)
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
                       }) $
          tycheckCommands coms
        return $ com' : coms'

    CClass _ constrs classNm tyIndex methods ->
      let cls = TypeClass { tyclass_constrs = constrs
                          , tyclass_name = classNm
                          , tyclass_index = tyIndex
                          , tyclass_methods = methods } in
      local (\ctx ->
               ctx {
                -- Add class to φ
                ctx_classes = flip (add classNm) (ctx_classes ctx) cls
                -- Add methods to φ
                , ctx_methods =
                    foldl (flip $ flip add cls) (ctx_methods ctx)
                    (fst <$> methods)
                -- Add methods to γ
                , ctx_gamma =
                    foldl (\acc (nm, ty) ->
                              Symtab.add nm
                              (generalize_ty True
                               -- Include superclass constraints as well
                               (propagateClassConstraints
                                 (zip (repeat nm) constrs) ty)) acc)
                    (ctx_gamma ctx) methods } ) $ do
      coms' <- tycheckCommands coms
      return $ com' : coms'

    -- TODO: build dictionary and add instance to the context.
    -- The dictionary itself should be parameterized by other
    -- dictionaries rather than the individual methods being
    -- parameterized.
    
    -- To achieve this, we first generalize the methods as normal, and
    -- then create one big abstraction for the entire dictionary which
    -- applies the methods to their dictionary arguments inside the
    -- body where the tuple is constructed.
    -- Don't forget to include dictionary arguments for superclasses
    -- (recursively).
    CInstance _ constrs classNm ty methods -> do
      ctx <- ask
      let generalized = mapSnd (generalize_term ctx) <$> methods
      local (updInstances $ \ψ ->
                Symtab.add classNm (buildInstance :
                                    case Symtab.get classNm ψ of
                                      Just instances -> instances
                                      Nothing -> []) ψ) $ do
        coms' <- tycheckCommands coms
        return $ com' : coms'

    _ -> do
      coms' <- tycheckCommands coms
      return $ com' : coms'


buildInstance :: ClassInstance
buildInstance = undefined

tycheckProg :: Show α => Prog α -> TycheckM (Prog TyData)
tycheckProg p = do
  coms <- tycheckCommands (prog_of p)
  return $ Prog { pdata_of = mkData TyBool, prog_of = coms }


----------
-- | Misc

ty_of_term :: Term TyData -> Type
ty_of_term = unTyData . data_of_term


-- Enforce value restriction since we have mutable references.  I.e.,
-- only generalize the type when then term is a syntactic value. See
-- TAPL or Xavier Leroy's PhD thesis.

-- TODO: resolve instances here, possibly modifying the term to take
-- extra dictionary arguments (which also changes its type..) and
-- substituting method selectors for placeholders.

-- I guess we first scan the term for all placeholders... also note
-- that any term that isn't polymorphic shouldn't require dictionary
-- arguments since all of its types are known.

-- Then we need to replace each placeholder with either 1) an instance
-- method, 2) a selector, or 3) a combination of both (e.g.,
-- application of an instance method to a selector in the case of type
-- constructors). I guess this operation that folds over the
-- placeholders and substitutes for them in the term can accumulate
-- the list of classes needed for type variables which can then be
-- added as dictionary arguments afterward. We should be able to use a
-- naming scheme like ?dict_MyClass_a for the dictionary argument
-- corresponding to the MyClass instance for type variable a.

-- TODO: compute placeholder stuff before the typescheme so we can
-- pass dictargs to generalize_ty and mkTypeScheme.
generalize_term :: Context -> Term TyData -> (Term TyData, TypeScheme)
generalize_term ctx tm =
  let placeholders = get_placeholders tm
      -- Fold over the placeholders, replacing them with the necessary
      -- instances or selectors in the term and accumulating a list of
      -- (class name, type index) pairs of the necessary dictionary
      -- arguments.
      (classes, tm') =
        foldl (\(classes, acc) p@(TmPlaceholder fi classNm methodNm ty) ->
                  ((classNm, ty) : classes,
                    termSubst (mkData TyUnit <$
                                resolve_method (ctx_instances ctx) classNm ty)
                    p acc))
        ([], tm) placeholders
      ty = ty_of_term tm
      tyscheme = if isValue tm then debugPrint ("IS VALUE: " ++ show tm) $
                                    generalize_ty' ty
                 else debugPrint ("IS NOT VALUE: " ++ show tm) $
                      mkTypeScheme' [] ty
  in
    (tm, tyscheme)


-- get_placeholders :: Term TyData -> [(Id, Id, Type)]
-- get_placeholders = (.) nub $ termRec2 $
--   \tm -> case tm of
--     TmPlaceholder _ classNm methodNm ty -> [(classNm, methodNm, ty)]
--     _ -> []

get_placeholders :: Term TyData -> [Term TyData]
get_placeholders = (.) nub $ termRec2 $
  \tm -> case tm of
    TmPlaceholder _ _ _ _ -> [tm]
    _ -> []


-- TODO: maybe we should write the CInstance code that generates
-- dictionaries first. We can make the entire dictionary parameterized
-- by the dictionaries corresponding to the instance's class
-- constraints (including superclass constraints I think). Then this
-- becomes a relatively straightfoward recursive dictionary building
-- algorithm for resolving instances.

-- instance context, class name, type index
resolve_method :: Symtab [ClassInstance] -> Id -> Type -> Term ()
resolve_method = undefined

-- instance context, class name, method name (if nothing then we just
-- want the whole instance dictionary, otherwise generate a selector
-- to grab the method), type index
-- resolve_method :: Symtab [ClassInstance] -> Id -> Maybe Id -> Type ->
--                   Term ()
-- resolve_method ctx classNm methodNm ty =
--   case Symtab.get classNm ctx of
--     Just instances ->
--       fromJust $
--       foldl (\acc inst ->
--                case acc of
--                  Just _ -> acc
--                  Nothing ->
--                    let dict = Just $
--                          go inst methodNm ty (instance_ty inst) in
--                      dict
--             ) Nothing instances
--     Nothing -> error ""
--   where
--     go :: ClassInstance -> Maybe Id -> Type -> Type -> Term ()
    
--     go inst methodNm TyUnit TyUnit =
--       gen_selector methodNm $ instance_dict inst
--     go inst methodNm TyBool TyBool =
--       gen_selector methodNm $ instance_dict inst
--     go inst methodNm TyInt  TyInt  =
--       gen_selector methodNm $ instance_dict inst
--     go inst methodNm TyChar TyChar =
--       gen_selector methodNm $ instance_dict inst

--     go inst methodNm (TyRef s) (TyRef t) =
--       let arg = resolve_method ctx Nothing s t in
--         undefined
    
--     go _ _ _ _ = undefined


gen_selector :: Maybe Id -> Term () -> Term ()
gen_selector = undefined

-- The first type scheme argument should be that obtained from
-- typechecking the body of a let command, and the second should be
-- the declared type. We expect the first to be more general than the
-- second.
unify_tyschemes :: Show α => α -> TypeScheme -> TypeScheme -> TycheckM Type
unify_tyschemes fi tyscheme1 tyscheme2 = do
  η <- asks ctx_datatypes
  ψ <- asks ctx_instances
  ty1 <- instantiate_tyscheme fi False tyscheme1
  -- Hold type variables of this one rigid.
  ty2 <- instantiate_tyscheme fi True tyscheme2
  debugPrint "\nunify_tyschemes" $
    debugPrint ("tyscheme1: " ++ show tyscheme1) $
    debugPrint ("tyscheme2: " ++ show tyscheme2) $
    debugPrint ("ty1: " ++ show ty1) $
    debugPrint ("ty2: " ++ show ty2) $
    case unify fi η ψ [(ty1, ty2)] of
      Left (s, t, msg) -> unifyError s t fi msg
      Right tsubst ->
        debugPrint ("tsubst: " ++ show tsubst ++ "\n") $
        return $ tysubstAll' tsubst ty1
  

set_rigid :: Bool -> Type -> Type
set_rigid b = typeRec $
  \ty -> case ty of
    TyVar _ ctx x -> TyVar b ctx x
    _ -> ty

-- Make all type variables in a type non-rigid.
-- TODO: this may not be necessary now that we just choose rigidness
-- at typescheme instantiation time.
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
  -- return (TyVariant (Id "Pair") [ty1, ty2] [],
  --         binds1 ++ binds2, cs1 ++ cs2)
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
  debugPrint "PConstructor" $
    case variantTypeConstr of
      Just vTyConstr -> do
        -- vTy@(TyVariant _ _ ctors) <-
        --   pure (unfold fi) <*> asks ctx_datatypes <*>
        --   instantiate_tyscheme fi vTyConstr
        -- debugPrint "" $

        temp <- pure (unfold fi) <*> asks ctx_datatypes <*>
                instantiate_tyscheme' fi vTyConstr
        debugPrint "\n" $
          debugPrint ("temp: " ++ show temp) $ do
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
    recTy@(TyRecord _ _ fields) <- instantiate_tyscheme' fi $ tys'!!0
    cs' <- mapM (\(nm, ty) ->
                     case assocGet nm fields of
                       Just ty' -> return (ty, ty')
                       Nothing -> throwError $ "invalid record field " ++
                                  show nm ++ " at " ++ show fi) $
           zip nms tys
    return (recTy, binds, cs ++ cs')


-- -- Abstract a type over a list of Ids. We assume their kinds to be *
-- -- for now.
-- abstractType :: [Id] -> Type -> Type
-- abstractType [] = id
-- abstractType (x:xs) = TyAbs x KStar . abstractType xs


-- Pass through the input type, raising an error if it isn't
-- well-kinded.
wellKinded :: Show α => α -> Type -> TycheckM Type
wellKinded fi ty = do
  η <- asks ctx_datatypes
  case kindCheck $ unfold fi η ty of
    Just _ -> return ty
    _ -> throwError $ "Type error: " ++ show ty ++
         " is not well-kinded"

-- -- Replace all TyNames with TyVars of the same Id.
-- nameToVar :: Id -> Type -> Type
-- nameToVar nm = typeRec $
--   \ty -> case ty of
--     TyName nm' -> if nm == nm' then mkTyVar nm else TyName nm'
--     _ -> ty
