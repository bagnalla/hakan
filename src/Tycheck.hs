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
import Data.List (nub, unzip4, intercalate)
import Data.Maybe (fromJust)
import Data.Tree
import Data.Tuple (swap)

import Ast
import Core (kindCheck, idOfType, isTyVar)
import Gensym (nextSym, nextSymN)
import Symtab (Id(..), add, get, assocGet, assocIndex, Symtab)
import Context
import Unify (ConstrSet, unify, printConstrSet, printUnifyLog)
import Util

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

unifyError :: Show α => Type -> Type -> α -> String -> TycheckM b
unifyError s t fi msg =
  -- throwError $ "Type error: unable to unify\n" ++ show s ++ "\nand\n" ++
  -- show t ++ " at " ++ show fi ++ ".\nReason: " ++ msg
  throwError $ "Type error: unable to unify\n" ++ showTypeLight s ++
  "\nand\n" ++ showTypeLight t ++ " at " ++ show fi ++ ".\nReason: " ++ msg

tryUnify :: Show α => α -> ConstrSet -> (TypeSubst -> TycheckM a) ->
            TycheckM a
tryUnify fi c f = do
  -- debugPrint ("\ntrying to unify constraint set:\n" ++ printConstrSet c) $ do
  η <- asks ctx_datatypes
  ψ <- asks ctx_instances
  let c' = bimap normalize_ty normalize_ty <$> c
  -- debugPrint ("\nc: " ++ intercalate "\n" (show <$> c)) $
  --   debugPrint ("\nc': " ++ intercalate "\n" (show <$> c')) $ do
  let (result, log) = runWriter $ unify fi η ψ c
  case result of
    Left (s, t, msg) ->
      debugPrint (printUnifyLog log) $
      unifyError s t fi msg
    Right tsubst ->
      -- debugPrint (printUnifyLog log) $
      f tsubst


tycheckTerm :: Show α => Term α -> TycheckM (Term TyData, ConstrSet)

-- When the name refers to a class method, we replace the variable
-- with a placeholder to be filled in later with a selector for the
-- resolved instance.
tycheckTerm (TmVar fi x) =
  debugPrint "\nTmVar" $
  debugPrint ("TmVar x: " ++ show x) $ do
  tyscheme <- asks $ Symtab.get x . ctx_gamma
  debugPrint ("TmVar tyscheme: " ++ show tyscheme) $ do
    cls <- asks $ Symtab.get x . ctx_methods
    -- methods <- asks ctx_methods
    case tyscheme of
      Just tyscheme' -> do
        ty <- set_rigid False <$> instantiate_tyscheme' fi tyscheme'
      -- debugPrint ("TmVar tyscheme: " ++ show tyscheme') $
        debugPrint ("TmVar ty: " ++ showTypeLight ty) $
      --   debugprint ("TmVar ty normalized: " ++ show (normalize_ty ty)) $
          if isMethod tyscheme' then
            case cls of
              Just (TypeClass { tyclass_name = classNm
                              , tyclass_index = classTyIndex }) -> do
                let open = open_tyscheme tyscheme'
                -- debugPrint ("classNm: " ++ show classNm) $
                -- debugPrint ("classTyIndex: " ++ show classTyIndex) $
                -- debugPrint ("open: " ++ show open) $ do
            -- debugPrint ("\nattempting to match " ++
            --             showTypeLight (normalize_ty ty) ++ " with " ++
            --             show classTyIndex ++ " in " ++ showTypeLight open) $ do
                let tyIndex = fromJust $
                              match_type classTyIndex (normalize_ty ty) open
              -- debugPrint ("tyIndex: " ++ show tyIndex) $
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
  -- debugPrint "\nTmAbs" $ do
  ty' <- wellKinded fi ty
  (tm', c) <- local (updGamma $ add x $ mkTypeScheme [] False ty') $
              tycheckTerm tm
  let ty'' = ty_of_term tm'
  -- debugPrint ("abs nm: " ++ show x) $
  --   debugPrint ("abs tm: " ++ show tm') $
  --   debugPrint ("abs tm ty: " ++ show (ty_of_term tm')) $
  --   debugPrint ("abs ty: " ++ show ty) $
  --   debugPrint ("abs ty': " ++ show ty') $
  --   debugPrint ("abs tyscheme: " ++ show ty') $
  --   debugPrint ("abs ty'': " ++ show ty'') $ do
  y <- nextSym "?Y_"
  let tyy = mkTyVar (Id y)
  let c' = c ++ [(tyy, TyArrow ty' ty'')]
  -- debugPrint ("abs c: " ++ show c') $
  -- debugPrint ("abs c: " ++ show (bimap normalize_ty normalize_ty <$> c')) $
  tryUnify fi c' $
    \tsubst ->
      -- debugPrint ("abs tsubst: " ++ show (bimap normalize_ty normalize_ty <$> tsubst)) $
      return (tysubstAll' tsubst $ TmAbs (mkData tyy) x ty' tm', c')

tycheckTerm (TmApp fi t1 t2) = do
  -- debugPrint "TmApp" $ do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  -- debugPrint ("app tm1: " ++ show t1') $
  --   debugPrint ("app tm2: " ++ show t2') $
  --   debugPrint ("app ty1: " ++ show (normalize_ty ty1)) $
  --   debugPrint ("app ty2: " ++ show (normalize_ty ty2)) $ do
  x <- nextSym "?Y_"
  let tyx = mkTyVar (Id x)
  let c = c1 ++ c2 ++ [(ty1, TyArrow ty2 tyx)]
  -- debugPrint ("app c: " ++ show c) $
  --   debugPrint ("app c normalized: " ++ show (bimap normalize_ty normalize_ty <$> c)) $
  tryUnify fi c $
    \tsubst ->
      -- debugPrint ("app tsubst: " ++ show tsubst ++ "\n") $
      return (tysubstAll' tsubst $ TmApp (mkData tyx) t1' t2', c)

tycheckTerm (TmBool _ b) =
  -- debugPrint "TmBool\n" $
  return (TmBool (mkData TyBool) b, [])

tycheckTerm (TmIf fi t1 t2 t3) = do
  -- debugPrint "TmIf\n" $ do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  (t3', c3) <- tycheckTerm t3
  let (ty1, ty2, ty3) = (ty_of_term t1', ty_of_term t2', ty_of_term t3')
  let c = c1 ++ c2 ++ c3 ++ [(ty1, TyBool), (ty2, ty3)]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll' tsubst $ TmIf (mkData ty2) t1' t2' t3', c)

tycheckTerm (TmUnit _) =
  -- debugPrint "TmUnit\n" $
  return (TmUnit (mkData TyUnit), [])

tycheckTerm (TmInt _ i) =
    -- debugPrint "TmInt\n" $
  return (TmInt (mkData TyInt) i, [])

tycheckTerm (TmChar _ c) =
    -- debugPrint "TmChar\n" $
  return (TmChar (mkData TyChar) c, [])

tycheckTerm (TmUnop fi u tm) = do
  -- debugPrint "TmUnop\n" $ do
  (tm', c) <- tycheckTerm tm
  let ty = ty_of_term tm'
  case u of

    UFix -> do
      -- debugPrint "UFix" $ do
      y <- nextSym "?Y_"
      let tyy = mkTyVar (Id y)
      let c' = c ++ [(ty, TyArrow tyy tyy)]
      -- debugPrint "UFix 2" $
      tryUnify fi c' $
        \tsubst ->
          -- debugPrint "UFix tsubst" $
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
tycheckTerm (TmBinop fi b t1 t2) = do
  -- debugPrint "TmBinop\n" $ do
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
  -- debugPrint "TmLet" $ do
  (tm1', c1) <- tycheckTerm tm1
  tryUnify fi c1 $
    \tsubst -> do
      -- ctx <- ask
      (gen, tyscheme) <- process_term fi tsubst tm1'
      -- debugPrint ("tyscheme: " ++ show tyscheme ++ "\n") $ do
      (tm2', c2) <- local (updGamma $ add x tyscheme)  $
                    tycheckTerm tm2
      let c = c1 ++ c2
      tryUnify fi c $
        \tsubst' ->
          return (tysubstAll' tsubst' $
                  TmLet (mkData $ ty_of_term tm2') x gen tm2', c)

-- Not sure that we need this since TmVariants don't appear in the
-- syntax of the program (the programmer creates them via application
-- of constructor functions), only as intermediate terms generated by
-- the interpreter.
tycheckTerm (TmVariant _ _ _) =
  throwError "unexpected TmVariant in typechecker"

tycheckTerm (TmMatch fi discrim cases) = do
  -- debugPrint "TmMatch 1\n" $ do
  (discrim', c1) <- tycheckTerm discrim
  -- debugPrint "TmMatch 2\n" $ do
  (tys, binds, c2, tms') <-
    quadmap id concat concat id . unzip4 <$>
    mapM (\(p, tm) -> do
             (ty, binds, cs) <- patternType fi p
             (tm', cs') <-
               local (updGamma $
                       flip (foldl (\acc (x, t) ->
                                       add x (mkTypeScheme [] False t) acc)) binds)
               $ tycheckTerm tm
             return (ty, binds, cs ++ cs', tm')) cases
    -- debugPrint "TmMatch 3\n" $
    --   debugPrint ("tys: " ++ show tys) $ do
      -- Need a type variable for the overall type, and if there are any
      -- cases then we constrain it to be equal to their type. Also need
      -- to constrain all of the case types to be the same.
  y <- mkTyVar . Id <$> nextSym "?Y_"
  let c = c1 ++ c2 ++ map (\ty ->
                              -- debugPrint ("asdf: " ++ show ty) $
                              (ty, ty_of_term discrim')) tys ++
          if length cases > 0 then
            (y, ty_of_term $ tms'!!0) :
            map (\tm -> (ty_of_term tm, ty_of_term (tms'!!0))) tms'
          else []
          -- debugPrint "TmMatch 4\n" $
  tryUnify fi c $
    \tsubst ->
      -- debugPrint "TmMatch 5\n" $
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
  -- debugPrint ("\nx: " ++ show x) $
  --   debugPrint ("\ny: " ++ show y ++ "\n") $ do
  recordTy@(TyConstructor (TypeConstructor
                            { tycon_instantiated =
                                TyRecord recordNm _ recordFields })) <-
    unfold fi η <$>
    (instantiate_tyscheme' fi =<< case Symtab.get (nms!!0) ε of
        Just ty ->
          -- debugPrint (show ty) $
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
  -- debugPrint ("\nCDecl ty: " ++ show ty) $
  η <- asks ctx_datatypes
  CDecl (mkData TyUnit) x <$>
    (wellKinded fi $ rigidify_type $ normalize_ty $ resolveTyNames fi η ty)
    -- (wellKinded fi $ rigidify_type $ resolveTyNames fi η ty)

tycheckCommand (CLet fi x tm) = do
  -- debugPrint "\nCLet 1" $ do
  (tm', c) <- tycheckTerm tm
  -- debugPrint "\nCLet 2" $
  tryUnify fi c $
    \tsubst ->
      -- debugPrint ("CLet x: " ++ show x) $
      -- debugPrint ("CLet tm: " ++ show tm) $
      -- debugPrint ("CLet tm': " ++ show tm') $
      -- debugPrint ("CLet ty: " ++ show (ty_of_term tm')) $
      -- debugPrint ("CLet c: " ++ show c) $
      -- debugPrint ("CLet c normalized: " ++ show (bimap normalize_ty normalize_ty <$> c)) $
      -- debugPrint ("CLet tsubst: " ++ show tsubst) $
      -- debugPrint ("CLet ty': " ++ show (tysubstAll' tsubst (ty_of_term tm'))) $
      return $ CLet (mkData (tysubstAll' tsubst $ ty_of_term tm')) x $
      tysubstAll' tsubst <$> tysubstAll' tsubst tm'
      
      -- this tysubst on tm' isn't doing quite what we want since it
      -- doesn't affect the type metadata... so we also fmap the
      -- tysubst over it. TODO: make it nicer somehow.
      -- Or at least factor it out into an operation.

tycheckCommand (CEval fi tm) = do
  -- ctx <- ask
  (tm', c) <- tycheckTerm tm
  tryUnify fi c $
    \tsubst -> do
      -- debugPrint "\nCEval" $
      -- debugPrint ("tm: " ++ show tm) $
      -- debugPrint ("tm': " ++ show tm') $
      -- debugPrint ("c: " ++ show c) $
      -- debugPrint ("tsubst: " ++ show tsubst) $
      -- debugPrint ("tm' substed: " ++ show (tysubstAll' tsubst <$>
      --                                       tysubstAll' tsubst tm')) $ do
      -- debugPrint ("CEval tm'': " ++ show (fst $ generalize_term ctx $
      --                                     tysubstAll' tsubst <$>
      --                                     tysubstAll' tsubst tm')) $ do
      (gen, _) <- process_term fi tsubst tm'
      -- debugPrint ("constrs: " ++ show constrs) $
      -- debugPrint ("gen: " ++ show gen) $
      return $ CEval (mkData $ ty_of_term gen) gen
  
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
    return $ CClass (mkData TyUnit) constrs nm tyvar methods
    -- mapSnd rigidify_type <$> methods
  else
    throwError $ "Type error: duplicate method names in declaration of class "
    ++ show nm

-- Typecheck method bodies and make sure the instance is a well-formed
-- instance for the class (also ensuring the class exists of course).
tycheckCommand (CInstance fi constrs classNm ty methods) = do
  ϕ <- asks ctx_classes
  ψ <- asks ctx_instances
  case Symtab.get (unClassNm classNm) ϕ of
    Just (TypeClass { tyclass_index = tyIndex
                    , tyclass_methods = clsMethods }) -> do
      (methods', c) <- mapSnd concat . unzip <$>
                       mapM (\(x, tm) -> do
                                -- debugPrint ("\ntypechecking method " ++ show x) $
                                -- debugPrint ("method body: " ++ show tm) $ do
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
                       -- debugPrint ("constrs: " ++ show (swap <$> constrs)) $
                       -- debugPrint ("methodTy after substitution: " ++
                       --          show (propagateClassConstraints (swap <$> constrs)
                       --                (rigidify_type
                       --                 (tysubst' ty (mkTyVar tyIndex) methodTy)))) $
                       return (ty_of_term instanceTy,
                                propagateClassConstraints constrs
                                (rigidify_type (tysubst' ty (mkTyVar tyIndex) methodTy)))
                     Nothing ->
                       throwError $ "Type error: instance of class " ++
                       show classNm ++ " for type " ++ show ty ++
                       " doesn't implement the method " ++ show methodNm ++
                       " at " ++ show fi)
          clsMethods
        -- debugPrint ("\n\nZZZZZZZZZZ\nc': " ++ show c') $
        tryUnify fi (c ++ c') $
          \tsubst ->
            -- debugPrint ("tsubst: " ++ show tsubst) $
            return $ tysubstAll' tsubst $
            CInstance (mkData TyUnit) constrs classNm ty methods'
        else
        throwError $ "Type error: instance of class " ++ show classNm ++
        " for type " ++ show ty ++ " has the wrong number of methods at "
        ++ show fi
    Nothing ->
      throwError "bowlop"


tycheckCommands :: Show α => [Command α] -> TycheckM [Command TyData]
tycheckCommands [] = return []
tycheckCommands (com:coms) = do
  ϕ <- asks ctx_classes
  let fi = data_of_command com
  com' <- tycheckCommand com
  case com' of

    -- TODO: check for existing declarations of the same name (error).
    -- It should also probably be an error if a declaration is never
    -- given a definition.
    CDecl _ x ty -> do
      let tyscheme = mkTypeScheme (all_class_constraints ϕ ty) False ty
      -- debugPrint ("\nCDecl' x: " ++ show x) $
      --   debugPrint ("CDecl' tyscheme: " ++ show tyscheme) $ do
      coms' <- local (updDecls $ add x $ tyscheme) $
               tycheckCommands coms
      return $ com' : coms'

    -- TODO: produce a warning if shadowing an existing binding.
    CLet fi' x tm -> do
      -- debugPrint "\nCLet 3" $
      -- debugPrint ("tm: " ++ show tm) $
      -- debugPrint ("ty: " ++ show (ty_of_term tm)) $ do
      -- ctx <- ask
      δ <- asks ctx_decls
      γ <- asks ctx_gamma
      (gen, tyscheme) <- process_term fi [] tm
      case Symtab.get x δ of
        Just declTyscheme -> do
          -- Ignore the result of unifying the type schemes since we
          -- want to use the exact type declared by the programmer.
          _ <- unify_tyschemes (data_of_command com) tyscheme declTyscheme
          -- debugPrint "\nCLet 4" $
          --   debugPrint ("gen: " ++ show gen) $
          --   debugPrint ("tyscheme: " ++ show tyscheme) $
          --   debugPrint ("declTyscheme: " ++ show declTyscheme) $ do
          coms' <- local (updGamma $ const $
                           add x declTyscheme γ) $
                   tycheckCommands coms
          return $ CLet fi' x gen : coms'
        Nothing -> do
          coms' <- local (updGamma $ const $
                           add x tyscheme γ) $
                   tycheckCommands coms
          return $ com' : coms'

    CData _ nm tyvars ctors -> do
      -- debugPrint ("\nCData") $ do
      let ty = mkTypeConstructor' nm tyvars (const KStar <$> tyvars) $
               TyVariant nm (mkTyVar <$> tyvars) ctors
      -- debugPrint (show ty) $ do
      let tyscheme = mkTypeScheme (zip tyvars $ repeat []) False
                     (mkTyApp ty $ mkTyVar <$> tyvars)
      let open = open_tyscheme tyscheme
        -- debugPrint ("nm: " ++ show nm) $
        --   debugPrint ("ctors: " ++ show ctors) $
        --   debugPrint ("ty: " ++ show ty) $
        --   debugPrint ("tyscheme: " ++ show tyscheme) $
        --   debugPrint ("open: " ++ show open) $ do
      ctorFuns <-
        mapM (mapSndM $ \ctorTys ->
                          return $ mkTypeScheme (zip tyvars $ repeat []) False
                          (mkArrowType $ ctorTys ++ [open])) ctors
      let fvs = nub $ concat $ map (freetyvars . snd) ctors
      if not $ all (`elem` map mkTyVar tyvars) fvs then
        throwError $ "Type error : free type variable in definition of "
        ++ show nm
        else do
        -- debugPrint (show fvs) $
        --   debugPrint (show $ mkTyVar <$> tyvars) $ do
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
  
    CRecord _ nm tyvars fields -> do
      -- debugPrint ("CRecord") $ do
      γ <- asks ctx_gamma
      mapM_ (\x -> case Symtab.get x γ of
                      Just _ -> throwError $ "field name " ++ show x
                                ++ " already exists at " ++ show fi
                      Nothing -> return ()) $ fst $ unzip fields
      let ty = mkTypeConstructor' nm tyvars (const KStar <$> tyvars) $
               TyRecord nm (mkTyVar <$> tyvars) fields
      let tyscheme = mkTypeScheme (zip tyvars $ repeat []) False
                     (mkTyApp ty $ mkTyVar <$> tyvars)
      let open = open_tyscheme tyscheme
      -- debugPrint ("nm: " ++ show nm) $
      --   debugPrint ("fields: " ++ show fields) $
      --   debugPrint ("ty: " ++ show ty) $
      --   debugPrint ("tyscheme: " ++ show tyscheme) $
      --   debugPrint ("open: " ++ show open ++ "\n") $ do
      fieldFuns <- mapM (mapSndM $ \fieldTy ->
                            -- mkTypeScheme' tyvars <$> (normalize fi $
                            --   tysubst' ty (TyVar False nm) $
                            return $ mkTypeScheme (zip tyvars $ repeat [])
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
                ctx_classes =
                    flip (add $ unClassNm classNm) (ctx_classes ctx) cls
                -- Add methods to φ
                , ctx_methods =
                    foldl (flip $ flip add cls) (ctx_methods ctx)
                    (fst <$> methods)
                -- Add methods to γ
                , ctx_gamma =
                    foldl (\acc (nm, ty) ->
                             -- debugPrint ("\n\nASDF") $
                             -- debugPrint ("classNm: " ++ show classNm) $
                             -- debugPrint ("nm: " ++ show nm) $
                             -- debugPrint ("constrs: " ++ show constrs) $
                             -- debugPrint ("ty: " ++ show ty) $
                             -- debugPrint (show $
                             --             (zip (repeat tyIndex)
                             --              (classNm : constrs))) $
                             -- debugPrint
                             -- ("ty': " ++
                             --   show (propagateClassConstraints
                             --          (zip (classNm : constrs)
                             --           (repeat tyIndex)) ty)) $
                             Symtab.add nm
                             -- (generalize_ty (ctx_classes ctx) True
                             -- (mkTypeScheme [] True -- TODO: all_class_constraints?
                             (generalize_ty True
                               -- Include superclass constraints as well
                               (propagateClassConstraints
                                 -- (zip (classNm : constrs)
                                 --  (repeat tyIndex)) ty)) acc)
                                 (zip (repeat tyIndex) (classNm : constrs)) ty)) acc)
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
    CInstance fi constrs classNm ty methods -> do
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
              show classNm ++ ". " ++ show fi

      -- Get any constraints on variables necessary to resolve
      -- superclass instances.
      -- let super_var_constrs =
      --       concat $ flip (variable_constraints fi ctx) ty <$> supers
      super_var_constrs <-
        concat <$> (sequence $ flip (variable_constraints fi ctx) ty <$> supers)
      -- Add them to our own instance constraints.
      let all_constrs = super_var_constrs ++ constrs

      -- Resolve instances as much as possible within the method
      -- bodies, generating dictionary variables for unknown type
      -- variable instances. Any such dictionary variable should
      -- correspond to one of our instance constraints -- otherwise it
      -- isn't satisfiable.
      -- let specialized =
      --       mapSnd (specialize_term ctx . snd . fill_placeholders ctx)
      --       <$> methods
      let specialized = mapSnd (snd . fill_placeholders ctx) <$> methods

      -- debugPrint ("\nCInstance") $
      --   debugPrint ("classNm: " ++ show classNm) $
      --   debugPrint ("ty: " ++ showTypeLight ty) $
      --   debugPrint ("supers: " ++ show supers) $
      --   debugPrint ("constrs: " ++ show constrs) $
      --   debugPrint ("super_var_constrs: " ++ show super_var_constrs) $
        -- debugPrint ("\nmethods: " ++ show methods) $
        -- debugPrint ("\nspecialized: " ++ show specialized) $ do
      inst <- buildInstance fi all_constrs classNm ty specialized
      -- debugPrint ("\n@@@\nINST\n@@@\n" ++ show inst) $
      local (updInstances $ \ψ ->
                Symtab.add (unClassNm classNm)
                (inst :
                  case Symtab.get (unClassNm classNm) ψ of
                    Just instances -> instances
                    Nothing -> []) ψ) $ do
        coms' <- tycheckCommands coms
        return $ com' : coms'
    _ -> do
      coms' <- tycheckCommands coms
      return $ com' : coms'

buildInstance :: Show α => α -> [(Id, ClassNm)] -> ClassNm -> Type ->
                 [(Id, Term α)] -> TycheckM ClassInstance
buildInstance fi constrs classNm ty methods = do
  -- debugPrint ("\nbuildInstance") $
  -- debugPrint ("constrs: " ++ show constrs) $
  -- debugPrint ("classNm: " ++ show classNm) $
  -- debugPrint ("ty: " ++ showTypeLight ty) $ do
  --   debugPrint ("methods: " ++ show methods) $ do
  -- vars <- fmap Id <$> (nextSymN "?Y_" $ length constrs)
  ctx <- ask
  -- let supers = superclasses (ctx_classes ctx) classNm
  -- let super_constrs = concat $ variable_constraints ctx ty <$> supers
  -- let vars = uncurry mkDictId . swap <$> super_constrs ++ constrs
  let vars = uncurry mkDictId . swap <$> constrs
  let dict = mkAbs vars $ mkTuple $
             -- flip mkApp (TmVar () <$> vars) <$>
             (eraseData . snd <$> methods)
  -- let dict = mkAbs vars $ mkTuple $ eraseData . snd <$> methods
      -- debugPrint ("\nvars: " ++ show vars) $
    -- debugPrint ("super_constrs: " ++ show super_constrs) $
  -- debugPrint ("dict: " ++ show dict) $
  return $ ClassInstance { instance_ctx = constrs
                         , instance_classname = classNm
                         -- TODO: turn into type constructor if
                         -- abstraction or application? The type here
                         -- should always be a named type, either
                         -- primitive or a type constructor (possibly
                         -- applied). That's what's a bit weird, that
                         -- the type here could be a TyApp that needs
                         -- to be turned into a partially or fully
                         -- applied type constructor.
                         
                         -- I don't know.. maybe we can just leave it
                         -- the way it is and deal with
                         -- matching/unifying type constructors with
                         -- naked abstractions/applications. I suppose
                         -- it isn't that hard.. just pull out the
                         -- tycon_instantiated field from the type
                         -- constructor to compare against (and treat
                         -- TyNames equal to TyVariants and stuff with
                         -- the same name).
                         -- , instance_ty = ty -- ^
                         -- , instance_ty = normalize_ty ty
                         , instance_ty =
                             normalize_ty (resolveTyNames fi (ctx_datatypes ctx) ty)
                         , instance_dict = dict }


tycheckProg :: Show α => Prog α -> TycheckM (Prog TyData)
tycheckProg p = do
  coms <- tycheckCommands (prog_of p)
  return $ Prog { pdata_of = mkData TyBool, prog_of = coms }


----------
-- | Misc

ty_of_term :: Term TyData -> Type
ty_of_term = unTyData . data_of_term


-- get_class_constraints_tm :: Term TyData -> [(Id, Id)]
-- get_class_constraints_tm = map swap . nub . (termRec2 $
--   \tm -> case tm of
--     TmVar (TyData ty) _ -> get_class_constraints_ty ty
--     TmPlaceholder _ _ _ _ ->
--       error "get_class_constraints_tm: unexpected placeholder"
--     _ -> [])

-- get_class_constraints_ty :: Type -> [(Id, Id)]
-- get_class_constraints_ty = flattenSnd . classConstraints . freetyvars


get_placeholders :: Term TyData -> [Term TyData]
get_placeholders = (.) nub $ termRec2 $
  \tm -> case tm of
    TmPlaceholder _ _ _ _ -> [tm]
    _ -> []


-- -- Produces a forest because the type may be a type variable with
-- -- multiple constraints (which should always include the one passed
-- -- here as classNm..) in which case we generate instances for each of
-- -- the constraints.
-- instance_forest :: Context -> Type -> Id -> Forest (Term ())
-- instance_forest ctx ty classNm =
--   debugPrint "\ninstance_forest" $
--   debugPrint ("ty: " ++ show ty) $
--   case ty of
--     -- When it's a variable..
--     TyVar _ constrs x -> map (variable_instance_tree ctx x) constrs
--     -- When it's not a variable...
--     _ ->
--       let Just (ClassInstance { instance_ctx = constrs
--                               , instance_ty = inst_ty
--                               , instance_dict = dict }) =
--             get_instance ctx ty classNm in
--         debugPrint ("constrs: " ++ show constrs) $
--         debugPrint ("inst_ty: " ++ show inst_ty) $
--         (:[]) . Node dict . concat $
--         map (\(classNm', var) ->
--                debugPrint (show (classNm', var)) $
--                 case match_type var ty inst_ty of
--                   Just ty' -> instance_forest ctx ty' classNm'
--                   Nothing ->
--                     error "instance_forest: incompatible types.. \
--                           \this shouldn't be possible!")
--         constrs

-- Ignore constraints on type variables. Just produce the instance for
-- the given class.
instance_tree :: Context -> Type -> ClassNm -> Tree (Term ())
instance_tree ctx ty classNm =
  -- debugPrint "\ninstance_tree" $
  case ty of
    -- When it's a variable..
    -- TyVar _ _ x -> variable_instance_tree ctx x classNm

    -- We no longer recursively generate applications to
    -- superclasses. Instead we assume that the missing dictionary
    -- will be provided from the context pre-assembled.
    TyVar _ _ x ->
      -- debugPrint ("var name: " ++ show x) $
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
        -- debugPrint ("instance constrs: " ++ show constrs) $
        -- debugPrint ("ty: " ++ showTypeLight ty) $
        -- debugPrint ("inst_ty: " ++ showTypeLight inst_ty) $
        -- debugPrint ("classNm: " ++ show classNm) $
        Node dict $
        map (\(var, classNm') ->
               -- debugPrint (show (var, classNm')) $
                -- debugPrint ("\nattempting to match " ++
                --             showTypeLight ty ++ " with " ++
                --             show var ++ " in " ++ showTypeLight inst_ty) $ do
               case match_type var ty inst_ty of
                 Just ty' ->
                   -- debugPrint ("matched " ++ show var ++ " with " ++
                   --              showTypeLight ty') $
                   instance_tree ctx ty' classNm'
                 Nothing ->
                   error "instance_tree: incompatible types.. \
                         \this shouldn't be possible!")
        constrs

-- -- variable name, class_name
-- variable_instance_tree :: Context -> Id -> Id -> Tree (Term ())
-- variable_instance_tree ctx var classNm = do
--   case Symtab.get classNm (ctx_classes ctx) of
--     Just (TypeClass { tyclass_constrs = supers }) ->
--       Node (TmVar () $ mkDictId classNm var) $
--       map (variable_instance_tree ctx var) supers
--     Nothing -> error $ "class " ++ show classNm ++ " not found. ctx:\n"
--                ++ show ctx

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
    TyVar _ _ x -> TmVar () $ mkDictId classNm x
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
unify_tyschemes :: Show α => α -> TypeScheme -> TypeScheme -> TycheckM Type
unify_tyschemes fi tyscheme1 tyscheme2 = do
  η <- asks ctx_datatypes
  ψ <- asks ctx_instances
  ty1 <- instantiate_tyscheme fi False tyscheme1
  -- Hold type variables of this one rigid.
  ty2 <- instantiate_tyscheme fi True tyscheme2
  -- debugPrint "\nunify_tyschemes" $
  -- debugPrint ("\ntyscheme1: " ++ show tyscheme1) $
  --   debugPrint ("\ntyscheme2: " ++ show tyscheme2) $
  --   debugPrint ("\nty1: " ++ showTypeLight ty1) $
  --   debugPrint ("\nty2: " ++ showTypeLight ty2) $
  --   debugPrint ("\nty2': " ++ show ty2) $ do
  let (result, log) = runWriter $ unify fi η ψ [(ty1, ty2)]
  case result of
    Left (s, t, msg) ->
      debugPrint (printUnifyLog log) $
      unifyError s t fi msg
    Right tsubst ->
      -- debugPrint ("tsubst: " ++ show tsubst ++ "\n") $
      return $ tysubstAll' tsubst ty1
  
  -- case runWriterT $ unify fi η ψ [(ty1, ty2)] of
  --   Left (s, t, msg) -> unifyError s t fi msg
  --   Right (tsubst, log) ->
  --     -- debugPrint ("tsubst: " ++ show tsubst ++ "\n") $
  --     return $ tysubstAll' tsubst ty1
  

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
  -- debugPrint "PConstructor" $
  case variantTypeConstr of
    Just vTyConstr -> do
      -- vTy@(TyVariant _ _ ctors) <-
      --   pure (unfold fi) <*> asks ctx_datatypes <*>
      --   instantiate_tyscheme fi vTyConstr
      -- debugPrint "" $

      temp <- pure (unfold fi) <*> asks ctx_datatypes <*>
              instantiate_tyscheme' fi vTyConstr
        -- debugPrint "\n" $
        --   debugPrint ("temp: " ++ show temp) $ do
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

mkDictId :: ClassNm -> Id -> Id
mkDictId classNm var = Id $ "?" ++ show classNm ++ "_" ++ show var


-- Given a type (possibly containing type variables) and a class name,
-- determine the constraints on type variables needed to resolve an
-- instance of the class for the type.
variable_constraints :: Show α => α -> Context -> ClassNm -> Type -> TycheckM [(Id, ClassNm)]
variable_constraints fi ctx classNm ty = do
  -- debugPrint "\nvariable_constraints" $
  case ty of
    TyVar _ _ x ->
      return [(x, classNm)]
      -- case Symtab.get classNm (ctx_classes ctx) of
      --   Just (TypeClass { tyclass_constrs = constrs }) ->
      --     let all_constrs = classNm :
      --           (concat $ superclasses (ctx_classes ctx) <$> constrs) ++
      --           constrs in
      --       zip all_constrs $ repeat x
      --   Nothing -> error $ "class " ++ show classNm ++
      --              " not found. ctx:\n" ++ show ctx
    _ ->
      -- debugPrint ("ty: " ++ showTypeLight ty) $
      -- debugPrint ("ty: " ++ show ty) $
      -- debugPrint ("classNm: " ++ show classNm) $
      
      -- TODO: This may fail if there is no instance, which should be
      -- a type error. Is there somewhere we can check that before
      -- reaching this point? This may be the most straightforward
      -- place since it's the natural point of failure.
      -- let Just (ClassInstance { instance_ctx = constrs
      --                         , instance_ty = inst_ty }) =
      --       get_instance ctx ty classNm in
      --   debugPrint ("constrs: " ++ show constrs) $
      --   -- debugPrint ("inst_ty: " ++ showTypeLight inst_ty) $
      --   concat $ map (\(classNm', var) ->
      --                   debugPrint ("attempting to match " ++ showTypeLight ty ++ " with " ++ show var ++ " in " ++ showTypeLight inst_ty) $
      --                   case match_type var ty inst_ty of
      --                     Just ty' -> variable_constraints fi ctx classNm' ty'
      --                     Nothing ->
      --                       error "variable_constraints: incompatible types.. \
      --                             \this shouldn't be possible!")
      --   constrs

      case get_instance ctx ty classNm of
        Just (ClassInstance { instance_ctx = constrs
                            , instance_ty = inst_ty }) -> do
          -- debugPrint ("constrs: " ++ show constrs) $ do
          -- debugPrint ("inst_ty: " ++ showTypeLight inst_ty) $
          concat <$> mapM (\(var, classNm') ->
                              -- debugPrint ("attempting to match " ++ showTypeLight ty
                              --              ++ " with " ++ show var ++ " in " ++
                              --              showTypeLight inst_ty) $
                              case match_type var ty inst_ty of
                                Just ty' ->
                                  -- debugPrint ("matched " ++ show var ++
                                  --              " with " ++ showTypeLight ty') $
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
fill_placeholder :: Context -> TypeClass -> Id -> Type -> Term ()
fill_placeholder ctx (TypeClass { tyclass_name = classNm
                                , tyclass_methods = classMethods })
  methodNm tyIndex =
  let index = fromJust $ assocIndex methodNm classMethods
      tree = instance_tree ctx tyIndex classNm
  in
    -- debugPrint "\nfill_placeholder" $
    -- debugPrint ("index: " ++ show index) $
    -- debugPrint ("tree: " ++ show tree) $
    -- debugPrint ("appTree: " ++ show (mkAppTree tree)) $
    -- debugPrint ("result: " ++ show (mkTupleProjection index (length classMethods) $ mkAppTree tree)) $
    mkTupleProjection index (length classMethods) $ mkAppTree tree

-- Fill all placeholders in a term and also return the (class, type)
-- pairs that were encountered.
fill_placeholders :: Context -> Term TyData -> ([(ClassNm, Type)], Term TyData)
fill_placeholders ctx tm =
  -- debugPrint "\nfill_placeholders" $
  -- debugPrint ("tm: " ++ show tm) $
  -- debugPrint ("placeholders: " ++ show (get_placeholders tm)) $
  bimap nub id $
  foldl (\(classes, acc) p@(TmPlaceholder _ classNm methodNm ty) ->
            -- debugPrint ("\nclassNm: " ++ show classNm) $
            -- debugPrint ("methodNm: " ++ show methodNm) $
            -- debugPrint ("ty: " ++ showTypeLight ty) $
            -- debugPrint ("class: " ++ show (Symtab.get classNm $ ctx_classes ctx)) $
            -- debugPrint ("asdf: " ++ show ((mkData (ty_of_term p) <$
            --               fill_placeholder ctx
            --               (fromJust $ Symtab.get classNm $
            --                 ctx_classes ctx) methodNm ty))) $
            -- debugPrint ("p: " ++ show p) $
            -- debugPrint ("acc: " ++ show acc) $
            ((classNm, ty) : classes,
              termSubst (mkData (ty_of_term p) <$
                          fill_placeholder ctx
                          (fromJust $ Symtab.get (unClassNm classNm) $
                            ctx_classes ctx) methodNm ty)
              p acc))
  ([], tm) (get_placeholders tm)


get_typescheme_constraints :: Context -> Term TyData -> [(Id, ClassNm)]
get_typescheme_constraints ctx = termRec2 $
  \tm -> case tm of
    TmVar _ x ->
      case Symtab.get x $ ctx_gamma ctx of
        Just tyscheme -> -- constrsOfTypeScheme tyscheme
          let ty = normalize_ty $ ty_of_term tm
              open = open_tyscheme tyscheme
              match = nub $ typesRec (\s t ->
                                        case t of
                                          TyVar _ _ _ -> [(s, t)]
                                          _ -> []) ty open
              constrs = flattenSnd $ varsOfTypeScheme tyscheme
              -- constrs' = (\(var, classNm) ->
              --               (tysubstAll' match $ TyVar False [classNm] var,
              --                classNm)) <$> constrs in
              constrs' = pairFun (tysubstAll' match . mkTyVar) id <$> constrs in
            mapFst idOfType <$> filter (isTyVar . fst) constrs'
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

-- TODO: we should use a newtype for class names or something to
-- prevent the annoying swapping of the order of constraints. So a
-- constraint would be something like (Id, ClassNm) instead of (Id,
-- Id).
-- Maybe we should just rewrite this function completely to first scan
-- the term for dictionary variables based on naming convention and
-- then construct and apply the dictionaries.

-- specialize_term :: Context -> Term TyData -> Term TyData
-- specialize_term ctx =
--   -- debugPrint "\nspecialize_term" $
--   termRec $
--   \tm ->
--     -- debugPrint ("\nspec tm: " ++ show tm) $
--     case tm of
--     TmVar _ x ->
--       case Symtab.get x $ ctx_gamma ctx of
--         Just tyscheme ->
--           let ty = normalize_ty $ ty_of_term tm
--               open = open_tyscheme tyscheme
--               match = nub $ typesRec (\s t ->
--                                         case t of
--                                           TyVar _ _ _ -> [(s, t)]
--                                           _ -> []) ty open
--               constrs = flattenSnd $ varsOfTypeScheme tyscheme
--               constrs' = pairFun (tysubstAll' match . mkTyVar) id <$> constrs
--               -- constrs' = (\(var, classNm) ->
--               --               (tysubstAll' match $ TyVar False [classNm] var,
--               --                classNm)) <$> constrs
--               trees = uncurry (instance_tree ctx) <$> constrs'
--               dicts = mkAppTree <$> trees
--               -- dicts =  uncurry (get_dict ctx) <$> constrs'
--               -- dict_vars = filter isTmVar dicts
--               result = mkApp tm $ (mkData TyUnit <$) <$> dicts
--           in
--             -- debugPrint ("\nspec tm: " ++ show tm) $
--             -- debugPrint ("spec ty: " ++ showTypeLight ty) $
--             -- debugPrint ("spec tyscheme: " ++ show tyscheme)
--             -- debugPrint ("spec tyscheme_ty: " ++
--             --             show (typeOfTypeScheme tyscheme))
--             -- debugPrint ("spec open: " ++ show open) $
--             -- debugPrint ("spec ctx: " ++ show (varsOfTypeScheme tyscheme)) $
--             -- debugPrint ("spec match: " ++ show match) $
--             -- debugPrint ("spec constrs': " ++ show constrs') $
--             -- debugPrint ("spec dicts: " ++ show dicts) $
--             -- debugPrint ("spec dict_vars: " ++ show dict_vars) $
--             -- debugPrint ("spec result: " ++ show result) $
            
--             -- debugPrint ("\nCTX decls: " ++ show (ctx_decls ctx)) $
--             -- debugPrint ("\nCTX gamma: " ++ show (ctx_gamma ctx)) $
--             -- debugPrint ("\nCTX datatypes: " ++ show (ctx_datatypes ctx)) $
--             -- debugPrint ("\nCTX ctors: " ++ show (ctx_ctors ctx)) $
--             -- debugPrint ("\nCTX fields: " ++ show (ctx_fields ctx)) $
--             -- debugPrint ("\nCTX classes: " ++ show (ctx_classes ctx)) $
--             -- debugPrint ("\nCTX methods: " ++ show (ctx_methods ctx)) $
--             -- debugPrint ("\nCTX instances: " ++ show (ctx_instances ctx)) $
            
--             result
--         Nothing -> tm
--     _ -> tm


generalize_term :: Context -> [(Id, ClassNm)] -> Term TyData -> (Term TyData, TypeScheme)
generalize_term ctx constrs tm =
  debugPrint ("\ngeneralize_term") $
  debugPrint ("constrs: " ++ show constrs) $
  debugPrint ("tm: " ++ show tm) $
  let ty = ty_of_term tm
      all_constrs = nub $ flattenSnd (classConstraints (freetyvars ty))
                    ++ constrs
      tyscheme = if isValue tm then
                   mkTypeScheme' all_constrs False ty
                 else
                   mkTypeScheme [] False ty
  in
    debugPrint ("ty: " ++ showTypeLight ty) $
    debugPrint ("tyscheme: " ++ show tyscheme) $
    debugPrint ("all_constrs: " ++ show all_constrs) $
    debugPrint ("fvs: " ++ show (freetyvars ty)) $
    let args = fmap (\(var, classNm) -> mkDictId classNm var) constrs
        tm' = mkAbs args tm
    in
      (tm', tyscheme)


process_term :: Show α => α -> TypeSubst -> Term TyData -> TycheckM (Term TyData, TypeScheme)
process_term fi tsubst tm = do
  ctx <- ask
  let (constrs1, spec) = fill_placeholders ctx $ tysubstAll' tsubst <$>
                         tysubstAll' tsubst tm
  -- asdf <- 
  -- let var_constrs1 =
  --       concat $ uncurry (variable_constraints fi ctx) <$> constrs1
  var_constrs1 <-
    concat <$> (sequence $ uncurry (variable_constraints fi ctx) <$> constrs1)
  let var_constrs2 = get_typescheme_constraints ctx spec
  -- let spec = specialize_term ctx filled
  -- let spec = filled
  let all_constrs = var_constrs1 ++ var_constrs2
  -- TODO: propagate these constraints? through spec before passing to
  -- generalize_term.
  let (gen, tyscheme) = generalize_term ctx all_constrs spec
  -- debugPrint ("TODO: need to propagate " ++ show all_constrs ++
  --             " in type " ++ show (ty_of_term spec)) $
  -- debugPrint ("\nconstrs1: " ++ show constrs1) $
  --   debugPrint ("var_constrs1: " ++ show var_constrs1) $
  --   debugPrint ("var_constrs2: " ++ show var_constrs2) $
  -- debugPrint ("\nfilled: " ++ show filled) $
  -- debugPrint ("\ntm: " ++ show tm) $
  -- debugPrint ("\ntm: " ++ show (tysubstAll' tsubst <$>
  --                               tysubstAll' tsubst tm)) $
  --   debugPrint ("all_constrs: " ++ show all_constrs) $
    -- debugPrint ("filled: " ++ show filled) $
    -- debugPrint ("spec: " ++ show spec) $
  -- debugPrint ("\ngen: " ++ show gen) $
    -- debugPrint ("tsubst: " ++ show tsubst) $
  return (gen, tyscheme)
