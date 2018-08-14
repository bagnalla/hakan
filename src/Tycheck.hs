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
             TySubstable(..), tysubstAll, fixTy)
import Gensym (nextSym, nextSym2, nextSym3)
import Parser
import Symtab (Symtab, Id(..), empty, add, get, exists, assocGet)
import Util

-- TODO: need to deal with TyName types. They should probably be
-- replaced by the actual types (for now just variant types) that they
-- refer to. Later there will also be named record types. And we will
-- probably want type synonyms and/or newtypes at some point.

---------------------------------------------
-- | The type of metadata for typechecked terms.

newtype TyData = TyData { unTyData :: Type }
               deriving (Show)

mkData ty = TyData ty

-- TyData can receive type substitution
instance TySubstable TyData where
  tysubst s t fi = TyData (tysubst s t (unTyData fi))


-----------------
-- | Typechecker

data Context =
  Context {
  -- explicit type declarations
  ctx_decls :: Symtab TypeScheme,
  -- regular typing context
  ctx_gamma :: Symtab TypeScheme,
  -- user-defined datatypes
  ctx_datatypes :: Symtab TypeScheme,
  -- -- map constructor names to their datatypes
  ctx_ctors :: Symtab TypeScheme
  }
  deriving Show

initCtx :: Context
initCtx = Context { ctx_decls = empty
                  , ctx_gamma = empty
                  , ctx_datatypes = empty
                  , ctx_ctors = empty }

updDecls :: (Symtab TypeScheme -> Symtab TypeScheme) -> Context -> Context
updDecls f ctx = ctx { ctx_decls = f $ ctx_decls ctx }

updGamma :: (Symtab TypeScheme -> Symtab TypeScheme) -> Context -> Context
updGamma f ctx = ctx { ctx_gamma = f $ ctx_gamma ctx }

-- The reader carries two contexts. The first is for explicit type
-- declarations given by the programmer, and the second is the regular
-- typing context.
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
tycheckTerm (TmVar fi x) = do
  -- 'asks' takes a function mapping the context to a value
  tyscheme <- asks (Symtab.get x . ctx_gamma)
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

tycheckTerm (TmAbs fi x ty tm) = do
  (tm', c) <- local (updGamma $ add x (mkTypeScheme [] ty)) $
              tycheckTerm tm
  let ty' = ty_of_term tm'
  debugPrint ("abs nm: " ++ show x) $
    debugPrint ("abs tm: " ++ show tm') $
    debugPrint ("abs ty: " ++ show ty) $
    debugPrint ("abs tyscheme: " ++ show (mkTypeScheme [] ty)) $
    debugPrint ("abs ty': " ++ show ty') $ do
    y <- nextSym "?Y_"
    let tyy = TyVar False (Id y)
    let c' = c ++ [(tyy, TyArrow ty ty')]
    debugPrint ("abs c: " ++ show c') $
      tryUnify fi c' $
      \tsubst ->
        debugPrint ("abs tsubst: " ++ show tsubst ++ "\n") $
        return (tysubstAll tsubst $
                TmAbs (mkData tyy) x ty tm', c')
  
tycheckTerm (TmApp fi t1 t2) = do
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

tycheckTerm (TmBool fi b) =
  return (TmBool (mkData TyBool) b, [])

tycheckTerm (TmIf fi t1 t2 t3) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  (t3', c3) <- tycheckTerm t3
  let (ty1, ty2, ty3) = (ty_of_term t1', ty_of_term t2', ty_of_term t3')
  let c = c1 ++ c2 ++ c3 ++ [(ty1, TyBool), (ty2, ty3)]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $ TmIf (mkData ty2) t1' t2' t3', c)

tycheckTerm (TmUnit fi) =
  return (TmUnit (mkData TyUnit), [])

tycheckTerm (TmInt fi i) =
  return (TmInt (mkData TyInt) i, [])

tycheckTerm (TmUnop fi u tm) = do
  (tm', c) <- tycheckTerm tm
  let ty = ty_of_term tm'
  case u of

    UFix -> do
      y <- nextSym "?Y_"
      let tyy = TyVar False (Id y)
      let c' = c ++ [(ty, TyArrow tyy tyy)]
      tryUnify fi c' $
        \tsubst ->
          return (tysubstAll tsubst $ TmUnop (mkData tyy) u tm', c')

    _ | u == UFst || u == USnd -> do
          (x, y) <- nextSym2 "?Y_"
          let (tyx, tyy) = (TyVar False (Id x), TyVar False (Id y))
          let c' = c ++ [(ty_of_term tm', TyPair tyx tyy)]
          tryUnify fi c' $
            \tsubst ->
              let fi' = mkData $ if u == UFst then tyx else tyy in
                return (tysubstAll tsubst $ TmUnop fi' u tm', c')
  
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
tycheckTerm (TmBinop fi b t1 t2) = do
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
          
tycheckTerm (TmPair fi t1 t2) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  y <- nextSym "?Y_"
  let tyy = TyVar False (Id y)
  let c = c1 ++ c2 ++ [(tyy, TyPair (ty_of_term t1') (ty_of_term t2'))]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $ TmPair (mkData tyy) t1' t2', c)

tycheckTerm (TmInl fi tm ty) = do
  (tm', c) <- tycheckTerm tm
  x <- nextSym "?Y_"
  let tyx = TyVar False (Id x)
  let c' = c ++ [(ty, TySum (ty_of_term tm') tyx)]
  tryUnify fi c' $
    \tsubst ->
      return (tysubstAll tsubst $ TmInl (mkData ty) tm' ty, c')

tycheckTerm (TmInr fi tm ty) = do
  (tm', c) <- tycheckTerm tm
  x <- nextSym "?Y_"
  let tyx = TyVar False (Id x)
  let c' = c ++ [(ty, TySum tyx (ty_of_term tm'))]
  tryUnify fi c' $
    \tsubst ->
      return (tysubstAll tsubst $ TmInr (mkData ty) tm' ty, c')

tycheckTerm (TmCase fi discrim nm1 t1 nm2 t2) = do
  (discrim', c1) <- tycheckTerm discrim
  let ty = ty_of_term discrim'
  (x, y, z) <- nextSym3 "?Y_"
  let (tyx, tyy, tyz) = (TyVar False (Id x), TyVar False (Id y),
                         TyVar False (Id z))
  (t1', c2) <- local (updGamma $ add nm1 (mkTypeScheme [] tyy)) $
               tycheckTerm t1
  (t2', c3) <- local (updGamma $ add nm2 (mkTypeScheme [] tyz)) $
               tycheckTerm t2
  let c = c1 ++ c2 ++ c3 ++ [(ty, TySum tyy tyz),
                             (ty_of_term t1', ty_of_term t2')]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $
              TmCase (mkData tyx) discrim' nm1 t1' nm2 t2', c)

tycheckTerm (TmLet fi x tm1 tm2) = do
  (tm1', c1) <- tycheckTerm tm1
  let ty1 = ty_of_term tm1'
  tyscheme <- if isValue tm1' then generalize_ty ty1
              else return $ mkTypeScheme [] ty1
  debugPrint ("let ty: " ++ show ty1) $
    debugPrint ("let tyscheme: " ++ show tyscheme ++ "\n") $ do
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
-- tycheckTerm (TmVariant fi x tms) = do (tms', cs) <-
-- unzip <$> mapM tycheckTerm tms error ""

tycheckTerm (TmMatch fi discrim cases) = do
  (discrim', c1) <- tycheckTerm discrim
  (tys, binds, c2, tms') <-
    quadmap id concat concat id . unzip4 <$>
    mapM (\(p, tm) -> do
             (ty, binds, cs) <- patternType fi p
             (tm', cs') <-
               local (updGamma $
                      flip (foldl (\acc (x, t) ->
                                      add x (mkTypeScheme [] t) acc)) binds)
               $ tycheckTerm tm
             return (ty, binds, cs ++ cs', tm')) cases
  -- Need a type variable for the overall type, and if there are any
  -- cases then we constrain it to be equal to their type. Also need
  -- to constrain all of the case types to be the same.
  y <- TyVar False . Id <$> nextSym "_Y?"
  let c = c1 ++ c2 ++ map (\ty -> (ty, ty_of_term discrim')) tys ++
          if length cases > 0 then
            (y, ty_of_term (tms'!!0)) :
            map (\tm -> (ty_of_term tm,
                         ty_of_term (tms'!!0))) tms'
          else []
  ctx <- ask
  -- debugPrint (show tys) $
    -- debugPrint (show $ ty_of_term discrim') $
    -- debugPrint (show c1) $
    -- debugPrint (show c) $
    -- debugPrint (show ctx) $ do
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $
               TmMatch (mkData y) discrim' (zip (fst $ unzip cases) (tms')),
               c)


tycheckCommand :: Show α => Command α -> TycheckM (Command TyData)
tycheckCommand (CDecl fi x ty) = return $ CDecl (mkData TyUnit) x ty

tycheckCommand (CLet fi x t) = do
  (t', c) <- tycheckTerm t
  tryUnify fi c $
    \tsubst ->
      debugPrint ("CLet " ++ show x) $
      debugPrint ("t': " ++ show t') $
      debugPrint ("ty: " ++ show (ty_of_term t')) $
      debugPrint ("c: " ++ show c) $
      debugPrint ("tsubst: " ++ show tsubst) $
      debugPrint ("ty': " ++ show (tysubstAll tsubst (ty_of_term t'))) $
      debugPrint ("ty'': " ++ show (ty_of_term $ tysubstAll tsubst t')) $
      return $ CLet (mkData (tysubstAll tsubst $ ty_of_term t')) x $
      tysubstAll tsubst <$> tysubstAll tsubst t'
      -- this tysubst on t' isn't doing quite what we want since it
      -- doesn't affect the type metadata... so we also fmap the
      -- tysubst over it. TODO: make it nicer somehow.
      
    -- return $ CLet (mkData (ty_of_term t')) x t'

tycheckCommand (CEval fi t) = do
  (t', _) <- tycheckTerm t
  return $ CEval (mkData (ty_of_term t')) t'

tycheckCommand (CData fi nm tyvars ctors) =
  return $ CData (mkData TyUnit) nm tyvars ctors


tycheckCommands :: Show α => [Command α] -> TycheckM [Command TyData]
tycheckCommands [] = return []
tycheckCommands (com:coms) = do
  com' <- tycheckCommand com
  case com' of

    CDecl _ x ty -> do
      let fvs = freetyvars ty
      tyscheme <- generalize_ty ty
      tyscheme' <- instantiate_tyscheme tyscheme
      debugPrint ("CDecl ty: " ++ show ty) $
        debugPrint ("CDecl tyscheme: " ++ show tyscheme) $
        debugPrint ("CDecl fvs: " ++ show fvs ++ "\n") $ do
        coms' <- local (updDecls $ add x tyscheme) $
                 tycheckCommands coms
        return $ com' : coms'

    CLet fi x tm -> do
      decls <- asks ctx_decls
      gamma <- asks ctx_gamma
      let ty = ty_of_term tm
      -- Enforce value restriction since we have mutable references.
      -- I.e., only generalize the type when then term is a syntactic
      -- value. See TAPL or Xavier Leroy's PhD thesis.
      tyscheme <- if isValue tm then generalize_ty ty
                  else return $ mkTypeScheme [] ty
      case Symtab.get x decls of
        Just declTyscheme -> do
          -- Ignore the result of unifying the type schemes since we
          -- want to use the exact type declared by the programmer.
          _ <- unify_tyschemes (data_of_command com) tyscheme declTyscheme
          let tyscheme' = loosen_tyscheme declTyscheme
          coms' <- local (updGamma $ const $ add x tyscheme' gamma) $
                   tycheckCommands coms
          return $ com' : coms'
        Nothing -> do
          coms' <- local (updGamma $ const $ add x tyscheme gamma) $
                   tycheckCommands coms
          return $ com' : coms'

    -- Need to ty the knot between the variant type and the types of
    -- its constructors, since their return type is the variant type
    -- itself (and it contains their types of course).
    -- We should be able to just tie the knot on the variant type like
    -- normal and then just build the types of the constructor
    -- functions after the fact.

    -- TODO: ensure that all free type variables appearing in the
    -- constructor signatures are in the tyvars list, and generate a
    -- warning if any tyvars are unused.
    CData fi nm tyvars ctors -> do
      let ty = fixTy nm $ TyVariant nm tyvars ctors
      let tyscheme = mkTypeScheme tyvars ty
      debugPrint (show tyscheme) $ do
        coms' <-
          local (\ctx ->
                   ctx { ctx_datatypes = add nm tyscheme $ ctx_datatypes ctx
                       , ctx_ctors = foldl (\acc x -> add x tyscheme acc)
                                     (ctx_ctors ctx) (fst $ unzip ctors)
                       
                       -- Add types of curried constructor functions
                       -- to the typing context.
                       , ctx_gamma =
                           foldl (\acc (ctorName, ctorTys) ->
                                    add ctorName
                                    (mkTypeScheme tyvars $ mkArrowType $
                                     ctorTys ++ [ty]) acc)
                           (ctx_gamma ctx) ctors
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

-- ty_of_command :: Command TyData -> Type
-- ty_of_command = unTyData . data_of_command

generalize_ty :: Type -> TycheckM TypeScheme
generalize_ty ty = do
  -- (_, ctx) <- ask
  gamma <- asks ctx_gamma
  let fvs= freetyvars ty
  let generalizable = map (fromJust . idOfType)
        (filter (\(TyVar _ x) -> not $ x `exists` gamma) fvs)
  return $ mkTypeScheme generalizable ty

-- Passing False for the type variables rigidness doesn't matter since
-- the Eq instance for types ignores it.
instantiate_tyscheme :: TypeScheme -> TycheckM Type
instantiate_tyscheme tyscheme = do
  tyscheme' <- foldM (\acc x -> do
                         y <- nextSym "?Y_"
                         return $ tysubst (TyVar False (Id y))
                           (TyVar False x) acc)
         tyscheme (ts_tyvars_of tyscheme)
  return (ts_ty_of tyscheme')

-- The first type scheme argument should be that obtained from
-- typechecking the body of a let command, and the second should be
-- the declared type. We expect the first to be more general than the
-- second.
unify_tyschemes :: Show α => α -> TypeScheme -> TypeScheme -> TycheckM Type
unify_tyschemes fi tyscheme1 tyscheme2 = do
  ty1 <- instantiate_tyscheme tyscheme1
  ty2 <- instantiate_tyscheme tyscheme2
  case unify [(ty1, ty2)] of
    Left (s, t) -> unifyError s t fi
    Right tsubst -> return $ tysubstAll tsubst ty1


-- Make all type variables in a typescheme non-rigid.
loosen_tyscheme :: TypeScheme -> TypeScheme
loosen_tyscheme tyscheme =
  tyscheme { ts_ty_of = typeRec (\t ->
                                   case t of
                                     TyVar _ x -> TyVar False x
                                     _ -> t) $
                        ts_ty_of tyscheme }


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
patternType fi (PPair p1 p2) = do
  (ty1, binds1, cs1) <- patternType fi p1
  (ty2, binds2, cs2) <- patternType fi p2
  return (TyPair ty1 ty2, binds1 ++ binds2, cs1 ++ cs2)

-- We return a freshly instantiated copy of the variant type, with the
-- types it associates with the current constructor name constrained
-- to be equal to the types computed by recursion on the subpatterns.
patternType fi (PConstructor nm ps) = do
  (tys, binds, cs) <- trimap id concat concat . unzip3 <$>
                      mapM (patternType fi) ps
  variantTyscheme <- asks (Symtab.get nm . ctx_ctors)
  case variantTyscheme of
    Just vTyscheme -> do
      vTy@(TyVariant _ _ ctors) <- instantiate_tyscheme vTyscheme
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


-- Look up all TyNames and replace them with their actual types,
-- substituting the tyvars into the type.
-- TODO: verify that this works and use when typechecking CDecl and
-- TAbs.
resolveTyNames :: Show α => α -> Type -> TycheckM Type
resolveTyNames fi =
  typeRecM $
  \ty -> case ty of
    TyName nm tyvars -> do
      γ <- asks ctx_gamma
      case Symtab.get nm γ of
        Just tyscheme ->
          case ts_ty_of tyscheme of
            ty'@(TyVariant _ tyvars' _) ->
              if length tyvars == length tyvars' then
                return $ foldl (\acc (s, t) -> tysubst s t acc) ty' $
                bimap (TyVar False) (TyVar False) <$> zip tyvars tyvars'
              else
                throwError $ "resolveTyNames: wrong number of type" ++
                " arguments to type " ++ show ty ++ " at " ++ show fi
            _ -> throwError "resolveTyNames: TODO"
        Nothing ->
          throwError $ "resolveTyNames: unbound type identifier " ++
          show nm ++ " at " ++ show fi
