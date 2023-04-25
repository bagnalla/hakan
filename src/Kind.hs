module Kind where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader

import Data.Bifunctor (bimap, second)
import Data.Maybe (fromJust)
import Data.Monoid

import Ast
import Gensym (nextSym, nextSymN)
import Symtab (Id(..), Symtab, empty, add, fromList)
import qualified Symtab (get)
import Util (bimap', mapEitherRight, debugPrint, fst3, trimap)

-- A recursion scheme for kinds.
kindRec :: (Kind -> Kind) -> Kind -> Kind
kindRec f (KArrow k1 k2) = f $ KArrow (kindRec f k1) (kindRec f k2)
kindRec f k = f k

kindRec2 :: Monoid a => (Kind -> a) -> Kind -> a
kindRec2 f k@(KArrow k1 k2) = f k <> kindRec2 f k1 <> kindRec2 f k2
kindRec2 f k = f k


isKArrow :: Kind -> Bool
isKArrow (KArrow _ _) = True
isKArrow _ = False

isKVar :: Kind -> Bool
isKVar (KVar _) = True
isKVar _ = False

freeKVars :: Kind -> [Kind]
freeKVars = kindRec2 $
  \k -> if isKVar k then [k] else []

kindsubst :: Kind -> Kind -> Kind -> Kind
kindsubst s t = kindRec $
  \k -> if k == t then s else k

-- The order of substitution matters -- so we use foldl.
kindsubstAll :: KindSubst -> Kind -> Kind
kindsubstAll  = flip $ foldl (\acc (x, y) -> kindsubst x y acc)

kindsubstType :: KindSubst -> Type -> Type
kindsubstType = typeKindRec . kindsubstAll

-- Replace all kind variables with KStar.
concretifyKind :: Kind -> Kind
concretifyKind = kindRec $
  \k -> if isKVar k then KStar else k

concretifyType :: Type -> Type
concretifyType = typeKindRec concretifyKind

mkKArrow :: [Kind] -> Kind
mkKArrow [] = KStar
mkKArrow (k:ks) = KArrow k $ mkKArrow ks


-- Take a symtab for the kinds of named types
kindOfType :: Symtab Kind -> Type -> Maybe Kind
kindOfType _ (TyVar _ k _ _) = return k
kindOfType δ (TyAbs _ k s) = do
  s' <- kindOfType δ s
  return $ KArrow k s'
kindOfType δ (TyApp s _) =
  case kindOfType δ s of
    Just (KArrow _ k) -> return k
    _ -> Nothing
kindOfType δ (TyConstructor
              (TypeConstructor { tycon_tyargs = tyargs
                               , tycon_kinds = kinds })) =
  return $ mkKArrow $ drop (length tyargs) kinds
kindOfType δ (TyName x) = Symtab.get x δ
kindOfType _ _ = return KStar


---------------------
-- | Kinding contexts

data KContext =
  KContext {
  -- map TyVars to kinds (γ)
  kctx_gamma :: Symtab Kind,
  -- map named types to their kinds (δ)
  kctx_delta :: Symtab Kind
  }
  deriving Show

updKGamma :: (Symtab Kind -> Symtab Kind) -> KContext -> KContext
updKGamma f ctx = ctx { kctx_gamma = f $ kctx_gamma ctx }

updKDelta :: (Symtab Kind -> Symtab Kind) -> KContext -> KContext
updKDelta f ctx = ctx { kctx_delta = f $ kctx_delta ctx }

-- The type of kind substitutions
type KindSubst = [(Kind, Kind)]


----------------
-- | Kindchecker

type KindcheckM a =
  ReaderT KContext (ExceptT String (StateT Int Identity)) a

runKindcheckM :: KindcheckM a -> KContext -> Int -> (Either String a, Int)
runKindcheckM m ctx s =
  runIdentity $ flip runStateT s $ runExceptT $ runReaderT m ctx

runKindCheck' :: KindcheckM (Type, Kind, KConstrSet) -> KContext -> Int ->
                 Either String Type
runKindCheck' m ctx s =
    case fst $ runIdentity $ flip runStateT s $ runExceptT $
         runReaderT m ctx of
      Left msg -> Left msg
      Right (ty, _, cs) ->
        case kunify cs of
          Left _ ->
            Left "runKindCheck: kind unification error \
                 \(this should never happen)"
          Right ksubst ->
            return $ concretifyType $ kindsubstType ksubst ty

runKindCheck :: Symtab Kind -> [(Id, Kind)] -> Type -> Either String Type
runKindCheck δ cs ty =
  let (γ, s) = initGamma cs [ty] 0 in
    case γ of
      Just γ' ->
        runKindCheck' (kindCheck ty) (KContext { kctx_gamma = γ'
                                               , kctx_delta = δ }) s
      Nothing ->
        Left $ "type " ++ show ty ++ " is not well-kinded"

kindCheck :: Type -> KindcheckM (Type, Kind, KConstrSet)

kindCheck (TyVar b k ctx x) = do
  γ <- asks kctx_gamma
  case Symtab.get x γ of
    Just k' ->
      case k of
        KUnknown ->
          return (TyVar b k' ctx x, k', [])
        _ ->
          return (TyVar b k ctx x, k, [(k, k')])
    Nothing -> throwError $ "unbound kind variable " ++ show x

kindCheck (TyAbs x k s) = do
  (s', k1, c) <- local (updKGamma $ add x k) $
                 kindCheck s
  return (TyAbs x k s', KArrow k k1, c)

kindCheck (TyApp s t) = do
  δ <- asks kctx_delta
  (s', k1, c1) <- kindCheck s
  (t', k2, c2) <- kindCheck t
  n <- get
  k <- KVar . Id <$> nextSym "?Z_"
  let c = c1 ++ c2 ++ [(k1, KArrow k2 k)]
  n' <- get
  tryKUnify c $
    \ksubst ->
      return (TyApp s' t', k, c)

kindCheck (TyArrow s t) = do
  (s', _, c1) <- kindCheck s
  (t', _, c2) <- kindCheck t
  let c = c1 ++ c2
  tryKUnify c $
    \_ ->
      return (TyArrow s' t', KStar, c)

kindCheck (TyName x) = do
  δ <- asks kctx_delta
  case Symtab.get x δ of
    Just k -> return (TyName x, k, [])
    Nothing ->
      throwError $ "unbound type name '" ++ show x ++ "'"

kindCheck (TyConstructor
           tycon@(TypeConstructor { tycon_kinds = kinds
                                  , tycon_tyargs = tyargs
                                  , tycon_ty = uninst
                                  , tycon_instantiated = inst })) = do
  γ <- asks kctx_gamma
  δ <- asks kctx_delta
  (tyargs', ks, cs) <- trimap id id concat . unzip3 <$>
                       (sequence $ kindCheck <$> tyargs)
  (uninst', k1, c1) <- kindCheck uninst
  -- We should be able to to just ignore inst but we still kindcheck
  -- it for the sake of properly updating the TypeConstructor
  -- record. We assume it isn't messed up.
  (inst', _, _) <- kindCheck inst
  let c = cs ++ c1 ++ [(k1, mkKArrow kinds)] ++ zip kinds ks
  tryKUnify c $
    \_ -> do
      let ty' = TyConstructor $
                tycon { tycon_tyargs = tyargs'
                      , tycon_ty = uninst'
                      , tycon_instantiated = inst' }
      return (ty', fromJust $ kindOfType δ ty', c)

kindCheck (TyRef s) = do
  (s', _, c) <- kindCheck s
  return (TyRef s', KStar, c)

kindCheck (TyVariant x tyargs ctors) = do
  δ <- asks kctx_delta
  case Symtab.get x δ of
    Just k -> do
      (tyargs', ks, cs) <- trimap id id concat . unzip3 <$>
                          (sequence $ kindCheck <$> tyargs)
      (ctors', _, cs') <-
        trimap id id concat . unzip3 <$>
        mapM (\(y, tys) -> do
                 (tys', _, cs'') <- trimap id id concat . unzip3 <$>
                                    (sequence $ kindCheck <$> tys)
                 return ((y, tys'), (), cs'')) ctors
      let c = cs ++ cs' ++ [(k, mkKArrow ks)]
      tryKUnify c $
        \_ ->
          return (TyVariant x tyargs' ctors', KStar, c)
    Nothing ->
      throwError $ "unbound type name '" ++ show x ++ "'"

kindCheck (TyRecord x ctx fields) = do
  δ <- asks kctx_delta
  case Symtab.get x δ of
    Just k -> do
      (ctx', _, cs) <- trimap id id concat . unzip3 <$>
                       (sequence $ kindCheck <$> ctx)
      (fields', _, cs') <-
        trimap id id concat . unzip3 <$>
        mapM (\(y, ty) -> do
                 (ty', _, cs'') <- kindCheck ty
                 return ((y, ty'), (), cs'')) fields
      let c = cs ++ cs'
      tryKUnify c $
        \_ ->
          return (TyRecord x ctx' fields', KStar, c)
    Nothing ->
      throwError $ "unbound type name '" ++ show x ++ "'"

kindCheck ty = do
  δ <- asks kctx_delta
  case kindOfType δ ty of
    Just k -> return (ty, k, [])
    Nothing -> throwError $ show ty ++ "is not well-kinded"


-- Create the initial context with mappings for all the type variables
-- and the name of the variant type being checked. Then at the end we
-- combine all of the generated constraints with a new one relating
-- the kind of the variant type with those of the type variables and
-- make sure it all unifies.
initGamma :: [(Id, Kind)] -> [Type] -> Int -> (Maybe (Symtab Kind), Int)
initGamma cs tys s =
  flip runState s $ do
  foldM (\γ (TyVar _ k _ x) ->
            case γ of
              Just γ' ->
                case k of
                  KUnknown ->
                    case Symtab.get x γ' of
                      Just _ -> return $ Just γ'
                      Nothing -> do
                        k' <- KVar . Id <$> nextSym "?Z_"
                        return $ Just $ Symtab.add x k' γ'
                  _ ->
                    case Symtab.get x γ' of
                      Just k' ->
                        if k == k' then
                          return (Just γ')
                        else
                          return Nothing
                      Nothing -> return $ Just $ Symtab.add x k γ'
              _ -> return Nothing)
    (Just $ Symtab.fromList cs)
    (concat $ freetyvars <$> tys)

initDelta :: Id -> Int -> Symtab Kind -> (Symtab Kind, Int)
initDelta nm s δ =
  (Symtab.add nm (KVar $ Id $ "?Z_" ++ show s) δ, s + 1)

initKCtx :: Id -> [Type] -> Int -> Symtab Kind -> (Maybe KContext, Int)
initKCtx nm tys s δ =
  let (γ, s') = initGamma [] tys s
      (δ', s'') = initDelta nm s' δ in
    case γ of
      Just γ' -> (Just $ KContext { kctx_gamma = γ'
                                  , kctx_delta = δ' }, s'')
      Nothing -> (Nothing, s'')


kindCheckVariantOrRecord :: Id -> [Id] -> [Type] -> Symtab Kind ->
                            Either String (Kind, [Kind])
kindCheckVariantOrRecord nm tyvars tys δ =
  let (kctx, s) = initKCtx nm tys 0 δ in
    case kctx of
      Just kctx' ->
        case runKindcheckM (go tys) kctx' s of
          (Left msg, _) -> Left msg
          (Right (tys, ks, cs), s) ->
            let ks = getGamma kctx' <$> tyvars
                k = mkKArrow ks in
              case kunify (cs ++ [(getDelta kctx' nm, k)]) of
                Left (s, t, msg) -> Left msg
                Right ksubst ->
                  Right (concretifyKind $ kindsubstAll ksubst k,
                         (concretifyKind . kindsubstAll ksubst) <$> ks)
      Nothing ->
        Left "kindCheckVariantOrRecord: error initializing context"
  where
    go :: [Type] -> KindcheckM ([Type], [Kind], KConstrSet)
    go tys = do
      (tys, ks, cs) <- trimap id id concat . unzip3 <$> mapM kindCheck tys
      return (tys, ks, cs)
    getGamma :: KContext -> Id -> Kind
    getGamma (KContext { kctx_gamma = γ }) x = fromJust $ Symtab.get x γ
    getDelta :: KContext -> Id -> Kind
    getDelta (KContext { kctx_delta = δ }) x = fromJust $ Symtab.get x δ


---------------------
-- | Kind unification

-- The type of kind constraint sets
type KConstrSet = [(Kind, Kind)]

tryKUnify :: KConstrSet -> (KindSubst -> KindcheckM a) -> KindcheckM a
tryKUnify constrs f =
  case kunify constrs of
    Left (s, t, msg) ->
      throwError $ "kinds " ++ show s ++ " and " ++ show t ++
      " can't be unified. Reason: " ++ msg
    Right ksubst -> f ksubst


kunify :: KConstrSet -> Either (Kind, Kind, String) KindSubst
kunify [] = return []
kunify ((s, t) : constrs) =
  if s == t then
    kunify constrs
  else
    case (s, t) of
      (KVar _, _)
        | not $ s `elem` freeKVars t -> do
            rest <- kunify $ bimap' (kindsubst t s) <$> constrs
            return $ (t, s) : rest
      (_, KVar _)
        | not $ t `elem` freeKVars s ->
            kunify ((t, s) : constrs)
      (KArrow s1 s2, KArrow t1 t2) ->
        kunify ((s1, t1) : (s2, t2) : constrs)
      _ ->
        Left $ (s, t, "incompatible kinds")
