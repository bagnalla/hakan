{-# LANGUAGE FlexibleContexts #-}

module Context (
  Context(..), TypeScheme, unfold, instantiate_tyscheme, generalize_ty,
  mkTypeScheme, initCtx, updDecls, updGamma, open_tyscheme, updClasses,
  typeOfTypeScheme, instantiate_tyscheme'
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Data.List (intercalate)
import Data.Maybe (fromJust)

import Ast
import Core
import Gensym (nextSym)
import Symtab (Id(..), Symtab, empty, exists, get)
import Util


--------------------
-- | Typing contexts

data Context =
  Context {
  -- explicit type declarations (δ)
  ctx_decls :: Symtab TypeScheme,
  -- regular typing context (γ)
  ctx_gamma :: Symtab TypeScheme,
  -- user-defined datatypes (η)
  ctx_datatypes :: Symtab TypeScheme,
  -- map constructor names to their datatypes (ε)
  ctx_ctors :: Symtab TypeScheme,
  -- map field names to their record types (ε)
  ctx_fields :: Symtab TypeScheme,
  -- map class names to TypeClasses (φ)
  ctx_classes :: Symtab TypeClass,
  -- map method names to TypeClasses (φ)
  ctx_methods :: Symtab TypeClass,
  -- map class names to association lists mapping types to class
  -- instances (ψ)
  ctx_instances :: Symtab [ClassInstance]
  }
  deriving Show

-- map types to instances. types including arrow types and everything,
-- including abstractions. When we search for types in the instance
-- database, instead of checking for equality we hold their type
-- variables rigid and try to unify with the type we're searching
-- for. Then we will know the class constraints .. ?

-- Or maybe we just use a slightly different notion of equality -- up
-- to renaming of variables (including free variables) (so we don't
-- have to invoke unification). Then we actually hold the variables of
-- the type we're searching for fixed and do renaming on the types
-- we're searching through. When we have a match the constraints of
-- the matching type will be exactly what we want.

initCtx :: Context
initCtx = Context { ctx_decls = empty
                  , ctx_gamma = empty
                  , ctx_datatypes = empty
                  , ctx_ctors = empty
                  , ctx_fields = empty
                  , ctx_classes = empty
                  , ctx_methods = empty
                  , ctx_instances = empty }

updDecls :: (Symtab TypeScheme -> Symtab TypeScheme) ->
            Context -> Context
updDecls f ctx = ctx { ctx_decls = f $ ctx_decls ctx }

updGamma :: (Symtab TypeScheme -> Symtab TypeScheme) ->
            Context -> Context
updGamma f ctx = ctx { ctx_gamma = f $ ctx_gamma ctx }

updClasses :: (Symtab TypeClass -> Symtab TypeClass) ->
              Context -> Context
updClasses f ctx = ctx { ctx_classes = f $ ctx_classes ctx }

-----------------
-- | Type schemes

-- We don't export the TypeScheme constructor, so the only way to
-- construct one from outside of this module is through the
-- mkTypeScheme function. This is a really thin layer of abstraction
-- that doesn't do much.. it could probably be improved.

-- newtype TypeScheme = TypeScheme { unTypeScheme :: Type }
--   deriving Eq

-- For each type variable we store its name (as bound in the type) and
-- list of class constraints.
data TypeScheme =
  TypeScheme { tyscheme_ty :: Type
             , tyscheme_vars :: [(Id, [Id])] }
  deriving Eq

typeOfTypeScheme :: TypeScheme -> Type
typeOfTypeScheme = tyscheme_ty

instance TySubstable TypeScheme where
  -- tysubst b s t (TypeScheme ty) = TypeScheme $ tysubst b s t ty
  tysubst b s t tyscheme@(TypeScheme { tyscheme_ty = ty }) =
     tyscheme { tyscheme_ty = tysubst b s t ty }

instance FreeTyVars TypeScheme where
  -- freetyvars = freetyvars . unTypeScheme
    freetyvars = freetyvars . tyscheme_ty

instance Show TypeScheme where
  -- show (TypeScheme ty) = "(TypeScheme " ++ show ty ++ ")"
  show (TypeScheme { tyscheme_ty = ty, tyscheme_vars = vars }) =
    "(TypeScheme " ++ show ty ++ " (" ++
    intercalate ", " (show <$> vars) ++ "))"

generalize_ty :: Type -> TypeScheme
generalize_ty ty =
  mkTypeScheme (map (\tyvar ->
                       case tyvar of
                         TyVar _ ctx nm -> (nm, ctx)
                         _ -> error "generalize_ty: expected TyVar") $
                 freetyvars ty) ty

-- Build a type scheme from a list of type variables and a body type,
-- where the variables may appear free in the body. Each variable is
-- described by a name and a list of class constraints.
mkTypeScheme :: [(Id, [Id])] -> Type -> TypeScheme
-- mkTypeScheme vars ty = TypeScheme { tyscheme_ty = go (fst <$> vars) ty
--                                   , tyscheme_vars = vars }
mkTypeScheme vars ty =
  let x = TypeScheme { tyscheme_ty = mkTyAbs (fst <$> vars) ty
                     , tyscheme_vars = vars } in
    debugPrint "\n\nmkTypeScheme" $
    debugPrint ("vars: " ++ show vars) $
    debugPrint ("ty: " ++ show ty) $
    debugPrint ("tyscheme: " ++ show x) x


-- -- Build a type scheme from a list of Ids and a type, where the Ids
-- -- may appear free as type variables in the body.
-- mkTypeScheme :: [Id] -> Type -> TypeScheme
-- mkTypeScheme xs = TypeScheme . go xs
--   where
--     go :: [Id] -> Type -> Type
--     go [] ty = ty
--     go (y:ys) ty = TyAbs y KStar $ go ys ty


-- Strip off type abstractions, leaving the body unchanged.
open_tyscheme :: TypeScheme -> Type
open_tyscheme (TypeScheme { tyscheme_ty = ty }) = go ty
  where
    go :: Type -> Type
    go (TyAbs _ _ s) = go s
    go t = t

-- map_tyscheme :: (Type -> Type) -> TypeScheme -> TypeScheme
-- map_tyscheme f = TypeScheme . f . unTypeScheme

-- mapM_tyscheme :: Monad m => (Type -> m Type) -> TypeScheme -> m TypeScheme
-- mapM_tyscheme f = fmap TypeScheme . f . unTypeScheme

-- Passing False for the type variables rigidness doesn't matter since
-- the Eq instance for types ignores it.
instantiate_tyscheme :: (Show α, Num s, Show s, MonadState s m) =>
                        α -> Bool -> TypeScheme -> m Type
-- instantiate_tyscheme fi = (go >=> normalize fi) . unTypeScheme
-- instantiate_tyscheme _ = go . unTypeScheme
--   where
--     go :: (Num s, Show s, MonadState s m) => Type -> m Type
--     -- go (TyAbs x k s) = do
--     --   s' <- go s
--     --   TyApp (TyAbs x k s') <$> TyVar False . Id <$> nextSym "?Y_"
--     -- This is cool but the above version seems much easier to read
--     -- and understand.
--     go (TyAbs x k s) =
--       pure (TyApp . TyAbs x k) <*> go s <*>
--       (mkTyVar . Id <$> nextSym "?Y_")      
--     go ty = return ty

-- TODO: make this version work. The one below does.. which makes me
-- suspect that we just aren't building the typeschemes right
-- (tyscheme_vars needs to be correct).
instantiate_tyscheme fi b (TypeScheme { tyscheme_ty = ty
                                      , tyscheme_vars = vars }) =
  debugPrint ("\n\n\ninstantiate_tyscheme") $
  debugPrint ("ty: " ++ show ty) $
  debugPrint ("vars: " ++ show vars) $ do
  x <- foldM (\acc (nm, ctx) ->
                 TyApp acc <$> TyVar b ctx . Id <$> nextSym "?Y_")
       ty vars
  debugPrint ("x: " ++ show x) $ return x

-- instantiate_tyscheme _ = go . typeOfTypeScheme
--   where
--     go :: (Num s, Show s, MonadState s m) => Type -> m Type
--     -- go (TyAbs x k s) = do
--     --   s' <- go s
--     --   TyApp (TyAbs x k s') <$> TyVar False . Id <$> nextSym "?Y_"
--     -- This is cool but the above version seems much easier to read
--     -- and understand.
--     go (TyAbs x k s) =
--       pure (TyApp . TyAbs x k) <*> go s <*>
--       (mkTyVar . Id <$> nextSym "?Y_")      
--     go ty = return ty

instantiate_tyscheme' :: (Show α, Num s, Show s, MonadState s m) =>
                         α -> TypeScheme -> m Type
instantiate_tyscheme' fi = instantiate_tyscheme fi False


-----------------------
-- | Type normalization

-- For some reason we can't use the monadic recursion scheme here
-- because it diverges on infinite types. I don't understand why
-- though... It also diverges if we try to print the type being
-- normalized. This could just take η as an argument instead of being
-- in the reader monad but so far it's fine like this.
-- normalize :: (Show α, MonadReader Context m) => α -> Type -> m Type
-- normalize fi ty = do
--   η <- asks ctx_datatypes
--   return $ (typeRec $
--             \ty ->
--               case ty of
--                 TyApp (TyAbs x _ t) s ->
--                   tysubst' s (TyVar False x) t
--                 _ -> resolveTyNames fi η ty) ty

-- normalize :: Show α => α -> Symtab TypeScheme -> Type -> Type
-- normalize fi η = typeRec $
--   \ty ->
--     case ty of
--       TyApp (TyAbs x _ t) s ->
--         tysubst' s (mkTyVar x) t
--       -- TyApp (TyConstructor tycon@(TypeConstructor
--       --                             { tycon_tyvars = tyvars
--       --                             , tycon_kinds = kinds
--       --                             , tycon_tyargs = tyargs
--       --                             , tycon_instantiated = t })) s ->
--       --   let x = tyvars !! length tyargs in
--       --     TyConstructor $
--       --     tycon { tycon_kinds = kinds ++ [KStar]
--       --           , tycon_tyargs = tyargs ++ [s]
--       --           , tycon_instantiated = tysubst' s (mkTyVar x) t }
--       _ -> resolveTyNames fi η ty


unfold :: Show α => α -> Symtab TypeScheme -> Type -> Type
unfold fi η (TyName nm) =
  case Symtab.get nm η of
    Just tyscheme -> typeOfTypeScheme tyscheme
    Nothing ->
      error $ "Type error: unbound type identifier "
      ++ show nm ++ " at " ++ show fi
-- unfold fi η (TyApp ty s) =
--   let (TyAbs x _ t) = unfold fi η ty in
--     unfold fi η $ tysubst' s (mkTyVar x) t

unfold fi η (TyApp ty s) =
  case unfold fi η ty of
    TyAbs x _ t ->
      unfold fi η $ tysubst' s (mkTyVar x) t
    TyConstructor tycon@(TypeConstructor
                          { tycon_tyvars = tyvars
                          , tycon_kinds = kinds
                          , tycon_tyargs = tyargs
                          , tycon_instantiated = t }) ->
      if length tyvars == length tyargs then
        error $ "unfold: type constructor " ++ show tycon ++
        " is already fully applied"
      else
        debugPrint ("\nAPPLYING " ++ show tycon ++ " to " ++ show s) $
        let x = tyvars !! length tyargs in
          TyConstructor $
          tycon { tycon_kinds = kinds ++ [KStar]
                , tycon_tyargs = tyargs ++ [s]
                , tycon_instantiated = unfold fi η $ TyApp t s }
    _ -> error "unfold: expected type abstraction or type constructor on \
               \left side of application"

unfold fi η (TyConstructor tycon) =
  TyConstructor $ mapTypeConstructor (unfold fi η) tycon
unfold _ _ ty = ty


-- Look up all TyNames and replace them with their actual types. This
-- has to be outside the reader monad so we can use it from inside the
-- non-monadic part of normalize, which kind of sucks because we can't
-- use throwError.
resolveTyNames :: Show α => α -> Symtab TypeScheme -> Type -> Type
resolveTyNames fi η =
  typeRec $
    \ty ->
      case ty of
        TyName nm ->
          case Symtab.get nm η of
            Just tyscheme -> tyscheme_ty tyscheme
            Nothing ->
              error $ "Type error: unbound type identifier " ++
              show nm ++ " at " ++ show fi
        _ -> ty
