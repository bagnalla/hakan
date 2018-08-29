{-# LANGUAGE FlexibleContexts #-}

module Context (
  Context(..), TypeScheme, normalize, instantiate_tyscheme, generalize_ty,
  mkTypeScheme, initCtx, updDecls, updGamma, unTypeScheme, open_tyscheme,
  map_tyscheme, mapM_tyscheme, updClasses
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe (fromJust)

import Ast
import Core
import Gensym (nextSym)
import Symtab (Id(..), Symtab, empty, exists, get)


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

newtype TypeScheme = TypeScheme { unTypeScheme :: Type }
  deriving Eq

instance TySubstable TypeScheme where
  tysubst b s t (TypeScheme ty) = TypeScheme $ tysubst b s t ty

instance FreeTyVars TypeScheme where
  freetyvars = freetyvars . unTypeScheme

instance Show TypeScheme where
  show (TypeScheme ty) = "(TypeScheme " ++ show ty ++ ")"

generalize_ty :: Type -> TypeScheme
generalize_ty ty =
  mkTypeScheme (idOfType <$> freetyvars ty) ty


-- Build a type scheme from a list of Ids and a type, where the Ids
-- may appear free as type variables in the body.
mkTypeScheme :: [Id] -> Type -> TypeScheme
mkTypeScheme xs = TypeScheme . go xs
  where
    go :: [Id] -> Type -> Type
    go [] ty = ty
    go (y:ys) ty = TyAbs y KStar $ go ys ty


-- Strip off type abstractions, leaving the body unchanged.
open_tyscheme :: TypeScheme -> Type
open_tyscheme (TypeScheme ty) = go ty
  where
    go :: Type -> Type
    go (TyAbs _ _ s) = go s
    go t = t

map_tyscheme :: (Type -> Type) -> TypeScheme -> TypeScheme
map_tyscheme f = TypeScheme . f . unTypeScheme

mapM_tyscheme :: Monad m => (Type -> m Type) -> TypeScheme -> m TypeScheme
mapM_tyscheme f = fmap TypeScheme . f . unTypeScheme


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

normalize :: Show α => α -> Symtab TypeScheme -> Type -> Type
normalize fi η = typeRec $
  \ty ->
    case ty of
      TyApp (TyAbs x _ t) s ->
        tysubst' s (mkTyVar x) t
      _ -> resolveTyNames fi η ty


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
            Just tyscheme -> unTypeScheme tyscheme
            Nothing ->
              error $ "Type error: unbound type identifier " ++
              show nm ++ " at " ++ show fi
        _ -> ty

-- Passing False for the type variables rigidness doesn't matter since
-- the Eq instance for types ignores it.
instantiate_tyscheme :: (Show α, Num s, Show s, MonadState s m) =>
                        α -> TypeScheme -> m Type
-- instantiate_tyscheme fi = (go >=> normalize fi) . unTypeScheme
instantiate_tyscheme _ = go . unTypeScheme
  where
    go :: (Num s, Show s, MonadState s m) => Type -> m Type
    -- go (TyAbs x k s) = do
    --   s' <- go s
    --   TyApp (TyAbs x k s') <$> TyVar False . Id <$> nextSym "?Y_"

    -- This is cool but the above version seems much easier to read
    -- and understand.
    go (TyAbs x k s) =
      pure (TyApp . TyAbs x k) <*> go s <*>
      (mkTyVar . Id <$> nextSym "?Y_")      
    go ty = return ty
