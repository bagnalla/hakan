{-# LANGUAGE FlexibleContexts #-}

module Context (
  Context(..), TypeScheme, unfold, instantiate_tyscheme,
  mkTypeScheme, initCtx, updDecls, updGamma, open_tyscheme, updClasses,
  typeOfTypeScheme, instantiate_tyscheme', mkTypeScheme',
  isMethod, updInstances, classConstraints, normalize_ty, varsOfTypeScheme,
  superclasses, all_class_constraints, constrsOfTypeScheme
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Data.List (groupBy, intercalate, nub)
-- import Data.Maybe (fromJust)
import Data.Tuple (swap)

import Ast
import Core
import Gensym (nextSym)
import Symtab (Id(..), Symtab, empty, exists, get, assocGet, assocSet)
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
-- variables rigidand try to unify with the type we're searching
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

updInstances :: (Symtab [ClassInstance] -> Symtab [ClassInstance]) ->
                Context -> Context
updInstances f ctx = ctx { ctx_instances = f $ ctx_instances ctx }

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

-- tyscheme_vars tells us the dictionary arguments that the term
-- should take, and in what order.
data TypeScheme =
  TypeScheme { tyscheme_ty :: Type
             , tyscheme_vars :: [(Id, [Id])]
             
             -- This is so we know when to replace a method call with
             -- a placeholder when typechecking.
             , tyscheme_ismethod :: Bool }
  deriving Eq

typeOfTypeScheme :: TypeScheme -> Type
typeOfTypeScheme = tyscheme_ty

varsOfTypeScheme :: TypeScheme -> [(Id, [Id])]
varsOfTypeScheme = tyscheme_vars

constrsOfTypeScheme :: TypeScheme -> [(Id, Id)]
constrsOfTypeScheme = map swap . flattenSnd . tyscheme_vars

isMethod :: TypeScheme -> Bool
isMethod (TypeScheme { tyscheme_ismethod = b }) = b

instance TySubstable TypeScheme where
  tysubst b s t tyscheme@(TypeScheme { tyscheme_ty = ty }) =
     tyscheme { tyscheme_ty = tysubst b s t ty }

instance FreeTyVars TypeScheme where
    freetyvars = freetyvars . tyscheme_ty

instance Show TypeScheme where
  show (TypeScheme { tyscheme_ty = ty, tyscheme_vars = vars }) =
    "(TypeScheme " ++ show ty ++ " (" ++
    intercalate ", " (show <$> vars) ++ "))"


-- Recursively get all superclasses
superclasses :: Symtab TypeClass -> Id -> [Id]
superclasses ϕ classNm = do
  case Symtab.get classNm ϕ of
    Just (TypeClass { tyclass_constrs = constrs
                    , tyclass_index = tyIndex }) ->
      -- pure (++) <*> concat <$> (sequence $ superclasses <$> constrs) <*>
      -- pure constrs
      concat (superclasses ϕ <$> constrs) ++ constrs
    Nothing ->
      error $ "superclasses: class " ++ show classNm ++
      " not found. Known classes:\n" ++ show ϕ

-- TODO: Should we include superclass constraints as well? It would
-- probably make sense so then the list of constraints is the
-- definitive list.. but we would need to take the typing context as
-- an argument here (or at least the symtab of known classes).
-- generalize_ty :: [(Id, [Id])] -> Bool -> Type -> TypeScheme
-- generalize_ty constrs ismethod ty = mkTypeScheme constrs ismethod ty

-- generalize_ty' :: [(Id, Id)] -> Bool -> Type -> TypeScheme
-- generalize_ty' constrs =
--   let constrs' = (\l -> (fst (head l), snd <$> l)) <$>
--                  groupBy (\x y -> fst x == fst y) constrs in
--     generalize_ty constrs'

-- generalize_ty' :: [(Id, [Id])] -> Type -> TypeScheme
-- generalize_ty' = flip generalize_ty False

all_class_constraints :: Symtab TypeClass -> Type -> [(Id, [Id])]
all_class_constraints ϕ =
  -- map (mapSnd $ nub . concat . map
  --      (\constr -> superclasses ϕ constr ++ [constr])) .
  classConstraints . freetyvars

-- Get all of the class constraints of a list of types. Not sure if
-- it's necessary to do it this way.. since there shouldn't be any
-- duplicate types (and if there were, they would have the same
-- constraints) in the places we are using this currently.
classConstraints :: [Type] -> [(Id, [Id])]
classConstraints = flip foldl [] $
  \acc ty -> case ty of
    TyVar _ ctx nm ->
      case assocGet nm acc of
        Just ctx' -> assocSet nm (ctx ++ ctx') acc
        Nothing -> assocSet nm ctx acc
    _ -> acc

classConstraints' :: [Type] -> [(Id, Id)]
classConstraints' = flattenSnd . classConstraints

-- Build a type scheme from a list of type variables and a body type,
-- where the variables may appear free in the body. Each variable is
-- described by a name and a list of class constraints.
mkTypeScheme :: [(Id, [Id])] -> Bool -> Type -> TypeScheme
mkTypeScheme vars ismethod ty =
  let x = TypeScheme { tyscheme_ty = mkTyAbs (fst <$> vars) ty
                     , tyscheme_vars = vars
                     , tyscheme_ismethod = ismethod } in
    x
    -- debugPrint "\n\nmkTypeScheme" $
    -- debugPrint ("vars: " ++ show vars) $
    -- debugPrint ("ty: " ++ show ty) $
    -- debugPrint ("tyscheme: " ++ show x) x

mkTypeScheme' :: [(Id, Id)] -> Bool -> Type -> TypeScheme
mkTypeScheme' constrs =
  let constrs' = (\l -> (fst (head l), snd <$> l)) <$>
                 groupBy (\x y -> fst x == fst y) constrs in
    mkTypeScheme constrs'


-- mkTypeScheme' :: [(Id, [Id])] -> Type -> TypeScheme
-- mkTypeScheme' vars ty = mkTypeScheme vars ty False

-- mkTypeScheme' :: [(Id, [Id])] -> Type -> TypeScheme
-- mkTypeScheme' constrs ty = mkTypeScheme constrs ty False

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
instantiate_tyscheme fi b (TypeScheme { tyscheme_ty = ty
                                      , tyscheme_vars = vars }) = do
  debugPrint ("\ninstantiate_tyscheme") $
    debugPrint ("ty: " ++ show ty) $
    debugPrint ("vars: " ++ show vars) $ do
    x <- foldM (\acc (nm, ctx) ->
                  TyApp acc <$> TyVar b ctx . Id <$> nextSym "?Y_")
         ty vars
    debugPrint ("x: " ++ show x) $
      debugPrint ("x normalized: " ++ show (normalize_ty x)) $
      return x

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

normalize_ty :: Type -> Type
normalize_ty = typeRec $
  \ty -> case ty of
    TyApp (TyAbs x _ t) s -> tysubst' s (mkTyVar x) t
    _ -> ty

unfold :: Show α => α -> Symtab TypeScheme -> Type -> Type
unfold fi η (TyName nm) =
  case Symtab.get nm η of
    Just tyscheme -> typeOfTypeScheme tyscheme
    Nothing ->
      error $ "Type error: unbound type identifier "
      ++ show nm ++ " at " ++ show fi
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
        -- debugPrint ("\nAPPLYING " ++ show tycon ++ " to " ++ show s) $
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
