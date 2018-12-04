{-# LANGUAGE FlexibleContexts #-}

module Context (
  Context(..), TypeScheme, unfold, instantiate_tyscheme,
  mkTypeScheme, initCtx, updDecls, updGamma, open_tyscheme, updClasses,
  typeOfTypeScheme, instantiate_tyscheme', mkTypeScheme',
  isMethod, updInstances, classConstraints, normalize_ty, varsOfTypeScheme,
  superclasses, all_class_constraints, constrsOfTypeScheme, generalize_ty,
  resolveTyNames, updKinds, addConstraintsToTypeScheme
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Data.List (groupBy, intercalate, nub)
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
  ctx_instances :: Symtab [ClassInstance],
  -- map named types to their kinds (ι)
  ctx_kinds :: Symtab Kind
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
                  , ctx_instances = empty
                  , ctx_kinds = empty }

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

updKinds :: (Symtab Kind -> Symtab Kind) -> Context -> Context
updKinds f ctx = ctx { ctx_kinds = f $ ctx_kinds ctx }

-----------------
-- | Type schemes

-- We don't export the TypeScheme constructor, so the only way to
-- construct one from outside of this module is through the
-- mkTypeScheme function. This is a really thin layer of abstraction
-- that doesn't do much.. it could probably be improved.

-- For each type variable we store its name (as bound in the type) and
-- list of class constraints.

-- tyscheme_vars tells us the dictionary arguments that the term
-- should take, and in what order.
data TypeScheme =
  TypeScheme { tyscheme_ty :: Type
             , tyscheme_vars :: [(Id, Kind, [ClassNm])]

             -- This is so we know when to replace a method call with
             -- a placeholder when typechecking.
             , tyscheme_ismethod :: Bool }
  deriving Eq

typeOfTypeScheme :: TypeScheme -> Type
typeOfTypeScheme = tyscheme_ty

varsOfTypeScheme :: TypeScheme -> [(Id, Kind, [ClassNm])]
varsOfTypeScheme = tyscheme_vars

constrsOfTypeScheme :: TypeScheme -> [(Id, Kind, ClassNm)]
constrsOfTypeScheme = flattenThird . tyscheme_vars

isMethod :: TypeScheme -> Bool
isMethod (TypeScheme { tyscheme_ismethod = b }) = b

instance TySubstable TypeScheme where
  tysubst b s t tyscheme@(TypeScheme { tyscheme_ty = ty }) =
     tyscheme { tyscheme_ty = tysubst b s t ty }

instance FreeTyVars TypeScheme where
    freetyvars = freetyvars . tyscheme_ty

instance Show TypeScheme where
  show (TypeScheme { tyscheme_ty = ty, tyscheme_vars = vars }) =
    "(TypeScheme " ++ showTypeLight ty ++ " [" ++
    intercalate ", " (show <$> vars) ++ "])"


-- Recursively get all superclasses
superclasses :: Symtab TypeClass -> ClassNm -> [ClassNm]
superclasses ϕ classNm = do
  case Symtab.get (unClassNm classNm) ϕ of
    Just (TypeClass { tyclass_constrs = constrs
                    , tyclass_index = tyIndex }) ->
      concat (superclasses ϕ <$> constrs) ++ constrs
    Nothing ->
      error $ "superclasses: class " ++ show classNm ++
      " not found. Known classes:\n" ++ show ϕ


addConstraintsToTypeScheme :: [(Id, Kind, ClassNm)] -> TypeScheme -> TypeScheme
addConstraintsToTypeScheme constrs ts@(TypeScheme { tyscheme_vars = vars }) =
  ts { tyscheme_vars =
       flattenTuple3 <$> (go constrs (unflattenTuple3 <$> vars)) }
  where
    go [] vars = vars
    go ((x, k, classNm):xs) vars =
      case assocGet x $ go xs vars of
        Just (k', ys) -> assocSet x (k', (nub $ classNm : ys)) vars
        Nothing -> assocSet x (k, [classNm]) vars

generalize_ty :: Bool -> Type -> TypeScheme
generalize_ty ismethod ty =
  mkTypeScheme (classConstraints $ freetyvars ty) ismethod ty


all_class_constraints :: Type -> [(Id, Kind, [ClassNm])]
all_class_constraints =
  classConstraints . freetyvars


-- Get all of the class constraints of a list of types. Not sure if
-- it's necessary to do it this way.. since there shouldn't be any
-- duplicate types (and if there were, they would have the same
-- constraints) in the places we are using this currently. We assume
-- any two occurrences have the same kind.
classConstraints :: [Type] -> [(Id, Kind, [ClassNm])]
classConstraints = map flattenTuple3 . (flip foldl [] $
  \acc ty -> case ty of
    TyVar _ k ctx nm ->
      case assocGet nm acc of
        Just (_, ctx') -> assocSet nm (k, ctx ++ ctx') acc
        Nothing -> assocSet nm (k, ctx) acc
    _ -> acc)


-- Build a type scheme from a list of type variables and a body type,
-- where the variables may appear free in the body. Each variable is
-- described by a name and a list of class constraints.
mkTypeScheme :: [(Id, Kind, [ClassNm])] -> Bool -> Type -> TypeScheme
mkTypeScheme vars ismethod ty =
  let x = TypeScheme { tyscheme_ty =
                       mkTyAbs ((\(x, y, z) -> (x, y)) <$> vars) ty
                     , tyscheme_vars = vars
                     , tyscheme_ismethod = ismethod } in
    x

-- Assume all variables with the same Id have the same kind.
mkTypeScheme' :: [(Id, Kind, ClassNm)] -> Bool -> Type -> TypeScheme
mkTypeScheme' constrs =
  let constrs' = (\l -> (fst3 (head l), snd3 (head l), thd3 <$> l)) <$>
                 groupBy (\x y -> fst3 x == fst3 y) constrs in
    mkTypeScheme constrs'


-- Strip off type abstractions, leaving the body unchanged.
open_tyscheme :: TypeScheme -> Type
open_tyscheme (TypeScheme { tyscheme_ty = ty }) = go ty
  where
    go :: Type -> Type
    go (TyAbs _ _ s) = go s
    go t = t


-- Passing False for the type variables rigidness doesn't matter since
-- the Eq instance for types ignores it.
instantiate_tyscheme :: (Show α, Num s, Show s, MonadState s m) =>
                        α -> Bool -> TypeScheme -> m Type
instantiate_tyscheme _ b (TypeScheme { tyscheme_ty = ty
                                     , tyscheme_vars = vars }) = do
  x <- foldM (\acc (nm, k, ctx) ->
                 TyApp acc <$> TyVar b k ctx . Id <$> nextSym "?Y_")
       ty vars
  return x

instantiate_tyscheme' :: (Show α, Num s, Show s, MonadState s m) =>
                         α -> TypeScheme -> m Type
instantiate_tyscheme' fi = instantiate_tyscheme fi False


-----------------------
-- | Type normalization

normalize_ty :: Type -> Type
normalize_ty = typeRec $
  \ty -> case ty of
    -- Regular old application of type abstractions.
    TyApp (TyAbs x _ t) s -> tysubst' s (mkTyVar x) t
    -- Type constructors can be applied.
    TyApp s@(TyConstructor _) t ->
      case applyTypeConstructor s t of
        TyConstructor tycon@(TypeConstructor { tycon_instantiated = u }) ->
          TyConstructor $ tycon { tycon_instantiated = normalize_ty u }
        _ -> ty
    -- Like eta reduction to remove abstractions from the outside of
    -- type constructors (unapplying the arguments to the type
    -- constructor).
    TyAbs x _ (TyConstructor _) -> etaReduceTypeConstructor ty
    -- Eta reduction
    TyAbs x _ (TyApp s (TyVar _ _ _ y)) ->
      debugPrint ("normalize_ty: " ++ show x ++ " " ++ show y) $
      if x == y then s else ty
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
                          , tycon_ty = inst
                          , tycon_instantiated = t }) ->
      if length tyvars == length tyargs then
        error $ "unfold: type constructor " ++ show tycon ++
        " is already fully applied"
      else
        let s' = unfold fi η s in
          TyConstructor $
          tycon { tycon_kinds = kinds ++ [KStar]
                , tycon_tyargs = tyargs ++ [s']
                , tycon_ty = unfold fi η inst
                , tycon_instantiated = unfold fi η $ TyApp t s' }
    _ -> 
      TyApp (unfold fi η ty) $ unfold fi η s
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
