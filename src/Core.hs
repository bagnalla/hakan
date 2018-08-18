{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- | This module provides utility functions for working with the inner
-- language (mostly related to evaluation of terms).

module Core (
  TySubstable(..),
  genTypeVars,
  FreeTyVars(..),
  ConstrSet,
  TypeSubst,
  unify,
  tysubstAll,
  idOfType,
  isTyVar,
  fixTy,
  normalize,
  kindCheck
  ) where

-- import Control.Applicative (liftA2)
import Control.Monad.State
import Data.Bifunctor
import Data.List (nub)
import qualified Data.Traversable as T

import Ast
import Gensym (nextSym)
import Symtab (Id(..), Symtab, map)
import Util (debugPrint)

----------------
-- | Unification

-- The type of constraint sets
type ConstrSet = [(Type, Type)]

-- The type of type substitutions
type TypeSubst = [(Type, Type)]

unify :: ConstrSet -> Either (Type, Type) TypeSubst
-- unify [] = Right []
unify [] = debugPrint "unify terminating" $ Right []

-- Rigid type variables refuse to change.
unify ((s, t) : xs) =
  if s == t then
    unify xs
  else if isTyVar s && (not $ isRigid s) &&
          (not $ s `elem` freetyvars t) then
    do
      rest <- unify $ tysubst t s xs
      return $ (t, s) : rest
  else if isTyVar t && (not $ isRigid t) &&
          (not $ t `elem` freetyvars s) then
    do
      rest <- unify $ tysubst s t xs
      return $ (s, t) : rest
  else if isBiType s && isBiType t then
    let (s1, s2) = pairOfType s
        (t1, t2) = pairOfType t in
      unify $ (s1, t1) : (s2, t2) : xs
  else if isTyRef s && isTyRef t then
    let s' = tyOfRefType s
        t' = tyOfRefType t in
      unify $ (s', t') : xs
  else if isVariantTy s && isVariantTy t &&
          idOfTy s == idOfTy t then
    let s' = tyargsOfTy s
        t' = tyargsOfTy t in
      unify $ zip s' t' ++ xs
  else
    -- Failed to unify s and t
    Left (s, t)

-- -- Rigid type variables refuse to change.
-- unify ((s, t) : xs) =
--   debugPrint ("unifying " ++ show s ++ "  with " ++ show t) $
--   if s == t then
--     unify xs
--   else if isTyVar s && (not $ isRigid s) &&
--           (not $ s `elem` freetyvars t) then
--     debugPrint "unify s 1" $ do
--     let xs' = tysubst t s xs
--     debugPrint "unify s 2" $ do
--       rest <- unify xs'
--       debugPrint "unify s 3" $ do
--         return $ (t, s) : rest
--   else if isTyVar t && (not $ isRigid t) &&
--           (not $ t `elem` freetyvars s) then
--     debugPrint "unify t" $ do
--     rest <- unify $ tysubst s t xs
--     debugPrint "unify t after" $ do
--       return $ (s, t) : rest
--   else if isBiType s && isBiType t then
--     debugPrint "unify pair" $ do
--     let (s1, s2) = pairOfType s
--         (t1, t2) = pairOfType t in
--       unify $ (s1, t1) : (s2, t2) : xs
--   else if isTyRef s && isTyRef t then
--     debugPrint "unify ref" $ do
--     let s' = tyOfRefType s
--         t' = tyOfRefType t in
--       unify $ (s', t') : xs
--   else if isVariantTy s && isVariantTy t &&
--           idOfTy s == idOfTy t then
--     debugPrint "unify variant" $
--     let s' = tyargsOfTy s
--         t' = tyargsOfTy t in
--       debugPrint ("s': " ++ show s') $
--       debugPrint ("t': " ++ show t') $
--       unify $ zip s' t' ++ xs
--   else
--     -- Failed to unify s and t
--     Left (s, t)


-------------------------------
-- | Type variable substitution

class TySubstable a where
  tysubst :: Type -> Type -> a -> a

-- Lift type substitution to lists.
instance TySubstable a => TySubstable [a] where
  tysubst s t = fmap $ tysubst s t

-- Lift type substitution to any bifunctor (e.g., pair). It would be
-- nice to use a similar instance for functors so we don't need the
-- list instance but then we have overlapping instances (incoherent
-- instances?) for Term.
instance (Bifunctor f, TySubstable a, TySubstable b) =>
         TySubstable (f a b) where
  tysubst s t = bimap (tysubst s t) (tysubst s t)

-- Substitute one type for another in a type.
instance TySubstable Type where
  tysubst s t = typeRec $ \ty -> if ty == t then s else ty

-- Substitute one type for another in a lambda term.
instance TySubstable α => TySubstable (Term α) where
  tysubst s t = termTypeRec $ tysubst s t

-- Substitute one type for another in a typing context.
instance (TySubstable β) => TySubstable (Symtab β) where
  tysubst s t = Symtab.map (tysubst s t)

-- Fold over a list of individual substitutions on an instance of
-- TySubstClass.
tysubstAll :: TySubstable a => TypeSubst -> a -> a
tysubstAll tsubst x =
  foldl (\acc (s, t) -> tysubst s t acc) x tsubst


--------------------------
-- | Well-kindedness check

-- Assume type variables have kind *.
kindCheck :: Type -> Maybe Kind
kindCheck (TyAbs _ k s) = KArrow k <$> (kindCheck s)
kindCheck (TyApp s t) = do
  s' <- kindCheck s
  t' <- kindCheck t
  case s' of
    KArrow s'' t'' -> if s'' == t' then return t'' else Nothing
    _ -> Nothing
kindCheck _ = Just KStar


-----------------------
-- | Type normalization

-- I think it's fine to use the recursion scheme for this.
normalize :: Type -> Type
normalize = typeRec $
  \ty -> case ty of
    TyApp (TyAbs x _ t) s -> tysubst s (TyVar False x) t
    _ -> ty


-------------------------
-- | Free type variables

class FreeTyVars a where
  freetyvars :: a -> [Type]

-- NOTE: remember to update this when extending the language types,
-- since it isn't using any of the recursion schemes or catamorphisms.

-- This isn't the most satisfying solution... we just use a depth
-- bound to avoid infinite cycles in recursive types. It would be nice
-- to somehow determine a minimum (or approximately minimum) value of
-- d necessary to sufficiently search a type. The current solution is
-- 1) inefficient, and 2) potentially unsound for very large types.
instance FreeTyVars Type where
  freetyvars = nub . go [] 100
    where
      go :: [Type] -> Int -> Type -> [Type]
      go _ d _ | d <= 0 = []
      go xs d ty@(TyVar _ _) = if ty `elem` xs then [] else [ty]
      go xs d (TyAbs x _ s) = go (TyVar False x : xs) (d-1) s
      go xs d (TyApp s t) = go xs (d-1) s ++ go xs (d-1) t
      go xs d (TyArrow s t) = go xs (d-1) s ++ go xs (d-1) t
      go xs d (TyPair s t) = go xs (d-1) s ++ go xs (d-1) t
      go xs d (TyRef s) = go xs (d-1) s
      go xs d (TyVariant _ tyargs ctors) =
        -- debugPrint (show d) $
        concat (go xs (d-1) <$> tyargs) ++
        concat (go xs (d-1) <$> (concat $ snd $ unzip ctors))
      go _ _ _ = []

---------------------------------------------------------------
-- | Fill in omitted typed annotations with auto-generated type
-- variables.  Uses prefix "?X_".

class GenTyVars a where
  gentyvars :: a -> State Int a

-- Generate fresh type variables for a type
instance GenTyVars Type where
  gentyvars = typeRecM $
    \ty -> case ty of
      TyVar b (Id "") -> TyVar b . Id <$> nextSym "?X_"
      _ -> return ty
  
-- Generate fresh type variables for a single term (including its
-- subterms).
instance GenTyVars (Term α) where
  gentyvars = termTypeRecM gentyvars

instance GenTyVars Pattern where
  gentyvars = return

-- Generate fresh type variables for a single command
instance GenTyVars (Command α) where
  gentyvars = commandTypeRecM gentyvars

-- Generate fresh type variables for an entire program.
genTypeVars :: Prog α -> Prog α
genTypeVars p =
  p { prog_of = fst (runState (T.mapM gentyvars (prog_of p)) 0)}


--------------------------
-- | Recursive type stuff

abstractTy :: Id -> Type -> Type -> Type
abstractTy x ty s = tysubst s (TyVar False x) ty

abstractTys :: [Id] -> [Type] -> [Type] -> [Type]
abstractTys xs tys tys' =
  Prelude.map (\ty -> foldl f ty (zip xs tys')) tys
  where f acc (x, ty) =
          tysubst (TyVar False x) ty acc

fixTy :: Id -> Type -> Type
fixTy x ty = fix (abstractTy x ty)

fixTys :: [Id] -> [Type] -> [Type]
fixTys xs tys =
  fix (abstractTys xs tys) 


---------
-- | Misc

boolOfTerm :: Term α -> Bool
boolOfTerm (TmBool _ b) = b
boolOfTerm _ = error "boolOf: expected boolean term"

intOfTerm :: Term α -> Integer
intOfTerm (TmInt _ i) = i
intOfTerm _ = error "intOf: expected integer term"

idOfType :: Type -> Maybe Id
idOfType (TyVar _ x) = Just x
idOfType _           = Nothing

isTyVar :: Type -> Bool
isTyVar (TyVar _ _) = True
isTyVar _         = False

isBiType :: Type -> Bool
isBiType (TyArrow _ _) = True
isBiType (TyPair _ _)  = True
isBiType _ = False

isTyRef :: Type -> Bool
isTyRef (TyRef _) = True
isTyRef _ = False

isVariantTy :: Type -> Bool
isVariantTy (TyVariant _ _ _) = True
isVariantTy _ = False

isRigid :: Type -> Bool
isRigid (TyVar True _) = True
isRigid _ = False

pairOfType :: Type -> (Type, Type)
pairOfType (TyArrow s t) = (s, t)
pairOfType (TyPair s t)  = (s, t)
pairOfType _ = error "pairOfType: expected arrow or pair type"

tyOfRefType :: Type -> Type
tyOfRefType (TyRef t) = t
tyOfRefType _ = error "tyOfRef: expected ref type"

idOfTy :: Type -> Id
idOfTy (TyVar _ x) = x
idOfTy (TyVariant x _ _) = x
idOfTy _ = error "idOfTy: expected variable or variant type"

tyargsOfTy :: Type -> [Type]
tyargsOfTy (TyVariant _ tyargs _) = tyargs
tyargsOfTy _ = error "tyargsOfTy: expected variant type"
