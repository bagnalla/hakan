{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- | This module provides utility functions for working with the inner
-- language (mostly related to evaluation of terms).

module Core (
  genTypeVars,
  ConstrSet,
  unify,
  idOfType,
  isTyVar,
  fixTy,
  kindCheck
  ) where

-- import Control.Applicative (liftA2)
import Control.Monad.State
import Data.Bifunctor
import Data.List (nub, union)
import qualified Data.Traversable as T

import Ast
import Gensym (nextSym)
import Symtab (Id(..), Symtab, map, get)
import Util (debugPrint, mapSnd, isPermutationOf)


----------------
-- | Unification

-- The type of constraint sets
type ConstrSet = [(Type, Type)]


-- TODO: unification needs to be aware of all currently known instance
-- declarations in order to do context reduction when a type or type
-- constructor is unified with a type variable that has class
-- constraints. We look up the type instance, the instances it depends
-- on, etc. until all constraints are eliminated (by finding instances
-- for them). Then we know it's safe to unify. When two type variables
-- are unified, we just take the set union of their class
-- constraints. At the end of the day we have either type variables
-- with all necessary class constraints attached, or concrete types
-- which are known to satisfy the necessary class constraints.

unify :: Symtab [ClassInstance] -> ConstrSet ->
         Either (Type, Type, String) TypeSubst
unify _ [] = Right []

-- Rigid type variables refuse to change.
unify ψ ((s, t) : xs) =
  -- Ensure equal type variables have the same class constraints since
  -- the Eq instance for types only checks their Ids. Not sure that
  -- this is actually necessary.
  if isTyVar s && isTyVar t && s == t then
    if ctxOfType s `isPermutationOf` ctxOfType t then
      unify ψ xs
    else
      Left (s, t, "Class constraints don't match")
  else if s == t then
    unify ψ xs
  else if isTyVar s && (not $ isRigid s) &&
          (not $ s `elem` freetyvars t) then
    do
      case t of
        TyVar b ctx x -> do
          rest <- unify ψ $
            tysubst' (TyVar b (ctx `union` ctxOfType s) x) s xs
          return $ (t, s) : rest
        _ -> do
          let ctx = ctxOfType s -- list of Class name Ids
          -- Do context reduction for each class. The type we are
          -- unifying s with must satisfy all of the class constraints
          -- on s.

          -- For each class name, search through the instance database
          -- looking for a match using a simplified unification
          -- algorithm which only unifies type variables and fails if
          -- the structure of the types are not exactly the same
          -- module type variables.

          case resolveInstances ψ t ctx of
            Left classNm ->
              Left (s, t, "Unable to satisfy class constraint " ++
                     show classNm ++ " for type " ++ show t)
            Right constrs -> do
              -- Propagate constraints to type variables in t and xs
              -- before continuing unification.
              let t' = propagateClassConstraints constrs t
              let xs' = bimap (propagateClassConstraints constrs)
                        (propagateClassConstraints constrs) <$> xs
              rest <- unify ψ $ tysubst' t' s xs'
              return $ (t, s) : rest

  -- Just handle the above case and then in this one do a recursive
  -- call with s and t swapped.
  else if isTyVar t && (not $ isRigid t) &&
          (not $ t `elem` freetyvars s) then
    unify ψ $ (t, s) : xs

  else if isBiType s && isBiType t then
    let (s1, s2) = pairOfType s
        (t1, t2) = pairOfType t in
      unify ψ $ (s1, t1) : (s2, t2) : xs
  else if isTyRef s && isTyRef t then
    let s' = tyOfRefType s
        t' = tyOfRefType t in
      unify ψ $ (s', t') : xs
  else if (isVariantTy s && isVariantTy t ||
           isRecordTy s && isRecordTy t) &&
          idOfType s == idOfType t then
    let s' = tyargsOfTy s
        t' = tyargsOfTy t in
      unify ψ $ zip s' t' ++ xs
  else
    -- Failed to unify s and t
    Left (s, t, "Incompatible types")


resolveInstances :: Symtab [ClassInstance] -> Type -> [Id] ->
                    Either Id [(Id, Id)]
resolveInstances ψ ty = fmap concat . (mapM $ resolveInstance ψ ty)


resolveInstance :: Symtab [ClassInstance] -> Type -> Id ->
                   Either Id [(Id, Id)]
resolveInstance ψ ty classNm =
  case Symtab.get classNm ψ of
    Just [] -> Left classNm
    Just insts -> do
      -- This must be wrong. This pattern works if we need all of the
      -- computations to succeed, but here we only need one.
      -- case concat <$> (sequence $ go ψ ty . instance_ty <$> insts) of
      --   Just constrs -> Right constrs
      --   Nothing -> Left classNm
      let res = foldl (\acc x ->
                         case (acc, x) of
                           (Nothing, Just constrs) -> Just constrs
                           (Just constrs, _) -> Just constrs
                           _ -> Nothing)
                Nothing $ go ψ ty . instance_ty <$> insts
      case res of
        Nothing -> Left classNm
        Just constrs -> Right constrs
    Nothing -> Left classNm
  where
    go :: Symtab [ClassInstance] -> Type -> Type -> Maybe [(Id, Id)]
    go ψ (TyVar _ ctx1 x) (TyVar _ ctx2 y) =
      return $ zip (repeat x) (nub $ ctx1 ++ ctx2)
    go ψ s (TyVar _ ctx2 _) =
      -- If the discriminee is not a type variable and the instance
      -- pattern type is, we must find instances of all of the
      -- variable's classes for the discriminee.
      case resolveInstances ψ s ctx2 of
        Left _ -> Nothing
        Right constrs -> Just constrs
    go ψ TyUnit TyUnit = return []
    go ψ TyBool TyBool = return []
    go ψ TyInt TyInt = return []
    go ψ TyChar TyChar = return []
    go ψ (TyRef s) (TyRef t) = go ψ s t
    go ψ (TyArrow s1 t1) (TyArrow s2 t2) =
      pure (++) <*> go ψ s1 s2 <*> go ψ t1 t2
    go ψ
      (TyConstructor (TypeConstructor { tycon_name = nm1,
                                        tycon_tyargs = tyargs1 }))
      (TyConstructor (TypeConstructor { tycon_name = nm2,
                                        tycon_tyargs = tyargs2 })) =
      -- Match if the names are the same and they are applied to the
      -- same number of arguments.
      if nm1 == nm2 && length tyargs1 == length tyargs2 then
        concat <$> sequence ((uncurry $ go ψ) <$> zip tyargs1 tyargs2)
      else
        Nothing
    -- Everything else should fail.
    go _ _ _ = Nothing


-- unify :: ConstrSet -> Either (Type, Type) TypeSubst
-- unify [] = Right []

-- -- Rigid type variables refuse to change.
-- unify ((s, t) : xs) =
--   if s == t then
--     unify xs
--   else if isTyVar s && (not $ isRigid s) &&
--           (not $ s `elem` freetyvars t) then
--     do
--       rest <- unify $ tysubst' t s xs
--       return $ (t, s) : rest
--   else if isTyVar t && (not $ isRigid t) &&
--           (not $ t `elem` freetyvars s) then
--     do
--       rest <- unify $ tysubst' s t xs
--       return $ (s, t) : rest
--   else if isBiType s && isBiType t then
--     let (s1, s2) = pairOfType s
--         (t1, t2) = pairOfType t in
--       unify $ (s1, t1) : (s2, t2) : xs
--   else if isTyRef s && isTyRef t then
--     let s' = tyOfRefType s
--         t' = tyOfRefType t in
--       unify $ (s', t') : xs
--   else if (isVariantTy s && isVariantTy t ||
--            isRecordTy s && isRecordTy t) &&
--           idOfType s == idOfType t then
--     let s' = tyargsOfTy s
--         t' = tyargsOfTy t in
--       unify $ zip s' t' ++ xs
--   else
--     -- Failed to unify s and t
--     Left (s, t)

-- -- Rigid type variables refuse to change.
-- unify ((s, t) : xs) =
--   debugPrint ("unifying " ++ show s ++ "  with " ++ show t) $
--   if s == t then
--     unify xs
--   else if isTyVar s && (not $ isRigid s) &&
--           (not $ s `elem` freetyvars t) then
--     debugPrint "unify s 1" $ do
--     let xs' = tysubst' t s xs
--     debugPrint "unify s 2" $ do
--       rest <- unify xs'
--       debugPrint "unify s 3" $ do
--         return $ (t, s) : rest
--   else if isTyVar t && (not $ isRigid t) &&
--           (not $ t `elem` freetyvars s) then
--     debugPrint "unify t" $ do
--     rest <- unify $ tysubst' s t xs
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


-- -------------------------------
-- -- | Type variable substitution

-- -- The boolean determines whether to do capture avoiding substitution
-- -- or not. Not sure if it's necessary anymore since we stopped
-- -- explicitly tying the knot on recursive types.
-- class TySubstable a where
--   tysubst :: Bool -> Type -> Type -> a -> a

-- -- Lift type substitution to lists.
-- instance TySubstable a => TySubstable [a] where
--   tysubst b s t = fmap $ tysubst b s t

-- -- Lift type substitution to any bifunctor (e.g., pair). It would be
-- -- nice to use a similar instance for functors so we don't need the
-- -- list instance but then we have overlapping instances (incoherent
-- -- instances?) for Term.
-- instance (Bifunctor f, TySubstable a, TySubstable b) =>
--          TySubstable (f a b) where
--   tysubst b s t = bimap (tysubst b s t) (tysubst b s t)

-- -- Substitute one type for another in a type.
-- instance TySubstable Type where
--   tysubst b s t ty@(TyAbs x k ty1) =
--     if t == mkTyVar x then ty else
--       if b && mkTyVar x `elem` freetyvars s then
--       -- I don't think type variables from local binders should ever
--       -- have class constraints. Otherwise we need to copy over the
--       -- constraints from x here.
--       let x' = Id $ unId x ++ "_" in
--         TyAbs x' k $ tysubst b s t
--         (tysubst b (mkTyVar x') (mkTyVar x) ty1)
--       else
--         TyAbs x k $ tysubst b s t ty1
--   tysubst b s t (TyApp ty1 ty2) =
--     TyApp (tysubst b s t ty1) (tysubst b s t ty2)
--   tysubst b s t (TyArrow ty1 ty2) =
--     TyArrow (tysubst b s t ty1) (tysubst b s t ty2)
--   tysubst b s t (TyRef ty) = TyRef (tysubst b s t ty)
--   tysubst b s t (TyVariant x tyargs ctors) =
--     TyVariant x (tysubst b s t <$> tyargs) $
--     fmap (mapSnd $ fmap $ tysubst b s t) ctors
--   tysubst b s t (TyRecord x tyargs fields) =
--     TyRecord x (tysubst b s t <$> tyargs) $
--     fmap (mapSnd $ tysubst b s t) fields
--   tysubst _ s t ty = if ty == t then s else ty

-- -- Substitute one type for another in a lambda term.
-- instance TySubstable α => TySubstable (Term α) where
--   tysubst b s t = termTypeRec $ tysubst b s t

-- -- Substitute one type for another in a typing context.
-- instance (TySubstable β) => TySubstable (Symtab β) where
--   tysubst b s t = Symtab.map (tysubst b s t)

-- tysubst' :: TySubstable a => Type -> Type -> a -> a
-- tysubst' =
--   debugPrint "tysubst'" $
--   tysubst True

-- -- Fold over a list of individual substitutions on an instance of
-- -- TySubstClass.
-- tysubstAll :: TySubstable a => Bool -> TypeSubst -> a -> a
-- tysubstAll b tsubst x =
--   foldl (\acc (s, t) -> tysubst b s t acc) x tsubst

-- tysubstAll' :: TySubstable a => TypeSubst -> a -> a
-- tysubstAll' tsubst x =
--   foldl (\acc (s, t) -> tysubst' s t acc) x tsubst


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


---------------------------------------------------------------
-- | Fill in omitted typed annotations with auto-generated type
-- variables.  Uses prefix "?X_".

class GenTyVars a where
  gentyvars :: a -> State Int a

-- Generate fresh type variables for a type
instance GenTyVars Type where
  gentyvars = typeRecM $
    \ty -> case ty of
      TyVar b ctx (Id "") -> TyVar b ctx . Id <$> nextSym "?X_"
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
-- abstractTy x ty s = tysubst False s (TyVar False x) ty
abstractTy x ty s = tysubst' s (mkTyVar x) ty

abstractTys :: [Id] -> [Type] -> [Type] -> [Type]
abstractTys xs tys tys' =
  Prelude.map (\ty -> foldl f ty (zip xs tys')) tys
  where f acc (x, ty) =
          -- tysubst False (TyVar False x) ty acc
          tysubst' (mkTyVar x) ty acc

fixTy :: Id -> Type -> Type
fixTy x ty = fix (abstractTy x ty)

fixTys :: [Id] -> [Type] -> [Type]
fixTys xs tys =
  fix (abstractTys xs tys) 


---------
-- | Misc

boolOfTerm :: Term α -> Bool
boolOfTerm (TmBool _ b) = b
boolOfTerm _ = error "boolOfTerm: expected boolean term"

intOfTerm :: Term α -> Integer
intOfTerm (TmInt _ i) = i
intOfTerm _ = error "intOfTerm: expected integer term"

charOfTerm :: Term α -> Char
charOfTerm (TmChar _ c) = c
charOfTerm _ = error "charOfTerm: expected char term"

idOfType :: Type -> Id
idOfType (TyVar _ _ x) = x
idOfType (TyVariant x _ _) = x
idOfType (TyRecord x _ _) = x
idOfType _ = error "idOfType: expected variable, variant, or record type"

ctxOfType :: Type -> [Id]
ctxOfType (TyVar _ ctx _) = ctx
ctxOfType _ = error "ctxOfType: expected type variable"

isTyVar :: Type -> Bool
isTyVar (TyVar _ _ _) = True
isTyVar _         = False

isBiType :: Type -> Bool
isBiType (TyArrow _ _) = True
isBiType _ = False

isTyRef :: Type -> Bool
isTyRef (TyRef _) = True
isTyRef _ = False

isVariantTy :: Type -> Bool
isVariantTy (TyVariant _ _ _) = True
isVariantTy _ = False

isRecordTy :: Type -> Bool
isRecordTy (TyRecord _ _ _) = True
isRecordTy _ = False

isRigid :: Type -> Bool
isRigid (TyVar True _ _) = True
isRigid _ = False

pairOfType :: Type -> (Type, Type)
pairOfType (TyArrow s t) = (s, t)
pairOfType _ = error "pairOfType: expected arrow or pair type"

tyOfRefType :: Type -> Type
tyOfRefType (TyRef t) = t
tyOfRefType _ = error "tyOfRef: expected ref type"

tyargsOfTy :: Type -> [Type]
tyargsOfTy (TyVariant _ tyargs _) = tyargs
tyargsOfTy (TyRecord _ tyargs _) = tyargs
tyargsOfTy _ = error "tyargsOfTy: expected variant or record xtype"
