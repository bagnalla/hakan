module Unify (
  ConstrSet, unify,
  ) where

import Data.Bifunctor
import Data.List (nub, union)

import Ast
import Context
import Core
import Symtab (Id(..), Symtab, map, get)
import Util

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

unify :: Show α => α -> Symtab TypeScheme -> Symtab [ClassInstance] ->
         ConstrSet -> Either (Type, Type, String) TypeSubst
unify _ _ _ [] = Right []

-- Rigid type variables refuse to change.
unify fi η ψ ((s', t') : xs) =
  let s = unfold fi η s'
      t = unfold fi η t'
  in
  debugPrint ("s: " ++ show s) $
  debugPrint ("t: " ++ show t) $
  debugPrint ("xs: " ++ show xs) $
  -- debugPrint "unify" $
  -- Ensure equal type variables have the same class constraints since
  -- the Eq instance for types only checks their Ids. Not sure that
  -- this is actually necessary.
  if isTyVar s && isTyVar t && s == t then do
    -- if ctxOfType s `isPermutationOf` ctxOfType t then
    --   unify fi η ψ xs
    -- else
    --   Left (s, t, "Class constraints don't match")
    let (TyVar b ctx x) = t
    let t' = TyVar b (ctx `union` ctxOfType s) x
    rest <- unify fi η ψ $ tysubst' t' s xs
    return $ (t', s) : rest
  else if s == t then
    unify fi η ψ xs
  else if isTyVar s && (not $ isRigid s) &&
          (not $ s `elem` freetyvars t) then
    do
      case t of
        TyVar b ctx x -> do
          let t' = TyVar b (ctx `union` ctxOfType s) x
          rest <- unify fi η ψ $ tysubst' t' s xs
          return $ (t', s) : rest
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
              rest <- unify fi η ψ $ tysubst' t' s xs'
              return $ (t', s) : rest

  -- Just handle the above case and then in this one do a recursive
  -- call with s and t swapped.
  else if isTyVar t && (not $ isRigid t) &&
          (not $ t `elem` freetyvars s) then
    unify fi η ψ $ (t, s) : xs

  else if isArrowType s && isArrowType t then
    let (s1, s2) = pairOfType s
        (t1, t2) = pairOfType t in
      unify fi η ψ $ (s1, t1) : (s2, t2) : xs
  else if isTyRef s && isTyRef t then
    let s' = tyOfRefType s
        t' = tyOfRefType t in
      unify fi η ψ $ (s', t') : xs
  -- else if (isVariantTy s && isVariantTy t ||
  --          isRecordTy s && isRecordTy t) &&
  --         idOfType s == idOfType t then
  --   let s' = tyargsOfTy s
  --       t' = tyargsOfTy t in
  --     unify fi η ψ $ zip s' t' ++ xs
  else if isTyConstructor s && isTyConstructor t &&
          idOfType s == idOfType t then
    let s' = tyargsOfTy s
        t' = tyargsOfTy t in
      unify fi η ψ $ zip s' t' ++ xs
  else if isTyApp s && isTyApp t then
    case (s, t) of
      (TyApp s1@(TyVar _ _ x) s2, TyApp t1@(TyVar _ _ y) t2) ->
        unify fi η ψ $ [(s1, t1), (s2, t2)] ++ xs
      _ -> Left (s, t, "Incompatible types")
  else
    -- Failed to unify s and t
    -- debugPrint ("xs: " ++ show xs) $
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
