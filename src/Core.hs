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
  fixTy
  ) where

import Control.Applicative (liftA2)
import Control.Monad.State
import Data.Bifunctor
import Data.List (nub)
import qualified Data.Traversable as T
-- import System.IO.Unsafe

import Ast
import Gensym (nextSym)
import Symtab (Id(..), Symtab(..), map)


----------------
-- | Unification

-- The type of constraint sets
type ConstrSet = [(Type, Type)]

-- The type of type substitutions
type TypeSubst = [(Type, Type)]

unify :: ConstrSet -> Either (Type, Type) TypeSubst
unify [] = Right []

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
    let s' = tysOfTy s
        t' = tysOfTy t in
      unify $ zip s' t' ++ xs
  else
    -- Failed to unify s and t
    Left (s, t)

-- -- Rigid type variables refuse to change.
-- unify ((s, t) : xs) =
--   if s == t then
--     unify xs
--   else if isTyVar s && (not $ isRigid s) &&
--           (not $ s `elem` freetyvars t) then
--     seq (unsafePerformIO $ putStrLn $ show xs) $
--     seq (unsafePerformIO $ putStrLn $ show (t, s)) $
--     seq (unsafePerformIO $ putStrLn $ show $ tysubst t s xs) $ do
--     rest <- unify $ tysubst t s xs
--     return $ (t, s) : rest
--   else if isTyVar t && (not $ isRigid t) &&
--           (not $ t `elem` freetyvars s) then
--     seq (unsafePerformIO $ putStrLn $ show xs) $
--     seq (unsafePerformIO $ putStrLn $ show (s, t)) $
--     seq (unsafePerformIO $ putStrLn $ show $ tysubst s t xs) $ do
--       rest <- unify $ tysubst s t xs
--       return $ (s, t) : rest
--   else if isBiType s && isBiType t then
--     let (s1, s2) = pairOfType s
--         (t1, t2) = pairOfType t in
--       unify $ (s1, t1) : (s2, t2) : xs
--   else if isTyRef s && isTyRef t then
--     let s' = tyOfRefType s
--         t' = tyOfRefType t in
--       unify $ (s', t') : xs
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

-- Substitute one type for another in a type scheme.
instance TySubstable TypeScheme where
  tysubst s t ts =
    case s of
      TyVar b x -> 
        if x `elem` ts_tyvars_of ts || b then ts
        else ts { ts_ty_of = tysubst s t (ts_ty_of ts) }
      _ -> ts { ts_ty_of = tysubst s t (ts_ty_of ts) }

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


-- Not used currently since we moved from substitution to closure
-- semantics.
-- class FreeVars a where freevars :: a -> [Id]

-----------------------------
-- | Free variables of a term

-- instance FreeVars (Term α) where
--   freevars = aux []
--     where
--       aux bv (TmVar _ x)      = if x `elem` bv then [] else [x]
--       aux bv (TmAbs _ x _ t)  = aux (x:bv) t
--       aux bv (TmApp _ t1 t2)   = aux bv t1 ++ aux bv t2
--       aux bv (TmIf _ t1 t2 t3) = aux bv t1 ++ aux bv t2 ++ aux bv t3
--       aux _ _                  = []


-------------------------
-- | Free type variables

class FreeTyVars a where
  freetyvars :: a -> [Type]

freeTyVarsAux :: [Id] -> Type -> [Type]
freeTyVarsAux ids = typeRec2 $
                    \ty -> case ty of
                      TyVar b x -> if x `elem` ids then []
                                   else [TyVar b x]
                      _ -> []

instance FreeTyVars Type where
  freetyvars = nub . freeTyVarsAux []

-- Forall quantified type variables of the type scheme are not free
instance FreeTyVars TypeScheme where
  freetyvars ts = nub $ freeTyVarsAux (ts_tyvars_of ts) (ts_ty_of ts)


---------------------------------------------------------------
-- | Fill in omitted typed annotations with auto-generated type
-- variables.  Uses prefix "?X_".

-- TODO: monadic catamorphisms to generalize these operations?

class GenTyVars a where
  gentyvars :: a -> State Int a

instance GenTyVars Id where
  gentyvars = return

instance GenTyVars a => GenTyVars [a] where
  gentyvars = mapM gentyvars

instance (GenTyVars a, GenTyVars b) => GenTyVars (a, b) where
  gentyvars = uncurry (liftA2 (,)) . bimap gentyvars gentyvars

-- Generate fresh type variables for a type
instance GenTyVars Type where
  gentyvars (TyVar b (Id "")) = do
    id' <- nextSym "?X_"
    return (TyVar b (Id id'))
  gentyvars (TyArrow ty1 ty2) =
    pure TyArrow <*> gentyvars ty1 <*> gentyvars ty2
  gentyvars (TyPair ty1 ty2) =
    pure TyPair <*> gentyvars ty1 <*> gentyvars ty2
  gentyvars (TySum ty1 ty2) =
    pure TySum <*> gentyvars ty1 <*> gentyvars ty2
  gentyvars (TyRef ty) = TyRef <$> gentyvars ty
  gentyvars (TyVariant nm tyvars ctors) =
    TyVariant nm tyvars <$> gentyvars ctors
  gentyvars ty = return ty

-- Generate fresh type variables for a single term (including its
-- subterms).
instance GenTyVars (Term α) where
  gentyvars (TmAbs fi x ty t) =
    pure (TmAbs fi x) <*> gentyvars ty <*> gentyvars t
  gentyvars (TmApp fi t1 t2) =
    pure (TmApp fi) <*> gentyvars t1 <*> gentyvars t2
  gentyvars (TmIf fi t1 t2 t3) =
    pure (TmIf fi) <*> gentyvars t1 <*> gentyvars t2 <*> gentyvars t3
  gentyvars (TmUnop fi u t) = TmUnop fi u <$> gentyvars t
  gentyvars (TmBinop fi b t1 t2) =
    pure (TmBinop fi b) <*> gentyvars t1 <*> gentyvars t2
  gentyvars (TmPair fi t1 t2) =
    pure (TmPair fi) <*> gentyvars t1 <*> gentyvars t2
  gentyvars (TmInl fi tm ty) =
    pure (TmInl fi) <*> gentyvars tm <*> gentyvars ty
  gentyvars (TmInr fi tm ty) =
    pure (TmInr fi) <*> gentyvars tm <*> gentyvars ty
  gentyvars (TmCase fi discrim nm1 tm1 nm2 tm2) = do
    discrim' <- gentyvars discrim
    tm1' <- gentyvars tm1
    tm2' <- gentyvars tm2
    return $ TmCase fi discrim' nm1 tm1' nm2 tm2'
  gentyvars (TmLet fi x tm1 tm2) =
    pure (TmLet fi x) <*> gentyvars tm1 <*> gentyvars tm2
  gentyvars (TmVariant fi nm tm) =
    TmVariant fi nm <$> gentyvars tm
  gentyvars (TmMatch fi discrim cases) =
    pure (TmMatch fi) <*> gentyvars discrim <*> gentyvars cases    
  gentyvars t@(TmVar _ _) = return t
  gentyvars t@(TmUnit _) = return t
  gentyvars t@(TmBool _ _) = return t
  gentyvars t@(TmInt _ _) = return t

instance GenTyVars Pattern where
  gentyvars = return

-- Generate fresh type variables for a single command
instance GenTyVars (Command α) where
  gentyvars (CDecl fi x ty) = CDecl fi x <$> gentyvars ty
  gentyvars (CLet fi x t) = CLet fi x <$> gentyvars t
  gentyvars (CEval fi t) = CEval fi <$> gentyvars t
  gentyvars (CData fi nm tyvars ctors) =
    CData fi nm tyvars <$> gentyvars ctors

-- -- Generate fresh type variables for an entire program.
-- instance GenTyVars (Prog α) where
--   gentyvars p =
--     p { prog_of = fst (runState (T.mapM gentyvars (prog_of p)) 0)}

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
isBiType (TySum _ _)   = True
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
pairOfType (TySum s t)   = (s, t)
pairOfType _ = error "pairOfType: expected arrow, pair, or sum type"

tyOfRefType :: Type -> Type
tyOfRefType (TyRef t) = t
tyOfRefType _ = error "tyOfRef: expected ref type"

idOfTy :: Type -> Id
idOfTy (TyVar _ x) = x
idOfTy (TyVariant x _ _) = x
idOfTy _ = error "idOfTy: expected variable or variant type"

tysOfTy :: Type -> [Type]
tysOfTy (TyVariant _ _ ctors) = concat $ snd <$> ctors
tysOfTy _ = error "tysOfTy: expected variant type"
