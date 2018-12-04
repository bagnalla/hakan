{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- | This module provides utility functions for working with the inner
-- language (mostly related to evaluation of terms).

module Core (
  genTypeVars, idOfType, isTyVar, fixTy, kindCheck, ctxOfType, isRigid,
  isArrowType, pairOfType, isTyRef, tyOfRefType, isVariantTy, isRecordTy,
  tyargsOfTy, isTyConstructor, isTyApp, constraintOfPlaceholder
  ) where

import Control.Monad.State
import Data.List (nub)
import qualified Data.Traversable as T

import Ast
import Gensym (nextSym)
import Kind (kindCheck)
import Symtab (Id(..), Symtab, map, get)
import Util (debugPrint, mapSnd, isPermutationOf)


-- -- The typechecker monad.
-- type TycheckM a =
--   WriterT [String]
--   (ReaderT Context
--    (ExceptT String
--     (StateT Int Identity))) a


---------------------------------------------------------------
-- | Fill in omitted typed annotations with auto-generated type
-- variables.  Uses prefix "?X_".

class GenTyVars a where
  gentyvars :: a -> State Int a

-- Generate fresh type variables for a type
instance GenTyVars Type where
  gentyvars = typeRecM $
    \ty -> case ty of
      TyVar b k ctx (Id "") -> TyVar b k ctx . Id <$> nextSym "?X_"
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

constraintOfPlaceholder :: Term α -> (Type, ClassNm)
constraintOfPlaceholder (TmPlaceholder _ classNm _ x) = (x, classNm)
constraintOfPlaceholder _ =
  error "constraintOfPlaceholder: expected TmPlaceholder"

idOfType :: Type -> Id
idOfType (TyVar _ _ _ x) = x
idOfType (TyVariant x _ _) = x
idOfType (TyRecord x _ _) = x
idOfType (TyConstructor (TypeConstructor { tycon_name = nm })) = nm
idOfType _ =
  error "idOfType: expected variable, variant, record, or type constructor"

ctxOfType :: Type -> [ClassNm]
ctxOfType (TyVar _ _ ctx _) = ctx
ctxOfType _ = error "ctxOfType: expected type variable"

isTyVar :: Type -> Bool
isTyVar (TyVar _ _ _ _) = True
isTyVar _         = False

isArrowType :: Type -> Bool
isArrowType (TyArrow _ _) = True
isArrowType _ = False

isTyRef :: Type -> Bool
isTyRef (TyRef _) = True
isTyRef _ = False

isVariantTy :: Type -> Bool
isVariantTy (TyVariant _ _ _) = True
isVariantTy _ = False

isRecordTy :: Type -> Bool
isRecordTy (TyRecord _ _ _) = True
isRecordTy _ = False

isTyConstructor :: Type -> Bool
isTyConstructor (TyConstructor _) = True
isTyConstructor _ = False

isTyApp :: Type -> Bool
isTyApp (TyApp _ _) = True
isTyApp _ = False

isRigid :: Type -> Bool
isRigid (TyVar True _ _ _) = True
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
tyargsOfTy (TyConstructor (TypeConstructor { tycon_tyargs = tyargs })) =
  tyargs
tyargsOfTy _ = error "tyargsOfTy: expected variant or record xtype"
