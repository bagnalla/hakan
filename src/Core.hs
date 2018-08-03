{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- | This module provides utility functions for working with the inner
-- language (mostly related to evaluation of terms).

module Core (
  TySubstable(..),
  genTypeVars,
  data_of_term,
  data_of_command,
  FreeTyVars(..),
  ConstrSet,
  TypeSubst,
  unify,
  tysubstAll,
  idOfType,
  ) where

import Control.Monad.State
import qualified Data.Traversable as T

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
  else
    -- Failed to unify s and t
    Left (s, t)


-------------------------------
-- | Type variable substitution

class TySubstable a where
  tysubst :: Type -> Type -> a -> a

-- Substitute one type for another (x for y) in a constraint set.
instance TySubstable ConstrSet where
  tysubst x y [] = []
  tysubst x y ((s, t):cs) =
    (if s == y then x else s, if t == y then x else t) : tysubst x y cs

-- Substitute one type for another in a type.
instance TySubstable Type where
  tysubst s t (TyArrow ty1 ty2) =
    TyArrow (tysubst s t ty1) (tysubst s t ty2)
  tysubst s t (TyPair ty1 ty2) =
    TyPair (tysubst s t ty1) (tysubst s t ty2)
  tysubst s t (TySum ty1 ty2) =
    TySum (tysubst s t ty1) (tysubst s t ty2)
  tysubst s t (TyRef ty) = TyRef (tysubst s t ty)
  tysubst s t ty = if ty == t then s else ty

-- Substitute one type for another in a type scheme.
instance TySubstable TypeScheme where
  tysubst s t ts =
    case s of
      TyVar b x -> 
        if x `elem` ts_tyvars_of ts || b then
          -- TODO: why isn't this just ts
          TypeScheme { ts_tyvars_of = ts_tyvars_of ts,
                       ts_ty_of     = ts_ty_of ts }
        else
          ts { ts_ty_of = tysubst s t (ts_ty_of ts) }
      _ -> ts { ts_ty_of = tysubst s t (ts_ty_of ts) }

-- Substitute one type for another in a lambda term.
instance TySubstable α => TySubstable (Term α) where
  tysubst s t (TmAbs fi x ty tm) =
    TmAbs (tysubst s t fi) x (tysubst s t ty) (tysubst s t tm)
  tysubst s t (TmApp fi tm1 tm2) =
    TmApp (tysubst s t fi) (tysubst s t tm1) (tysubst s t tm2)
  tysubst s t (TmIf fi tm1 tm2 tm3) =
    TmIf (tysubst s t fi) (tysubst s t tm1) (tysubst s t tm2)
    (tysubst s t tm3)
  tysubst s t (TmVar fi x)  = TmVar (tysubst s t fi) x
  tysubst s t (TmUnit fi)   = TmUnit (tysubst s t fi)
  tysubst s t (TmBool fi b) = TmBool (tysubst s t fi) b
  tysubst s t (TmInt fi i)  = TmInt (tysubst s t fi) i
  tysubst s t (TmUnop fi u t1) =
    TmUnop (tysubst s t fi) u (tysubst s t t1)
  tysubst s t (TmBinop fi b t1 t2) =
    TmBinop (tysubst s t fi) b (tysubst s t t1) (tysubst s t t2)
  tysubst s t (TmPair fi t1 t2) =
    TmPair (tysubst s t fi) (tysubst s t t1) (tysubst s t t2)
  tysubst s t (TmInl fi tm ty) =
    TmInl (tysubst s t fi) (tysubst s t tm) (tysubst s t ty)
  tysubst s t (TmInr fi tm ty) =
    TmInr (tysubst s t fi) (tysubst s t tm) (tysubst s t ty)
  tysubst s t (TmCase fi discrim nm1 t1 nm2 t2) =
    TmCase (tysubst s t fi) (tysubst s t discrim) nm1 (tysubst s t t1)
    nm2 (tysubst s t t2)
  tysubst s t (TmLet fi x tm1 tm2) =
    TmLet (tysubst s t fi) x (tysubst s t tm1) (tysubst s t tm2)

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

class FreeTyVars a where
  freetyvars :: a -> [Type]


----------------------------------
-- | Free type variables of a type

freeTyVarsAux :: [Id] -> Type -> [Type]
freeTyVarsAux ids = typeRec $
                    \ty -> case ty of
                      TyVar b x -> if x `elem` ids then [TyVar b x] else []
                      _ -> []

instance FreeTyVars Type where
  freetyvars = freeTyVarsAux []

-- Forall quantified type variables of the type scheme are not free
instance FreeTyVars TypeScheme where
  freetyvars ts = freeTyVarsAux (ts_tyvars_of ts) (ts_ty_of ts)


---------------------------------------------------------------
-- | Fill in omitted typed annotations with auto-generated type
-- variables.  Uses prefix "?X_".

class GenTyVars a where
  gentyvars :: a -> State Int a

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
  gentyvars t = return t

-- Generate fresh type variables for a single command
instance GenTyVars (Command α) where
  gentyvars (CDecl fi x ty) = CDecl fi x <$> gentyvars ty
  gentyvars (CLet fi x t) = CLet fi x <$> gentyvars t
  gentyvars (CEval fi t) = CEval fi <$> gentyvars t

-- -- Generate fresh type variables for an entire program.
-- instance GenTyVars (Prog α) where
--   gentyvars p =
--     p { prog_of = fst (runState (T.mapM gentyvars (prog_of p)) 0)}

-- Generate fresh type variables for an entire program.
genTypeVars :: Prog α -> Prog α
genTypeVars p =
  p { prog_of = fst (runState (T.mapM gentyvars (prog_of p)) 0)}

---------
-- | Misc

boolOfTerm :: Term α -> Bool
boolOfTerm (TmBool _ b) = b
boolOfTerm _           = error "boolOf: expected boolean term"

intOfTerm :: Term α -> Integer
intOfTerm (TmInt _ i) = i
intOfTerm _           = error "intOf: expected integer term"

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

data_of_term :: Term α -> α
data_of_term t =
  case t of
    TmVar fi _          -> fi
    TmAbs fi _ _ _      -> fi
    TmApp fi _ _        -> fi
    TmUnit fi           -> fi
    TmBool fi _         -> fi
    TmIf fi _ _ _       -> fi
    TmInt fi _          -> fi
    TmUnop fi _ _       -> fi
    TmBinop fi _ _ _    -> fi
    TmPair fi _ _       -> fi
    TmInl fi _ _        -> fi
    TmInr fi _ _        -> fi
    TmCase fi _ _ _ _ _ -> fi
    TmLet fi _ _ _      -> fi

data_of_command :: Command α -> α
data_of_command c =
  case c of
    CLet fi _ _ -> fi
    CEval fi _   -> fi

term_of_command :: Command α -> Term α
term_of_command c =
  case c of
    CLet _ _ t -> t
    CEval _ t   -> t
