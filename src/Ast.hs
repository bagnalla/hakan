{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}

-- | This module defines the internal language syntax.

-- Maybe we should make everything implicitly recursive (always
-- letrec), including mutual recursion. So all of the definitions in a
-- module are mutually recursive. We may also want an actual module
-- system.

-- I wonder if it's a good idea to treat sequencing specially instead
-- of just making it a derived form that desugars to
-- application. Maybe we will just detect the intro/elim pattern of
-- unit thunk sequencing and treat it specially in a different
-- representation during compilation.

-- TODO:
-- 1) add algebraic datatypes (probably using functor fixpoint stuff)
-- and remove sums.
-- 2) make a somewhat proper module system, probably like the modula
-- based one described in the ZINC report.
-- 3) char, string, and float types.
-- 4) I/O.
-- 5) typeclasses. We may way to hold off on floats until we can set
-- up a "numeric" typeclass.. but maybe not since this is probably a
-- ways off.


module Ast (
  Command(..), Prog(..), Term(..), Type(..), TypeScheme(..), Unop(..),
  Binop(..), mkTypeScheme, eraseData, isArithBinop, isComparisonBinop,
  isBUpdate, binopType, isValue, typeRec, typeRec2, termRec, termTypeRec
  ) where

import Data.List (intercalate)
import Data.Semigroup
import GHC.Generics (Generic)
import Generic.Random.Generic

import Test.QuickCheck

import Symtab (Id(..))
import Util


----------
-- | Types

data Type =
  TyUnit
  | TyBool
  | TyInt
  | TyArrow Type Type
  | TyVar Bool Id
  | TyPair Type Type
  | TySum Type Type
  | TyRef Type
  deriving Generic

-- A recursion scheme for types.
typeRec :: (Type -> Type) -> Type -> Type
typeRec f (TyArrow s t) = f $ TyArrow (typeRec f s) (typeRec f t)
typeRec f (TyPair s t)  = f $ TyPair (typeRec f s) (typeRec f t)
typeRec f (TySum s t)   = f $ TySum (typeRec f s) (typeRec f t)
typeRec f (TyRef s)     = f $ TyRef $ typeRec f s
typeRec f ty            = f ty

-- A kind of catamorphism for types, given that the output type is a
-- semigroup (can be built up using an associative operation). Used
-- for example in the 'freeTyVarsAux' function in Core.hs.
typeRec2 :: Semigroup a => (Type -> a) -> Type -> a
typeRec2 f ty@(TyArrow s t) = f ty <> typeRec2 f s <> typeRec2 f t
typeRec2 f ty@(TyPair s t)  = f ty <> typeRec2 f s <> typeRec2 f t
typeRec2 f ty@(TySum s t)   = f ty <> typeRec2 f s <> typeRec2 f t
typeRec2 f ty@(TyRef s)     = f ty <> typeRec2 f s
typeRec2 f ty               = f ty


-- Type schemes. A type scheme is a type together with a list of its
-- free type variables. The typechecker computes type schemes for
-- every term, although most have no type variables except for
-- let-bound abstractions (but only when they are syntactically values
-- due to the value restriction).
data TypeScheme =
  TypeScheme { ts_tyvars_of :: [Id],
               ts_ty_of     :: Type }
  deriving (Show, Eq)

mkTypeScheme :: [Id] -> Type -> TypeScheme
mkTypeScheme ids ty =
  TypeScheme { ts_tyvars_of = ids,
               ts_ty_of     = ty }

data Unop =
  UMinus
  | UNot
  | UFix
  | UFst
  | USnd
  | URef
  | UDeref
  deriving (Eq, Generic, Show)

data Binop =
  BPlus
  | BMinus
  | BMult
  | BDiv
  | BEq
  | BNeq
  | BLt
  | BLe
  | BGt
  | BGe
  | BAnd
  | BOr
  | BUpdate
  deriving (Eq, Generic, Show)


----------
-- | Terms

-- Terms are parameterized by α, the type of metadata (type, location
-- in source file, etc).

data Term α =
  TmVar α Id
  | TmAbs α Id Type (Term α)
  | TmApp α (Term α) (Term α)
  | TmUnit α
  | TmBool α Bool
  | TmInt α Integer
  | TmIf α (Term α) (Term α) (Term α)
  | TmUnop α Unop (Term α)
  | TmBinop α Binop (Term α) (Term α)
  | TmPair α (Term α) (Term α)
  | TmInl α (Term α) Type
  | TmInr α (Term α) Type
  | TmCase α (Term α) Id (Term α) Id (Term α)
  | TmLet α Id (Term α) (Term α)
  deriving (Eq, Functor, Generic)


-- A recursion scheme for terms.
termRec :: (Term α -> Term α) -> Term α -> Term α
termRec f (TmAbs fi x ty tm) = f $ TmAbs fi x ty (termRec f tm)
termRec f (TmIf fi tm1 tm2 tm3) =
  f $ TmIf fi (termRec f tm1) (termRec f tm2) (termRec f tm3)
termRec f (TmUnop fi u tm) = f $ TmUnop fi u (termRec f tm)
termRec f (TmBinop fi b tm1 tm2) =
  f $ TmBinop fi b (termRec f tm1) (termRec f tm2)
termRec f (TmPair fi tm1 tm2) =
  f $ TmPair fi (termRec f tm1) (termRec f tm2)
termRec f (TmInl fi tm ty) = f $ TmInl fi (termRec f tm) ty
termRec f (TmInr fi tm ty) = f $ TmInr fi (termRec f tm) ty
termRec f (TmCase fi tm1 x tm2 y tm3) =
  f $ TmCase fi (termRec f tm1) x (termRec f tm2) y (termRec f tm3)
termRec f (TmLet fi x tm1 tm2) =
  f $ TmLet fi x (termRec f tm1) (termRec f tm2)
termRec f tm = f tm

-- Map a type transformer over a term.
termTypeRec :: (Type -> Type) -> Term α -> Term α
termTypeRec f = termRec $
  \tm -> case tm of
           TmAbs fi x ty tm -> TmAbs fi x (f ty) tm
           TmInl fi tm ty -> TmInl fi tm (f ty)
           TmInr fi tm ty -> TmInr fi tm (f ty)
           _ -> tm


-------------
-- | Commands

data Command α =
  CDecl α Id Type
  | CLet α Id (Term α)
  | CEval α (Term α)
  | CCheck α (Term α)
  deriving (Functor, Generic)


------------
-- | Program

data Prog α =
  Prog { pdata_of :: α,
         prog_of  :: [Command α] }
  deriving (Functor, Generic)


-------------------
-- | Erase metadata

eraseData :: Functor f => f α -> f ()
eraseData = fmap $ const ()


------------------------
-- | Typeclass Instances

instance Show Type where
  show TyUnit = "Unit"
  show TyBool = "Bool"
  show TyInt  = "Int"
  show (TyArrow t1 t2) = "(" ++ show t1 ++ "->" ++ show t2 ++ ")"
  show (TyVar _ (Id s)) = "(TyVar " ++ s ++ ")"
  show (TyPair t1 t2) = "(" ++ show t1 ++ " * " ++ show t2 ++ ")"
  show (TySum t1 t2) = "(" ++ show t1 ++ " + " ++ show t2 ++ ")"
  show (TyRef ty) = "(TyRef " ++ show ty ++ ")"

instance Eq Type where
  TyUnit == TyUnit = True
  TyBool == TyBool = True
  TyInt == TyInt = True
  TyArrow s1 t1 == TyArrow s2 t2 = s1 == s2 && t1 == t2
  TyPair s1 t1 == TyPair s2 t2 = s1 == s2 && t1 == t2
  TySum s1 t1 == TySum s2 t2 = s1 == s2 && t1 == t2
  TyRef t1 == TyRef t2 = t1 == t2
  TyVar _ x == TyVar _ y = x == y
  t1 == t2 = False

instance Arbitrary Type where
  arbitrary = genericArbitrary' Z uniform
  shrink (TyArrow s t) = [s, t]
  shrink (TyPair s t) = [s, t]
  shrink (TySum s t) = [s, t]
  shrink (TyRef s) = [s]
  shrink _ = []


--------------------------------
-- | S-expression show instances

instance Show (Term α) where
  show (TmVar _ x)         = show x
  show (TmAbs _ x ty t)    = "(TmAbs " ++ show x ++ " " ++ show ty ++
                             " " ++ show t ++ ")"
  show (TmApp _ t1 t2)     = "(TmApp " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (TmBool _ b)        = show b
  show (TmIf _ t1 t2 t3)   = "(TmIf " ++ show t1 ++ " " ++ show t2 ++
                             " " ++ show t3 ++ ")"
  show (TmInt _ i)         = "(TmInt " ++ show i ++ ")"
  show (TmBinop _ b t1 t2) = "(TmBinop " ++ show b ++ " " ++ show t1 ++
                             " " ++ show t2 ++ ")"
  show (TmUnop _ u t)   = "(TmUnop " ++ show u ++ " " ++ show t ++ ")"
  show (TmUnit _)       = "tt"
  show (TmPair _ t1 t2) = "(TmPair " ++ show t1 ++ " " ++ show t2 ++ ")"
  show (TmInl _ tm ty)  = "(TmInl " ++ show tm ++ " " ++ show ty ++ ")"
  show (TmInr _ tm ty)  = "(TmInr " ++ show tm ++ " " ++ show ty ++ ")"
  show (TmCase _ discrim nm1 t1 nm2 t2) =
    "(TmCase " ++ show discrim ++ " " ++ show nm1 ++ " " ++ show t1 ++
    " " ++ show nm2 ++ " " ++ show t2 ++ ")"
  show (TmLet _ x tm1 tm2) =
    "(TmLet " ++ show x ++ " " ++ show tm1 ++ " " ++ show tm2 ++ ")"

instance Show α => Show (Command α) where
  show (CDecl _ s t) = "(CDecl " ++ show s ++ " " ++ show t ++ ")"
  show (CLet _ s t)  = "(CLet " ++ show s ++ " " ++ show t ++ ")"
  show (CEval _ t)   = "(CEval " ++ show t ++ ")"
  show (CCheck _ t)  = "(CCheck " ++ show t ++ ")"

instance Show α => Show (Prog α) where
  show (Prog { prog_of = p }) =
    "(Prog " ++ intercalate "" (map show p) ++ ")"


---------
-- | Misc

-- For the value restriction on polymorphism.
isValue :: Term α -> Bool
isValue (TmAbs _ _ _ _) = True
isValue (TmUnit _) = True
isValue (TmBool _ _) = True
isValue (TmInt _ _) = True
isValue (TmPair _ t1 t2) = isValue t1 && isValue t2
isValue (TmInl _ tm _) = isValue tm
isValue (TmInr _ tm _) = isValue tm
isValue _ = False

isArithBinop :: Binop -> Bool
isArithBinop BPlus  = True
isArithBinop BMinus = True
isArithBinop BMult  = True
isArithBinop BDiv   = True
isArithBinop _      = False

isComparisonBinop :: Binop -> Bool
isComparisonBinop BAnd = True
isComparisonBinop BOr  = True
isComparisonBinop _    = False

isBUpdate :: Binop -> Bool
isBUpdate BUpdate = True
isBUpdate _ = False

binopType :: Binop -> Type
binopType BPlus   = TyInt
binopType BMinus  = TyInt
binopType BMult   = TyInt
binopType BDiv    = TyInt
binopType BEq     = TyBool
binopType BNeq    = TyBool
binopType BLt     = TyBool
binopType BLe     = TyBool
binopType BGt     = TyBool
binopType BGe     = TyBool
binopType BAnd    = TyBool
binopType BOr     = TyBool
binopType BUpdate = TyUnit

-- isSimpleType :: Type -> Bool
-- isSimpleType TyUnit = True
-- isSimpleType TyBool = True
-- isSimpleType TyInt = True
-- isSimpleType (TyVar _ _) = True
-- isSimpleType _ = False
