{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}

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
-- 1) make a somewhat proper module system, probably like the modula
-- based one described in the ZINC report. The current import system
-- is a bit messed up -- we get a weird lexer error when trying to
-- import a file that itself imports another file.
-- 2) char, string, and float types.
-- 3) I/O.
-- 4) typeclasses. We may way to hold off on floats until we can set
-- up a "numeric" typeclass.. but maybe not since this is probably a
-- ways off.

-- 5) Records. I think having typeclasses alleviates the need for row
-- polymorphism, so we can probably just implement records without
-- worrying about that. One thing -- order of evaluation of record
-- fields at record formation time. Row types could be nice though..

-- Terms (maybe just abstractions?) will be marked as either pure or
-- impure. Pure is the default, but they may be marked as impure by
-- the programmer in the type declaration. It would be possible to
-- infer impurity of course, but we want the use of impurity to be as
-- explicit as possible. An impure term is able to use mutable
-- references and other impure terms. There will be some intrinsic
-- impure functions for I/O and things like that. The 'main' function
-- of a program can be impure. This is basically a conceptually
-- simpler (I think) alternative to the IO monad.

-- There is also the question of whether to add full-blown typeclasses
-- or just intrinsic support for certain concepts like functors and
-- monads.

-- We could probably remove the built in pairs as well, not just sums,
-- and implement them as a variant type in the prelude but keep the
-- syntactic sugar. That way if we have a mechanism for automatically
-- deriving fmap and stuff for ADTs we can get them for pairs through
-- that.

-- TODO: add a newtype for typeschemes, since they are regular types
-- but are used in a specific way.

module Ast (
  Command(..), Prog(..), Term(..), Type(..), Unop(..), Binop(..),
  eraseData, isArithBinop, isComparisonBinop, isBUpdate, binopType,
  isValue, typeRec, typeRec2, termRec, termTypeRec, mkArrowType,
  data_of_term, data_of_command, Pattern(..), typeRecM, Kind(..), mkAbs,
  termTypeRecM, commandTypeRecM
  ) where

import Data.List (intercalate)
import Data.Monoid
import GHC.Generics (Generic)
import Generic.Random.Generic

import Test.QuickCheck

import Symtab (Id(..))
import Util


----------
-- | Kinds

data Kind =
  KStar
  | KArrow Kind Kind
  deriving (Eq, Generic, Show)

-- A recursion scheme for kinds.
kindRec :: (Kind -> Kind) -> Kind -> Kind
kindRec f KStar = f KStar
kindRec f (KArrow k1 k2) = f $ KArrow (kindRec f k1) (kindRec f k2)

instance Arbitrary Kind where
  arbitrary = genericArbitrary' Z uniform
  shrink (KArrow s t) = [s, t]
  shrink _ = []

----------
-- | Types

data Type =
  TyVar Bool Id
  | TyAbs Id Kind Type
  | TyApp Type Type
  | TyUnit
  | TyBool
  | TyInt
  | TyChar
  | TyArrow Type Type
  | TyRef Type
  | TyName Id
  | TyVariant Id [Type] [(Id, [Type])]
  | TyRecord Id [Type] [(Id, Type)]
  deriving Generic

-- A recursion scheme for types.
typeRec :: (Type -> Type) -> Type -> Type
typeRec f (TyAbs x k s) = f $ TyAbs x k (typeRec f s)
typeRec f (TyApp s t)   = f $ TyApp (typeRec f s) (typeRec f t)
typeRec f (TyArrow s t) = f $ TyArrow (typeRec f s) (typeRec f t)
typeRec f (TyRef s)     = f $ TyRef $ typeRec f s
typeRec f (TyVariant nm tyargs ctors) =
  f $ TyVariant nm (map (typeRec f) tyargs) $
  map (mapSnd $ map $ typeRec f) ctors
typeRec f (TyRecord nm tyargs ctors) =
  f $ TyRecord nm (map (typeRec f) tyargs) $
  map (mapSnd $ typeRec f) ctors
typeRec f ty = f ty

-- A monadic recursion scheme for types.
typeRecM :: Monad m => (Type -> m Type) -> Type -> m Type
typeRecM f (TyAbs x k s) =
  TyAbs x k <$> typeRecM f s >>= f
typeRecM f (TyApp s t) =
  pure TyApp <*> typeRecM f s <*> typeRecM f t >>= f
typeRecM f (TyArrow s t) =
  pure TyArrow <*> typeRecM f s <*> typeRecM f t >>= f
typeRecM f (TyRef s) = TyRef <$> typeRecM f s >>= f
typeRecM f (TyVariant nm tyargs ctors) =
  pure (TyVariant nm) <*> mapM (typeRecM f) tyargs <*>
  mapM (mapSndM $ mapM $ typeRecM f) ctors >>= f
typeRecM f (TyRecord nm tyargs fields) =
  pure (TyRecord nm) <*> mapM (typeRecM f) tyargs <*>
  mapM (mapSndM $ typeRecM f) fields >>= f
typeRecM f ty = f ty

-- A sort of catamorphism for types (folding over a type to produce a
-- value), given that the output type is a monoid. Used for example in
-- the 'freeTyVarsAux' function in Core.hs.  Currently a "preorder"
-- traversal, for no reason really. I suppose we could define multiple
-- versions for the different traversal orders.
typeRec2 :: Monoid a => (Type -> a) -> Type -> a
typeRec2 f ty@(TyAbs _ _ s) = f ty <> typeRec2 f s
typeRec2 f ty@(TyApp s t)   = f ty <> typeRec2 f s <> typeRec2 f t
typeRec2 f ty@(TyArrow s t) = f ty <> typeRec2 f s <> typeRec2 f t
typeRec2 f ty@(TyRef s)     = f ty <> typeRec2 f s
typeRec2 f ty@(TyVariant _ tyargs ctors) =
  f ty <> (foldl (<>) mempty $ map (typeRec2 f) tyargs) <>
  (foldl (<>) mempty $ map (typeRec2 f) $ concat $ snd $ unzip ctors)
typeRec2 f ty@(TyRecord _ tyargs ctors) =
  f ty <> (foldl (<>) mempty $ map (typeRec2 f) tyargs) <>
  (foldl (<>) mempty $ map (typeRec2 f) $ snd $ unzip ctors)
typeRec2 f ty = f ty

-- -- A depth-bounded version of typeRec2.
-- typeRec2_d :: Monoid a => Int -> (Type -> a) -> Type -> a
-- typeRec2_d d f ty@(TyAbs _ _ s) = f ty <> typeRec2_d (d-1) f s
-- typeRec2_d d f ty | d <= 0 = f ty
-- typeRec2_d d f ty@(TyApp s t) =
--   f ty <> typeRec2_d (d-1) f s <> typeRec2_d (d-1) f t
-- typeRec2_d d f ty@(TyArrow s t) =
--   f ty <> typeRec2_d (d-1) f s <> typeRec2_d (d-1) f t
-- typeRec2_d d f ty@(TyRef s) = f ty <> typeRec2_d (d-1) f s
-- typeRec2_d d f ty@(TyVariant _ tyargs ctors) =
--   f ty <> (foldl (<>) mempty $ map (typeRec2_d (d-1) f) tyargs) <>
--   (foldl (<>) mempty $ map (typeRec2_d (d-1) f) $ concat $ snd $ unzip ctors)
-- typeRec2_d d f ty@(TyRecord _ tyargs ctors) =
--   f ty <> (foldl (<>) mempty $ map (typeRec2_d (d-1) f) tyargs) <>
--   (foldl (<>) mempty $ map (typeRec2_d (d-1) f) $ concat $ snd $ unzip ctors)
-- typeRec2_d _ f ty = f ty


data Unop =
  UMinus
  | UNot
  | UFix
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
  | TmChar α Char
  | TmIf α (Term α) (Term α) (Term α)
  | TmUnop α Unop (Term α)
  | TmBinop α Binop (Term α) (Term α)
  | TmLet α Id (Term α) (Term α)
  | TmVariant α Id [Term α]
  | TmMatch α (Term α) [(Pattern, Term α)]
  | TmRecord α [(Id, Term α)]
  deriving (Eq, Functor, Generic)

data Pattern =
  PVar Id
  | PUnit
  | PBool Bool
  | PInt Integer
  | PChar Char
  | PPair Pattern Pattern
  | PConstructor Id [Pattern]
  | PRecord [(Id, Pattern)]
  deriving (Eq, Show)


-- A recursion scheme for terms.
termRec :: (Term α -> Term α) -> Term α -> Term α
termRec f (TmAbs fi x ty tm) = f $ TmAbs fi x ty (termRec f tm)
termRec f (TmIf fi tm1 tm2 tm3) =
  f $ TmIf fi (termRec f tm1) (termRec f tm2) (termRec f tm3)
termRec f (TmUnop fi u tm) = f $ TmUnop fi u (termRec f tm)
termRec f (TmBinop fi b tm1 tm2) =
  f $ TmBinop fi b (termRec f tm1) (termRec f tm2)
termRec f (TmLet fi x tm1 tm2) =
  f $ TmLet fi x (termRec f tm1) (termRec f tm2)
termRec f (TmVariant fi x tms) =
  f $ TmVariant fi x $ map (termRec f) tms
termRec f (TmMatch fi discrim cases) =
  f $ TmMatch fi (termRec f discrim) $ mapSnd (termRec f) <$> cases
termRec f (TmRecord fi fields) =
  f $ TmRecord fi $ map (mapSnd $ termRec f) fields
termRec f tm = f tm

termRecM :: Monad m => (Term α -> m (Term α)) -> Term α -> m (Term α)
termRecM f (TmAbs fi x ty tm) = TmAbs fi x ty <$> termRecM f tm >>= f
termRecM f (TmIf fi tm1 tm2 tm3) =
  pure (TmIf fi) <*> termRecM f tm1 <*> termRecM f tm2 <*> termRecM f tm3
  >>= f
termRecM f (TmUnop fi u tm) = TmUnop fi u <$> termRecM f tm >>= f
termRecM f (TmBinop fi b tm1 tm2) =
  pure (TmBinop fi b) <*> termRecM f tm1 <*> termRecM f tm2 >>= f
termRecM f (TmLet fi x tm1 tm2) =
  pure (TmLet fi x) <*> termRecM f tm1 <*> termRecM f tm2 >>= f
termRecM f (TmVariant fi x tms) =
  TmVariant fi x <$> mapM (termRecM f) tms >>= f
termRecM f (TmMatch fi discrim cases) =
  pure (TmMatch fi) <*> termRecM f discrim <*>
  mapM (mapSndM $ termRecM f) cases >>= f
termRecM f (TmRecord fi fields) =
  TmRecord fi <$> mapM (mapSndM $ termRecM f) fields >>= f
termRecM f tm = f tm

-- Map a type transformer over a term.
termTypeRec :: (Type -> Type) -> Term α -> Term α
termTypeRec f = termRec $
  \tm -> case tm of
           TmAbs fi x ty tm -> TmAbs fi x (f ty) tm
           _ -> tm

termTypeRecM :: Monad m => (Type -> m Type) -> Term α -> m (Term α)
termTypeRecM f = termRecM $
  \tm -> case tm of
           TmAbs fi x ty tm -> pure (TmAbs fi x) <*> f ty <*> pure tm
           _ -> return tm


-------------
-- | Commands

data Command α =
  CDecl α Id Type
  | CLet α Id (Term α)
  | CEval α (Term α)
  | CCheck α (Term α)
  | CData α Id [Id] [(Id, [Type])]
  | CRecord α Id [Id] [(Id, Type)]
  | CAssert α (Term α)
  deriving (Functor, Generic)


commandTermRecM :: Monad m => (Term α -> m (Term α)) ->
                   Command α -> m (Command α)
commandTermRecM f (CLet fi x tm) = CLet fi x <$> f tm
commandTermRecM f (CEval fi tm) = CEval fi <$> f tm
commandTermRecM f (CCheck fi tm) = CCheck fi <$> f tm
commandTermRecM _ com = return com

commandTypeRecM :: Monad m => (Type -> m Type) -> Command α -> m (Command α)
commandTypeRecM f (CDecl fi x ty) = CDecl fi x <$> f ty
commandTypeRecM f (CLet fi x tm) = CLet fi x <$> termTypeRecM f tm
commandTypeRecM f (CEval fi tm) = CEval fi <$> termTypeRecM f tm
commandTypeRecM f (CCheck fi tm) = CCheck fi <$> termTypeRecM f tm
commandTypeRecM f (CData fi nm tyvars ctors) =
  CData fi nm tyvars <$> mapM (mapSndM $ mapM f) ctors
commandTypeRecM f (CRecord fi nm tyvars fields) =
  CRecord fi nm tyvars <$> mapM (mapSndM f) fields


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
  show = showType []

showType :: [Id] -> Type -> String
showType _ (TyVar b (Id s)) = "(TyVar " ++ show b ++ " " ++ s ++ ")"
showType nms (TyAbs x k s) = "(TyAbs " ++ show x ++ " " ++ show k ++
                             " " ++ showType nms s ++ ")"
showType nms (TyApp s t) =
  "(TyApp " ++ showType nms s ++ " " ++ showType nms t ++ ")"
showType _ TyUnit = "Unit"
showType _ TyBool = "Bool"
showType _ TyInt  = "Int"
showType _ TyChar = "Char"
showType nms (TyArrow t1 t2) =
  "(" ++ showType nms t1 ++ " -> " ++ showType nms t2 ++ ")"
showType nms (TyRef ty) = "(TyRef " ++ showType nms ty ++ ")"
showType _ (TyName nm) = "(TyName " ++ show nm ++ ")"
showType nms (TyVariant nm tyargs ctors) =
  if nm `elem` nms then "(TyVariant " ++ show nm ++ ")" else
    "(TyVariant " ++ show nm ++ " (" ++
    intercalate " " (map (showType (nm : nms)) tyargs) ++ ") (" ++
    intercalate " " (map (\(x, tys) ->
                            "(" ++ show x ++ " : " ++ intercalate " "
                           (map (showType (nm : nms)) tys) ++ ")")
                     ctors) ++ "))"
showType nms (TyRecord nm tyargs fields) =
  if nm `elem` nms then "(TyRecord " ++ show nm ++ ")" else
    "(TyRecord " ++ show nm ++ " (" ++
    intercalate " " (map (showType (nm : nms)) tyargs) ++ ") (" ++
    intercalate " " (map (\(x, ty) ->
                            "(" ++ show x ++ " : " ++
                            showType (nm : nms) ty ++ ")")
                      fields) ++ "))"

instance Eq Type where
  TyVar _ x == TyVar _ y = x == y
  TyAbs x k1 s == TyAbs y k2 t = x == y && k1 == k2 && s == t
  TyApp s1 t1 == TyApp s2 t2 = s1 == s2 && t1 == t2
  TyUnit == TyUnit = True
  TyBool == TyBool = True
  TyInt == TyInt   = True
  TyChar == TyChar = True
  TyArrow s1 t1 == TyArrow s2 t2 = s1 == s2 && t1 == t2
  TyRef t1 == TyRef t2 = t1 == t2
  TyName nm1 == TyName nm2 = nm1 == nm2
  TyVariant nm1 tyargs1 ctors1 == TyVariant nm2 tyargs2 ctors2 =
    nm1 == nm2 && tyargs1 == tyargs2
  TyRecord nm1 tyargs1 fields1 == TyRecord nm2 tyargs2 fields2 =
    nm1 == nm2 && tyargs1 == tyargs2
  _ == _ = False

instance Arbitrary Type where
  arbitrary = genericArbitrary' Z uniform
  shrink (TyArrow s t) = [s, t]
  shrink (TyRef s) = [s]
  shrink (TyVariant _ _ ctors) =
    concat $ concat $ shrink $ snd $ unzip ctors
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
  show (TmChar _ c)        = "(TmChar " ++ show c ++ ")"
  show (TmBinop _ b t1 t2) = "(TmBinop " ++ show b ++ " " ++ show t1 ++
                             " " ++ show t2 ++ ")"
  show (TmUnop _ u t)   = "(TmUnop " ++ show u ++ " " ++ show t ++ ")"
  show (TmUnit _)       = "tt"
  show (TmLet _ x tm1 tm2) =
    "(TmLet " ++ show x ++ " " ++ show tm1 ++ " " ++ show tm2 ++ ")"
  show (TmVariant _ x tms) =
    "(TmVariant " ++ show x ++ " " ++ show tms ++ ")"
  show (TmMatch _ discrim cases) =
    "(TmMatch " ++ show discrim ++ " " ++
    (intercalate " " (map show cases)) ++ ")"
  show (TmRecord _ fields) =
    "(TmRecord " ++ show fields ++ ")"
        
instance Show α => Show (Command α) where
  show (CDecl _ s t) = "(CDecl " ++ show s ++ " " ++ show t ++ ")"
  show (CLet _ s t)  = "(CLet " ++ show s ++ " " ++ show t ++ ")"
  show (CEval _ t)   = "(CEval " ++ show t ++ ")"
  show (CCheck _ t)  = "(CCheck " ++ show t ++ ")"
  show (CAssert _ t) = "(CAssert " ++ show t ++ ")"

instance Show α => Show (Prog α) where
  show (Prog { prog_of = p }) =
    "(Prog " ++ intercalate "" (map show p) ++ ")"


---------
-- | Misc

-- For the value restriction on polymorphism.
isValue :: Term α -> Bool
isValue (TmAbs _ _ _ _) = True
isValue (TmUnit _)   = True
isValue (TmBool _ _) = True
isValue (TmInt _ _)  = True
isValue (TmChar _ _) = True
isValue (TmVariant _ _ tms) = and (map isValue tms)
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
isBUpdate _       = False

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

data_of_term :: Term α -> α
data_of_term t =
  case t of
    TmVar fi _       -> fi
    TmAbs fi _ _ _   -> fi
    TmApp fi _ _     -> fi
    TmUnit fi        -> fi
    TmBool fi _      -> fi
    TmIf fi _ _ _    -> fi
    TmInt fi _       -> fi
    TmChar fi _      -> fi
    TmUnop fi _ _    -> fi
    TmBinop fi _ _ _ -> fi
    TmLet fi _ _ _   -> fi
    TmVariant fi _ _ -> fi
    TmMatch fi _ _   -> fi
    TmRecord fi _    -> fi

data_of_command :: Command α -> α
data_of_command c =
  case c of
    CDecl fi _ _   -> fi
    CLet fi _ _    -> fi
    CEval fi _     -> fi
    CCheck fi _    -> fi
    CData fi _ _ _ -> fi

term_of_command :: Command α -> Term α
term_of_command c =
  case c of
    CLet _ _ t -> t
    CEval _ t  -> t

mkArrowType :: [Type] -> Type
mkArrowType (x : [])     = x
mkArrowType (x : y : []) = TyArrow x y
mkArrowType (x : y : ys) = TyArrow x $ mkArrowType $ y : ys

-- Build a supercombinator with the given Ids (which may appear free
-- in the given body).
mkAbs :: [Id] -> Term α -> Term α
mkAbs [] tm = tm
mkAbs (x:xs) tm =
  TmAbs (data_of_term tm) x (TyVar False (Id "")) $ mkAbs xs tm
