{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module defines the internal language syntax.

module Ast (
  Command(..), Prog(..), Term(..), Type(..), Unop(..), Binop(..),
  eraseData, isArithBinop, isComparisonBinop, isBUpdate, binopType,
  isValue, typeRec, typeRec2, termRec, termTypeRec, mkArrowType,
  data_of_term, data_of_command, Pattern(..), typeRecM, Kind(..), mkAbs,
  termTypeRecM, commandTypeRec, commandTypeRecM, typeRec2M, mkTyVar,
  propagateClassConstraints, progTypeRec, TypeClass(..), ClassInstance(..),
  TySubstable(..), TypeSubst, FreeTyVars(..), tysubst', tysubstAll,
  tysubstAll', TypeConstructor(..), propagateClassConstraintsCom, mkTyAbs,
  mkTypeConstructor, mkTypeConstructor', mapTypeConstructor, mkTyApp,
  termRec2, termSubst
  ) where


-- I wonder if it's a good idea to treat sequencing specially instead
-- of just making it a derived form that desugars to
-- application. Maybe we will just detect the intro/elim pattern of
-- unit thunk sequencing and treat it specially in a different
-- representation during compilation.

-- TODO:
-- 1) make a somewhat proper module system, probably like the modula
-- based one described in the ZINC report. The current import system
-- is a bit messed up -- we get a weird lexer error when trying to
-- import a file that itself imports another file. We should keep it
-- simple.. maybe just essentially copy Haskell / Python. A module
-- should be contained entirely within one file, and module functors
-- and things like that are confusing.
-- 2) float type (maybe wait for typeclasses).
-- 3) I/O.
-- 4) typeclasses. We may way to hold off on floats until we can set
-- up a "numeric" typeclass.. but maybe not since this is probably a
-- ways off.
-- 5) type synonyms and newtypes

-- 6) Records. I think having typeclasses alleviates the need for row
-- polymorphism, so we can probably just implement records without
-- worrying about that. One thing -- order of evaluation of record
-- fields at record formation time. Row types could be nice though..
-- * Maybe we really do want row polymorphism.

-- Terms (maybe just abstractions?) will be marked as either pure or
-- impure. Pure is the default, but they may be marked as impure by
-- the programmer in the type declaration. It would be possible to
-- infer impurity of course, but we want the use of impurity to be as
-- explicit as possible. An impure term is able to use mutable
-- references and other impure terms. There will be some intrinsic
-- impure functions for I/O and things like that. The 'main' function
-- of a program can be impure. This is basically a conceptually
-- simpler (I think) alternative to the IO monad.

-- ^ Update to this. Four sorts of types:
-- 1) pure. no creation or update of references and no IO
-- 2) local impure. creation of references and updates to locally
-- allocated references, but no update of global references and no
-- IO. locally impure computations can be embedded inside pure
-- computations.
-- 3) global impure. unrestricted action on references but no IO.
-- 4) io. anything goes.

-- TODO: high level abstract syntax that can be directly generated by
-- the parser, then elaboration down to the core language (the current
-- AST). E.g., 'where' clauses, most of the sugar currently in the
-- parser, maybe type synonyms? If-then-else could be a derived form I
-- suppose, but it may be nice to have it in the core syntax
-- anyway. Let-bindings are similar, but we want them for
-- let-polymorphism. Also 'where' clauses would be nice. This could
-- all just be done in the parser I guess.. which is probably what
-- we'll do for now until it gets too complicated.

-- This is a bit of a stretch, but maybe we could use Z3 to
-- automatically check assertions whenever possible. A polymorphic
-- assertion could just be tested using a particular type such as
-- integers. This could be useful for little things like functor and
-- monad laws -- or anything small without recursion.

-- TODO: change type declarations so they are just an optional prefix
-- on definitions. This will remove the need for the extra symtab in
-- the typing context and simplify things like ensuring that every
-- declaration has a corresponding definition.

-- TODO: When we move to a module system, need to rethink the way
-- programs are structured and interpreted (and typechecked) a
-- bit. E.g., we first do a pass over the program to gather up all of
-- the declarations and definitions so that everything in a module can
-- be mutually recursive. Commands that the interpreter ignores should
-- be removed before reaching it. And the interpreter will probably
-- have to do a gathering pass in a similar way to create the
-- environment.

-- TODO: A bit of partial evaluation to specialize functions with
-- class dictionary arguments to their instances might be helpful for
-- performance.

import Control.Monad
import Control.Monad.State
import Data.Bifunctor
import Data.List (intercalate, nub)
import Data.Monoid
import GHC.Generics (Generic)
import Generic.Random.Generic

import Test.QuickCheck

import Symtab (Id(..), Symtab)
import qualified Symtab (map)
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


-----------------
-- | Type classes

-- TODO: default implementations
data TypeClass =
  TypeClass { tyclass_constrs :: [Id] -- superclass constraints
            , tyclass_name :: Id
            , tyclass_index :: Id
            , tyclass_methods :: [(Id, Type)]}
  deriving Show


-- Maybe we just need the dict and not the methods. The dict should
-- just be a tuple? It needs to be a term in the object language.

-- To obtain the type of the instance during instance resolution: Use
-- instance_tyname to look up the type and then apply it to the types
-- in instance_tyargs. The result may not necessarily be fully
-- applied, which would be the case when the type index for the class
-- is a type constructor.

-- Maybe we should just keep the result of that process around in the
-- record. instance_ty should be the result of doing that. So now
-- during resolution we can just match against instance_ty (any type
-- variables inside should have the constraints attached). So
-- basically the instance resolution algorithm is to try for every
-- known instance of the particular class to match the type we're
-- searching for, doing recursive resolution calls on type variables
-- and their constraints.
data ClassInstance =
  ClassInstance { -- instance_tyargs :: [Type]
                  instance_ctx :: [Id]
                , instance_tyname :: Id
                , instance_classname :: Id
                
                -- for matching against during instance resolution
                , instance_ty :: Type

                -- Gives the order in which the dictionary expects its
                -- dictionary arguments.
                , instance_args :: [Id]

                -- Gives the order in which the methods appear in the
                -- dictionary.
                , instance_methods :: [Id]

                -- The dictionary, when fully applied, is an n-tuple
                -- (iterated pairs starting from unit). It may be
                -- abstracted over other dictionaries though.
                , instance_dict :: Term () }
  deriving Show


-- ----------------------
-- -- | Class constraints

-- -- Associate a type variable with a class.
-- type ClassConstraint = (Id, TypeClass)

-- type ClassContext = [ClassConstraint]


----------
-- | Types

-- I wonder if it would be better to use de Bruijn indices for type
-- abstractions..

data Type =
  TyVar Bool [Id] Id
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
  | TyConstructor TypeConstructor
  deriving Generic


-- We represent type constructors explicitly like this so we can keep
-- track of metadata about them. This is for a couple reasons: 1)
-- easier to support class instances for type constructors, and 2)
-- when we encounter a fully applied type constructor, we can easily
-- tell exactly what the type constructor was and what arguments it
-- was applied to to arrive at the resulting type.
data TypeConstructor =
  TypeConstructor { tycon_name :: Id
                  , tycon_tyvars :: [Id]
                  , tycon_kinds :: [Kind]
                  , tycon_tyargs :: [Type]
                  , tycon_ty :: Type
                  , tycon_instantiated :: Type }
  deriving (Generic, Show)


-- Build a (possibly instantiated, fully or partially) type
-- constructor. The type argument is assumed to not be abstracted yet,
-- and we abstract out the type variables here.
mkTypeConstructor :: Id -> [Id] -> [Kind] -> [Type] -> Type -> Type
mkTypeConstructor nm tyvars kinds tyargs ty =
  TyConstructor $
  TypeConstructor { tycon_name = nm
                  , tycon_tyvars = tyvars
                  , tycon_kinds = kinds
                  , tycon_tyargs = tyargs
                  , tycon_ty = mkTyAbs tyvars ty
                  , tycon_instantiated =
                      mkTyApp (mkTyAbs tyvars ty) tyargs }

-- Build an uninstantiated type constructor.
mkTypeConstructor' :: Id -> [Id] -> [Kind] -> Type -> Type
mkTypeConstructor' nm tyvars kinds ty =
  mkTypeConstructor nm tyvars kinds [] ty


mapTypeConstructor :: (Type -> Type) -> TypeConstructor -> TypeConstructor
mapTypeConstructor f tycon@(TypeConstructor
                             { tycon_tyargs = tyargs
                             , tycon_ty = uninst
                             , tycon_instantiated = inst }) =
  tycon { tycon_tyargs = f <$> tyargs
        , tycon_ty = f uninst
        , tycon_instantiated = f inst }


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
typeRec f (TyConstructor
           tycon@(TypeConstructor { tycon_tyargs = tyargs
                                  , tycon_ty = ty
                                  , tycon_instantiated = inst })) =
  f $ TyConstructor $ tycon { tycon_tyargs = typeRec f <$> tyargs
                            , tycon_ty = typeRec f ty
                            , tycon_instantiated = typeRec f inst }
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
typeRecM f (TyConstructor
            tycon@(TypeConstructor { tycon_tyargs = tyargs
                                   , tycon_ty = ty
                                   , tycon_instantiated = inst })) = do
  tyargs' <- mapM (typeRecM f) tyargs
  ty' <- typeRecM f ty
  inst' <- typeRecM f inst  
  return $ TyConstructor $ tycon { tycon_tyargs = tyargs'
                                 , tycon_ty = ty'
                                 , tycon_instantiated = inst' }
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
typeRec2 f t@(TyConstructor (TypeConstructor { tycon_tyargs = tyargs
                                             , tycon_ty = ty
                                             , tycon_instantiated = inst })) =
  f t <> (foldl (<>) mempty $ typeRec2 f <$> tyargs) <>
  typeRec2 f ty <> typeRec2 f inst
typeRec2 f ty = f ty

-- A monadic version of typeRec2.
typeRec2M :: (Monoid a, Monad m) => (Type -> m a) -> Type -> m a
typeRec2M f ty@(TyAbs _ _ s) = pure (<>) <*> f ty <*> typeRec2M f s
typeRec2M f ty@(TyApp s t) =
  pure (<>) <*> (pure (<>) <*> f ty <*> typeRec2M f s) <*> typeRec2M f t
typeRec2M f ty@(TyArrow s t) =
  pure (<>) <*> (pure (<>) <*> f ty <*> typeRec2M f s) <*> typeRec2M f t
typeRec2M f ty@(TyRef s) =
  pure (<>) <*> f ty <*> typeRec2M f s
typeRec2M f ty@(TyVariant _ tyargs ctors) =
  pure (<>) <*> f ty <*>
  (pure (<>) <*>
    (foldM (\acc x -> (<>) acc <$> typeRec2M f x) mempty tyargs) <*>
    (foldM (\acc x -> (<>) acc <$> typeRec2M f x) mempty $
    concat $ snd $ unzip ctors))
typeRec2M f ty@(TyRecord _ tyargs fields) =
  pure (<>) <*> f ty <*>
  (pure (<>) <*>
    (foldM (\acc x -> (<>) acc <$> typeRec2M f x) mempty tyargs) <*>
    (foldM (\acc x -> (<>) acc <$> typeRec2M f x) mempty
     $ snd $ unzip fields))
typeRec2M f t@(TyConstructor (TypeConstructor { tycon_tyargs = tyargs
                                              , tycon_ty = ty
                                              , tycon_instantiated = inst })) =
  pure (<>) <*>
  (pure (<>) <*>
   (pure (<>) <*> f t <*>
     (foldM (\acc x -> (<>) acc <$> typeRec2M f x) mempty tyargs)) <*>
    typeRec2M f ty) <*> typeRec2M f inst
typeRec2M f ty = f ty


--------------------------------
-- | Unary and binary operations

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
  -- info, class name, method name, type index
  | TmPlaceholder α Id Id Type -- for class methods
  deriving (Eq, Foldable, Functor, Generic, Traversable)

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

termRec2 :: Monoid a => (Term α -> a) -> Term α -> a
termRec2 f tm@(TmAbs _ _ _ t) = f tm <> termRec2 f t
termRec2 f tm@(TmApp _ s t) = f tm <> termRec2 f s <> termRec2 f t
termRec2 f tm@(TmIf _ b s t) =
 f tm <> termRec2 f b <> termRec2 f s <> termRec2 f t
termRec2 f tm@(TmUnop _ _ t) = f tm <> termRec2 f t
termRec2 f tm@(TmBinop _ _ s t) = f tm <> termRec2 f s <> termRec2 f t
termRec2 f tm@(TmLet _ _ s t) = f tm <> termRec2 f s <> termRec2 f t
termRec2 f tm@(TmVariant _ _ tms) =
  f tm <> foldl (<>) mempty (termRec2 f <$> tms)
termRec2 f tm@(TmMatch _ s ps) =
  f tm <> termRec2 f s <> foldl (<>) mempty (termRec2 f . snd <$> ps)
termRec2 f tm@(TmRecord _ fields) =
  f tm <> foldl (<>) mempty (termRec2 f . snd <$> fields)
termRec2 f tm = f tm

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

termSubst :: Eq α => Term α -> Term α -> Term α -> Term α
termSubst s t = termRec $
  \tm -> if tm == t then s else tm

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
  -- constraints, class name, class type variable, method names and types
  | CClass α [Id] Id Id [(Id, Type)]
  -- constraints, class name, instance type, method names and definitions
  | CInstance α [Id] Id Type [(Id, Term α)]
  deriving (Functor, Generic)


commandTermRecM :: Monad m => (Term α -> m (Term α)) ->
                   Command α -> m (Command α)
commandTermRecM f (CLet fi x tm) = CLet fi x <$> f tm
commandTermRecM f (CEval fi tm) = CEval fi <$> f tm
commandTermRecM f (CCheck fi tm) = CCheck fi <$> f tm
commandTermRecM _ com = return com


commandTypeRec :: (Type -> Type) -> Command α -> Command α
commandTypeRec f (CDecl fi x ty) = CDecl fi x $ f ty
commandTypeRec f (CLet fi x tm) = CLet fi x $ termTypeRec f tm
commandTypeRec f (CEval fi tm) = CEval fi $ termTypeRec f tm
commandTypeRec f (CCheck fi tm) = CCheck fi $ termTypeRec f tm
commandTypeRec f (CData fi nm tyvars ctors) =
  CData fi nm tyvars $ map (mapSnd $ map f) ctors
commandTypeRec f (CRecord fi nm tyvars fields) =
  CRecord fi nm tyvars $ map (mapSnd f) fields
commandTypeRec f (CClass fi constrs nm tyvar methods) =
  CClass fi constrs nm tyvar $ map (mapSnd f) methods
commandTypeRec f (CInstance fi constrs nm ty methods) =
  CInstance fi constrs nm (f ty) $ map (mapSnd $ termTypeRec f) methods

commandTypeRecM :: Monad m => (Type -> m Type) -> Command α -> m (Command α)
commandTypeRecM f (CDecl fi x ty) = CDecl fi x <$> f ty
commandTypeRecM f (CLet fi x tm) = CLet fi x <$> termTypeRecM f tm
commandTypeRecM f (CEval fi tm) = CEval fi <$> termTypeRecM f tm
commandTypeRecM f (CCheck fi tm) = CCheck fi <$> termTypeRecM f tm
commandTypeRecM f (CData fi nm tyvars ctors) =
  CData fi nm tyvars <$> mapM (mapSndM $ mapM f) ctors
commandTypeRecM f (CRecord fi nm tyvars fields) =
  CRecord fi nm tyvars <$> mapM (mapSndM f) fields
commandTypeRecM f (CClass fi constrs nm tyvar methods) =
  CClass fi constrs nm tyvar <$> mapM (mapSndM f) methods
commandTypeRecM f (CInstance fi constrs nm ty methods) =
  pure (CInstance fi constrs nm) <*> f ty <*>
  mapM (mapSndM $ termTypeRecM f) methods


-- We should be able to use a simple recursion scheme and not worry
-- about capture here, since there are no naked abstractions outside
-- of type constructors during unification and we only ever need to
-- look at the tyargs of type constructors.
propagateClassConstraints :: [(Id, Id)] -> Type -> Type
propagateClassConstraints =
  flip $ foldl $
  \acc (classNm, x) ->
    flip typeRec acc $
    \ty -> case ty of
      TyVar b ctx y ->
        TyVar b (if x == y then classNm : ctx else ctx) y
      _ -> ty

-- This doesn't avoid capture. It assumes there are no type
-- abstractions.
propagateClassConstraintsCom :: [(Id, Id)] -> Command α -> Command α
propagateClassConstraintsCom constrs =
  commandTypeRec $ propagateClassConstraints constrs
  -- flip $ foldl $
  -- \com (x, classNm) ->
  --   flip commandTypeRec com $
  --   \ty -> case ty of
  --            TyVar b ctx y ->
  --              TyVar b (if x == y then classNm : ctx else ctx) y
  --            _ -> ty

------------
-- | Program

data Prog α =
  Prog { pdata_of :: α,
         prog_of  :: [Command α] }
  deriving (Functor, Generic)


progTypeRec :: (Type -> Type) -> Prog α -> Prog α
progTypeRec f (Prog { pdata_of = fi, prog_of = coms }) =
  Prog { pdata_of = fi, prog_of = commandTypeRec f <$> coms }


-------------------
-- | Erase metadata

eraseData :: Functor f => f α -> f ()
eraseData = (<$) ()
-- eraseData = void -- not found?


------------------------
-- | Typeclass Instances

instance Show Type where
  show =
    debugPrint "showType" $
    showType []

showType :: [Id] -> Type -> String
showType _ (TyVar b ctx (Id s)) =
  "(TyVar " ++ show b ++ " (" ++ intercalate " " (show <$> ctx) ++
  ") " ++ s ++ ")"
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
-- showType nms (TyConstructor (TypeConstructor { tycon_name = nm } )) =
--   "(TyConstructor " ++ show nm ++ ")"
showType nms (TyConstructor tycon) = "(TyConstructor " ++ show tycon ++ ")"

instance Eq Type where
  -- TyVar _ ctx1 x == TyVar _ ctx2 y = x == y && ctx1 == ctx2
  TyVar _ _ x == TyVar _ _ y = x == y
  TyAbs x k1 s == TyAbs y k2 t =
    -- x == y && k1 == k2 && s == t
    k1 == k2 && s == tysubst' (mkTyVar x) (mkTyVar y) t
  TyApp s1 t1 == TyApp s2 t2 = s1 == s2 && t1 == t2
  TyUnit == TyUnit = True
  TyBool == TyBool = True
  TyInt == TyInt   = True
  TyChar == TyChar = True
  TyArrow s1 t1 == TyArrow s2 t2 = s1 == s2 && t1 == t2
  TyRef t1 == TyRef t2 = t1 == t2
  TyName nm1 == TyName nm2 = nm1 == nm2
  TyVariant nm1 tyargs1 _ == TyVariant nm2 tyargs2 _ =
    nm1 == nm2 && tyargs1 == tyargs2
  TyRecord nm1 tyargs1 _ == TyRecord nm2 tyargs2 _ =
    nm1 == nm2 && tyargs1 == tyargs2
  -- TODO: type constructors
  _ == _ = False

instance Arbitrary Type where
  arbitrary = genericArbitrary' Z uniform
  shrink (TyArrow s t) = [s, t]
  shrink (TyRef s) = [s]
  shrink (TyVariant _ _ ctors) =
    concat $ concat $ shrink $ snd $ unzip ctors
  shrink _ = []

instance Arbitrary TypeConstructor where
  arbitrary = genericArbitrary' Z uniform
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
  show (TmPlaceholder _ classNm methodNm ty) =
    "(TmPlaceholder " ++ show classNm ++ " " ++ show methodNm ++ " "
    ++ show ty ++ ")"
        
instance Show α => Show (Command α) where
  show (CDecl _ s t) = "(CDecl " ++ show s ++ " " ++ show t ++ ")"
  show (CLet _ s t)  = "(CLet " ++ show s ++ " " ++ show t ++ ")"
  show (CEval _ t)   = "(CEval " ++ show t ++ ")"
  show (CCheck _ t)  = "(CCheck " ++ show t ++ ")"
  show (CAssert _ t) = "(CAssert " ++ show t ++ ")"
  show (CData _ x _ _) = "(CData " ++ show x ++ ")"
  show (CRecord _ x _ _) = "(CRecord " ++ show x ++ ")"
  show (CClass _ constrs nm tyvar methods) =
    "(CClass (" ++ intercalate " " (show <$> constrs) ++ ") " ++
    show nm ++ " " ++ show tyvar ++ " (" ++
    intercalate "" (show <$> methods) ++ "))"
  show (CInstance _ constrs nm ty methods) =
    "(CInstance (" ++ intercalate " " (show <$> constrs) ++ ") " ++
    show nm ++ " " ++ show ty ++ " (" ++
    intercalate "" (show <$> methods) ++ "))"

  
instance Show α => Show (Prog α) where
  show (Prog { prog_of = p }) =
    "(Prog\n" ++ intercalate "\n" (map show p) ++ "\n)"


---------
-- | Misc

-- For the value restriction on polymorphism.
isValue :: Term α -> Bool
isValue (TmAbs _ _ _ _) = True
isValue (TmUnit _)   = True
isValue (TmBool _ _) = True
isValue (TmInt _ _)  = True
isValue (TmChar _ _) = True
isValue (TmVariant _ _ tms) = and $ isValue <$> tms
isValue (TmRecord _ tms) = and $ isValue . snd <$> tms
isValue (TmUnop _ UFix (TmAbs _ _ _ tm)) = isValue tm
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
    TmPlaceholder fi _ _ _ -> fi

data_of_command :: Command α -> α
data_of_command c =
  case c of
    CDecl fi _ _         -> fi
    CLet fi _ _          -> fi
    CEval fi _           -> fi
    CCheck fi _          -> fi
    CData fi _ _ _       -> fi
    CRecord fi _ _ _     -> fi
    CAssert fi _         -> fi
    CClass fi _ _ _ _    -> fi
    CInstance fi _ _ _ _ -> fi


mkArrowType :: [Type] -> Type
mkArrowType [] = error "mkArrowType: empty list not allowed"
mkArrowType (x : [])     = x
mkArrowType (x : y : []) = TyArrow x y
mkArrowType (x : y : ys) = TyArrow x $ mkArrowType $ y : ys

-- Build a supercombinator with the given Ids (which may appear free
-- in the given body).
mkAbs :: [Id] -> Term α -> Term α
mkAbs [] tm = tm
mkAbs (x:xs) tm =
  TmAbs (data_of_term tm) x (mkTyVar $ Id "") $ mkAbs xs tm

-- Make a non-rigid type variable with no class constraints.
mkTyVar :: Id -> Type
mkTyVar s = TyVar False [] s

mkTyAbs :: [Id] -> Type -> Type
mkTyAbs [] ty = ty
mkTyAbs (y:ys) ty = TyAbs y KStar $ mkTyAbs ys ty

-- Apply a type to a list of arguments.
mkTyApp :: Type -> [Type] -> Type
mkTyApp s [] = s
mkTyApp s (t:ts) = mkTyApp (TyApp s t) ts

-------------------------------
-- | Type variable substitution

-- The type of type substitutions
type TypeSubst = [(Type, Type)]

-- The boolean determines whether to do capture avoiding substitution
-- or not. Not sure if it's necessary anymore since we stopped
-- explicitly tying the knot on recursive types.
class TySubstable a where
  tysubst :: Bool -> Type -> Type -> a -> a

-- Lift type substitution to lists.
instance TySubstable a => TySubstable [a] where
  tysubst b s t = fmap $ tysubst b s t

-- Lift type substitution to any bifunctor (e.g., pair). It would be
-- nice to use a similar instance for functors so we don't need the
-- list instance but then we have overlapping instances (incoherent
-- instances?) for Term.
instance (Bifunctor f, TySubstable a, TySubstable b) =>
         TySubstable (f a b) where
  tysubst b s t = bimap (tysubst b s t) (tysubst b s t)

-- Substitute one type for another in a type.
instance TySubstable Type where
  tysubst b s t ty@(TyAbs x k ty1) =
    if t == mkTyVar x then ty else
      if b && mkTyVar x `elem` freetyvars s then
      let x' = Id $ unId x ++ "_" in
        TyAbs x' k $ tysubst b s t
        (tysubst b (mkTyVar x') (mkTyVar x) ty1)
      else
        TyAbs x k $ tysubst b s t ty1
  tysubst b s t (TyApp ty1 ty2) =
    TyApp (tysubst b s t ty1) (tysubst b s t ty2)
  tysubst b s t (TyArrow ty1 ty2) =
    TyArrow (tysubst b s t ty1) (tysubst b s t ty2)
  tysubst b s t (TyRef ty) = TyRef (tysubst b s t ty)
  tysubst b s t (TyVariant x tyargs ctors) =
    TyVariant x (tysubst b s t <$> tyargs) $
    fmap (mapSnd $ fmap $ tysubst b s t) ctors
  tysubst b s t (TyRecord x tyargs fields) =
    TyRecord x (tysubst b s t <$> tyargs) $
    fmap (mapSnd $ tysubst b s t) fields
  tysubst b s t (TyConstructor ty) =
    TyConstructor $ tysubst b s t ty
  tysubst _ s t ty = if ty == t then s else ty

instance TySubstable TypeConstructor where
  tysubst b s t ty@(TypeConstructor
                     { tycon_tyargs = tyargs
                     , tycon_ty = uninst
                     , tycon_instantiated = inst }) =
    ty { tycon_tyargs = tysubst b s t <$> tyargs
       , tycon_ty = tysubst b s t uninst
       , tycon_instantiated = tysubst b s t inst }

-- Substitute one type for another in a lambda term.
instance TySubstable α => TySubstable (Term α) where
  tysubst b s t = termTypeRec $ tysubst b s t

instance TySubstable α => TySubstable (Command α) where
  tysubst b s t = commandTypeRec $ tysubst b s t

-- Substitute one type for another in a typing context.
instance (TySubstable β) => TySubstable (Symtab β) where
  tysubst b s t = Symtab.map (tysubst b s t)

tysubst' :: TySubstable a => Type -> Type -> a -> a
tysubst' = tysubst True

-- Fold over a list of individual substitutions on an instance of
-- TySubstClass.
tysubstAll :: TySubstable a => Bool -> TypeSubst -> a -> a
tysubstAll b tsubst x =
  foldl (\acc (s, t) -> tysubst b s t acc) x tsubst

tysubstAll' :: TySubstable a => TypeSubst -> a -> a
tysubstAll' tsubst x =
  foldl (\acc (s, t) -> tysubst' s t acc) x tsubst


-------------------------
-- | Free type variables

class FreeTyVars a where
  freetyvars :: a -> [Type]

instance FreeTyVars a => FreeTyVars [a] where
  freetyvars = nub . concat . fmap freetyvars

-- This relies on the fact that well-formed named types never have
-- free type variables, and that the argument type is not infinite
-- (don't normalize types before computing their free type variables).
instance FreeTyVars Type where
  freetyvars = nub . flip evalState [] .
    (typeRec2M $
     \ty ->
       case ty of
              ty@(TyVar _ _ _) -> do
                xs <- get
                return $ if ty `elem` xs then [] else [ty]
              ty@(TyAbs x _ _) ->
                modify ((:) $ mkTyVar x) >> return []
              ty@(TyConstructor (TypeConstructor
                                 { tycon_tyvars = tyvars })) ->
                modify ((++) $ mkTyVar <$> tyvars) >> return []
              _ -> return [])
