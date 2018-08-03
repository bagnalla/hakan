-- | This module contains the typechecker. It is a function from
-- untyped ASTs with line/column number metadata to ASTs with type
-- metadata.

module Tycheck (
  TyData, runTycheck, tycheckProg
  ) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

import Data.Maybe (fromJust)

import Ast
import Core (data_of_term, data_of_command, FreeTyVars(..), ConstrSet,
             TypeSubst, unify, idOfType, TySubstable(..), tysubstAll)
import Gensym (nextSym, nextSym2, nextSym3)
import Parser
import Symtab (Symtab, Id(..), empty, add, get, exists)


---------------------------------------------
-- | The type of metadata for typechecked terms.

newtype TyData = TyData { unTyData :: Type }
               deriving (Show)

mkData ty = TyData ty

-- TyData can receive type substitution
instance TySubstable TyData where
  tysubst s t fi = TyData (tysubst s t (unTyData fi))


-----------------
-- | Typechecker

type Context = Symtab TypeScheme

-- The reader carries two contexts. The first is for explicit type
-- declarations given by the programmer, and the second is the regular
-- typing context.
type TycheckM a =
  ReaderT (Context, Context) (ExceptT String (StateT Int Identity)) a

runTycheck :: TycheckM a -> Either String a
runTycheck t =
  fst $ runIdentity (runStateT (runExceptT (runReaderT t (empty, empty))) 0)

unifyError :: Show α => Type -> Type -> α -> TycheckM b
unifyError s t fi =
  throwError $ "Type error: unable to unify " ++ show s ++ " and " ++
  show t ++ " at " ++ show fi

tryUnify :: Show α => α -> ConstrSet -> (TypeSubst -> TycheckM a) ->
            TycheckM a
tryUnify fi c f =
  case unify c of
    Left (s, t) -> unifyError s t fi
    Right tsubst -> f tsubst

tycheckTerm :: Show α => Term α -> TycheckM (Term TyData, ConstrSet)
tycheckTerm (TmVar fi x) = do
  -- 'asks' takes a function mapping the context to a value
  tyscheme <- asks (Symtab.get x . snd)
  case tyscheme of
    Just tyscheme' -> do
      ty <- instantiate_tyscheme tyscheme'
      return $ (TmVar (mkData ty) x, [])
    Nothing ->
      throwError $ "Type error: unbound identifier " ++ show x ++
      " at " ++ show fi

tycheckTerm (TmAbs fi x ty tm) = do
  (tm', c) <- local (\(decls, ctx) ->
                       (decls, add x (mkTypeScheme [] ty) ctx)) $
              tycheckTerm tm
  let ty' = ty_of_term tm'
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $
               TmAbs (mkData $ TyArrow ty ty') x ty tm',
              c)

tycheckTerm (TmApp fi t1 t2) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  x <- nextSym "?Y_"
  let tyx = TyVar False (Id x)
  let c = c1 ++ c2 ++ [(ty1, TyArrow ty2 tyx)]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $ TmApp (mkData tyx) t1' t2', c)

tycheckTerm (TmBool fi b) =
  return (TmBool (mkData TyBool) b, [])

tycheckTerm (TmIf fi t1 t2 t3) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  (t3', c3) <- tycheckTerm t3
  let (ty1, ty2, ty3) = (ty_of_term t1', ty_of_term t2', ty_of_term t3')
  let c = c1 ++ c2 ++ c3 ++ [(ty1, TyBool), (ty2, ty3)]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $ TmIf (mkData ty2) t1' t2' t3', c)

tycheckTerm (TmUnit fi) =
  return (TmUnit (mkData TyUnit), [])

tycheckTerm (TmInt fi i) =
  return (TmInt (mkData TyInt) i, [])

tycheckTerm (TmUnop fi u tm) = do
  (tm', c) <- tycheckTerm tm
  let ty = ty_of_term tm'
  case u of

    UFix -> do
      y <- nextSym "?Y_"
      let tyy = TyVar False (Id y)
      let c' = c ++ [(ty, TyArrow tyy tyy)]
      tryUnify fi c' $
        \tsubst ->
          return (tysubstAll tsubst $ TmUnop (mkData tyy) u tm', c')

    _ | u == UFst || u == USnd -> do
          (x, y) <- nextSym2 "?Y_"
          let (tyx, tyy) = (TyVar False (Id x), TyVar False (Id y))
          let c' = c ++ [(ty_of_term tm', TyPair tyx tyy)]
          tryUnify fi c' $
            \tsubst ->
              let fi' = mkData $ if u == UFst then tyx else tyy in
                return (tysubstAll tsubst $ TmUnop fi' u tm', c')
  
    URef ->
      return (TmUnop (mkData $ TyRef ty) URef tm', c)

    UDeref -> do
      x <- nextSym "?Y_"
      let tyx = TyVar False (Id x)
      let c' = c ++ [(ty, TyRef tyx)]
      tryUnify fi c' $
        \tsubst ->
          return (tysubstAll tsubst $ TmUnop (mkData $ tyx) u tm',
                  c')

    -- UMinus, UNot
    -- This may be a little weird when we add floats. Maybe this is
    -- why OCaml has separate operators for them.
    _ -> do
      let c' = c ++ [(ty, case u of
                            UMinus -> TyInt
                            UNot -> TyBool)]
      tryUnify fi c' $
        \tsubst ->
          return (tysubstAll tsubst $ TmUnop (mkData ty) u tm', c')

-- When we add floats, we can just introduce a type variable for the
-- type of the binop term and add a constraint that it's equal to the
-- type of the arguments in the case of arithmetic operations (or
-- equal to bool in the other cases, etc.).
-- Is that really right though? We really need to ensure that the
-- operands have arithmetic types and not just arbitrary types that
-- happen to be the same on both sides.
-- Typeclasses would obviously fix the problem since we could have a
-- class for numeric types and provide instances for int and float.
tycheckTerm (TmBinop fi b t1 t2) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  let ty1 = ty_of_term t1'
  let ty2 = ty_of_term t2'
  let c = c1 ++ c2 ++
          if isBUpdate b then [(ty1, TyRef ty2)]
          else if isArithBinop b then [(ty1, ty2), (ty1, TyInt)]
          else if isComparisonBinop b then [(ty1, ty2), (ty1, TyBool)]
          else []
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $
              TmBinop (mkData $ binopType b) b t1' t2', c)
          
tycheckTerm (TmPair fi t1 t2) = do
  (t1', c1) <- tycheckTerm t1
  (t2', c2) <- tycheckTerm t2
  y <- nextSym "?Y_"
  let tyy = TyVar False (Id y)
  let c = c1 ++ c2 ++ [(tyy, TyPair (ty_of_term t1') (ty_of_term t2'))]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $ TmPair (mkData tyy) t1' t2', c)

tycheckTerm (TmInl fi tm ty) = do
  (tm', c) <- tycheckTerm tm
  x <- nextSym "?Y_"
  let tyx = TyVar False (Id x)
  let c' = c ++ [(ty, TySum (ty_of_term tm') tyx)]
  tryUnify fi c' $
    \tsubst ->
      return (tysubstAll tsubst $ TmInl (mkData ty) tm' ty, c')

tycheckTerm (TmInr fi tm ty) = do
  (tm', c) <- tycheckTerm tm
  x <- nextSym "?Y_"
  let tyx = TyVar False (Id x)
  let c' = c ++ [(ty, TySum tyx (ty_of_term tm'))]
  tryUnify fi c' $
    \tsubst ->
      return (tysubstAll tsubst $ TmInr (mkData ty) tm' ty, c')

tycheckTerm (TmCase fi discrim nm1 t1 nm2 t2) = do
  (discrim', c1) <- tycheckTerm discrim
  let ty = ty_of_term discrim'
  (x, y, z) <- nextSym3 "?Y_"
  let (tyx, tyy, tyz) = (TyVar False (Id x), TyVar False (Id y),
                         TyVar False (Id z))
  (t1', c2) <- local (\(decls, ctx) ->
                        (decls, add nm1 (mkTypeScheme [] tyy) ctx)) $
               tycheckTerm t1
  (t2', c3) <- local (\(decls, ctx) ->
                        (decls, add nm2 (mkTypeScheme [] tyz) ctx)) $
               tycheckTerm t2
  let c = c1 ++ c2 ++ c3 ++ [(ty, TySum tyy tyz),
                             (ty_of_term t1', ty_of_term t2')]
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $
              TmCase (mkData tyx) discrim' nm1 t1' nm2 t2', c)

tycheckTerm (TmLet fi x tm1 tm2) = do
  (tm1', c1) <- tycheckTerm tm1
  let ty1 = ty_of_term tm1'
  tyscheme <- if isValue tm1' then generalize_ty ty1
              else return $ mkTypeScheme [] ty1
  (tm2', c2) <- local (\(decls, ctx) ->
                         (decls, add x tyscheme ctx)) $
                tycheckTerm tm2
  let c = c1 ++ c2
  tryUnify fi c $
    \tsubst ->
      return (tysubstAll tsubst $
              TmLet (mkData $ ty_of_term tm2') x tm1' tm2', c)

tycheckCommand :: Show α => Command α -> TycheckM (Command TyData)
tycheckCommand (CDecl fi x ty) = return $ CDecl (mkData TyUnit) x ty

tycheckCommand (CLet fi x t) = do
  (t', _) <- tycheckTerm t
  return $ CLet (mkData (ty_of_term t')) x t'

tycheckCommand (CEval fi t) = do
  (t', _) <- tycheckTerm t
  return $ CEval (mkData (ty_of_term t')) t'

tycheckCommands :: Show α => [Command α] -> TycheckM [Command TyData]
tycheckCommands [] = return []
tycheckCommands (com:coms) = do
  com' <- tycheckCommand com
  case com' of
    CDecl _ x ty -> do
      tyscheme <- generalize_ty ty
      coms' <- local (\(decls, ctx) -> (add x tyscheme decls, ctx)) $
               tycheckCommands coms
      return $ com' : coms'
    CLet fi x tm -> do
      (decls, ctx) <- ask
      let ty = ty_of_term tm
      -- Enforce value restriction since we have mutable references.
      -- I.e., only generalize the type when then term is a syntactic
      -- value. See TAPL or Xavier Leroy's PhD thesis.
      tyscheme <- if isValue tm then generalize_ty ty
                  else return $ mkTypeScheme [] ty
      case Symtab.get x decls of
        Just declTyscheme -> do
          -- Ignore the result of unifying the type schemes since we
          -- want to use the exact type declared by the programmer.
          _ <- unify_tyschemes (data_of_command com) tyscheme declTyscheme
          let tyscheme' = loosen_tyscheme declTyscheme
          coms' <- local (const (decls, add x tyscheme' ctx)) $
                   tycheckCommands coms
          return $ com' : coms'
        Nothing -> do
          coms' <- local (const (decls, add x tyscheme ctx)) $
                   tycheckCommands coms
          return $ com' : coms'
    _ -> do
      coms' <- tycheckCommands coms
      return $ com' : coms'

tycheckProg :: Show α => Prog α -> TycheckM (Prog TyData)
tycheckProg p = do
  coms <- tycheckCommands (prog_of p)
  return $ Prog { pdata_of = mkData TyBool, prog_of = coms }


----------
-- | Misc

ty_of_term :: Term TyData -> Type
ty_of_term = unTyData . data_of_term

-- ty_of_command :: Command TyData -> Type
-- ty_of_command = unTyData . data_of_command

generalize_ty :: Type -> TycheckM TypeScheme
generalize_ty ty = do
  (_, ctx) <- ask
  let fvs= freetyvars ty
  let generalizable = map (fromJust . idOfType)
        (filter (\(TyVar _ x) -> not $ x `exists` ctx) fvs)
  return $ mkTypeScheme generalizable ty

-- Assumes type variables are not rigid.
instantiate_tyscheme :: TypeScheme -> TycheckM Type
instantiate_tyscheme tyscheme = do
  tyscheme' <- foldM (\acc x -> do
                         y <- nextSym "?Y_"
                         return $ tysubst (TyVar False x) (TyVar False (Id y)) acc)
         tyscheme (ts_tyvars_of tyscheme)
  return (ts_ty_of tyscheme')

-- The first type scheme argument should be that obtained from
-- typechecking the body of a let command, and the second should be
-- the declared type. We expect the first to be more general than the
-- second.
unify_tyschemes :: Show α => α -> TypeScheme -> TypeScheme -> TycheckM Type
unify_tyschemes fi tyscheme1 tyscheme2 = do
  ty1 <- instantiate_tyscheme tyscheme1
  ty2 <- instantiate_tyscheme tyscheme2
  case unify [(ty1, ty2)] of
    Left (s, t) -> unifyError s t fi
    Right tsubst -> return $ tysubstAll tsubst ty1


-- Make all type variables in a typescheme non-rigid.
loosen_tyscheme :: TypeScheme -> TypeScheme
loosen_tyscheme tyscheme =
  tyscheme { ts_ty_of = typeRec2 (\t ->
                                    case t of
                                      TyVar _ x -> TyVar False x
                                      _ -> t) $
                        ts_ty_of tyscheme }
