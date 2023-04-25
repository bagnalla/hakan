-- | Generate variant constructor and record projection functions.

{-# LANGUAGE LambdaCase #-}

module FunGen (funGen) where

import Ast
import Symtab (Id(..))
import Tycheck (TyData(..))

mkAbs' :: [(Id, Type)] -> Term TyData -> Term TyData
mkAbs' [] tm = tm
mkAbs' ((x, ty):xs) tm =
  let inner = mkAbs' xs tm in
    TmAbs (TyData $ TyArrow ty $ unTyData $ data_of_term inner) x ty $ mkAbs' xs tm

-- -- Build constructor functions and add them to the environment.
-- interpCommands (CData _ nm _ ctors : cs) = do
--   funs <-
--     mapM (\(x, tys) -> do
--              let ids = map (Id . (:[])) $
--                        take (length tys) ['a'..]
--              val <- eval $ mkAbs ids (TmVariant () x $ map (TmVar ()) ids)
--              return $ (x, val)) ctors
--   local (\(Env e) -> Env $ foldl (\acc (x, f) -> add x f acc) e funs) $
--     interpCommands cs
    
-- -- Build field projection functions and add them to the environment. 
-- interpCommands (CRecord _ nm _ fields : cs) = do
--   funs <- mapM (\(x, ty) -> do
--                    val <- eval $ TmAbs () (Id "x") TyUnit
--                           (TmMatch () (TmVar () (Id "x"))
--                            [(PRecord [(x, PVar (Id "y"))],
--                              TmVar () (Id "y"))])
--                    return (x, val)) fields
--   local (\(Env e) -> Env $ foldl (\acc (x, f) -> add x f acc) e funs) $
--     interpCommands cs

funGenCommand :: Command TyData -> [Command TyData]
funGenCommand = \case
  c@(CData (TyData ty) nm typarams ctors) -> c :
    map (\(ctor_nm, arg_tys) ->
            let args = map (\(i, ty) -> (Id $ "x" ++ show i, ty)) $ zip [0..] arg_tys in
              CLet (TyData $ mkArrowType $ arg_tys ++ [ty]) ctor_nm $
              mkAbs' args $ TmVariant (TyData ty) ctor_nm $
              map (\(x, ty) -> TmVar (TyData ty) x) (args)) ctors

  c@(CRecord (TyData ty) nm typarams fields) -> c :
    map (\(field_nm, field_ty) ->
           CLet (TyData $ mkArrowType [ty, field_ty]) field_nm $
           mkAbs' [(Id "x", ty)] $
           TmMatch (TyData field_ty) (TmVar (TyData ty) (Id "x"))
           [(PRecord [(field_nm, PVar (Id "y"))], TmVar (TyData field_ty) (Id "y"))]
        ) fields
  
  c -> [c]

  -- | PRecord [(Id, Pattern)]
  -- | TmMatch α (Term α) [(Pattern, Term α)]
  -- | TmVariant α Id [Term α]
    -- | CLet α Id (Term α)

-- data Command α =
--   | CData α Id [Id] [(Id, [Type])]
--   | CRecord α Id [Id] [(Id, Type)]

funGen :: Prog TyData -> Prog TyData
funGen p@(Prog { prog_of = cs }) =
  p { prog_of = concatMap funGenCommand cs }
