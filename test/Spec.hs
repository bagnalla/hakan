
-- import Data.List (nub)
-- import Generic.Random.Generic
-- import Test.QuickCheck
-- import Test.QuickCheck.All
-- -- import Test.Invariant

-- import Ast
-- import Core

-- -- tysubst and freetyvars commute for Types.
-- -- Oops, this isn't right unless we only substitute type variables for
-- -- type variables.
-- prop_tysubst_freetyvars_commute_Type :: Type -> Type -> Type -> Property
-- prop_tysubst_freetyvars_commute_Type s t x =
--   isTyVar s && isTyVar t ==>
--   freetyvars (tysubst s t x) == nub (tysubst s t (freetyvars x))

-- -- prop_tysubst_freetyvars_commute_Term :: Type -> Type -> (Term α) -> Property
-- -- prop_tysubst_freetyvars_commute_Term s t x =
-- --   isTyVar s && isTyVar t ==>
-- --   freetyvars (tysubst s t x) == nub (tysubst s t (freetyvars x))

main :: IO ()
-- Where is withMaxSuccess?
-- main = quickCheck $ withMaxSuccess 100 $ prop_tysubst_freetyvars_commute_Type
main = do
  putStrLn ""
  -- quickCheck $ prop_tysubst_freetyvars_commute_Type
  -- quickCheck $ prop_tysubst_freetyvars_commute_Type
