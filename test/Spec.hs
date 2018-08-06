
import Generic.Random.Generic
import Test.QuickCheck
import Test.QuickCheck.All
-- import Test.Invariant

import Ast
import Core

-- tysubst and freetyvars commute for Types
prop_tysubst_freetyvars_commute_Type :: Type -> Type -> Type -> Bool
prop_tysubst_freetyvars_commute_Type x s t =
  freetyvars (tysubst s t x) == tysubst s t (freetyvars x)

main :: IO ()
main = quickCheck $ prop_tysubst_freetyvars_commute_Type
