module My_add where

import qualified Prelude

data Nat =
   O
 | S Nat

my_add :: Nat -> Nat -> Nat
my_add n m =
  case n of {
   O -> m;
   S p -> my_add p (S m)}

