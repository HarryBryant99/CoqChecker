module Add where

import qualified Prelude

data Nat =
   O
 | S Nat

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

sum_n2 :: Nat -> Nat -> Nat
sum_n2 n s =
  case n of {
   O -> s;
   S p -> sum_n2 p (add p s)}

