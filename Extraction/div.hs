module Div where

import qualified Prelude

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

mul :: Nat -> Nat -> Nat
mul n m =
  case n of {
   O -> O;
   S p -> add m (mul p m)}

lef :: Nat -> Nat -> Bool
lef n m =
  case n of {
   O -> True;
   S n0 -> case m of {
            O -> False;
            S m0 -> lef n0 m0}}

div :: Nat -> ((Nat -> Nat -> Bool) -> Nat -> Nat) -> Nat
div x y =
  case x of {
   O -> O;
   S x' ->
    let {z = div x' y} in case mul (S z) (y lef x) of {
                           O -> S z;
                           S _ -> z}}

