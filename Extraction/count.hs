module Count where

import qualified Prelude

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

data List a =
   Nil
 | Cons a (List a)

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

lef :: Nat -> Nat -> Bool
lef n m =
  case n of {
   O -> True;
   S n0 -> case m of {
            O -> False;
            S m0 -> lef n0 m0}}

count :: Nat -> (List Nat) -> Nat
count n l =
  case l of {
   Nil -> O;
   Cons p tl ->
    case lef n p of {
     True ->
      case lef p n of {
       True -> add (S O) (count n tl);
       False -> count n tl};
     False -> count n tl}}

