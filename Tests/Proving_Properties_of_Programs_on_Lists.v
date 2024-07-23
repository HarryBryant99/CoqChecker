Require Import List.

Fixpoint lef (n m:nat) {struct m} : bool :=
  match n, m with
  | O, _ => true
  | _, O => false
  | S n, S m => lef n m
  end.

Fixpoint count n l :=
match l with
nil => 0
| a::tl =>
let r := count n tl in if lef n a then 
  if lef a n then 1+r else r
  else r
end.

Fixpoint insert n l :=
match l with
nil => n::nil
| a::tl => if (lef n a) then n::l else a::insert n tl
end.


Compute count 2 (2::2::nil).
Compute count 3 (2::2::nil).
Compute count 2 (2::3::nil).