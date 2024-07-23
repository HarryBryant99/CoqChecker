(*Utilities*)
Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | 0  , _   => true
  | _  , 0   => false
  | S n, S m => leb n m
  end.

Compute leb 2 2.

Fixpoint lt (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => false
         | S m => true
         end
  | S n' => match m with
            | O => false
            | S m' => lt n' m'
            end
  end.

Compute lt 2 2.

(*-------------------------------------------------------------------------*)

Check (fun x:nat => x = 3).

Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).

Locate "_ <= _".

Compute let f := fun x => (x * 3, x) in f 3.

Print pred.
Print Init.Nat.pred.

Fixpoint evenb n :=
match n with
0 => true
| 1 => false
| S (S p) => evenb p
end.

Compute evenb 2.

(*Exercise on functions:*)
Check fun a b c d e => a + b + c + d + e.
Compute (fun a b c d e => a + b + c + d + e) 1 2 3 4 5.

Require Import List.
Fixpoint first_n_aux (n:nat)(m:nat) :=
match n with 0 => nil | S p => m :: first_n_aux p (m+1) end.
Definition first_n (n:nat) := first_n_aux n 0.

Compute first_n 3.

(*Exercise on sorting*)
Definition head_sorted (l : list nat) : bool :=
match l with
a::b::_ => leb a b
| _ => true
end.
Fixpoint sorted (l : list nat) : bool :=
match l with
a::tl => if head_sorted (a::tl) then sorted tl else false
| nil => true
end.

Compute sorted (1::2::nil).
Compute sorted (1::2::3::nil).
Compute sorted (1::3::2::nil).

(*Exercise on counting*)
Fixpoint count (n : nat) (l : list nat) : nat :=
match l with
nil => 0
| h::tl => if Nat.eqb n h then 1 + count n tl else count n tl
end.