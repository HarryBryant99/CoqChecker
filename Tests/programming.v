Definition example1 := fun x : nat => x*x+2*x+1.
Definition example1B (x : nat) := x*x+2*x+1.

Check example1.
Compute example1 2.



Require Import Bool.

Compute if true then 3 else 5.

SearchPattern bool.

Definition is_zero (n:nat) :=
match n with
0 => true
| S p => false
end.

Compute is_zero 0.
Compute is_zero 1.

Print pred.

Print Init.Nat.pred.

Fixpoint sum_n n :=
match n with
0 => 0
| S p => p + sum_n p
end.

Compute sum_n 3.

Fixpoint sum_n2 n s :=
match n with
0 => s
| S p => sum_n2 p (p + s)
end.

Compute sum_n2 3 2.

Require Coq.extraction.Extraction.
Extraction Language Haskell.
Extraction "add.hs" sum_n2.

Require Import List.

Check 1::2::3::nil.

Compute map (fun x => x + 3) (1::3::2::nil).

Compute map S (1::22::3::nil).

Compute let l := (1::2::3::nil) in l ++ map (fun x => x + 3) l.

SearchPattern (nat -> nat -> bool).
Search Nat.eqb.



(*Exercise*)
Fixpoint first_n_aux (n:nat)(m:nat) :=
match n with 0 => nil | S p => m :: first_n_aux p (m+1) end.
Definition first_n (n:nat) := first_n_aux n 0.
Compute first_n 2.

Definition assign (n:nat) (m:nat) :=
match n with
0 => 0
| S p => p
end.

Compute assign 4 1.

Fixpoint test_aux (n:nat)(m:nat) :=
match n with 0 => nil | S p => p :: test_aux p (m+1) end.
Definition test (n:nat) := test_aux n 0.
Compute test 10.

(*Continuing Guide*)
Fixpoint evenb n :=
match n with
0 => true
| 1 => false
| S (S p) => evenb p
end.

Definition head_evb l :=
match l with nil => false | a::tl => evenb a end.

Fixpoint sum_list l :=
match l with nil => 0 | n::tl => n + sum_list tl end.


Fixpoint lef (n m:nat) {struct m} : bool :=
  match n, m with
  | O, _ => true
  | _, O => false
  | S n, S m => lef n m
  end.

Fixpoint insert n l :=
match l with
nil => n::nil
| a::tl => if (lef n a) then n::l else a::insert n tl
end.

Fixpoint sort l :=
match l with
nil => nil
| a::tl => insert a (sort tl)
end.

Compute sort (2::1::nil).


(*Exercise*)
Definition head_sorted (l : list nat) : bool :=
match l with
a::b::_ => lef a b
| _ => true
end.
Fixpoint sorted (l : list nat) : bool :=
match l with
a::tl => if head_sorted (a::tl) then sorted tl else false
| nil => true
end.

Compute sorted (2::32::3::nil).
Compute sorted (2::3::4::nil).

Fixpoint count (n : nat) (l : list nat) : nat :=
match l with
nil => 0
| p::tl => if (lef n p) 
  then if (lef p n) then
    1 + count n tl else count n tl
  else count n tl
end.

Compute count 1 (2::2::nil).

Extraction "count.hs" count.