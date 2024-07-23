Require Import Nat.
Require Import Arith.

Theorem QuotientRemainder : forall n d : nat,
  d > 0 ->
  exists q r : nat, (n = d * q + r) /\ (r >= 0) /\ (d > r).

Proof.
  intros n d d'. induction n.
  - (** base case where n = 0 **)
  exists 0. 
  exists 0.
  split. 
  ring. 
  split.
  auto.
  apply d'.

  - (** inductive step **)
  destruct IHn as [q IHn].
  destruct IHn as [r IHn].
  exists q.
  exists (r+1).
  split.
  rewrite Nat.add_assoc.
  rewrite Nat.add_1_r.
  apply f_equal.
  destruct IHn.
  apply H.
  split.
  destruct IHn.
  destruct H0.
  rewrite Nat.add_1_r.
  destruct H0.
  auto.
  auto.

  rewrite Nat.add_1_r.

  destruct IHn.
  
  destruct d.
  destruct H0 as [h1 h2].
  

  destruct H0.

  destruct H0.
  destruct 

  destruct r.
  simpl.
  destruct d.

  destruct H1.

  rewrite Nat.add_1_r.

  destruct d.
  destruct H1.
  assumption.
  intuition.
  destruct H1.
  contradiction.

  destruct H1.

  


  discriminate.




  destruct IHn.
  destruct H0 as [h1 h2].
  
  rewrite Nat.add_1_r.
  destruct h2.
  auto.
  
  intuition.
  
  destruct IHn.
  

  destruct h2.
  auto.

  destruct r.
  simpl.
  

  destruct IHn.
  destruct H.
  rewrite Nat.add_1_r.
  destruct H0.
  

  apply H1.
  

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

Fixpoint sub (n m:nat) : nat :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end
where "n - m" := (sub n m) : nat_scope.

Fixpoint sum_n n :=
match n with
0 => 0
| S p => p + sum_n p
end.

Compute sum_n 3.

Fixpoint quotient (v d q:nat) : nat:=
match v with
0 => q
| p => quotient (v-1) d q
end.

Fixpoint remainder (v d q:nat) : nat:= 
if lt v d then q
else remainder (sub v d) d q.

Definition division (v d) : nat:= remainder(v d 0).