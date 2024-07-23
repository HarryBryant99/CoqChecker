Require Reals.

SearchAbout ["Cauchy"].

Fixpoint power (x n : nat) {struct n} : nat :=
  match n with
  | O => 1
  | S m => x * power x m
  end.

Notation "x ^ n" := (power x n).

Theorem Test :
  (forall x y z n : nat, x^n + y^n = z^n -> n <= 2).
Proof.
mult