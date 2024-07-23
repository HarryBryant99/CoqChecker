Require Import Nat.
Require Import Arith.

Lemma example4 : 3 <= 5.
Proof.
apply le_S.
apply le_S.
apply le_n.
Qed.

Search (_ + _).

Check le_n.

Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
intros x y x10 y10.
apply Nat.le_trans with (m:=10).
assumption.
assumption.
Qed.

Lemma pred_S_eq : forall x y, x = S y -> Nat.pred x = y.
Proof.
intros x y q.
unfold Nat.pred.
rewrite q.
auto.
Qed.