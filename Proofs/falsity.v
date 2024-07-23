Lemma succ_neq_zero_lemma : forall n : nat, O = S n -> False.
Proof.
  intros.
  inversion H.
Qed.

Theorem succ_neq_zero : forall n m: nat, S n = m -> 0 = m -> False.
Proof.
  intros.
  symmetry in H.
  apply (succ_neq_zero_lemma n).
  transitivity m.
  assumption.
  assumption.
Qed.

Theorem succ_neq_zero2 : forall n m: nat, S n = m -> 0 = m -> False.
Proof.
intros n m H1 H2. rewrite <- H2 in H1. inversion H1.
Qed.