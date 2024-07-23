Inductive even : nat -> Prop :=
even0 : even 0
| evenS : forall x:nat, even x -> even (S (S x)).

Lemma even_mult : forall x, even x -> exists y, x = 2*y.
Proof.

Require Import ArithRing.

intros x H.
induction H.
exists 0.
ring.
destruct IHeven as [y Heq].
rewrite Heq.
exists (S y).
ring.
Qed.

Lemma not_even_1 : ~even 1.
Proof.
intros even1.
inversion even1.
Qed.

Lemma even_inv : forall x, even (S (S x)) -> even x.
Proof.
intros x H.
inversion H.
assumption.
Qed.

