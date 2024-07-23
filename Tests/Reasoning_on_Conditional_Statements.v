Definition is_zero (n:nat) :=
match n with
0 => true
| S p => false
end.

Lemma not_is_zero_pred :
forall x, is_zero x = false -> S (Nat.pred x) = x.
Proof.
intros x.
unfold is_zero, Nat.pred.
Print nat.
destruct x as [ | p].
discriminate.
intros H.
reflexivity.
Qed.