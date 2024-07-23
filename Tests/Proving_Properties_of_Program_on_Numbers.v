Fixpoint sum_n n :=
match n with
0 => 0
| S p => p + sum_n p
end.

Fixpoint evenb n :=
match n with
0 => true
| 1 => false
| S (S p) => evenb p
end.

Require Import ArithRing.

(* Require Import ZArith.
Open Scope Z_scope.

Goal forall a b c:Z,
    (a + b + c) ^ 2 =
     a * a + b ^ 2 + c * c + 2 * a * b + 2 * a * c + 2 * b * c.
intros.
ring.
Qed. *)

(*Induction*)
Lemma sum_n_p : forall n, 2 * sum_n n + n = n * n.
Proof.
induction n.
reflexivity.
assert (SnSn : S n * S n = n * n + 2 * n + 1).
ring.
rewrite SnSn.
rewrite <-IHn.
simpl.
ring.
Qed.

Lemma evenb_p : forall n, evenb n = true -> exists x, n = 2 * x.
Proof.
assert (Main: forall n, (evenb n = true -> exists x, n = 2 * x) /\
(evenb (S n) = true -> exists x, S n = 2 * x)).
induction n.
split.
exists 0; ring.
simpl; intros H; discriminate H.
split.
destruct IHn as [_ IHn']; exact IHn'.
simpl evenb; intros H; destruct IHn as [IHn' _].
assert (H' : exists x, n = 2 * x).
apply IHn'; exact H.
destruct H' as [x q]; exists (x + 1); rewrite q; ring.
intros n ev.
destruct (Main n) as [H _]; apply H; exact ev.
Qed.


(*Exercise*)
Fixpoint add n m := match n with 0 => m | S p => add p (S m) end.

Lemma add_n_S : forall n m, add n (S m) = S (add n m).
induction n; intros m; simpl.
reflexivity.
rewrite IHn; reflexivity.
Qed.

Lemma add_S_n : forall n m, add (S n) m = S (add n m).
intros n m; simpl; rewrite add_n_S; reflexivity.
Qed.

Lemma add_plus : forall n m, add n m = n + m.
induction n; intros m.
reflexivity.
rewrite add_S_n.
rewrite IHn.
reflexivity.
Qed.


Fixpoint sum_odd_n (n:nat) : nat :=
match n with 0 => 0 | S p => 1 + 2 * p + sum_odd_n p end.

Lemma sum_Odd : forall n:nat, sum_odd_n n = n*n.
induction n.
reflexivity.
simpl.
rewrite IHn.
ring.
Qed.

(*Continuing tutorial*)
