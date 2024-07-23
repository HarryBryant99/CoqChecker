Inductive bin : Type :=
L : bin
| N : bin -> bin -> bin.

Check N L (N L L).

(*Exercise*)
Inductive three : Type :=
three_constant
| three_3 (n : nat) (a b : three)
| three_4 (m : bool) (c d e : three).

Definition example7 (t : bin): bool :=
match t with N L L => false | _ => true end.

Fixpoint flatten_aux (t1 t2:bin) : bin :=
match t1 with
L => N L t2
| N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
end.
Fixpoint flatten (t:bin) : bin :=
match t with
L => L | N t1 t2 => flatten_aux t1 (flatten t2)
end.
Fixpoint size (t:bin) : nat :=
match t with
L => 1 | N t1 t2 => 1 + size t1 + size t2
end.

Compute flatten_aux (N L L) L.


(*Proof by Cases*)
Lemma example7_size :
forall t, example7 t = false -> size t = 3.
Proof.
intros t.
destruct t.
simpl.
discriminate.
destruct t1.
destruct t2.
simpl.
auto.
simpl.
discriminate.
simpl.
discriminate.
Qed.

Require Import ArithRing.

(*Proof by Induction*)
Lemma flatten_aux_size :
forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
Proof.
induction t1.
intros t2.
simpl.
ring.
intros t2.
simpl.
rewrite IHt1_1.
rewrite IHt1_2.
ring.
Qed.

(*Exercise*)
Lemma flatten_size : forall t, size (flatten t) = size t.
Proof.
intros t.
elim t.
simpl.
reflexivity.
intros t1 IH1 t2 IH2.
simpl.
rewrite flatten_aux_size.
rewrite IH2.
ring.
Qed.

(*Continuing Tutorial - Injection*)
Lemma not_subterm_self_l : forall x y, ~ x = N x y.
Proof.
induction x.
intros y.
discriminate.
intros y abs.
injection abs.
intros h2 h1.
assert (IHx1' : x1 <> N x1 x2).
apply IHx1.
case IHx1'.
exact h1.
Qed.