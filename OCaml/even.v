Inductive even : nat -> Prop :=
| even_0 : even O
| even_SS : forall n:nat, even n -> even (S (S n)).

Goal even 0.
Proof.
  (* Use the even_0 constructor to prove that 0 is even *)
  apply even_0.
Qed.

Goal even 2.
Proof.
  (* Use the even_SS constructor with even_0 to prove that 2 is even *)
  apply even_SS.
  apply even_0.
Qed.

Goal even 8.
Proof.
  apply even_SS.
  apply even_SS.
  apply even_SS.
  apply even_SS.
  apply even_0.
Qed.

Require Import Arith.
(*So we can rewrite the goal in the Induction Step*)

Lemma even_double : forall n : nat, even (n + n).
Proof.
  intros n.
  induction n as [| n' IHn].
  - (* Base case: n = 0 *)
    simpl. apply even_0.
  - (* Inductive case: n = S n' *)
    simpl. rewrite plus_comm. simpl. apply even_SS. apply IHn.
Qed.

(*
Lemma even_double_equals_m : forall n : nat, even n -> {m : nat | (m + m) = n}.
Proof.
intros.
elim H.
*)

Lemma even_double_equals_m : forall n : nat, even n -> exists m : nat, (m + m) = n.
Proof.
intros n u.
elim u.

(*Base Case*)
exists 0.
simpl.
reflexivity.

(*Inductive Case*)
intros n' IH.
intro t.
destruct t as [m' propm].
exists (S(m')).
rewrite <- propm.
simpl.
auto.
Qed.

(*Extract and run*)

Require Coq.extraction.Extraction.

(* Use the Extraction command to generate OCaml code *)
Extraction Language OCaml.
Extraction "C:\Users\z004u5bh\Documents\Coq\OCaml\even.ml" even_double_equals_m.
