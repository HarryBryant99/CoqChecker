Require Import Bool.
Require Import String.
Require Import List.
Import List.ListNotations.
Open Scope string_scope.

Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.
Definition clause := list(literal).
Definition formula := list(clause).

Lemma literal_eq_dec : forall (l1 l2 : literal), {l1 = l2} + {l1 <> l2}.
Proof.
intros.
decide equality; apply string_dec.
Defined.

Fixpoint literal_eq (l1 l2 : literal) : bool :=
  match l1, l2 with
  | pos s1, pos s2 => if string_dec s1 s2 then true else false
  | neg s1, neg s2 => if string_dec s1 s2 then true else false
  | _, _ => false
  end.

Fixpoint In (a:literal) (l:clause) : bool :=
    match l with
      | nil => false
      | b :: m => if literal_eq_dec a b then true else In a m
    end.

Compute In.

Definition memlc (l : literal) (c : clause) : bool :=
  In l c.

Lemma memlc_true_iff : forall (l : literal) (c : clause),
  memlc l c = true <-> In l c = true.
Proof.
  intros l c.
  split; intros H.
  - unfold memlc in H. assumption.
  - unfold memlc. assumption.
Qed.

Compute memlc.

Definition c1: clause := [pos "a"; pos "b"].
Compute In (pos "a") c1.
Compute In (pos "c") c1.
Compute memlc (pos "a") c1.
Compute memlc (pos "c") c1.

Definition c2: clause := [pos "a"].

Definition subset (c1 c2 : clause) : bool :=
  forallb (fun l => memlc l c2) c1.
Compute subset c2 c1.
Compute subset c1 c2.


Fixpoint memlc (a:literal) (l:clause) : bool :=
    match l with
      | nil => false
      | b :: m => if literal_eq_dec a b then true else memlc a m
    end.

Fixpoint clause_eq_dec (c1 c2 : clause) : bool :=
    match c1, c2 with
    | nil, nil => true
    | x :: xs, y :: ys => if literal_eq_dec x y then clause_eq_dec xs ys else false
    | _, _ => false
    end.

Fixpoint memcf (a:clause) (l:formula) : bool :=
    match l with
      | nil => false
      | b :: m => if clause_eq_dec a b then true else memcf a m
    end.