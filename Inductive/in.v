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

Fixpoint clause_eq (c1 c2 : clause) : bool :=
  match c1, c2 with
  | [], [] => true
  | x::xs, y::ys => if literal_eq x y then clause_eq xs ys else false
  | _, _ => false
  end.

Lemma In_dec : forall (a:literal) (l:clause), {In a l = true} + {In a l = false}.
Proof.
intros.
induction l as [|b m IHm].
- right. reflexivity.
- destruct (literal_eq_dec a b) as [Heq | Hneq].
  + left. rewrite Heq. simpl. destruct literal_eq_dec. reflexivity. auto.
  + destruct IHm as [Hin | Hnin].
    * left. simpl. rewrite Hin. destruct literal_eq_dec. reflexivity. reflexivity.
    * right. simpl. rewrite Hnin. destruct literal_eq_dec. contradiction. reflexivity.
Qed.

Definition c1: clause := [pos "a"; pos "b"].
Compute In (pos "a") c1.
Compute In (pos "") c1.
