Require Import Nat.
Require Import Arith.
Require Import ZArith.
Require Export ZArith Int.
Require Import ZAxioms ZMulOrder ZSgnAbs NZDiv.
Open Scope Int_scope.


Lemma QuotientRemainder : forall n d : nat,
  d > 0 ->
  exists q r : nat, (n = d * q + r) /\ (d > r).

Proof.
  intros n d D_pos. induction n.
  - (** base case where n = 0 **)
  exists 0. exists 0.
  split. ring. apply D_pos.
  - (** inductive step **)
  destruct IHn as [q IHn]. destruct IHn as [r IHn]. 
  
  (** 11/21
  case_eq (r + 1 - d).
  intros H. exists (q + 1). exists 0. destruct IHn. destruct H1. split.
  rewrite Nat.add_1_r. rewrite Nat.add_0_r. simpl. apply f_equal.
  rewrite Nat.mul_succ_r. rewrite Nat.add_assoc.
  rewrite Nat.mul_comm in H0. rewrite Nat.mul_succ_r in H0. 
  rewrite Nat.add_comm.
  rewrite Nat.mul_comm. rewrite Nat.add_comm in H0.

  assert (stupid : q * r + q = q + q * r). 
  { rewrite Nat.add_comm. reflexivity. }
  rewrite <- stupid. apply H0. apply D_pos.
  
  split. 


  assert (H_S: S n = d * (q + 1)). rewrite Nat.add_1_r. Search "mul". **)

  (** case distinction - is r + 1 < d or equal to d? **)
  destruct IHn. exists q. exists (r + 1). (* <- the 2nd exists causes problems *)
  split. rewrite Nat.add_assoc. rewrite Nat.add_1_r. apply f_equal.
  assumption. 
Admitted.

Lemma ExcludedMiddle : forall A : Prop,
  ~(A /\ ~A).
Proof.
intros A. unfold not. intros H. destruct H. apply H0. apply H.
Qed.

Lemma ExcludedMiddleImpliesB : forall A B : Prop,
  (A -> B) /\ (~A -> B) -> B.
Proof.
  intros A B. intros H_ex. destruct H_ex. unfold not in H0.
  (** case distinction on truth of A **)
Admitted.

(** destruct on a boolean b lays out case distinctions **)
(* this needs to be re-proven for literals instead of booleans *)
Lemma double_neg : forall b : bool,
  ~~b = b.
Proof.
  destruct b. auto. auto. 
  (** btw: auto solves this in one shot **)
Qed.

Lemma double_neg_prop : forall P : Prop,
  ~~P = P.
Proof.
  auto.
Qed.

(* taking a stab at defining inductive literal types here *)
Inductive literal : Type :=
| l
| notl.

(* we need some way to define a negated literal *)
Definition neg_lit (L : literal) : literal :=
  match L with
    | l => notl
    | notl => l
  end.

(* not sure what there is to prove since this is true by definition *)
(* did i do the literal definition correctly? *)
Lemma double_neg_lit:
  neg_lit notl = l.
Proof.
  auto.
Qed.

Check l.
Check notl.
Check neg_lit (neg_lit notl).