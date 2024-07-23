Require Import String.
Open Scope string_scope.

Inductive variable : Type := 
| var: string -> variable.


Inductive literal : Type :=
| pos: string -> literal
| neg: string -> literal.


Inductive clause : Type :=
| nilclause : clause
| consclause : literal -> clause -> clause.
Infix "::" := consclause (at level 60, right associativity) : clause_scope.
Open Scope clause_scope.

Inductive formula : Type :=
| nilformula : formula
| consformula : clause -> formula -> formula.
Infix "::" := consformula (at level 60, right associativity) : formula_scope.
Open Scope formula_scope.


Inductive valuation : Type :=
| nilvaluation : valuation
| consvaluation : literal -> valuation -> valuation.
Infix "::" := consvaluation (at level 60, right associativity) : valuation_scope.
Open Scope valuation_scope.


Definition opposite (L : literal) : literal :=
  match L with
    | pos string => neg string
    | neg string => pos string
  end.

(*Manual Checks of the Opposite Function*)
Definition A : literal := pos "A".
Definition B : literal := neg "B".

Check A.
Check B.

Compute opposite A.
Compute opposite B.
Compute opposite (opposite A).


(*Produce the opposite of all literals in a list*)
Open Scope list_scope.

Fixpoint oppositeList (l:list literal) {struct l} : list literal :=
  match l with
    | nil => nil
    | a :: l1 => opposite a :: oppositeList l1
    end.

(*Manual check of the Opposite List Function*)
Compute oppositeList (A::B::nil).





(*Get the first element of a clause*)
Open Scope clause_scope.

Definition hdclause (default:literal) (l:clause) :=
   match l with
     | nilclause => default
     | x :: _ => x
   end.

Definition c1 : clause := nilclause.
Definition c2 : clause := consclause A c1.
Check c2.
Definition start := hdclause B c2.
Print start.
Check start.
Compute opposite start.


Require Import Nat.
Require Import Arith.

(*Lemma: Opposite is Idempotent*)
Lemma opp_is_idempotent:
forall l : literal, opposite( opposite l) =  l.
Proof.
destruct l.
simpl.
reflexivity.
simpl.
reflexivity.
Qed. (*Can also use destruct to remove IH, also Intro*)

Require Import Bool.
(*Lemma: A literal is not equal to its opposite*)
Lemma opp_dif_from_lit:
forall l : literal, ((opposite l = l) -> False).
Proof.
destruct l.
intro H.
inversion H.
intro H.
inversion H.
Qed.

Lemma opp_dif_from_opp:
forall l : literal, ((l = opposite l) -> False).
Proof.
induction l.
intro H.
inversion H.
intro H.
inversion H.
Qed.

(* Lemma: Opposite equality implies inverse equality *)
Lemma opposite_is_symmetric : forall L L2 : literal,
  opposite L = L2 -> opposite L2 = L.
Proof.
  intros L L2 H.
  rewrite <- H.
  apply opp_is_idempotent.
Qed.

(*Lemma: If the opposites of two variables is equal then the variables themselves must also be equal*)
Lemma opp_uniqueness: forall L L2 : literal, opposite L = opposite L2 -> L = L2.
Proof.
  intros L L2 H.

  (* Apply opposite_symmetric twice to both sides *)
  rewrite <- opp_is_idempotent with (l := L).
  rewrite <- opp_is_idempotent with (l := L2).

  (* Use the hypothesis to simplify *)
  rewrite H.

  (* Now the goal is reflexivity, as both sides are the same *)
  reflexivity.
Qed.

(*Lemma: Proof of symmetry for clauses*)
Lemma clause_symmetrical: forall c c2 : clause, c2 = c -> c = c2.
Proof.
  intros c0 c2 H.
  rewrite H.
  reflexivity.
Qed.

(*Lemma: Proof of asymmetry property for clauses*)
Lemma clause_asymmetry : forall c c2 : clause, (c2 = c -> False) -> (c = c2 -> False).
Proof.
  intros c c2 H1 H2.
  apply H1. symmetry. exact H2.
Qed.

