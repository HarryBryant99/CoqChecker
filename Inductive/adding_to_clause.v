Require Import String.
Open Scope string_scope.

(* Given definitions for literal and clause *)
Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.

Inductive clause : Type :=
  | nilclause : clause
  | consclause : literal -> clause -> clause.
Infix "::" := consclause (at level 60, right associativity) : clause_scope.
Open Scope clause_scope.

(* Insert a literal into a clause *)
Fixpoint inslc (l : literal) (ls : clause) : clause :=
  match ls with
  | nilclause => l :: nilclause
  | consclause l' ls' => consclause l' (inslc l ls')
  end.

(* Computation rule for inslc *)
Lemma inslc_computation_rule : forall l,
  inslc l nilclause = l :: nilclause.
Proof.
  intros l.
  reflexivity.
Qed.

(* Example *)
Definition example_literal : literal := pos "example_lit".
Definition example_clause : clause := consclause (pos "existing_lit") nilclause.

(* Testing inslc function and lemma *)
Compute inslc example_literal example_clause.
(* Result should be: consclause (pos "existing_lit") (consclause (pos "example_lit") nilclause) *)

(* Using the computation rule *)
Lemma example_ins : inslc example_literal nilclause = example_literal :: nilclause.
Proof.
  apply inslc_computation_rule.
Qed.


(* Program constant for conclll *)
Definition conclll : literal -> clause -> clause := fun l ls => consclause l ls.

(* Computation rule for conclll *)
Lemma conclll_computation_rule : forall l ls,
  conclll l ls = consclause l ls.
Proof.
  intros l ls.
  reflexivity.
Qed.

(* Program constant for conclc *)
Definition conclc : literal -> clause -> clause := fun l ls => consclause (pos "CC") (conclll l ls).

(* Computation rule for conclc *)
Lemma conclc_computation_rule : forall l ls,
  conclc l (consclause (pos "CC") ls) = consclause (pos "CC") (conclll l (consclause (pos "CC") ls)).
Proof.
  intros l ls.
  reflexivity.
Qed.




