Require Import Bool.
Require Import String.
Open Scope string_scope.

Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.

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

Open Scope clause_scope.

(* Define a function for string equality *)
Definition string_dec (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

(* Define a function for string less than *)
Definition string_lt (s1 s2 : string) : bool :=
  if string_dec s1 s2 then false else true.

(* Define a function to extract the value of a literal *)
Definition v (l : literal) : string :=
  match l with
  | pos s => s
  | neg s => s
  end.

(* Define a function to measure the length of a clause *)
Fixpoint clause_length (c : clause) : nat :=
  match c with
  | nilclause => 0
  | consclause _ cs => S (clause_length cs)
  end.

Fixpoint Inslll (l : literal) (cls : clause) : clause :=
  match cls with
  | nilclause => l :: nilclause
  | consclause (pos v2) cls' =>
    if orb (string_dec (v l) v2) (string_lt (v l) v2) then
      l :: cls
    else
      pos v2 :: Inslll (pos (v l)) cls'
  | consclause (neg v2) cls' =>
    pos (v l) :: neg v2 :: cls'
  end.

(* Example usage *)
Definition example_clause : clause :=
  pos "apple" :: pos "banana" :: neg "orange" :: nilclause.

Definition test_inslll : clause :=
  Inslll (pos "grape") example_clause.

Compute test_inslll.

(*--------------------------------------------------------*)

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

(*Add a literal to the front of a list of literals*)
(* Program constant for conclll *)
Definition conclll : literal -> clause -> clause := fun l ls => consclause l ls.

(* Computation rule for conclll *)
Lemma conclll_computation_rule : forall l ls,
  conclll l ls = consclause l ls.
Proof.
  intros l ls.
  reflexivity.
Qed.

(* Add a literal to a clause *)
Fixpoint conccf (l : literal) (f : clause) : clause :=
  match f with
  | nilclause => l :: nilclause
  | consclause l' ls =>
    if string_dec (v l) (v l') then
      f
    else
      consclause l' (conccf l ls)
  end.

(* Computation rule for conccf *)
Lemma conccf_computation_rule : forall l f,
  conccf l f = match f with
               | nilclause => l :: nilclause
               | consclause l' ls =>
                 if string_dec (v l) (v l') then
                   f
                 else
                   consclause l' (conccf l ls)
               end.
Proof.
  intros l f.
  destruct f as [|l' ls].
  - reflexivity.
  - simpl. destruct (string_dec (v l) (v l')).
    + subst. reflexivity.
    + reflexivity.
Qed.

(* Remove a literal from a clause *)
Fixpoint remlc (l : literal) (f : clause) : clause :=
  match f with
  | nilclause => nilclause
  | consclause l' ls =>
    if string_dec (v l) (v l') then
      ls
    else
      consclause l' (remlc l ls)
  end.

(* Computation rule for remlc when removing from an empty clause *)
Lemma remlc_empty : forall l,
  remlc l nilclause = nilclause.
Proof.
  intros l.
  reflexivity.
Qed.

(* Computation rule for remlc *)
Lemma remlc_computation_rule : forall l l' ls,
  remlc l (consclause l' ls) =
  if string_dec (v l) (v l') then
    ls
  else
    consclause l' (remlc l ls).
Proof.
  intros l l' ls.
  simpl.
  destruct (string_dec (v l) (v l')).
  - reflexivity.
  - reflexivity.
Qed.

(*Test removal*)
Definition test_clause : clause :=
  pos "apple" :: pos "banana" :: neg "orange" :: nilclause.

(* Example usage of remlc *)
Definition test_remlc : clause :=
  remlc (pos "banana") test_inslll.

(* Compute results *)
Compute test_inslll.  (* Output: pos "grape" :: pos "apple" :: pos "banana" :: neg "orange" :: nilclause *)
Compute test_remlc.   (* Output: pos "grape" :: pos "apple" :: neg "orange" :: nilclause *)

(* Concatenate two clauses *)
Fixpoint concat_clauses (c1 c2 : clause) : clause :=
  match c1 with
  | nilclause => c2
  | consclause l ls => consclause l (concat_clauses ls c2)
  end.

(* Example usage *)
Definition example_clause1 : clause :=
  pos "apple" :: pos "banana" :: nilclause.

Definition example_clause2 : clause :=
  neg "orange" :: nilclause.

Definition concatenated_clause : clause :=
  concat_clauses example_clause1 example_clause2.

Compute concatenated_clause.

(* Define a function to check if a clause is non-empty *)
Definition NonEmptycla (c : clause) : bool :=
  match c with
  | nilclause => false
  | consclause _ _ => true
  end.

(* Define a function to check if a formula has no empty clauses *)
Fixpoint NoEmptyFormula (f : formula) : bool :=
  match f with
  | nilformula => true
  | consformula c rest => if NonEmptycla c then NoEmptyFormula rest else false
  end.

Open Scope clause_scope.

(* Example usage *)
Definition ec1 : clause :=
  pos "apple" :: pos "banana" :: nilclause.

Definition ec2 : clause :=
  neg "orange" :: nilclause.

Open Scope formula_scope.

Definition example_formula : formula :=
  ec1 :: ec2 :: nilformula.

Compute NonEmptycla ec1. (* Should be true *)
Compute NonEmptycla nilclause.        (* Should be false *)

Compute NoEmptyFormula example_formula. (* Should be true *)
Compute NoEmptyFormula (ec1 :: ec2 :: nilformula). (* Should be false *)

(* Function to check if two strings are equal *)
Definition string_beq (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

(* Function to check if two literals are equal *)
Definition literal_eqb (l1 l2 : literal) : bool :=
  match (l1, l2) with
  | (pos s1, pos s2) | (neg s1, neg s2) => string_beq s1 s2
  | (_, _) => false
  end.

(* Function to check if two clauses are equal *)
Fixpoint clause_eqb (c1 c2 : clause) : bool :=
  match (c1, c2) with
  | (nilclause, nilclause) => true
  | (consclause l1 ls1, consclause l2 ls2) =>
    if literal_eqb l1 l2 then clause_eqb ls1 ls2 else false
  | (_, _) => false
  end.

(* Remove a clause from a formula *)
Fixpoint remcf (c : clause) (f : formula) : formula :=
  match f with
  | nilformula => nilformula
  | consformula c' rest =>
    if clause_eqb c c' then remcf c rest else consformula c' (remcf c rest)
  end.

(* Example usage *)
Definition test_remcf : formula :=
  remcf example_clause1 example_formula.

Compute test_remcf.