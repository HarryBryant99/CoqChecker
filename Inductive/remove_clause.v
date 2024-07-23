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

(* Define a function to extract the value of a literal *)
Definition v (l : literal) : string :=
  match l with
  | pos s => s
  | neg s => s
  end.

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

(* Example usage *)
Definition example_literal : literal := pos "apple".

Definition example_clause : clause :=
  pos "apple" :: pos "banana" :: neg "orange" :: nilclause.

Definition test_remlc : clause :=
  remlc example_literal example_clause.

Compute test_remlc.


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
Definition example_clause1 : clause :=
  pos "apple" :: pos "banana" :: neg "orange" :: nilclause.

Definition example_clause2 : clause :=
  pos "grape" :: neg "pear" :: nilclause.

Open Scope formula_scope.

Definition example_formula : formula :=
  example_clause1 :: example_clause2 :: nilformula.

Definition test_remcf : formula :=
  remcf example_clause1 example_formula.

Compute test_remcf.


(*Proving remcf*)

Fixpoint NoEmptyFormula (f : formula) : bool :=
  match f with
  | nilformula => true
  | consformula c rest => NoEmptyClause c && NoEmptyFormula rest
  end.

Fixpoint remcf (c : clause) (f : formula) : formula :=
  match f with
  | nilformula => nilformula
  | consformula c' rest => if c =? c' then remcf c rest else consformula c' (remcf c rest)
  end.

Lemma NoEmptyFormula_remcf : forall c f,
  NoEmptyFormula f -> NoEmptyFormula (remcf c f).
Proof.
  intros c f H.
  induction f as [|c' rest IH].
  - (* Base case: f is nilformula *)
    simpl. reflexivity.
  - (* Inductive case: f is consformula c' rest *)
    simpl. simpl in H.
    destruct (c =? c') eqn:Eq.
    + (* c is equal to c' *)
      apply andb_true_iff in H as [Hc' Hrest].
      apply IH in Hrest.
      rewrite Hrest. reflexivity.
    + (* c is not equal to c' *)
      apply andb_true_iff in H as [Hc' Hrest].
      apply andb_true_intro. split.
      * assumption.
      * apply IH. assumption.
Qed.