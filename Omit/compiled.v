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

Inductive unitres :=
| subsumption : formula -> unitres
| resolution : unitres -> unitres -> unitres.

Open Scope clause_scope.

Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.

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

(* Function to check if two strings are equal *)
Definition string_beq (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.


(* Function to check if two literals are equal *)
Definition literal_eqb (l1 l2 : literal) : bool :=
  match (l1, l2) with
  | (pos s1, pos s2) | (neg s1, neg s2) => string_beq s1 s2
  | (_, _) => false
  end.

(* Remove a literal from a clause *)
Fixpoint remlc (l : literal) (f : clause) : clause :=
  match f with
  | nilclause => nilclause
  | consclause l' ls =>
    if literal_eqb l l' then
      ls
    else
      consclause l' (remlc l ls)
  end.

(* Concatenate two clauses *)
Fixpoint concat_clauses (c1 c2 : clause) : clause :=
  match c1 with
  | nilclause => c2
  | consclause l ls => consclause l (concat_clauses ls c2)
  end.

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



(*-------------------------------------*)
(*URES*)


(* Function to check if a clause has a single literal *)
Fixpoint has_single_literal (c : clause) : bool :=
  match c with
  | nilclause => false
  | consclause _ nilclause => true
  | consclause _ (consclause _ _) => false
  end.

(* Function to cancel a clause with a single literal and its opposite in a formula *)
Require Import Arith.Wf_nat.

Fixpoint remove_negated_literal (l : literal) (f : formula) : formula :=
  match f with
  | nilformula => nilformula
  | consformula c rest =>
    let c' := remlc (opposite l) c in
    consformula c' (remove_negated_literal l rest)
  end.




Definition example_literal : literal := pos "p".
Definition example_clause1 : clause := neg "p" :: pos "q" :: nilclause.
Definition example_clause2 : clause := pos "r" :: nilclause.
Open Scope formula_scope.
Definition example_formula : formula := example_clause1 :: example_clause2 :: nilformula.

Compute "Original Formula:".
Compute example_formula.

Compute "Literal to Remove:".
Compute example_literal.

Compute "Formula after Removing Negated Literal:".
Compute remove_negated_literal example_literal example_formula.

Compute remlc (neg "p") example_clause1.

Definition read_literal_from_clause (c : clause) : literal :=
  match c with
  | nilclause => pos "" (* or any default literal you want to return for an empty clause *)
  | consclause l _ => l
  end.

Fixpoint find_single_literal_clause (f : formula) : clause :=
  match f with
  | nilformula => nilclause
  | consformula c rest =>
    if has_single_literal c then
      c
    else
      find_single_literal_clause rest
  end.

Fixpoint formula_eqb (f1 f2 : formula) : bool :=
  match (f1, f2) with
  | (nilformula, nilformula) => true
  | (consformula c1 rest1, consformula c2 rest2) =>
    if clause_eqb c1 c2 then formula_eqb rest1 rest2 else false
  | (_, _) => false
  end.

Definition process_formula (f : formula) : formula :=
  let found_clause := find_single_literal_clause f in
  let lit := read_literal_from_clause found_clause in
  let modified_formula := remove_negated_literal lit f in
  if formula_eqb modified_formula f
  then f  (* No changes, return the original formula with the single literal clause *)
  else remcf found_clause modified_formula.

Open Scope clause_scope.
Definition example_clause3 : clause := neg "p" :: pos "q" :: nilclause.
Definition example_clause4 : clause := pos "p" :: nilclause.
Open Scope formula_scope.
Definition example_formula2 : formula := example_clause3 :: example_clause4 :: nilformula.

(* Test 1: Single literal clause with negation removed *)
Compute process_formula example_formula.

(* Test 2: No single literal clause with negation removed *)
Compute process_formula example_formula2.



(*With URes Definition*)


Fixpoint formula_to_subsumption (f : formula) : unitres :=
  match f with
  | nilformula => subsumption nilformula
  | consformula c rest => subsumption f
  end.

Fixpoint concat_formulas (f1 f2 : formula) : formula :=
  match f1 with
  | nilformula => f2
  | consformula c rest => consformula c (concat_formulas rest f2)
  end.

Fixpoint resolve_two_unitres (u1 u2 : unitres) : unitres :=
  match (u1, u2) with
  | (subsumption f1, subsumption f2) =>
    subsumption (process_formula (concat_formulas f1 f2))
  | (_, _) => resolution u1 u2
  end.

Open Scope clause_scope.
Definition clause1 : clause := neg "p" :: pos "q" :: nilclause.
Definition clause2 : clause := pos "p" :: nilclause.
Open Scope formula_scope.
Definition formula1 : formula := clause1 :: nilformula.
Definition formula2 : formula := clause2 :: nilformula.

(* Convert formula to subsumption *)
Definition subsumption_result := formula_to_subsumption example_formula.
Compute "Subsumption Result:".
Compute subsumption_result.

(* Create unitres with resolution *)
Definition resolution_result : unitres :=
  resolution (subsumption formula1) (subsumption formula2).
Compute "Original Resolution Result:".
Compute resolution_result.

(* Resolve the two unitres *)
Definition resolved_result := resolve_two_unitres (subsumption formula1) (subsumption formula2).
Compute "Resolved Result:".
Compute resolved_result.
