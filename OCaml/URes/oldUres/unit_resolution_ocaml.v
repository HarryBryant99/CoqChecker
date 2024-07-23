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

Fixpoint contains_clause (f : formula) (cl : clause) : bool :=
  match f with
  | nilformula => false
  | consformula cl' rest => clause_eqb cl cl' || contains_clause rest cl
  end.

Fixpoint add_unique_clauses (f1 f2 : formula) : formula :=
  match f1 with
  | nilformula => f2
  | consformula cl rest =>
    if contains_clause f2 cl
    then add_unique_clauses rest f2
    else add_unique_clauses rest (consformula cl f2)
  end.

Open Scope formula_scope.
Definition f1 : formula := (consclause (pos "p") nilclause) :: (consclause (pos "pp") nilclause) :: nilformula.
Definition empty : formula := nilformula.

Definition result_formula := add_unique_clauses f1 empty.
Compute result_formula.


Definition process_formula (f : formula) : formula :=
  let found_clause := find_single_literal_clause f in
  let lit := read_literal_from_clause found_clause in
  let modified_formula := remove_negated_literal lit f in
  if formula_eqb modified_formula f
  then f  (* No changes, return the original formula with the single literal clause *)
  else remcf found_clause modified_formula.

(*With URes Definition*)

Fixpoint formula_to_subsumption (f : formula) : unitres :=
  match f with
  | nilformula => subsumption nilformula
  | consformula c rest => subsumption (process_formula f)
  end.

Fixpoint concat_formulas (f1 f2 : formula) : formula :=
  match f1 with
  | nilformula => f2
  | consformula c rest => consformula c (concat_formulas rest f2)
  end.

Fixpoint readf (u : unitres) : formula :=
  match u with
  | subsumption f => f
  | resolution u1 u2 => concat_formulas (readf u1) (readf u2)
  end.

Definition resolve_two_unitres (u1 u2 : unitres) : unitres :=
  match (u1, u2) with
  | (subsumption f1, subsumption f2) =>
    resolution (subsumption (process_formula (concat_formulas f1 f2))) (subsumption nilformula)
  | _ =>
    let formula1 := readf u1 in
    let formula2 := readf u2 in
    let combined_formula := add_unique_clauses (process_formula (concat_formulas formula1 formula2)) empty in
    resolution (subsumption combined_formula) (subsumption nilformula)
  end.


(*Extraction*)

Require Coq.extraction.Extraction.
(* Use the Extraction command to generate OCaml code *)
Extraction Language OCaml.

(*
Extraction "ures.ml" resolve_two_unitres.
*)

Extraction "C:\Users\z004u5bh\Documents\Coq\OCaml\URes\ures.ml" 
resolve_two_unitres
readf concat_formulas
formula_to_subsumption
process_formula
add_unique_clauses
contains_clause
formula_eqb
find_single_literal_clause
read_literal_from_clause
remove_negated_literal
remcf
clause_eqb
NoEmptyFormula
NonEmptycla
concat_clauses
remlc
literal_eqb.
