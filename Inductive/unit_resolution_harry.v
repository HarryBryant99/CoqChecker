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
| subsumption : formula -> clause -> bool -> unitres
| resolution : unitres -> unitres -> bool -> unitres.

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

Fixpoint contains_clause (f : formula) (cl : clause) : bool :=
  match f with
  | nilformula => false
  | consformula cl' rest => clause_eqb cl cl' || contains_clause rest cl
  end.

(* Function to produce subsumption only if the bool is true *)
Definition subsumption_if_subset (f : formula) (c : clause) : unitres :=
  if contains_clause f c then subsumption f c true else subsumption nilformula nilclause false.

Open Scope clause_scope.
(* Example usage *)
Definition example_clause_subset : unitres := 
  subsumption_if_subset (consformula (pos "p" :: nilclause) nilformula) 
                        (pos "p" :: nilclause).

Definition example_clause_not_subset : unitres := 
  subsumption_if_subset (consformula (neg "p" :: nilclause) nilformula) 
                        (pos "p" :: nilclause).

Compute example_clause_subset.
Compute example_clause_not_subset.

(* Function to concatenate two formulas *)
Fixpoint concat_formulas (f1 f2 : formula) : formula :=
  match f1 with
  | nilformula => f2
  | consformula c rest => consformula c (concat_formulas rest f2)
  end.

Fixpoint has_single_literal (c : clause) : bool :=
  match c with
  | nilclause => false
  | consclause _ nilclause => true
  | consclause _ _ => false
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

Definition read_literal_from_clause (c : clause) : literal :=
  match c with
  | nilclause => pos "" (* or any default literal you want to return for an empty clause *)
  | consclause l _ => l
  end.

Definition resolution_if_true (res1 res2 : unitres) : unitres :=
  match has_single_literal (match res2 with
                             | subsumption _ c _ => c
                             | _ => nilclause
                             end) with
  | true =>
    match res1, res2 with
    | subsumption f1 c1 true, subsumption f2 c2 true =>
      (*let new_formula := concat_formulas f1 f2 in*)
      subsumption f1 (remlc (read_literal_from_clause c2) c1) true
    | _, _ => subsumption nilformula nilclause false
    end
  | false => subsumption nilformula nilclause false
  end.

(* Example usage *)
Definition example_resolution_true : unitres := 
  resolution_if_true (subsumption (consformula (pos "p" :: nilclause) nilformula) (pos "p" :: nilclause) true)
                     (subsumption (consformula (neg "p" :: nilclause) nilformula) (neg "p" :: nilclause) true).

Definition example_resolution_false : unitres := 
  resolution_if_true (subsumption (consformula (pos "p" :: nilclause) nilformula) (pos "p" :: nilclause) true)
                     (subsumption (consformula (neg "p" :: neg "z" :: nilclause) nilformula) (neg "p" :: neg "z"  :: nilclause) true).

Compute example_resolution_true.
Compute example_resolution_false.


(* Remove a clause from a formula *)
Fixpoint remcf (c : clause) (f : formula) : formula :=
  match f with
  | nilformula => nilformula
  | consformula c' rest =>
    if clause_eqb c c' then remcf c rest else consformula c' (remcf c rest)
  end.

Open Scope clause_scope.

Compute remcf c1 f1.