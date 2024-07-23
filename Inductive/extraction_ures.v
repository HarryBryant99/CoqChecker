(* Importing necessary libraries *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* Defining literal type *)
Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.

(* Defining clause and formula *)
Definition clause := list literal.
Definition formula := list clause.

(* Defining the ProofStep data type *)
Inductive ProofStep : Type :=
  | ass : nat -> ProofStep
  | res : nat -> nat -> clause -> ProofStep.

(* Defining PreProof as a list of ProofStep *)
Definition PreProof := list ProofStep.

(* Assumption is defined as a list of clauses *)
Definition Assumption := list clause.

(* Conclusion is defined as a list of clauses that have been checked*)
Definition Conclusion := list clause.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end.

Fixpoint nthWithDefault {X : Type} (n : nat) (l : list X) (default : X) : X :=
  match n, l with
  | _, [] => default
  | 0, x :: _ => x
  | S n', _ :: l' => nthWithDefault n' l' default
  end.

Definition findAssumption (ass : Assumption) (p : PreProof) (i : nat) : clause :=
  nth i ass []. (* Default to (ass 0) if index is out of bounds *)

Definition findConclusion (i : nat) (r : Conclusion) : clause :=
  nth i r []. (* Default to (res 0 0) if index is out of bounds *)

Axiom trueClause : clause.

(* nthElInSeq function *)
Fixpoint nthElInSeq {X : Type} (n : nat) (l : list X) (default : X) : X :=
  match n, l with
  | _, [] => default
  | 0, x :: _ => x
  | S n', _ :: l' => nthElInSeq n' l' default
  end.

Definition IsEmptyClause (c1 : clause) : bool :=
  match c1 with
  | [] => true
  | _ => false
  end.

Definition lit_eq_dec_bool (a b : literal) : bool :=
  match a, b with
  | pos s1, pos s2 => if string_dec s1 s2 then true else false
  | neg s1, neg s2 => if string_dec s1 s2 then true else false
  | _, _ => false
  end.

Fixpoint remove (x : literal) (l : list literal){struct l} : list literal :=
  match l with
    | nil => nil
    | y::tl => if (lit_eq_dec_bool x y) then remove x tl else y::(remove x tl)
  end.

Definition remove_literal_from_clause_bool (l : literal) (c : clause) : clause :=
  remove l c.

Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.

Definition clause_head (c : clause) (default : literal) : literal :=
  match c with
  | [] => default
  | l :: _ => l
  end.

Definition toResConclusion (c1 c2 : clause) : clause :=
  remove_literal_from_clause_bool (opposite (clause_head c2 (pos ""))) c1.

Definition computeresolution (step : ProofStep) (r : Conclusion) : clause :=
  match step with
  | res i j k =>
      let c1 := findConclusion i r in
      let c2 := findConclusion j r in
      toResConclusion c1 c2
  | _ => []
  end.

Definition get_k (r: ProofStep) : clause :=
  match r with
  | ass _ => []
  | res _ _ k => k
  end.

Definition add_clause (r : Conclusion) (c : clause) : Conclusion :=
  r ++ [c].

Fixpoint conclusions (ass : Assumption) (r : Conclusion) (p : PreProof) : Conclusion :=
  match p with
  | [] => r
  | step :: tl =>
      match step with
      | ass i => 
        let r' := add_clause r (findAssumption ass p i) in
        conclusions ass r' tl
      | _ =>
        let r' := add_clause r (get_k step) in
        conclusions ass r' tl
      end
  end.

(* ltb function *)
Definition ltb (n m : nat) : bool := Nat.ltb n m.

Definition is_unit_clause (c : clause) : bool :=
  match c with
  | nil => false
  | hd :: nil => true
  | _ :: _ => false
  end.

Fixpoint is_literal_in_clause_bool (l : literal) (c : clause) : bool :=
  match c with
  | nil => false
  | hd :: tl => if lit_eq_dec_bool l hd then true else is_literal_in_clause_bool l tl
  end.

Definition literal_eqb (l1 l2 : literal) : bool :=
  match l1, l2 with
  | pos s1, pos s2 => String.eqb s1 s2
  | neg s1, neg s2 => String.eqb s1 s2
  | _, _ => false
  end.

Fixpoint clause_eqb (c1 c2: clause) : bool :=
  match c1, c2 with
  | [], [] => true
  | l1 :: c1', l2 :: c2' => literal_eqb l1 l2 && clause_eqb c1' c2'
  | _, _ => false
  end.

Definition isRes (c1 c2 k : clause) : bool :=
  is_unit_clause c2 &&
  is_literal_in_clause_bool (opposite (clause_head c2 (pos ""))) c1 &&
  clause_eqb (toResConclusion c1 c2) k.

(* isCorrectLastStep function *)
Definition isCorrectLastStep (ass : Assumption) (conclusionpl : Conclusion) (p : ProofStep) (pl : PreProof) : bool :=
  match p with
  | ass n => ltb n (length ass)
  | res n m k =>
    let lengthConcll := length conclusionpl in
    andb (ltb n lengthConcll)
         (andb (ltb m lengthConcll)
               (isRes (findConclusion n conclusionpl) (findConclusion m conclusionpl) k))
  end.

Fixpoint checkAll (ass : Assumption)(conclusionpl : Conclusion) (pl : PreProof) : bool :=
  match pl with
  | [] => true
  | p :: l => andb (isCorrectLastStep ass conclusionpl p pl) (checkAll ass conclusionpl l)
  end.

Definition isCorrect (ass : Assumption) (pl : PreProof) : bool :=
  let conclusionpl := conclusions ass [] pl in
  checkAll ass conclusionpl pl.

Example list_ass : Assumption := [[pos "a"];[neg "a"]].
Example step0 : ProofStep := ass 0.
Example step1 : ProofStep := ass 1.
Example step2 : ProofStep := res 0 1 [].
Example step3 : ProofStep := res 0 1 [pos "a"].

(* Example usage: *)
Compute isCorrect list_ass [step0; step1; step2]. (*True*)
Compute isCorrect list_ass [step0; step2]. (*False*)
Compute isCorrect list_ass [step0; step1; step3]. (*False*)

(*---------------------------------------------------------------------*)
(*Extraction*)

Require Coq.extraction.Extraction.

(* Use the Extraction command to generate OCaml code *)
Extraction Language OCaml.

Extraction "C:\Users\z004u5bh\Documents\Coq\OCaml\URes\ures.ml" compute_subsumption is_resolution_complete.
