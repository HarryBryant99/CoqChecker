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
  | res : nat -> nat -> ProofStep.

(* Defining PreProof as a list of ProofStep *)
Definition PreProof := list ProofStep.

(* Assumption is defined as a list of clauses *)
Definition Assumption := list clause.

(* Assumption is defined as a list of clauses that have been checked*)
Definition Step := list clause.

Definition clause_head (c : clause) (default : literal) : literal :=
  match c with
  | [] => default
  | l :: _ => l
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

(* Function to retrieve the nth proof step in the preproof *)
Definition conclusion (ass : Assumption) (p : PreProof) (i : nat) : clause :=
  nth i ass []. (* Default to (res 0 0) if index is out of bounds *)

Definition findstep (s : Step) (i : nat) : clause :=
  nth i s []. (* Default to (res 0 0) if index is out of bounds *)

(* Function to compute the length of an Assumption *)
Fixpoint length_assumption (l: Assumption) : nat :=
  match l with
  | nil => 0
  | _ :: m => S (length_assumption m)
  end.

(* Function to compute the length of an Assumption *)
Fixpoint length_preproof (ps: PreProof) : nat :=
  match ps with
  | nil => 0
  | _ :: m => S (length_preproof m)
  end.

Fixpoint length_step (s: Step) : nat :=
  match s with
  | nil => 0
  | _ :: m => S (length_step m)
  end.

(* Less than function for natural numbers *)
Definition lt (n m : nat) : bool :=
  Nat.ltb n m.

Fixpoint is_literal_in_clause_bool (l : literal) (c : clause) : bool :=
  match c with
  | nil => false
  | hd :: tl => if lit_eq_dec_bool l hd then true else is_literal_in_clause_bool l tl
  end.

Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.

Definition is_unit_clause (c : clause) : bool :=
  match c with
  | nil => false
  | hd :: nil => true
  | _ :: _ => false
  end.

Definition correctconclusion (step : ProofStep) (ass : Assumption) (s : Step) (p : PreProof) : bool :=
  match step with
  | ass i => lt i (length_assumption ass)
  | res i j =>
      match lt i (length_step s), lt j (length_step s) with
      | true, true =>
          let c_j := findstep s j in
          is_unit_clause c_j &&
          is_literal_in_clause_bool (opposite (clause_head c_j (pos ""))) (findstep s i)
      | _, _ => false
      end
  end.

Definition a : Assumption := [[pos "a"]; [neg "a"]].
Definition p : PreProof := [ass 0; ass 1; res 0 1].
Definition s : Step := [[pos "a"]; [neg "a"]].
Definition testStep := res 0 1.
Compute correctconclusion testStep a s p.

(* Function to get the last element of a PreProof *)
Fixpoint last_step (s : Step) : clause :=
  match s with
  | [] => [] (* Default value when list is empty; adjust as needed *)
  | [step] => step (* Last element in the list *)
  | _ :: tl => last_step tl (* Recursively process the tail *)
  end.

Definition lastconclusion (s : Step) : bool :=
  match last_step s with
  | [] => true
  | _ => false
  end.

Definition computeresolution (step : ProofStep) (s : Step) : clause :=
  match step with
  | res i j =>
      let c1 := findstep s i in
      let c2 := findstep s j in
      remove_literal_from_clause_bool (opposite (clause_head c2 (pos ""))) c1
  | _ => []
  end.

Definition add_clause (s : Step) (c : clause) : Step :=
  s ++ [c].

(* Function to check all steps of a PreProof *)
Fixpoint check (ass : Assumption) (s : Step) (p : PreProof) : bool :=
  match p with
  | [] => true
  | step :: tl =>
      if correctconclusion step ass s p then
        match step with
        | ass i => 
          let s' := add_clause s (conclusion ass p i) in
          check ass s' tl
        | _ =>
          let s' := add_clause s (computeresolution step s) in
          check ass s' tl
        end
      else
        false (* Incorrect conclusion, halt *)
  end.

Definition emptyS : Step := []. 

Definition unsatcheck (ass : Assumption) (s : Step) (p : PreProof) : bool :=
  check ass s p && lastconclusion s.

(* Example usage *)
Definition example_clause1 := [pos "a"; neg "b"].
Definition example_clause2 := [neg "a"].
Definition example_clause3 := [pos "e"; neg "f"].
Definition example_clause4 := [neg "b"].
Definition example_clause5 := [pos "b"].
Definition example_ass := [example_clause1; example_clause2; example_clause3; example_clause4].
Definition example_ass2 := [example_clause1; example_clause2; example_clause5].
Definition example_ass3 := [example_clause1; example_clause2].

Definition example_preproof : PreProof :=
  [ass 0; ass 1; res 0 1; ass 2; res 5 6; ass 4; res 1 2; ass 3].

Definition example_preproof2 : PreProof :=
  [ass 0; ass 1; res 0 1; ass 2; res 3 2].

Definition example_preproof3 : PreProof :=
  [ass 0; ass 1; res 0 1].


Compute unsatcheck example_ass emptyS example_preproof.
Compute unsatcheck example_ass2 emptyS example_preproof2.

Compute check example_ass2 emptyS example_preproof2.
Compute check example_ass3 emptyS example_preproof3.

(*--------------------------------------------------------------------------*)
(*toproof*)

Fixpoint inb (l: literal) (c: clause) : bool :=
  match c with
  | [] => false
  | x :: xs => if lit_eq_dec_bool l x then true else inb l xs
  end.

Definition subset_bool (c1 c2: clause) : bool :=
  forallb (fun l => inb l c2) c1.

Fixpoint clause_eq_dec (c1 c2 : clause) : bool :=
    match c1, c2 with
    | nil, nil => true
    | x :: xs, y :: ys => if lit_eq_dec_bool x y then clause_eq_dec xs ys else false
    | _, _ => false
    end.

Fixpoint memcf (a:clause) (l:formula) : bool :=
    match l with
      | nil => false
      | b :: m => if clause_eq_dec a b then true else memcf a m
    end.

Inductive unitres : formula -> clause -> Type :=
| subsumption : forall (c c2 : clause) (f : formula),
    memcf c f = true ->
    subset_bool c c2 = true ->
    unitres f c2
| resolution : forall (c : clause) (l : literal) (f : formula),
    unitres f c ->
    is_literal_in_clause_bool l c = true ->
    unitres f (cons (opposite l) []) ->
    unitres f (remove_literal_from_clause_bool l c).

Definition toproof (ass : Assumption) (s : Step) (p : PreProof) (f : formula) : Set :=
  check ass s p = true ->
  forall c : clause, In c s -> unitres ass c.

Fixpoint memlc_bool (l:literal) (c:clause) : bool :=
    match c with
      | nil => false
      | b :: m => if lit_eq_dec_bool l b then true else memlc_bool l m
    end.

Definition model_property (m : literal -> bool) : Prop :=
    forall l:literal, ( m l = true -> m (opposite l) = true -> False) /\ ( (m (opposite l) = false -> False) -> m l = true).
Definition models_clause (m : literal -> bool) (c : clause) : Prop :=
  model_property m -> exists l: literal, memlc_bool l c = true /\ m l = true.
Definition models_formula (m : literal -> bool) (f : formula) : Prop :=
  model_property m -> forall c: clause, memcf c f = true -> models_clause m c.

(* Definition of unsatisfiability *)
Definition unsatisfiable (ass : Assumption) : Prop :=
  forall m : literal -> bool, models_formula m ass -> False.

Definition is_unsat (ass : Assumption) (s : Step) (p : PreProof) (f : formula) : Prop :=
    check ass a p = true ->
    lastconclusion s = true ->
    unsatisfiable ass.

(*Proofs*)

Lemma last_step_empty : forall (s : Step),
  lastconclusion s = true ->
  last_step s = [].
Proof.
Admitted.

Definition entails (f : formula) (c : clause) : Prop :=
  (forall (m : literal -> bool), model_property m -> models_formula m f -> models_clause m c).

Lemma URes_implies_Entailment :
  forall (f : formula) (c : clause),
  unitres f c ->
  entails f c.
Proof.
Admitted.

Definition conclusions (ass : assumptions) (p 

Theorem is_unsat_correct : forall (ass : Assumption) (p : PreProof),
  p <> [] ->
  check ass s p = true ->
  last_step s = c ->
  entails ass c.
Proof.
intros.
apply URes_implies_Entailment.
induction p0.
+ contradiction.
+ destruct p0.
  - destruct a0.
    * apply subsumption.
