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
  nth i ass []. (* Default to (res 0 0) if index is out of bounds *)

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

(*
(* Postulate (Axiom) declaration for isRes *)
Axiom isRes : clause -> clause -> bool.

(* Define the IsRes proposition *)
Definition IsRes (c1 c2 : clause) : Prop :=
  isRes c1 c2 = true.
*)

Definition IsEmptyClause (c1 : clause) : bool :=
  match c1 with
  | [] => true
  | _ => false
  end.

(*
Following Anton's definitions. Which doesn't work because they both rely on each other)

(* lastConclusion function *)
Definition lastConclusion (ass : Assumption) (p : ProofStep) (pl : PreProof) : clause :=
  match p with
  | ass n => nthElInSeq n ass
  | res n m =>
    let conclusionl := conclusions ass pl in
    toResConclusion (nthElInSeq n conclusionl) (nthElInSeq m conclusionl)
  end.

(* conclusions function *)
Fixpoint conclusions (ass : Assumption) (pl : PreProof) : list clause :=
  match pl with
  | [] => []
  | p :: pl' => lastConclusion ass p pl' :: conclusions ass pl'
  end.
*)

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
  | res i j =>
      let c1 := findConclusion i r in
      let c2 := findConclusion j r in
      toResConclusion c1 c2
  | _ => []
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
        let r' := add_clause r (computeresolution step r) in
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

Definition isRes (c1 c2 : clause) : bool :=
  is_unit_clause c2 &&
  is_literal_in_clause_bool (opposite (clause_head c2 (pos ""))) c1.

(*
Anton's way computes the list of conclusions at each step, and as the list shrinks
it fails to include all the elements


(* isCorrectLastStep function *)
Definition isCorrectLastStep (ass : list clause) (p : ProofStep) (pl : PreProof) : bool :=
  match p with
  | ass n => ltb n (length ass)
  | res n m =>
    let conclusionpl := conclusions ass [] pl in
    let lengthConcll := length conclusionpl in
    andb (ltb n lengthConcll)
         (andb (ltb m lengthConcll)
               (isRes (findConclusion n conclusionpl) (findConclusion m conclusionpl)))
  end.

(* Example usage: *)
Example step0 : ProofStep := ass 0.
Example step1 : ProofStep := ass 1.
Example step2 : ProofStep := res 0 1.
Compute isCorrectLastStep [[pos "a"]] step0 [step0].
Compute isCorrectLastStep [[pos "a"];[neg "a"]] step2 [step0; step1; step2].

(* isCorrect function *)
Fixpoint isCorrect (ass : list clause) (pl : PreProof) : bool :=
  match pl with
  | [] => true
  | p :: l => andb (isCorrectLastStep ass p pl) (isCorrect ass l)
  end.

(* Example usage: *)
Compute isCorrect [[pos "a"];[neg "a"]] [step0; step1; step2].
*)

(* isCorrectLastStep function *)
Definition isCorrectLastStep (ass : Assumption) (conclusionpl : Conclusion) (p : ProofStep) (pl : PreProof) : bool :=
  match p with
  | ass n => ltb n (length ass)
  | res n m =>
    let lengthConcll := length conclusionpl in
    andb (ltb n lengthConcll)
         (andb (ltb m lengthConcll)
               (isRes (findConclusion n conclusionpl) (findConclusion m conclusionpl)))
  end.

Fixpoint checkAll (ass : Assumption)(conclusionpl : Conclusion) (pl : PreProof) : bool :=
  match pl with
  | [] => true
  | p :: l => andb (isCorrectLastStep ass conclusionpl p pl) (checkAll ass conclusionpl l)
  end.

Definition isCorrect (ass : Assumption) (pl : PreProof) : bool :=
  let conclusionpl := conclusions ass [] pl in
  checkAll ass conclusionpl pl.

Example step0 : ProofStep := ass 0.
Example step1 : ProofStep := ass 1.
Example step2 : ProofStep := res 0 1.

(* Example usage: *)
Compute isCorrect [[pos "a"];[neg "a"]] [step0; step1; step2]. (*True*)
Compute isCorrect [[pos "a"];[neg "a"]] [step0; step2]. (*False*)

(* atom definition *)
Definition atom (b : bool) : Prop := b = true.

Definition IsRes (c1 c2 : clause) : Prop :=
  atom (isRes c1 c2).

Definition IsCorrectLastStep (ass : Assumption) (p : ProofStep) (pl : PreProof) : Prop :=
  match p with
  | ass n => n < length ass
  | res n m =>
      let conclusionpl := conclusions ass [] pl in
      let lengthConcll := length conclusionpl in
      (n < lengthConcll) /\
      (m < lengthConcll) /\
      (IsRes (nth n conclusionpl []) (nth m conclusionpl []))
  end.

Fixpoint IsCorrect (ass : Assumption) (p : PreProof) : Prop :=
  match p with
  | [] => True
  | p :: pl => IsCorrectLastStep ass p pl /\ IsCorrect ass pl
  end.

Definition IsCorrectLastStep' (ass : Assumption) (p : ProofStep) (pl : PreProof) : Prop :=
  atom (isCorrectLastStep ass (conclusions ass [] pl) p pl).

Definition IsCorrect' (ass : Assumption) (p : PreProof) : Prop :=
  atom (isCorrect ass p).

(* Helper function to lift a boolean conjunction to a proposition conjunction *)
Definition lift_andb_to_and (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
  end.

(*
Definition isCorrect'ToIsCorrectLastStep (ass : Assumption) (p : ProofStep) (pl : PreProof)
(c : IsCorrectLastStep' ass p pl) : IsCorrectLastStep ass p pl :=
  match p with
  | ass n => c
  | res n m =>
      let c' := lift_andb_to_and c in
      match c' with
      | conj H1 H2 => conj H1 H2
      end
  end.

(* Translation of isCorrect'ToIsCorrect *)
Fixpoint isCorrect'ToIsCorrect (ass : Assumption) (p : PreProof) (c : IsCorrect' ass p) : IsCorrect ass p :=
  match p with
  | [] => I
  | p :: pl =>
      let q := conj c (isCorrect'ToIsCorrect ass pl (lift_andb_to_and c)) in
      match q with
      | conj H1 H2 => conj H1 H2
      end
  end.
*)
Fixpoint memlc_bool (l:literal) (c:clause) : bool :=
  match c with
    | nil => false
    | b :: m => if lit_eq_dec_bool l b then true else memlc_bool l m
  end.

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

Definition model_property (m : literal -> bool) : Prop :=
    forall l:literal, ( m l = true -> m (opposite l) = true -> False) /\ ( (m (opposite l) = false -> False) -> m l = true).
Definition models_clause (m : literal -> bool) (c : clause) : Prop :=
  model_property m -> exists l: literal, memlc_bool l c = true /\ m l = true.
Definition models_formula (m : literal -> bool) (f : formula) : Prop :=
  model_property m -> forall c: clause, memcf c f = true -> models_clause m c.

Definition entails (f : formula) (c : clause) : Prop :=
  (forall (m : literal -> bool), model_property m -> models_formula m f -> models_clause m c).

Fixpoint entailsl (ass : Assumption) (clauses : Conclusion) : Prop :=
  match clauses with
  | [] => True
  | c :: d => entails ass c /\ entailsl ass d
  end.

(*
Definition entails (f : formula) (c : clause) : bool :=
  match find_counterexample f with
  | None => models_clause_dec all_models c  (* Check if all models satisfy c *)
  | Some m => negb (models_clause_dec [m] c)  (* Check if m does not satisfy c *)
  end.

Fixpoint entailsl (ass : Assumption) (clauses : Conclusion) : bool :=
  match clauses with
  | [] => true
  | c :: d => entails_bool ass c && entailsl ass d
  end.
*)

(*
Axiom Unsatisfiable : list clause -> Prop.
*)

Definition Unsatisfiable (f : formula) : Prop :=
  forall m : literal -> bool, ~models_formula m f.

(* Define the entails⊥-unsat postulate *)
Axiom entails_bot_unsat : forall (ass : Assumption) (c : clause),
  entails ass c -> IsEmptyClause c = true -> Unsatisfiable ass.

(* Define the assCor postulate *)
(* The nth element of a clause is entailed from a clause should be true even for 
the default element since we use the true clause*)
Axiom assCor : forall (n : nat) (ass : list clause), entails ass (nthElInSeq n ass []).

(* Define the resCor postulate *)
(* If we have a resolution step of proofs which conclusion c1 and c2 and the assumptions 
are entail c1 and c2 then they entail as well the conclusion*)
Axiom resCor : forall (ass : Assumption) (c1 c2 : clause),
  entails ass c1 ->
  entails ass c2 ->
  isRes c1 c2 = true ->
  entails ass (toResConclusion c1 c2).

(* Define the trueentailed postulate *)
Axiom trueentailed : forall (ass : list clause), entails ass trueClause.

(*
(* Helper function for entailslToNth *)
Fixpoint entailslToNth_helper (ass : formula) (cl : list clause) (n : nat)
                               (p : entailsl ass cl) : clause :=
  match cl, p with
  | [], _ => []  (* Base case: empty list, return empty clause *)
  | x :: cl', conj p1 p2 =>
      match n with
      | O => x  (* Base case: n = 0, return the first clause *)
      | S n' => entailslToNth_helper ass cl' n' p2  (* Recursive case: decrement n and recurse *)
      end
  end.
*)

(* Helper function to determine the nth element or default *)
Definition nthElInSeq_clause (n : nat) (cl : list clause) : clause :=
  nthElInSeq n cl trueClause.

(* Helper function for entailslToNth *)
Fixpoint entailslToNth_helper (ass : formula) (cl : list clause) (n : nat) (p : entailsl ass cl) : 
entails ass (nthElInSeq n cl trueClause) :=
  match n, cl, p with
  | O, x :: _, conj prf _ => prf
  | S n', _ :: cl', conj _ p' => entailslToNth_helper ass cl' n' p'
  | _, [], _ => trueentailed ass  (* Handle the case where cl is empty *)
  end.

(* Top-level entailslToNth function *)
Definition entailslToNth (ass : formula) (cl : list clause) (n : nat) (p : entailsl ass cl) : 
entails ass (nthElInSeq n cl trueClause) :=
  entailslToNth_helper ass cl n p.

Lemma and_intro (P Q : Prop) : P -> Q -> P /\ Q.
Proof.
  intros. split; assumption.
Qed.

Lemma lemPreProofEntails : forall (ass : Assumption) (pl : PreProof),
  isCorrect ass pl = true -> entailsl ass (conclusions ass [] pl).
Proof.
  intros ass0 pl.
  revert ass0.
  induction pl.
  +
    (* pl = [] *)
    intros * Ha.
    exact I.
  +
    (* pl = a :: pl *)
    intros * Ha.
    simpl in * |- *.
    destruct a as [i | i j].
    ++
      (* a = ass i *)
      cbn in * |- *.
      eapply andb_true_iff in Ha.
      destruct Ha as (Hal & Har).
      unfold findAssumption in * |- *.
      admit.
    ++
      cbn in * |- *.



