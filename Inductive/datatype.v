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
Definition Result := list clause.

Definition add_clause (r : Result) (c : clause) : Result :=
  r ++ [c].

(* Function to retrieve the nth proof step in the preproof *)
Definition conclusion (ass : Assumption) (p : PreProof) (i : nat) : clause :=
  nth i ass []. (* Default to (res 0 0) if index is out of bounds *)

Definition findResult (r : Result) (i : nat) : clause :=
  nth i r []. (* Default to (res 0 0) if index is out of bounds *)

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

Definition computeresolution (step : ProofStep) (r : Result) : clause :=
  match step with
  | res i j =>
      let c1 := findResult r i in
      let c2 := findResult r j in
      remove_literal_from_clause_bool (opposite (clause_head c2 (pos ""))) c1
  | _ => []
  end.

Fixpoint toResults (ass : Assumption) (r : Result) (p : PreProof) : Result :=
  match p with
  | [] => r
  | step :: tl =>
      match step with
      | ass i => 
        let r' := add_clause r (conclusion ass p i) in
        toResults ass r' tl
      | _ =>
        let r' := add_clause r (computeresolution step r) in
        toResults ass r' tl
      end
  end.

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

Fixpoint length_result (r: Result) : nat :=
  match r with
  | nil => 0
  | _ :: m => S (length_result m)
  end.

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

(* Less than function for natural numbers *)
Definition lt (n m : nat) : bool :=
  Nat.ltb n m.

Definition correctconclusion (step : ProofStep) (ass : Assumption) (r : Result) (p : PreProof) : bool :=
  match step with
  | ass i => lt i (length_assumption ass)
  | res i j =>
      match lt i (length_result r), lt j (length_result r) with
      | true, true =>
          let c_j := findResult r j in
          is_unit_clause c_j &&
          is_literal_in_clause_bool (opposite (clause_head c_j (pos ""))) (findResult r i)
      | _, _ => false
      end
  end.

(* Function to check all steps of a PreProof *)
Fixpoint check (ass : Assumption) (r : Result) (p : PreProof) : bool :=
  match p with
  | [] => true
  | step :: tl =>
      if correctconclusion step ass r p then
        check ass r tl
      else
        false (* Incorrect conclusion, halt *)
  end.

Definition emptyR : Result := []. 

Definition correct (ass : Assumption) (p : PreProof) : bool :=
  let r := toResults ass emptyR p in
  check ass r p.

(* Function to get the last element of a PreProof *)
Fixpoint last_result (r : Result) : clause :=
  match r with
  | [] => [] (* Default value when list is empty; adjust as needed *)
  | [step] => step (* Last element in the list *)
  | _ :: tl => last_result tl (* Recursively process the tail *)
  end.

Definition lastconclusion (r : Result) : bool :=
  match last_result r with
  | [] => true
  | _ => false
  end.

Definition unsatcheck (ass : Assumption) (r : Result) (p : PreProof) : bool :=
  check ass r p && lastconclusion r.

Fixpoint memlc_bool (l:literal) (c:clause) : bool :=
    match c with
      | nil => false
      | b :: m => if lit_eq_dec_bool l b then true else memlc_bool l m
    end.

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

Definition model_property (m : literal -> bool) : Prop :=
    forall l:literal, ( m l = true -> m (opposite l) = true -> False) /\ ( (m (opposite l) = false -> False) -> m l = true).
Definition models_clause (m : literal -> bool) (c : clause) : Prop :=
  model_property m -> exists l: literal, memlc_bool l c = true /\ m l = true.
Definition models_formula (m : literal -> bool) (f : formula) : Prop :=
  model_property m -> forall c: clause, memcf c f = true -> models_clause m c.

Definition entails (f : formula) (c : clause) : Prop :=
  (forall (m : literal -> bool), model_property m -> models_formula m f -> models_clause m c).

Fixpoint entailList (ass : list clause) (clauses : Result) : Prop :=
  match clauses with
  | [] => True
  | c :: d => entails ass c /\ entailList ass d
  end.

Lemma add_clause_empty : forall c, add_clause emptyR c = [c].
Proof.
  intros c.
  unfold add_clause.
  reflexivity.
Qed.

Lemma conclusion_nth : forall ass n tl, conclusion ass (datatype.ass n :: tl) n = nth n ass [].
Proof.
  intros ass n tl.
  unfold conclusion.
  reflexivity.
Qed.

Lemma toResults_add_clause : 
  forall ass r p c, 
  toResults ass (add_clause r c) p = add_clause (toResults ass r p) c.
Proof.
Admitted.

Theorem correctness_implies_entailment :
  forall (p : PreProof) (ass : Assumption),
  correct ass p = true -> entailList ass (toResults ass emptyR p).
Proof.
  intros p ass Hcorrect.
  unfold correct in Hcorrect.
  remember (toResults ass emptyR p) as r eqn:Hr.
  assert (Hcheck: check ass r p = true) by (subst; assumption).
  clear Hcorrect.

  induction p as [| step tl IH].
  - (* Base case: p = [] *)
    simpl in *.
    subst.
    unfold entailList.
    exact I.

  - (* Inductive case: step :: tl *)
    simpl in *.
    destruct step as [n | n m].

    + (* Case: step = ass n *)
      subst.
      simpl in *.
      assert (Hlt: lt n (length_assumption ass) = true).
      {
        unfold correctconclusion in Hcheck.
        simpl in Hcheck.
        destruct (lt n (length_assumption ass)); try discriminate.
        reflexivity.
      }
      rewrite Hlt in Hcheck.

      (* Prove entailList for the first clause *)
      assert (Hconcl: nth n ass [] = nth n ass []).
      {
        reflexivity.
      }

      (* Use the induction hypothesis *)
      apply IH.
      *  
        admit.
      * (* Use the Hcheck assertion *)
        assumption.
    + admit.
Admitted.

  simpl in *.
  destruct step.


    + (* Case: step = ass n *)
      subst.
      unfold entailList.
      apply IH.
      * admit.
      * apply Hcheck.
    + (* Case: step = res n m *)
      simpl.
      admit.
Qed.


induction p as [| step tl IH].

- (* Base case: p = [] *)
    simpl in *. subst.
    unfold entailList. exact I.
- simpl in *.
  destruct step.
    + (* Case: step = ass n *)
      simpl.
      admit.
    + (* Case: step = res n m *)
      simpl.
      admit.
Qed.


