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

Definition findAssumption (ass : Assumption) (i : nat) : clause :=
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

Fixpoint remove2 (x : literal) (l : list literal){struct l} : list literal :=
  match l with
    | nil => nil
    | y::tl => if (lit_eq_dec_bool x y) then remove2 x tl else y::(remove2 x tl)
  end.

Definition remove_literal_from_clause_bool (l : literal) (c : clause) : clause :=
  remove2 l c.

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
  c :: r.

(*
Fixpoint conclusions (ass : Assumption) (r : Conclusion) (p : PreProof) : Conclusion :=
  match p with
  | [] => r
  | step :: tl =>
      match step with
      | ass i => 
        let r' := add_clause r (findAssumption ass i) in
        conclusions ass r' tl
      | _ =>
        let r' := add_clause r (get_k step) in
        conclusions ass r' tl
      end
  end.
*)


Fixpoint conclusions (ass : Assumption)(p : PreProof) : Conclusion :=
  match p with
  | [] => []
  | step :: tl =>
      match step with
      | ass i => 
        (findAssumption ass i) :: conclusions ass tl
      | res _ _ k =>
        k :: conclusions ass tl
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
Definition isCorrectLastStep (ass : Assumption) (conclusionpl : Conclusion) 
(p : ProofStep): bool :=
  match p with
  | ass n => ltb n (length ass)
  | res n m k =>
    let lengthConcll := length conclusionpl in
    andb (ltb n lengthConcll)
         (andb (ltb m lengthConcll)
               (isRes (findConclusion n conclusionpl) (findConclusion m conclusionpl) k))
  end.

(*
Fixpoint checkAll (ass : Assumption) (conclusionpl : Conclusion) (pl : PreProof) : bool :=
  match pl with
  | [] => true
  | p :: l => andb (isCorrectLastStep ass conclusionpl p pl) (checkAll ass conclusionpl l)
  end.
*)

Lemma andatomic1 : forall (a b : bool),
andb a b = true -> a = true.
Proof.
intros.
destruct a.
reflexivity.
destruct H.
split.
Qed.

Lemma andatomic2 : forall (a b : bool),
andb a b = true -> b = true.
Proof.
intros.
destruct b.
reflexivity.
destruct a.
destruct H.
split.
destruct H.
split.
Qed.

Fixpoint checkAll (ass : Assumption) (pl : PreProof) : bool :=
  match pl with
  | [] => true
  | p :: l => andb (isCorrectLastStep ass (conclusions ass l) p) (checkAll ass l)
  end.
(*was conclusions ass l*)

(*1 goal
ass0 : Assumption
n : nat
p : list ProofStep
H : ass n :: p <> []
H0 : checkAll ass0 (ass n :: p) = true
IHp : p <> [] ->
      checkAll ass0 p = true ->
      unitres ass0 (last_step (conclusions ass0 p))
______________________________________(1/1)
ltb n (length ass0) = true
*)
Lemma checkall_implies_ltb : forall (ass0 : Assumption) (p : PreProof) (n : nat),
checkAll ass0 (ass n :: p) = true -> ltb n (length ass0) = true.
Proof.
intros.
unfold checkAll in H.
apply andatomic1 in H.
destruct H.
unfold isCorrectLastStep.
reflexivity.
Qed.

Lemma successor : forall (a b : nat),
a = b -> S a = S b.
Proof.
intros.
congruence.
Qed.

Lemma lengthp : forall (ass0 : Assumption) (p : PreProof),
length (conclusions ass0 p) = length p.
Proof.
intros.
induction p.
+
simpl.
reflexivity.
+
(*Lemma:
length (conclusions ass0 (a :: p)) = S(length (conclusions ass0 p))
*)
destruct a.
-
unfold conclusions.
unfold length.
apply successor.
Admitted.

Lemma checkall_resolution1 : forall (ass0 : Assumption) (p : PreProof) (i j: nat) (k : clause),
checkAll ass0 (res i j k :: p) = true -> ltb i (length p) = true.
Proof.
intros.
unfold checkAll in H.
apply andatomic1 in H.
apply andatomic1 in H.
destruct H.
unfold isCorrectLastStep.
Admitted.

(*
need to check j and that k is the correct result.
*)

Example list_ass : Assumption := [[pos "a"];[neg "a"]].
Example step0 : ProofStep := ass 0.
Example step1 : ProofStep := ass 1.
Example step2 : ProofStep := res 0 1 [].
Example step3 : ProofStep := res 0 1 [pos "a"].
Compute checkAll list_ass [step0; step1; step2].

Compute conclusions list_ass [step0; step1; step2].

(* atom definition *)
Definition atom (b : bool) : Prop := b = true.

Definition IsRes (c1 c2 k: clause) : Prop :=
  atom (isRes c1 c2 k).

Definition IsCorrectLastStep (ass : Assumption) (p : ProofStep) (pl : PreProof) : Prop :=
  match p with
  | ass n => n < length ass
  | res n m k =>
      let conclusionpl := conclusions ass pl in
      let lengthConcll := length conclusionpl in
      (n < lengthConcll) /\
      (m < lengthConcll) /\
      (IsRes (nth n conclusionpl []) (nth m conclusionpl []) k)
  end.

Fixpoint IsCorrect (ass : Assumption) (p : PreProof) : Prop :=
  match p with
  | [] => True
  | p :: pl => IsCorrectLastStep ass p pl /\ IsCorrect ass pl
  end.

Definition IsCorrectLastStep' (ass : Assumption) (p : ProofStep) (pl : PreProof) : Prop :=
  atom (isCorrectLastStep ass (conclusions ass pl) p).

(* Helper function to lift a boolean conjunction to a proposition conjunction *)
Definition lift_andb_to_and (b : bool) : Prop :=
  match b with
  | true => True
  | false => False
  end.

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

(*New Proof*)

Definition subset (c1 c2 : clause) : Prop :=
  forall l : literal, In l c1 -> In l c2.

Fixpoint is_literal_in_clause (l : literal) (c : clause) : Prop :=
  match c with
  | nil => False
  | hd :: tl => hd = l \/ is_literal_in_clause l tl
  end.

Lemma lit_eq_dec : forall a b : literal, {a = b} + {a <> b}.
Proof.
   intros a b.
   destruct a as [s1 | s1]; destruct b as [s2 | s2].
   - destruct (string_dec s1 s2).
    + left. rewrite e. reflexivity.
    + right. intro H. inversion H. contradiction.
   - right. intro H. inversion H.
   - right. intro H. inversion H.
   - destruct (string_dec s1 s2).
    + left. rewrite e. reflexivity.
    + right. intro H. inversion H. contradiction.
Qed.
(* Instance literal_EqDec : EqDec literal :=
  { eq_dec: forall x y : literal, {x = y} + {x <> y}}.
*)
Definition remove_literal_from_clause (l : literal) (c : clause) : clause :=
  remove lit_eq_dec l c.

Inductive unitres : formula -> clause -> Prop :=
| subsumption : forall (c c2 : clause) (f : formula),
    In c f ->
    subset c c2 ->
    unitres f c2
| resolution : forall (c : clause) (l : literal) (f : formula),
    unitres f c ->
    is_literal_in_clause l c ->
    unitres f (cons (opposite l) []) ->
    unitres f (remove_literal_from_clause l c).

Definition last_step (s : Conclusion) : clause :=
  match s with
  | [] => [] (* Default value when list is empty; adjust as needed *)
  | a :: tl => a (* Recursively process the tail *)
  end.

(*
1 goal
ass0 : Assumption
n : nat
p : list ProofStep
H : ass n :: p <> []
H0 : isCorrect ass0 (ass n :: p) = true
IHp : p <> [] ->
      isCorrect ass0 p = true ->
      unitres ass0 (last_step (conclusions ass0 p))
______________________________________(1/1)
In (nth n ass0 []) ass0
*)
Lemma in_assumptions : forall (ass0 : Assumption)  (n : nat),
ltb n (length ass0) = true -> In (nth n ass0 []) ass0.
Proof.
intros.
Admitted.

Inductive unitresList : Assumption -> Conclusion -> Prop :=
| empty : forall (ass : Assumption), unitresList ass []
| consURL : forall (ass : Assumption) (cl : Conclusion) (c : clause),
    unitresList ass cl -> unitres ass c -> unitresList ass (c :: cl).

Lemma preproof_implies_unitreslist : forall (ass : Assumption) (p : PreProof),
  p <> [] ->
  checkAll ass p = true -> 
  unitresList ass (conclusions ass p).
Proof.
intros.
induction p.
+ unfold conclusions.
  apply empty.
+ 
  induction p.
  *
  destruct a.
  - unfold conclusions.
    apply consURL.
    apply empty.
    apply subsumption with (findAssumption ass0 n).
      apply in_assumptions.
      apply checkall_implies_ltb with [].
      assumption.
      unfold subset.
      intros.
      assumption.
  - unfold conclusions.
    apply consURL.
    apply empty.
    
  *
  destruct a.
  -
    unfold conclusions.
(*   consURL   (subsumption ...) (unitresList ass (conclusions ass0 p))*)
    apply consURL.
    * apply IHp.

    * apply subsumption with (findAssumption ass0 n).
      apply in_assumptions.
      apply checkall_implies_ltb with p.
      assumption.
      unfold subset.
      intros.
      assumption.
Admittwed.



Lemma preproof_implies_unitres : forall (ass : Assumption) (p : PreProof),
  p <> [] ->
  checkAll ass p = true -> 
  unitres ass (last_step (conclusions ass p)).
Proof.
intros.
induction p.
+ contradiction.
+ simpl.
  destruct a.
  -  
    apply subsumption with (last_step (findAssumption ass0 n :: conclusions ass0 p)).
    * unfold findAssumption.
      unfold last_step.
      apply in_assumptions.
      apply checkall_implies_ltb with p.
      assumption.
    * unfold subset.
      intros.
      assumption.
  -
    
    



Fixpoint entailsl (ass : Assumption) (clauses : Conclusion) : Prop :=
  match clauses with
  | [] => True
  | c :: d => entails ass c /\ entailsl ass d
  end.

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
Axiom resCor : forall (ass : Assumption) (c1 c2 k: clause),
  entails ass c1 ->
  entails ass c2 ->
  isRes c1 c2 k = true ->
  entails ass (toResConclusion c1 c2).

(* Define the trueentailed postulate *)
Axiom trueentailed : forall (ass : list clause), entails ass trueClause.

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

(*
Lemma entails_empty_assumption : forall i : nat,
  entails [] (match i with
             | 0 => []
             | _ => []
             end) /\ True.
Proof.
  intros i. split.
  - (* entails [] (match i with | 0 => [] | _ => [] end) *)
    destruct i; simpl.
    + (* Case i = 0 *)
      unfold entails. intros m H H0.
      unfold models_clause. simpl.
      (* models_clause m [] is trivially true *)
      intros l Hl. inversion Hl.
    + (* Case i > 0 *)
      unfold entails. intros m H H0.
      unfold models_clause. simpl.
      (* models_clause m [] is trivially true *)
      intros l Hl. inversion Hl.
  - (* True *)
    auto.
Qed.
*)

Lemma entails_empty_assumption : forall i : nat,
  entails [] (match i with
             | 0 => []
             | _ => []
             end) /\ True.
Proof.
  intros i. split.
  - (* entails [] (match i with | 0 => [] | _ => [] end) *)
    destruct i; simpl.
    + unfold entails.

intros.
unfold models_formula in H0.
unfold memcf in H0.


      admit.
    + admit.
  - (* True *)
    auto.
Admitted.

(*
Lemma rewrite_conclusions : forall (ass0 : Assumption) (i : nat),
  entailsl ass0 (conclusions ass0 [nth i ass0 []] []) <-> 
  entailsl ass0 (conclusions ass0 [] []).
Proof.
  intros ass0 i.
  split.
  - (* => direction *)
    intros H.
    destruct (ass0) eqn:Heq.
    + (* ass0 is empty *)
      simpl in H.
      simpl.
      auto.
    + (* ass0 is not empty *)
      simpl in H.
      destruct i.
      * (* i = 0 *)
        simpl in *. auto.
      * (* i > 0 *)
        simpl in *. auto.
  - (* <- direction *)
    intros H.
    destruct ass0 eqn:Heq.
simpl. simpl in H. apply entails_empty_assumption.
Admitted.
*)

(*
Lemma rewrite_conclusions : forall (ass0 : Assumption) (i : nat),
  entailsl ass0 (conclusions ass0 [nth i ass0 []] []) <->
  entailsl ass0 (conclusions ass0 [] []).
Proof.
  intros ass0 i.
  split.
  - (* => direction *)
    intros H.
    (* Here, you might want to consider cases based on whether ass0 is empty or not *)
    (* Case 1: ass0 is empty *)
    destruct (ass0) eqn:Heq.
    + (* ass0 is empty *)
      simpl in H.
      simpl.
      auto.
    + (* ass0 is not empty *)
      simpl in H.
      destruct i.
      * (* i = 0 *)
        simpl in *. auto.
      * (* i > 0 *)
        simpl in *. auto.
  - (* <= direction *)
    intros H.
    destruct ass0 as [| c0 ass'] eqn:Heq.
    + (* ass0 = [] *)
      simpl. simpl in H. apply entails_empty_assumption.
    + (* ass0 = c0 :: ass' *)
      simpl. simpl in H.
      destruct i.
      * (* i = 0 *)
        simpl in *. auto.
      * (* i > 0 *)
        simpl in *. auto.
Admitted.
*)

Lemma rewrite_conclusions : forall (ass0 : Assumption) (pl : PreProof) (i : nat),
entailsl ass0 (conclusions ass0 [nth i ass0 []] pl) <->
entailsl ass0 (conclusions ass0 [] pl).
Proof.
  intros ass0 pl.
  revert ass0.
  induction pl as [| a pl' IHpl']; intros ass0 i.
  - (* Base case: pl = [] *)
    simpl. split. trivial. 
    intros.
    split.
    + admit.
    + assumption.
  - simpl.
    destruct a as [j | j k l].
    + (* a = ass j *)
      admit.
    + (* a = res j k l *)
      simpl.
      admit.
Admitted.

Lemma checkAll_implies_isCorrect : forall (ass : Assumption) (pl : PreProof) (c : Conclusion),
  checkAll ass c pl = true -> isCorrect ass pl = true.
Proof.
  intros ass pl c H.
  induction pl as [| p l IHpl].
  - simpl. reflexivity.
  - simpl in H. destruct p as [n | n m k].
    + (* Case p = ass n *)
      simpl. apply andb_true_iff in H as [H1 H2].
      rewrite andb_true_iff. split; assumption.
    + (* Case p = res n m k *)
      simpl. apply andb_true_iff in H as [H1 H2].
      apply andb_true_iff. split; assumption.
Admitted.

Lemma lemPreProofEntails : forall (ass : Assumption) (pl : PreProof),
  isCorrect ass pl = true -> entailsl ass (conclusions ass [] pl).
Proof.
  intros ass0 pl.
  revert ass0.
  induction pl.
  + (*Base Case*)
    (* pl = [] *)
    intros * Ha.
    exact I.
  + (*Inductive Case*)
    (* pl = a :: pl *)
    intros * Ha.
    simpl in * |- *.
    destruct a as [i | i j k].
    ++
      (* a = ass i *)
      cbn in * |- *.
      eapply andb_true_iff in Ha.
      destruct Ha as (Hal & Har).
      unfold findAssumption in * |- *.

      rewrite rewrite_conclusions.
      apply IHpl.

      apply checkAll_implies_isCorrect with (c := conclusions ass0 [nth i ass0 []] pl).
      assumption.
    ++
      admit.



