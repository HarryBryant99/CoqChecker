Require Import Bool.
Require Import String.
Require Import List.
Import List.ListNotations.
Open Scope string_scope.
(* Class EqDec A : Type := {
  eq_dec: forall a1 a2 : A, {a1 = a2} + {a1 <> a2}
  }.
*)
Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.
Inductive clause : Type :=
  | consclause : list(literal) -> clause.
Inductive formula : Type :=
  | nilformula : formula
  | consformula : list(clause) -> formula.
Fixpoint contains_clause (f : formula) (cl : clause) : Prop :=
  match f with
  | nilformula => False
  | consformula cs  => In cl cs
  end.
Fixpoint is_unit_clause (l : literal) (c : clause)  : Prop :=
  match c with
  | consclause (nil) => False
  | consclause (l::nil)=> True
  | consclause _ => False
  end.
Fixpoint concat_clauses (c1 c2 : clause) : clause :=
  match c1 with
  | consclause ls1 => 
    match c2 with
     | consclause ls2 => consclause (ls1 ++ ls2)
    end
  end. 
Fixpoint is_literal_in_clause (l : literal) (c : clause) : Prop :=
  match c with
  | consclause ls => In l ls
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
  match c with
  | consclause ls => consclause (remove lit_eq_dec l ls)
  end.

Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.
Definition memlc (l : literal) (c : clause) : Prop :=
  match c with
  | consclause ls => In l ls
  end.
 
 
Definition subset (c1 c2 : clause) : Prop :=
  match c1 with
  | consclause ls1 => forall (l : literal), In l ls1 -> memlc l c2
  end.

Inductive unitres : formula -> clause -> Prop :=
| subsumption : forall c:clause, forall f:formula, contains_clause f c -> 
    forall c2:clause, subset c c2 -> unitres f c2
| resolution : forall c:clause, forall f:formula, unitres f c -> 
                forall l, is_literal_in_clause l c ->
                     unitres f (consclause [opposite l]) -> 
                      unitres f (remove_literal_from_clause l c) .


(*Proofs*)
Definition model_property (m : literal -> Prop) : Prop :=
    forall l:literal, ( m l -> m (opposite l) -> False) /\ ( (m (opposite l) -> False) -> m l).
Definition models_clause (m : literal -> Prop) (c : clause) : Prop :=
  model_property m -> exists l: literal, memlc l c /\ m l.
Definition models_formula (m : literal -> Prop) (f : formula) : Prop :=
  model_property m -> forall c: clause, contains_clause f c -> models_clause m c.

Definition entails (f : formula) (c : clause) : Prop :=
  (forall (m : literal -> Prop), model_property m -> models_formula m f -> models_clause m c).
(*
Assume m is a model of f, and c is a member of f, if c is derived from f with unit resolution then c is we have Logical Entailment
*)

Lemma subset_clause_prop : forall c1:clause,forall m:literal->Prop, (exists l:literal , memlc l c1 /\ m l) -> 
  forall c2:clause, subset c1 c2 -> exists l2:literal, memlc l2 c2 /\ m l2.
Proof.
intros c1 m c1prop c2 c1c2subset.
elim c1prop.
intros l0 meml0prop.
exists l0.
unfold subset in c1c2subset.
induction c1.
specialize c1c2subset with (l := l0).
unfold memlc in meml0prop.
split.
apply c1c2subset.
apply meml0prop.
apply meml0prop. 
Qed.

(*Lemma: Opposite is Idempotent*)
Lemma opp_is_idempotent:
forall l : literal, opposite( opposite l) =  l.
Proof.
destruct l.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

(* Function to check if two strings are equal *)
Definition string_beq (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

(* Function to check if two literals are equal *)
Definition literal_eqb (l1 l2 : literal) : bool :=
  match (l1, l2) with
  | (pos s1, pos s2) | (neg s1, neg s2) => string_beq s1 s2
  | (_, _) => false
  end.

Lemma remove_literal_from_empty_clause : forall l : literal,
  remove_literal_from_clause l (consclause []) = consclause [].
Proof.
  intros l.
  unfold remove_literal_from_clause.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma models_remove_literal_from_empty_clause : forall m l,
  (models_clause m (remove_literal_from_clause l (consclause [])) <-> 
  models_clause m (consclause [])).
Proof.
  intros m l.
  split.
  - (* Proving the forward direction *)
    intros H.
    rewrite remove_literal_from_empty_clause in H.
    exact H.
  - (* Proving the backward direction *)
    intros H.
    rewrite remove_literal_from_empty_clause.
    exact H.
Qed.

(*
1 goal
m : literal -> Prop
l' : literal
ls : list literal
l : literal
Hm_c : models_clause m (consclause (l' :: ls))
Hm_neg_l : models_clause m (consclause [opposite l])
IHls : models_clause m (consclause ls) ->
       models_clause m (remove_literal_from_clause l (consclause ls))
Heq : l' = l
______________________________________(1/1)
models_clause m (remove_literal_from_clause l (consclause (l' :: ls)))
*)

Theorem remove_equals : forall (l : literal) (ls : list literal),
(remove lit_eq_dec l (l :: ls) = 
remove lit_eq_dec l ls).
Proof.
Search (remove _ _ (_::_)). 
apply remove_cons.
Qed.

Lemma remove_l_from_cons_l : forall
(ls : list literal)
(l : literal), ((remove_literal_from_clause l (consclause (l :: ls))) = 
(remove_literal_from_clause l (consclause ls))).
Proof.
intros.
cbn.
destruct (lit_eq_dec l l) as [H | H] eqn:Ha.
reflexivity.
contradiction.
Qed.

(*1 goal
m : literal -> Prop
ls : list literal
l : literal
Hm_c : models_clause m (consclause (l :: ls))
Hm_neg_l : models_clause m (consclause [opposite l])
IHls : models_clause m (consclause ls) ->
       models_clause m (remove_literal_from_clause l (consclause ls))
______________________________________(1/1)
models_clause m (consclause ls)
*)

Lemma models_ls : forall 
(m : literal -> Prop) 
(ls : list literal)
(l : literal),
models_clause m (consclause (l :: ls)) ->
models_clause m (consclause [opposite l]) ->
models_clause m (consclause ls).
Proof.
intros m ls l.

unfold models_clause.

unfold memlc.

intros.

specialize (H H1).
specialize (H0 H1).

destruct H as (l2 & (H2L & H2R)).
destruct H0 as (l3 & (H3L & H3R)).

destruct H2L.

-(*Case 1: l = l2*)
  rewrite <- H in H2R.

  unfold model_property in H1.

  assert ( m l -> m (opposite l) -> False).
  apply H1.

  specialize (H0 H2R).
  unfold In in H3L.
  destruct H3L as [H3LL | H3LR].

  (*case opposite l = l3*)
    rewrite <- H3LL in H3R.
    contradiction.
    contradiction.

-(*Case 2: l2 in ls*)
  exists l2.
  split.
  assumption.
  apply H2R.
Qed.

Lemma models_c_implies_models_l_or_ls:
forall (m : literal -> Prop) (l l' : literal) (ls : list literal),
  model_property m ->
  models_clause m (consclause (l' :: ls)) ->
  models_clause m (consclause [l']) \/ models_clause m (consclause ls).
Proof.
intros.
destruct H0.
assumption.
destruct H0 as [Ha Hb].
destruct Ha.

-(* Case H0: l' = x)*)
  rewrite <- H0 in Hb.
  unfold models_clause.
  left.
  exists l'.
  split.
  unfold memlc.
  simpl.
  left.
  reflexivity.
  assumption.

-(* Case H0: in x ls)*)
  unfold models_clause.
  right.
  intros.
  exists x.
  split.
  unfold memlc.
  assumption.
  assumption.
Qed.

(* Lemma 5    l not= l’   implies    remove  l  (l’ :: c’) = l’  :: (remove l c’)*)
Lemma five :
  forall (l l' : literal) (ls : list literal),
  l'<>l -> 
  (remove_literal_from_clause l (consclause (l'::ls))) =
  (consclause (l' :: (remove lit_eq_dec l ls))).
Proof.
intros.
unfold remove_literal_from_clause.
simpl.
(*Rewrite the assumption to make the proof simpler*)
assert (l <> l') as H_neq_rev by auto.
destruct (lit_eq_dec l l') as [H_eq | H_neq].
- (* Case where l = l' *)
  contradiction.
- (* Case where l <> l' *)
  reflexivity.
Qed.

Lemma m_models_ls_implies_m_models_l_colon_ls :
  forall (m : literal -> Prop) (l' : literal) (ls : list literal),
  model_property m ->
  models_clause m (consclause ls) ->
  models_clause m (consclause (l' :: ls)).
Proof.
  intros.
  unfold models_clause in *.
  intros.
  specialize (H0 H1).
  destruct H0 as (l0 & H0').
  exists l0.
  destruct H0' as (H0'L & H0'R).
  split.
  unfold memlc.
  unfold In.
  right.
  apply H0'L.
  assumption.
Qed.

Lemma m_models_l_implies_m_models_l_colon_ls :
  forall (m : literal -> Prop) (l' : literal) (ls : list literal),
  model_property m ->
  models_clause m (consclause [l']) ->
  models_clause m (consclause (l' :: ls)).
Proof.
  intros.
  unfold models_clause in *.
  intros.
  specialize (H0 H1).
  destruct H0 as (l0 & H0').
  exists l0.
  split.
  destruct H0' as (H0'L & H0'R).
  unfold memlc.
  unfold In.
  left.
  unfold memlc in H0'L.
  unfold In in H0'L.
  destruct H0'L as [H0'LL | H0'LR].
  assumption.
  contradiction.
  apply H0'.
Qed.

Lemma models_clause_remove_literal :
  forall (m : literal -> Prop) (c : clause) (l : literal),
    models_clause m c ->
    models_clause m (consclause [opposite l]) ->
    models_clause m (remove_literal_from_clause l c).
Proof.
  intros m c l Hm_c Hm_neg_l.
  destruct c as [ls].
  induction ls as [| l' ls IHls].
  - (* Base case: c is empty *)
    rewrite remove_literal_from_empty_clause.
    apply Hm_c.
  - (* Inductive case: c = l' :: ls *)
    destruct (lit_eq_dec l' l) as [Heq | Hneq].    
    + (* Case 1: l' = l *)
      rewrite Heq.
      rewrite remove_l_from_cons_l.
      subst.
      apply IHls.

      revert Hm_neg_l.
      revert Hm_c.
      apply models_ls. 
    + (* Case 2: l' != l *)

      unfold models_clause.
      intros.

      pose proof (models_c_implies_models_l_or_ls m l l' ls H Hm_c) as Hm_c'.

(*      specialize (IHls Hm_c').*)
      destruct Hm_c'.

      (*Case m models consclause l'*)

      (*By lemma 5: remove l (l’:: c’)=    l’ :: remove l c’*)
      pose proof (five l l' ls Hneq) as H1.
      rewrite H1.

      (*By  models l’ we get  m models ( l’  ::  remove l c’ ) and 
      therefore m models  ( remove l (l’ :: c’))*)
      apply m_models_l_implies_m_models_l_colon_ls.
      assumption.
      assumption.
      assumption.

      (*Case m models consclause ls*)

      (*Then m models (remove l c’)  by IH
      Therefore m models ( l’  ::  (remove l c’))*)
      specialize (IHls H0).

      (* Lemma 5: l not= l' implies remove l (l’ :: c’) = l’ :: (remove l c’)*)
      pose proof (five l l' ls Hneq) as H1. 

      rewrite H1.

      (*m models ( l’  ::  (remove l c’)) (M models ls -> M models l’:ls)*)
      assert (models_clause m (consclause (l' :: remove lit_eq_dec l ls))).
      apply m_models_ls_implies_m_models_l_colon_ls.
      assumption.
      apply IHls.

      unfold models_clause in H2.
      specialize (H2 H).
      destruct H2 as (l0 & (H2l & H2r)).
      exists l0.
      split.
      assumption.
      assumption.
Qed.

Lemma entailment_models :
  forall (f : formula) (c : clause) (l : literal),
    entails f c ->
    entails f (consclause [opposite l]) ->
    entails f (remove_literal_from_clause l c). 
Proof.
  intros f c l.
  intros f_entails_c f_entails_neg_l.

  intros m Hmodel_prop.
  intros Hmodels_f.

  (* Now need to prove that m satisfies c and ¬l *)
  assert (Hm_c: models_clause m c).
  { apply f_entails_c; assumption. }
  assert (Hm_neg_l: models_clause m (consclause [opposite l])).
  { apply f_entails_neg_l; assumption. }

  (*Duplicate for later*)
  assert (models_clause m (consclause [opposite l])).
  apply Hm_neg_l.

  (* Use the fact that ¬l being true in m implies l is false in m *)
  unfold models_clause in Hm_neg_l.
  destruct Hm_neg_l as [lit [H_mem H_model]].
  apply Hmodel_prop; assumption.

  destruct c.
  destruct l0.
  apply models_remove_literal_from_empty_clause.
  assumption.

  apply models_clause_remove_literal.
  assumption.
  assumption. 
Qed.

(*Goal: Unit Resolution (f, c) -> Logical Entailment (f, c)*)
Lemma URes_implies_Entailment :
  forall (f : formula) (c : clause),
  unitres f c ->
  entails f c.
Proof.
intros f c1 U.
induction U.

- (*Subsumption Case*)
unfold entails.
intros.
unfold models_formula in H2.
specialize (H2 H1).

specialize (H2 c H).
unfold models_clause in *.
intros.
specialize (H2 H1).
destruct H2 as (l0 & (H2L & H2R)).
exists l0.
split.

unfold subset in H0.

destruct c.
apply H0.
apply H2L.
assumption.

- (*Resolution Case*)
apply entailment_models.
assumption.
assumption.
Qed.



(*Proof that UnitResolution preserves falsity*)
Lemma unitres_no_model_false_formula :
  forall (m : literal -> Prop) (l : literal) (f : formula) (c : clause),
    ~ models_formula m f ->
    unitres f c ->
    ~ models_clause m c.
Proof.
intros m l f c.
intros.

induction H0.
-(*Subsumption Case*)
intro.

destruct H.

unfold models_formula.
intros.
unfold models_clause in *.
specialize (H2 H).
intros.
destruct H2 as (l0 & H2').
exists l0.
split.
unfold contains_clause in H3.
unfold memlc.

admit.
apply H2'.

contradiction.
-(*Resolution Case*)