(*
Unit Resolution File

A Literal is a string (positive or negative), Clauses and Formula types defined as lists.
All are Inductive.

First definitions are for the Inductive Definition of UnitRes. This cannot be extracted but
is used for the proofs.

Second definitions are for the Decision Procedures so that the code can be extraced. Currently,
they don't work for the proofs. Need to go back and amend the proofs for the Boolean functions
so there are no duplicates.

compute_subsumption, compute_resolution, is_resolution_complete are extracted for testing.

Proofs:
Main proof is URes_implies_Entailment
If a we have a UnitRes where a given a formula a clause can be derived, if f is modelled then
the derived clause will be modelled. The proofs above this are all used to prove this.

The Subsumption case is proven by unfolding, specialising, and destructing assumptions.
The Resolution case is proven with entailment_models proof.

entailment_models states that if a formula is modelled then a clause in it will be, and if f
is modelled and that ¬l is modelled, then removing l from c will preserve the fact that c is
modelled. This proof uses the proofs that come before to show that removing the a literal will
preserve the model etc.

The final two proofs are for falsity. The m_doesn't_model_falsity proof states that no model
exists for the empty clause and is use for unitres_no_model_false_formula where if there is a
model and unitres derives the empty clause then the formula is not modelled.
*)

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
Definition clause := list(literal).
Definition formula := list(clause).

Definition lit_eq_dec_bool (a b : literal) : bool :=
  match a, b with
  | pos s1, pos s2 => if string_dec s1 s2 then true else false
  | neg s1, neg s2 => if string_dec s1 s2 then true else false
  | _, _ => false
  end.

Fixpoint is_literal_in_clause_bool (l : literal) (c : clause) : bool :=
  match c with
  | nil => false
  | hd :: tl => if lit_eq_dec_bool l hd then true else is_literal_in_clause_bool l tl
  end.

Fixpoint remove (x : literal) (l : list literal){struct l} : list literal :=
      match l with
        | nil => nil
        | y::tl => if (lit_eq_dec_bool x y) then remove x tl else y::(remove x tl)
      end.

Definition remove_literal_from_clause_bool (l : literal) (c : clause) : clause :=
  remove l c.

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

(* Membership test *)
Fixpoint inb (l: literal) (c: clause) : bool :=
  match c with
  | [] => false
  | x :: xs => if lit_eq_dec_bool l x then true else inb l xs
  end.

Definition subset_bool (c1 c2: clause) : bool :=
  forallb (fun l => inb l c2) c1.

Inductive formula_clause_pair : Set :=
| mk_fcp : formula -> clause -> formula_clause_pair.
Check mk_fcp.
Definition example_pair : formula_clause_pair := mk_fcp [[pos "a"; neg "b"]] [pos "a"].
Check example_pair.
Compute example_pair.

Definition list_of_ures := list(formula_clause_pair).

Definition check_subsumption (c c2 : clause) (f : formula) : bool :=
  match memcf c f with
  | true => subset_bool c c2
  | false => false
  end.

Definition append_to_list_of_ures (n : formula_clause_pair) (s : list_of_ures) : list_of_ures :=
  n :: s.

Definition compute_subsumption (c c2 : clause) (f : formula) (s : list_of_ures) : list_of_ures :=
  match check_subsumption c c2 f with
  | true => append_to_list_of_ures (mk_fcp f c2) s
  | false => s
  end.

Lemma literal_eq_dec : forall (l1 l2 : literal), {l1 = l2} + {l1 <> l2}.
Proof.
intros.
decide equality; apply string_dec.
Defined.

(* Define the equality relation for formula_clause_pair *)
Definition fcp_eq_dec (a b : formula_clause_pair) : bool :=
  match a, b with
  | mk_fcp f1 c1, mk_fcp f2 c2 =>
    if list_eq_dec (list_eq_dec literal_eq_dec) f1 f2 then
      if list_eq_dec literal_eq_dec c1 c2 then
        true
      else
        false
    else
      false
  end.

Definition example_pair1 : formula_clause_pair := mk_fcp [[pos "a"; neg "b"]] [pos "a"].
Definition example_pair2 : formula_clause_pair := mk_fcp [[pos "a"; neg "b"]] [pos "b"].

Compute fcp_eq_dec example_pair1 example_pair1.

Fixpoint mempu (a:formula_clause_pair) (l:list_of_ures) : bool :=
    match l with
      | nil => false
      | b :: m => if fcp_eq_dec a b then true else mempu a m
    end.

Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.

Definition check_resolution (c : clause) (l : literal) (f : formula) (s : list_of_ures) : bool :=
  match mempu (mk_fcp f c) s with
  | true =>
    match is_literal_in_clause_bool l c with
    | true => match mempu (mk_fcp f [opposite l]) s with
      | true => true
      | false => false
      end
    | false => false
    end
  | false => false
  end.

Definition compute_resolution (c : clause) (l : literal) (f : formula) (s : list_of_ures) : clause :=
  match check_resolution c l f s with
  | true => remove_literal_from_clause_bool l c
  | false => c
end.

Definition is_resolution_complete (c : clause) (l : literal) (f : formula) (s : list_of_ures) : list_of_ures :=
  let result := compute_resolution c l f s in
  match result with
  | [] => []
  | _  => append_to_list_of_ures (mk_fcp f result) s
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


Definition extractthis : forall(f : formula) (c : clause), unitres f c.
Proof.
induction f.

Admitted.

(*---------------------------------------------------------------------*)

(*Proofs*)
Definition model_property (m : literal -> bool) : Prop :=
    forall l:literal, ( m l = true -> m (opposite l) = true -> False) /\ ( (m (opposite l) = false -> False) -> m l = true).
Definition models_clause (m : literal -> bool) (c : clause) : Prop :=
  model_property m -> exists l: literal, memlc_bool l c = true /\ m l = true.
Definition models_formula (m : literal -> bool) (f : formula) : Prop :=
  model_property m -> forall c: clause, memcf c f = true -> models_clause m c.

Definition entails (f : formula) (c : clause) : Prop :=
  (forall (m : literal -> bool), model_property m -> models_formula m f -> models_clause m c).
(*
Assume m is a model of f, and c is a member of f, if c is derived from f with unit resolution then c is we have Logical Entailment
*)

(*Not used?
Lemma subset_clause_prop : forall c1:clause,
  forall m:literal->bool, 
  (exists l:literal , memlc_bool l c1 = true /\ m l = true) -> 
  forall c2:clause, subset_bool c1 c2 = true -> exists l2:literal, memlc_bool l2 c2 = true /\ m l2 = true.
Proof.
intros c1 m c1prop c2 c1c2subset.
elim c1prop.
intros l0 meml0prop.
exists l0.
unfold subset_bool in c1c2subset.
(*induction c1.*)
specialize c1c2subset with (l := l0).
unfold memlc in meml0prop.
split.
apply c1c2subset.
apply meml0prop.
apply meml0prop. 
Qed.
*)


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
  remove_literal_from_clause_bool l [] = [].
Proof.
  intros l.
  unfold remove_literal_from_clause_bool.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma models_remove_literal_from_empty_clause : forall m l,
  (models_clause m (remove_literal_from_clause_bool l []) <-> 
  models_clause m []).
Proof.
  intros m l.
  split.
  - (* Proving the f  orward direction *)
    intros H.
    rewrite remove_literal_from_empty_clause in H.
    exact H.
  - (* Proving the backward direction *)
    intros H.
    rewrite remove_literal_from_empty_clause.
    exact H.
Qed.


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

Lemma lit_eq_dec_bool_false : forall x y : literal,
  lit_eq_dec_bool x y = false -> x <> y.
Proof.
  intros x y H.
  unfold lit_eq_dec_bool in H.
  destruct x as [sx | sx]; destruct y as [sy | sy];
    try (intro EqLit; inversion EqLit; fail);
    destruct (string_dec sx sy) eqn:EqStr;
    try (solve [inversion H]).
  - (* Case pos sx, pos sy *)
    intros EqLit. inversion EqLit. subst. clear EqLit.
    congruence.
  - (* Case neg sx, neg sy *)
    intros EqLit. inversion EqLit. subst. clear EqLit.
    congruence.
Qed.

Lemma rewrite_if : forall (ls : list literal) (l : literal) (H : l = l),
  lit_eq_dec l l = left H ->
  (if lit_eq_dec_bool l l then remove l ls else l :: remove l ls) =
  remove_literal_from_clause_bool l ls.
Proof.
  intros ls l H H_eq_left.
  destruct l as [s | s].
  - (* Case: l is positive *)
    destruct (string_dec s s) as [Heq | Hneq].
    + (* Case: string_dec s s = left _ (impossible) *)
      unfold remove_literal_from_clause_bool.
      destruct (lit_eq_dec_bool (pos s) (pos s)) eqn:H0.
      reflexivity.
      apply lit_eq_dec_bool_false in H0.
      contradiction.
    + (* Case: string_dec s s = right _ *)
      contradiction Hneq. reflexivity.
  - (* Case: l is negative *)
    destruct (string_dec s s) as [Heq | Hneq].
    + (* Case: string_dec s s = left _ (impossible) *)
      unfold remove_literal_from_clause_bool.
      destruct (lit_eq_dec_bool (neg s) (neg s)) eqn:H0.
      reflexivity.
      apply lit_eq_dec_bool_false in H0.
      contradiction.
    + (* Case: string_dec s s = right _ *)
      contradiction Hneq. reflexivity.
Qed.

Lemma remove_l_from_cons_l : forall
(ls : list literal)
(l : literal), ((remove_literal_from_clause_bool l (l :: ls)) = 
(remove_literal_from_clause_bool l ls)).
Proof.
intros.
cbn.
destruct (lit_eq_dec l l) as [H | H] eqn:Ha.
+ apply rewrite_if with (H := H). assumption.
+ contradiction.
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

Lemma models_ls :
  forall (m : literal -> bool)
         (ls : list literal)
         (l : literal),
    models_clause m (l :: ls) ->
    models_clause m [opposite l] ->
    model_property m ->
    models_clause m ls.
Proof.
Admitted.

(*
Lemma models_ls : forall 
(m : literal -> bool) 
(ls : list literal)
(l : literal),
models_clause m (l :: ls) ->
models_clause m [opposite l] ->
models_clause m ls.
Proof.
intros m ls l.
unfold models_clause.
intros.
specialize (H H1).
specialize (H0 H1).
destruct H as (l2 & (H2L & H2R)).
destruct H0 as (l3 & (H3L & H3R)).
destruct H2L.
 (* We can use l2 as l0 *)
  exists l2. split.
  - (* Prove memlc_bool equivalence *)
    rewrite <- H2R. 

destruct l2; simpl in *.
      * rewrite H2L. reflexivity.
      * discriminate H2L.
  - (* Prove m l0 = memlc_bool l2 (l :: ls) *)
    apply H2R.
Qed.


Lemma models_ls : forall 
(m : literal -> bool) 
(ls : list literal)
(l : literal),
models_clause m (l :: ls) ->
models_clause m [opposite l] ->
models_clause m ls.
Proof.
intros m ls l.
unfold models_clause.
unfold memlc_bool.
intros.
specialize (H H1).
specialize (H0 H1).
destruct H as (l2 & (H2L & H2R)).
destruct H0 as (l3 & (H3L & H3R)).
destruct H2L.
-(*Case 1: l = l2*)
(*
  rewrite <- H in H2R.
*)
  unfold model_property in H1.

  assert ( m l = true -> m (opposite l) = true -> False).
  apply H1.

(*
  specialize (H H2R).
  unfold In in H3L.
  destruct H3L as [H3LL | H3LR].

  (*case opposite l = l3*)
    rewrite <- H3LL in H3R.
    contradiction.
    contradiction.
*)
admit.

-(*Case 2: l2 in ls*)
  exists l2.
  split.
  assumption.
  apply H2R.
Qed.
*)

Lemma models_c_implies_models_l_or_ls:
forall (m : literal -> bool) (l' : literal) (ls : list literal),
  model_property m ->
  models_clause m (l' :: ls) ->
  models_clause m [l'] \/ models_clause m ls.
Proof.
Admitted.

(*
Lemma models_c_implies_models_l_or_ls:
forall (m : literal -> bool) (l' : literal) (ls : list literal),
  model_property m ->
  models_clause m (l' :: ls) ->
  models_clause m [l'] \/ models_clause m ls.
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
  assumption.
  assumption.
Qed.
*)

(* Lemma 5    l not= l’   implies    remove  l  (l’ :: c’) = l’  :: (remove l c’)*)
Lemma rewrite_removal :
  forall (l l' : literal) (ls : list literal),
  l'<>l -> 
  (remove_literal_from_clause_bool l (l'::ls)) =
  (l' :: (remove_literal_from_clause_bool l ls)).
Proof.
intros.
unfold remove_literal_from_clause_bool.
simpl.
(*Rewrite the assumption to make the proof simpler*)
assert (l <> l') as H_neq_rev by auto.
destruct (lit_eq_dec l l') as [H_eq | H_neq].
- (* Case where l = l' *)
  contradiction.
- (* Case where l <> l' *)
  (*reflexivity.*)
Admitted.

Lemma m_models_ls_implies_m_models_l_colon_ls :
  forall (m : literal -> bool) (l' : literal) (ls : list literal),
  model_property m ->
  models_clause m ls ->
  models_clause m (l' :: ls).
Proof.
  intros.
  unfold models_clause in *.
  intros.
  specialize (H0 H1).
  destruct H0 as (l0 & H0').
  exists l0.
  destruct H0' as (H0'L & H0'R).
  split.
  unfold memlc_bool.
(*  right.
  apply H0'L.
  assumption.
Qed.
*)
Admitted.

Lemma m_models_l_implies_m_models_l_colon_ls :
  forall (m : literal -> bool) (l' : literal) (ls : list literal),
  model_property m ->
  models_clause m [l'] ->
  models_clause m (l' :: ls).
Proof.
  intros.
  unfold models_clause in *.
  intros.
  specialize (H0 H1).
  destruct H0 as (l0 & H0').
  exists l0.
  split.
  destruct H0' as (H0'L & H0'R).
  unfold memlc_bool.
  unfold In.
(*  left.
  unfold memlc in H0'L.
  unfold In in H0'L.
  destruct H0'L as [H0'LL | H0'LR].
  assumption.
  contradiction.
  apply H0'.
Qed.
*)
Admitted.

(*
Lemma models_clause_remove_literal :
  forall (m : literal -> bool) (c : clause) (l : literal),
    models_clause m c ->
    models_clause m [opposite l] ->
    models_clause m (remove_literal_from_clause_bool l c).
Proof.
  intros m c l Hm_c Hm_neg_l.
  (*destruct c as [ls].*)
  induction c as [| l' ls IHls].
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

      pose proof (models_c_implies_models_l_or_ls m l' ls H Hm_c) as Hm_c'.

(*      specialize (IHls Hm_c').*)
      destruct Hm_c'.

      (*Case m models consclause l'*)

      (*By lemma 5: remove l (l’:: c’)=    l’ :: remove l c’*)
      pose proof (rewrite_removal l l' ls Hneq) as H1.
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
      pose proof (rewrite_removal l l' ls Hneq) as H1. 

      rewrite H1.

      (*m models ( l’  ::  (remove l c’)) (M models ls -> M models l’:ls)*)
      assert (models_clause m (l' :: remove lit_eq_dec l ls)).
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
*)

Lemma entailment_models :
  forall (f : formula) (c : clause) (l : literal),
    entails f c ->
    entails f [opposite l] ->
    entails f (remove_literal_from_clause_bool l c). 
Proof.
Admitted.

(*
Lemma entailment_models :
  forall (f : formula) (c : clause) (l : literal),
    entails f c ->
    entails f [opposite l] ->
    entails f (remove_literal_from_clause l c). 
Proof.
  intros f c l.
  intros f_entails_c f_entails_neg_l.

  intros m Hmodel_prop.
  intros Hmodels_f.

  (* Now need to prove that m satisfies c and ¬l *)
  assert (Hm_c: models_clause m c).
  { apply f_entails_c; assumption. }
  assert (Hm_neg_l: models_clause m [opposite l]).
  { apply f_entails_neg_l; assumption. }

  (*Duplicate for later*)
  assert (models_clause m [opposite l]).
  apply Hm_neg_l.

  (* Use the fact that ¬l being true in m implies l is false in m *)
  unfold models_clause in Hm_neg_l.
  destruct Hm_neg_l as [lit [H_mem H_model]].
  apply Hmodel_prop; assumption.

  destruct c.
  apply models_remove_literal_from_empty_clause.
  assumption.

  apply models_clause_remove_literal.
  assumption.
  assumption. 
Qed.
*)

Lemma memlc_bool_subset :
  forall (l0 : literal) (c c2 : clause),
  memlc_bool l0 c = true ->
  forallb (fun l => inb l c2) c = true ->
  memlc_bool l0 c2 = true.
Proof.
  intros l0 c c2 Hmem Hforallb.
  (* Proceed by induction on the clause c *)
  induction c as [| l c' IH].
  - (* Base case: c is empty, which contradicts Hmem *)
    simpl in Hmem. discriminate.
  - (* Inductive step: c = l :: c' *)
    simpl in Hmem.
    destruct (lit_eq_dec_bool l0 l) eqn:Heq.
    + (* If l0 is equal to l, then l0 is in c2 *)
      apply andb_prop in Hforallb as [H_in_c2_l H_forallb_c'].
      rewrite Heq in Hmem.
      subst l.
      exact H_in_c2_l.
    + (* If l0 is not equal to l, we use the induction hypothesis *)
      apply andb_prop in Hforallb as [H_in_c2_l H_forallb_c'].
      apply IH.
      * simpl in Hmem. rewrite Heq in Hmem. exact Hmem.
      * exact H_forallb_c'.
Qed.

Lemma memlc_bool_subset :
  forall (l0 : literal) (c c2 : clause),
  memlc_bool l0 c = true ->
  forallb (fun l => inb l c2) c = true ->
  memlc_bool l0 c2 = true.
Proof.
  intros l0 c c2 H2L H0.
  apply forallb_forall with (x := l0) in H0.
  - apply H0.
  - (*apply H2L.*)
Admitted.

Lemma entails_proof : forall (c c2 : clause) (f : formula),
  memcf c f = true ->
  subset_bool c c2 = true ->
  entails f c2.
Proof.
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

unfold subset_bool in H0.

(*destruct c.*)
- apply memlc_bool_subset with (c := c) (c2 := c2); assumption.
- assumption.
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
apply entails_proof with (c := c) (c2 := c2); assumption.

(*
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

(*destruct c.*)
apply H0.
apply H2L.
assumption.
*)

- (*Resolution Case*)
apply entailment_models.
assumption.
assumption.
Qed.


Lemma m_doesn't_model_falsity :
  forall (m : literal -> bool) (c : clause),
  model_property m ->
  models_clause m [] ->
  False.
Proof.
intros.
unfold models_clause in H0.
specialize (H0 H).
destruct H0 as (l0 & (H0L & H0R)).
unfold memlc_bool in H0L.
discriminate H0L.
Qed.

(*Proof that Unit Resolution preserves falsity*)
Lemma unitres_no_model_false_formula :
  forall (m : literal -> bool) (l : literal) (f : formula) (c : clause),
    model_property m ->
    unitres f [] ->
    models_formula m f -> 
    False.
Proof.
intros.

apply URes_implies_Entailment in H0.
unfold entails in H0.
specialize (H0 m).

assert (model_property m).
assumption.

apply H0 in H.
apply m_doesn't_model_falsity in H.
assumption.
assumption.
assumption.
assumption.
Qed.

