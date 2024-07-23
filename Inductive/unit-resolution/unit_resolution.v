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
Fixpoint unit_literal_in_clause (l : literal) (c : clause)  : Prop :=
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
Lemma eq_dec : forall a b : literal, {a = b} + {a <> b}.
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
Fixpoint remove_literal_from_clause (l : literal) (c : clause) : clause :=
  match c with
  | consclause ls => consclause (remove eq_dec l ls)
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
| subsumption : forall c:clause, forall f:formula, contains_clause f c -> forall c2:clause, subset c c2 -> unitres f c2
| resolution : forall c:clause, forall f:formula, unitres f c -> 
                forall l, is_literal_in_clause l c -> 
                  forall c2:clause, unit_literal_in_clause (opposite l) c2 ->
                     unitres f c2 -> unitres f (remove_literal_from_clause l c) .


Definition subsumption_unitres (c : clause) (f : formula) (c2 : clause) : Prop :=
  forall (H : contains_clause f c), subset c c2 -> unitres f c2.
(* 
Compute subsumption_unitres
  (consclause [pos "p"; neg "q"; pos "r"])
  (consformula [consclause [pos "p"; neg "q"; pos "r"]; consclause [neg "p"; pos "q"; pos "s"]; consclause [pos "p"; pos "q"; neg "r"]])
  (consclause [pos "p"; neg "q"; pos "r"; neg "s"]).
Definition resolution_unitres (c : clause) (f : formula) (l : literal) (c2 : clause) : Prop :=
  forall (H : unitres f c),
  forall (H_lit : is_literal_in_clause l c),
  forall (H_unit : unit_literal_in_clause (opposite l) c2),
  unitres f (remove_literal_from_clause l c).
Compute resolution_unitres
  (consclause [pos "p"; neg "q"; pos "r"])
  (consformula [consclause [pos "p"; neg "q"; pos "r"]; consclause [neg "p"; pos "q"; pos "s"]; consclause [pos "p"; pos "q"; neg "r"]])
  (pos "r")
  (consclause [pos "p"; neg "q"; pos "r"; neg "s"]).
*)
(*Proofs*)
Definition model_property (m : literal -> Prop) : Prop :=
    forall l:literal, ( m l -> m (opposite l) -> False) /\ ( (m (opposite l) -> False) -> m l).
Definition models_clause (m : literal -> Prop) (c : clause) : Prop :=
  model_property m -> exists l: literal, memlc l c /\ m l.
Definition models_formula (m : literal -> Prop) (f : formula) : Prop :=
  model_property m -> forall c: clause, contains_clause f c -> models_clause m c.

Definition entails (f : formula) (c : clause) : Prop :=
  (forall (m : literal -> Prop), model_property m -> models_formula m f -> models_clause m c).
 
 
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

(*
Lemma unit_literal_in_clause_opposite_eq : forall l l0,
  unit_literal_in_clause (opposite l) (consclause l0) -> consclause l0 = consclause [opposite l].
Proof.
  intros l l0 H.
  unfold unit_literal_in_clause in H.

  destruct l0.
  destruct l.
  contradiction.
  contradiction.


  destruct l1 as [|].
  simpl in H.

  destruct l1 as [|].

  destruct l0.

(*
  induction l0 as [| hd tl IH].
  induction l.
  contradiction.
  contradiction.
*)
Qed.
*)

Lemma entailment_models :
  forall (f : formula) (c : clause) (l : literal),
    entails f c ->
    entails f (consclause [opposite l]) ->
    entails f (remove_literal_from_clause (opposite l) c).
Proof.
  intros f c l.
  intros f_entails_c f_entails_neg_l.

  intros m Hmodel_prop.
  intros Hmodels_f.

  (* Now we need to prove that m satisfies c and ¬l *)
  assert (Hm_c: models_clause m c).
  { apply f_entails_c; assumption. }
  assert (Hm_neg_l: models_clause m (consclause [opposite l])).
  { apply f_entails_neg_l; assumption. }

(* We assert that l is false in m *)
assert (~ m l) as H_not_m_l.
{

 }

(* Now, we conclude that l is false in m *)
apply Hm_neg_l.




intros f c l Hentails_c Hentails_opposite_l m Hm_prop Hmodels_f.
  specialize (Hentails_c m Hm_prop Hmodels_f) as [l' [Hl' Hm_l']].
  specialize (Hentails_opposite_l m Hm_prop Hmodels_f) as [l'' [Hl'' Hm_opposite_l']].
  apply Hm_prop.
  apply Hm_prop.

  unfold models_clause.
  intros Hm_prop'.
  exists l'.
  split.
  - apply Hl'.
  - intros Hm_l'.
    apply (remove_literal_from_clause_preserve_models m (opposite l) c l').
    + intros H_eq.
      apply Hm_l'.
      rewrite <- H_eq.
      apply Hm_opposite_l'.
    + assumption.
Qed.


Theorem unit_resolution_soundness : forall (f : formula) (c : clause),
    unitres f c ->
    entails f c.
Proof.
 
    unfold entails.
    intros f c1 unitres_c1.

    (*elim unitres_c1.*)

    induction unitres_c1. 

    (* Subsumption case *)

    unfold models_formula, models_clause in *.

    intros H_model_clause h_model_clause_prop h_model_prop h_model_clause_prop2.
    specialize h_model_prop with (c := c).
    specialize (h_model_prop h_model_clause_prop H h_model_clause_prop) .
    elim h_model_prop.
    intros l0 l0prop.
    destruct (subset_clause_prop c H_model_clause h_model_prop c2).
    apply H0.
    exists x.
    apply H1.
 
    (* Resolution case *)
    intros m m_prop m_f_prop.
    unfold models_formula, models_clause, model_property in *.
    intros inst_model_prop.

(*
prove a lemma: Anton proof with cases


if from f you can prove c,
from f you can proof ¬l,
can prove c / l

if in a model holds c, and l is false, f / c holds


*)











    (* Since m (opposite l) must hold, there must be another literal in c 
    other than l which holds in the model *)
    intros m H_model_prop H_model_formula.
    unfold models_formula, models_clause, model_property in *.
    
    intros H_model_property.
    destruct (remove_literal_from_clause l c) eqn:H_remove.
    destruct l0 as [|l1 ls] eqn:Heq_l0.

(* Case: l0 is empty *)
  (* Since l0 is empty, consclause [] should not be the result of removing l from c *)
  (* We can use this fact to derive a contradiction *)
  rewrite <- H_remove in *.
  destruct c as [la ls].
  destruct la as [| l1 ls].
  contradiction.





    